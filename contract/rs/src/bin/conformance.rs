//! Conformance CLI (rs) — a dev/CI artifact, NOT part of the published lib API.
//!
//! `conformance v1` protocol (ADR 0006): `conformance <family>` reads the family's
//! vector JSON on stdin and writes one NDJSON line per case to stdout, in input
//! order. It bakes in the `demo_v1` profile and **ignores** any expected
//! `outcome`/`id` in the input — it computes its own. The language-agnostic harness
//! (`conformance/harness.mjs`) drives this (and the go/ts CLIs) as black boxes and
//! asserts each line against the hand-authored oracle.
//!
//!   check   : in `{program, cases:[{name, claim, derivation, limits?}]}`
//!             out `{"name":…,"outcome":"accept"|{"reject":"<code>"}}`
//!   account : in `{clauses:[{name, head, body}]}`
//!             out `{"name":…,"id":"<hex>"}`
//!
//! The theory-decision families (`arithmetic`, `list`, `term`, `text`, `compound`) share
//! one shape: each drives a standard checkable [`Theory`]'s `decide` over the shared
//! `vectors/<family>.json` `decisions` array.
//!   `<theory>`: in `{identity, owns, decisions:[{name, pred, args}]}`
//!             out one `{"name":…,"outcome":"holds"|{"fails":"<code>"}}` line per decision,
//!                 then `{"name":"__identity__","outcome":"<config_digest_hex>"}` pinning
//!                 the theory's identity config digest (zero for the single theories, the
//!                 ordered-membership digest for compound).

use logos_contract::intval::BigInt;
use logos_contract::{
    check, check_with_cert_context, check_with_cert_memo, ArithmeticTheory, BigDecimal, BodyLit,
    CertContext, CertId, CertSizeDecl, CheckLimits, CheckProfile, Clause, ClauseId,
    ClosedModelCert, ClosureWitness, CompoundTheory, CountLit, Derivation, Evidence, FiniteDomain,
    Goal, GroundLiteral, Hash, LeafOutcome, LeafVerifier, ListTheory, MapProgram, Node, NodeMeta,
    NonMemberProof, Outcome, PredicateRef, PredicateSet, Premise, ProjectSpec, RelationTable,
    StratumPrefix, Subst, SupportEdge, SupportRef, SupportWitness, Symbol, Term, TermTheory,
    TextTheory, Theory, TheoryOutcome, WorldMemo,
};
use std::collections::BTreeMap;
use std::io::Read;

// =============================== demo_v1 profile ===============================
// Baked into this CLI (behaviour can't be serialized). Identical to the spec's
// reference profile; the harness drives the same protocol against arche's own CLI,
// which bakes in arche's profile instead.

struct LtTheory;
// test-double: consumer(a less-than theory over atoms)
impl Theory for LtTheory {
    logos_contract::cannot_copy!(Theory, "the conformance binary's fixed comparison theory; the binary never rebinds or examines an engine");
    fn owns(&self, pred: &Symbol) -> bool {
        pred.bytes() == b"lt"
    }
    /// #3142: every decision completes (a byte comparison of two atoms).
    fn completion(&self, _pred: &Symbol) -> logos_contract::DecisionCompletion {
        logos_contract::DecisionCompletion::StopsAreTyped
    }
    fn decide(&self, atom: &GroundLiteral) -> TheoryOutcome {
        match atom.args.as_slice() {
            [a, b] => match (a.as_atom(), b.as_atom()) {
                (Some(a), Some(b)) if a.bytes() < b.bytes() => TheoryOutcome::Holds,
                _ => TheoryOutcome::Fails {
                    code: "not_less_than".into(),
                },
            },
            _ => TheoryOutcome::Fails {
                code: "lt_arity".into(),
            },
        }
    }
}

struct EdgeLeaves {
    extensional: PredicateSet,
}
impl EdgeLeaves {
    fn new() -> Self {
        EdgeLeaves {
            extensional: PredicateSet::from_iter(["edge"]),
        }
    }
}
// test-double: consumer(admits every leaf of its extensional set)
impl LeafVerifier<()> for EdgeLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _atom: &GroundLiteral, _evidence: &Evidence, _ctx: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
}

fn demo_profile(limits: CheckLimits) -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(LtTheory),
        leaves: Box::new(EdgeLeaves::new()),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits,
    }
}

/// The `negation_v1` profile (ADR 0007 vectors): EDB leaves named by the vector's
/// `extensional` list, attesting an EDB-of-record snapshot from the vector's `edb`
/// map (ADR 0007 §3.6); `lt` theory for builtin support refs. `denied`/`permit` are
/// intensional (rule heads).
struct NegLeaves {
    extensional: PredicateSet,
    edb: std::collections::BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
}
// test-double: consumer(admits every leaf of its extensional set and attests an EDB snapshot)
impl LeafVerifier<()> for NegLeaves {
    fn extensional(&self) -> &PredicateSet {
        &self.extensional
    }
    fn verify(&self, _atom: &GroundLiteral, _evidence: &Evidence, _ctx: &()) -> LeafOutcome {
        LeafOutcome::Admit
    }
    fn edb_snapshot(&self, pred: &Symbol, _ctx: &()) -> Option<logos_contract::Hash> {
        match self.edb.get(pred.bytes()) {
            Some(rows) => Some(logos_contract::edb_table_hash(pred, rows)),
            None if self.extensional.contains(pred) => {
                Some(logos_contract::edb_table_hash(pred, &[]))
            }
            None => None,
        }
    }
}

fn negation_profile(
    limits: CheckLimits,
    extensional: PredicateSet,
    edb: std::collections::BTreeMap<Vec<u8>, Vec<GroundLiteral>>,
) -> CheckProfile<()> {
    CheckProfile {
        theory: Box::new(negation_theory()),
        leaves: Box::new(NegLeaves { extensional, edb }),
        admit: Box::new(logos_contract::AlwaysAdmit),
        limits,
    }
}

// ============================ tiny JSON reader ===============================
// Self-contained so the binding stays serde-free (mirrors ontos's vector runners).

#[derive(Debug, Clone, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    // The parsed f64 AND the verbatim source literal. The literal is retained because an
    // exact integer near or beyond i64::MAX (e.g. the `is_boundary_i64_max` vector's
    // 9223372036854775807) is NOT representable in f64; the theory families recover it from
    // the source text via `int_i64`.
    Num(f64, String),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

struct P<'a> {
    b: &'a [u8],
    i: usize,
}
impl<'a> P<'a> {
    fn new(s: &'a str) -> Self {
        P {
            b: s.as_bytes(),
            i: 0,
        }
    }
    fn ws(&mut self) {
        while self.i < self.b.len() && matches!(self.b[self.i], b' ' | b'\t' | b'\r' | b'\n') {
            self.i += 1;
        }
    }
    fn value(&mut self) -> Json {
        self.ws();
        match self.b[self.i] {
            b'{' => self.obj(),
            b'[' => self.arr(),
            b'"' => Json::Str(self.string()),
            b't' => {
                self.i += 4;
                Json::Bool(true)
            }
            b'f' => {
                self.i += 5;
                Json::Bool(false)
            }
            b'n' => {
                self.i += 4;
                Json::Null
            }
            _ => self.num(),
        }
    }
    fn obj(&mut self) -> Json {
        self.i += 1;
        let mut out = Vec::new();
        self.ws();
        if self.b[self.i] == b'}' {
            self.i += 1;
            return Json::Obj(out);
        }
        loop {
            self.ws();
            let k = self.string();
            self.ws();
            self.i += 1; // :
            let v = self.value();
            out.push((k, v));
            self.ws();
            let c = self.b[self.i];
            self.i += 1; // , or }
            if c == b'}' {
                break;
            }
        }
        Json::Obj(out)
    }
    fn arr(&mut self) -> Json {
        self.i += 1;
        let mut out = Vec::new();
        self.ws();
        if self.b[self.i] == b']' {
            self.i += 1;
            return Json::Arr(out);
        }
        loop {
            out.push(self.value());
            self.ws();
            let c = self.b[self.i];
            self.i += 1; // , or ]
            if c == b']' {
                break;
            }
        }
        Json::Arr(out)
    }
    fn string(&mut self) -> String {
        self.i += 1;
        let mut s = String::new();
        while self.b[self.i] != b'"' {
            let c = self.b[self.i];
            if c == b'\\' {
                self.i += 1;
                let e = self.b[self.i];
                match e {
                    b'n' => s.push('\n'),
                    b't' => s.push('\t'),
                    b'r' => s.push('\r'),
                    b'"' => s.push('"'),
                    b'\\' => s.push('\\'),
                    b'/' => s.push('/'),
                    _ => s.push(e as char),
                }
                self.i += 1;
            } else {
                s.push(c as char);
                self.i += 1;
            }
        }
        self.i += 1;
        s
    }
    fn num(&mut self) -> Json {
        let start = self.i;
        while self.i < self.b.len()
            && matches!(
                self.b[self.i],
                b'0'..=b'9' | b'-' | b'+' | b'.' | b'e' | b'E'
            )
        {
            self.i += 1;
        }
        let lit = std::str::from_utf8(&self.b[start..self.i]).unwrap();
        Json::Num(lit.parse().unwrap(), lit.to_string())
    }
}
impl Json {
    fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(kvs) => kvs.iter().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    fn arr(&self) -> &[Json] {
        match self {
            Json::Arr(a) => a,
            _ => panic!("expected array, got {self:?}"),
        }
    }
    fn obj(&self) -> &[(String, Json)] {
        match self {
            Json::Obj(kvs) => kvs,
            _ => panic!("expected object, got {self:?}"),
        }
    }
    fn str(&self) -> &str {
        match self {
            Json::Str(s) => s,
            _ => panic!("expected string, got {self:?}"),
        }
    }
    fn int(&self) -> usize {
        match self {
            Json::Num(n, _) => *n as usize,
            _ => panic!("expected number, got {self:?}"),
        }
    }
    /// Exact i64 of an integer literal, recovered from the source text (f64 cannot hold an
    /// integer near or beyond i64::MAX without rounding — see the `Num` doc).
    fn int_i64(&self) -> i64 {
        match self {
            Json::Num(_, lit) => lit
                .parse()
                .unwrap_or_else(|_| panic!("number {lit:?} is not an i64")),
            _ => panic!("expected number, got {self:?}"),
        }
    }
}

// ===================== authoring notation -> contract types ====================

fn hex_to_bytes(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "hex must be even length: {s:?}");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn term_from_json(j: &Json) -> Term {
    if let Some(a) = j.get("atom") {
        Term::atom(hex_to_bytes(a.str()))
    } else if let Some(a) = j.get("atom_str") {
        Term::atom(a.str().as_bytes().to_vec())
    } else if let Some(t) = j.get("tuple") {
        Term::tuple(t.arr().iter().map(term_from_json).collect::<Vec<_>>())
    } else if let Some(v) = j.get("var") {
        Term::var(v.str())
    } else if let Some(n) = j.get("nest") {
        // #2731: `{nest: {functor, times, leaf}}` is functor(functor(...leaf...)), `times` levels
        // around `leaf`, expanded by a loop, so a term past any JSON parser's nesting limit is
        // authored flat.
        let functor = n
            .get("functor")
            .expect("nest.functor")
            .str()
            .as_bytes()
            .to_vec();
        let mut term = term_from_json(n.get("leaf").expect("nest.leaf"));
        for _ in 0..n.get("times").expect("nest.times").int() {
            term = Term::tuple([Term::atom(functor.clone()), term]);
        }
        term
    } else {
        panic!("term must be atom/atom_str/tuple/var/nest: {j:?}");
    }
}

fn goal_from_json(j: &Json) -> Goal {
    let pred = Symbol::new(j.get("pred").unwrap().str().as_bytes().to_vec());
    let args = j
        .get("args")
        .unwrap()
        .arr()
        .iter()
        .map(term_from_json)
        .collect::<Vec<_>>();
    Goal { pred, args }
}

fn ground_from_json(j: &Json) -> GroundLiteral {
    goal_from_json(j)
        .as_ground()
        .expect("conclusion/claim must be ground in the vector")
}

fn subst_from_json(j: &Json) -> Subst {
    let mut subst: Subst = BTreeMap::new();
    for (var, term) in j.obj() {
        subst.insert(var.as_str().into(), term_from_json(term));
    }
    subst
}

/// A premise authoring form: a **bare integer** is a positive premise (so existing
/// `check.json` premise lists decode byte-identically), and `{ "neg": { "atom":
/// <lit>, "cert": <int>, "nonmember": "direct_lookup" } }` is a negated premise.
fn premise_from_json(j: &Json) -> Premise {
    match j {
        Json::Num(..) => Premise::pos(j.int() as u64),
        Json::Obj(_) => {
            // ADR 0023 count premise — the aggregation vectors' authoring form, admitted in the
            // negation family for ADR 0030 G2's count-over-partial case: `{ "count": { pred,
            // filter, project, k, cert } }`, where `k` is a bare integer and each filter entry
            // binds a position to a GROUND value.
            if let Some(c) = j.get("count") {
                let filter: Vec<(u32, ontos_core::Value)> = c
                    .get("filter")
                    .map(|a| {
                        a.arr()
                            .iter()
                            .map(|e| {
                                let pos = e.get("pos").expect("count filter pos").int() as u32;
                                let value =
                                    term_from_json(e.get("value").expect("count filter value"))
                                        .erase_ground()
                                        .expect("count filter value must be ground");
                                (pos, value)
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                return Premise::Count {
                    pred: pred_ref_from_json(c.get("pred").expect("count pred")),
                    filter,
                    project: project_from_json(c.get("project").expect("count project")),
                    k: BigInt::from_i128(c.get("k").expect("count k").int_i64() as i128)
                        .to_int_term()
                        .erase_ground()
                        .expect("ground int"),
                    cert: CertId::from(c.get("cert").expect("count cert").int() as u64),
                };
            }
            let neg = j
                .get("neg")
                .expect("premise object must have a `neg` or a `count` key");
            let atom = ground_from_json(neg.get("atom").unwrap());
            let cert = CertId::from(neg.get("cert").unwrap().int() as u64);
            // `nonmember` defaults to direct_lookup (the only v1 form).
            let nonmember = NonMemberProof::DirectLookup;
            Premise::Neg {
                atom,
                cert,
                nonmember,
            }
        }
        other => panic!("premise must be an int or a {{neg:...}} object: {other:?}"),
    }
}

fn node_from_json(j: &Json) -> Node {
    let conclusion = ground_from_json(j.get("conclusion").unwrap());
    match j.get("kind").unwrap().str() {
        "rule" => Node::Rule {
            conclusion,
            clause: ClauseId::new(j.get("clause").unwrap().str()),
            subst: subst_from_json(j.get("subst").unwrap()),
            premises: j
                .get("premises")
                .unwrap()
                .arr()
                .iter()
                .map(premise_from_json)
                .collect(),
            meta: NodeMeta::default(),
        },
        "builtin" => Node::Builtin { conclusion },
        "leaf" => Node::Leaf {
            conclusion,
            evidence: Evidence::default(),
        },
        other => panic!("unknown node kind {other:?}"),
    }
}

/// A body-literal authoring form: a **bare goal** (`{pred, args}`) is positive (so
/// existing `check.json`/`account.json` bodies decode byte-identically), and
/// `{ "neg": <goal> }` is a negated body literal.
fn body_lit_from_json(j: &Json) -> BodyLit<Term> {
    // ADR 0023 count body literal — the aggregation vectors' `count_lit` form, admitted in the
    // negation family for ADR 0030 G2's count-over-partial case. A clause-body filter entry binds
    // a position to a variable (`{pos, var}`) or a ground atom (`{pos, atom_str}`); the count
    // slot is a term (a variable, or a ground ontos-data int in the tuple/atom notation).
    if let Some(c) = j.get("count_lit") {
        let filter: Vec<(u32, Term)> = c
            .get("filter")
            .map(|a| {
                a.arr()
                    .iter()
                    .map(|e| {
                        let pos = e.get("pos").expect("count_lit filter pos").int() as u32;
                        let term = match e.get("var") {
                            Some(v) => Term::var(v.str()),
                            None => term_from_json(e),
                        };
                        (pos, term)
                    })
                    .collect()
            })
            .unwrap_or_default();
        return BodyLit::Count(CountLit {
            pred: pred_ref_from_json(c.get("pred").expect("count_lit pred")),
            filter,
            project: project_from_json(c.get("project").expect("count_lit project")),
            count: term_from_json(c.get("count").expect("count_lit count slot")),
        });
    }
    if let Some(neg) = j.get("neg") {
        BodyLit::Neg(goal_from_json(neg))
    } else {
        BodyLit::Pos(goal_from_json(j))
    }
}

/// `{ "name": <pred>, "arity": <n> }` — the counted predicate of a count premise / literal.
fn pred_ref_from_json(j: &Json) -> PredicateRef {
    PredicateRef::new(
        j.get("name").expect("pred name").str(),
        j.get("arity").expect("pred arity").int() as u32,
    )
}

/// `"rows"` or `{ "distinct" | "sum" | "min" | "max": <attr> }` (ADR 0023, #587).
fn project_from_json(j: &Json) -> ProjectSpec {
    if let Json::Str(s) = j {
        if s == "rows" {
            return ProjectSpec::Rows;
        }
    }
    if let Some(a) = j.get("distinct") {
        return ProjectSpec::Distinct {
            attr: a.int() as u32,
        };
    }
    if let Some(a) = j.get("sum") {
        return ProjectSpec::Sum {
            attr: a.int() as u32,
        };
    }
    if let Some(a) = j.get("min") {
        return ProjectSpec::Min {
            attr: a.int() as u32,
        };
    }
    if let Some(a) = j.get("max") {
        return ProjectSpec::Max {
            attr: a.int() as u32,
        };
    }
    panic!("project must be 'rows' or {{distinct|sum|min|max:<attr>}}: {j:?}");
}

fn clause_from_json(head: &Json, body: &Json) -> Clause {
    let head = goal_from_json(head);
    let body = body
        .arr()
        .iter()
        .map(body_lit_from_json)
        .collect::<Vec<_>>();
    Clause::new(head, body)
}

fn program_from_json(j: &Json) -> MapProgram {
    let mut program = MapProgram::new();
    for (id, clause) in j.obj() {
        let c = clause_from_json(clause.get("head").unwrap(), clause.get("body").unwrap());
        program.insert(ClauseId::new(id.as_str()), c);
    }
    program
}

// ============================== output =====================================

/// Minimal JSON string escaping for a case name (names are simple, but be safe).
fn jstr(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

fn run_check(doc: &Json) {
    let program = program_from_json(doc.get("program").unwrap());
    for case in doc.get("cases").unwrap().arr() {
        let name = case.get("name").unwrap().str();
        let claim = ground_from_json(case.get("claim").unwrap());
        let deriv_j = case.get("derivation").unwrap();
        let nodes = deriv_j
            .get("nodes")
            .unwrap()
            .arr()
            .iter()
            .map(node_from_json)
            .collect::<Vec<_>>();
        let root = deriv_j.get("root").unwrap().int();
        let deriv = Derivation::new(nodes, root as u64);
        let limits = limits_from_json(case.get("limits"));
        let profile = demo_profile(limits);
        // The `check` family is all-positive: the zero cert context is never
        // consulted (no `closed_world`), so this is byte-identical to `check`.
        let outcome = match check_with_cert_context(
            &program,
            &claim,
            &deriv,
            &(),
            &profile,
            &CertContext::zero(),
        ) {
            Outcome::Accept => "\"accept\"".to_string(),
            Outcome::Reject { code, .. } => format!("{{\"reject\":{}}}", jstr(code.code())),
        };
        println!("{{\"name\":{},\"outcome\":{}}}", jstr(name), outcome);
    }
}

/// Decode an optional `limits` object, defaulting unspecified fields. `max_nodes` /
/// `max_depth` are read when present; the cert budgets keep their finite defaults
/// unless overridden, so existing `check.json` cases (no cert fields) are unaffected.
fn limits_from_json(j: Option<&Json>) -> CheckLimits {
    let mut limits = CheckLimits::default();
    if let Some(l) = j {
        if let Some(v) = l.get("max_nodes") {
            limits.max_nodes = v.int();
        }
        if let Some(v) = l.get("max_depth") {
            limits.max_depth = v.int();
        }
        if let Some(v) = l.get("max_term_depth") {
            limits.max_term_depth = v.int();
        }
        if let Some(v) = l.get("max_cert_bytes") {
            limits.max_cert_bytes = v.int();
        }
        if let Some(v) = l.get("max_cert_facts") {
            limits.max_cert_facts = v.int();
        }
        if let Some(v) = l.get("max_domain_values") {
            limits.max_domain_values = v.int();
        }
        if let Some(v) = l.get("max_support_edges") {
            limits.max_support_edges = v.int();
        }
        if let Some(v) = l.get("max_rule_groundings") {
            limits.max_rule_groundings = v.int();
        }
        if let Some(v) = l.get("max_join_steps") {
            limits.max_join_steps = v.int();
        }
    }
    limits
}

fn run_account(doc: &Json) {
    for case in doc.get("clauses").unwrap().arr() {
        let name = case.get("name").unwrap().str();
        // Body literals may be bare goals (Pos) or `{neg: <goal>}` (Neg); existing
        // all-positive account vectors decode byte-identically.
        let clause = clause_from_json(case.get("head").unwrap(), case.get("body").unwrap());
        let id = ClauseId::canonical(&clause);
        println!("{{\"name\":{},\"id\":{}}}", jstr(name), jstr(id.as_str()));
    }
}

// ===================== negation family (ADR 0007) decoders ====================

/// A 32-byte hash, authored as 64 lowercase-hex chars. A missing/short value pads
/// with zero so a vector can write `"00"` etc. for the all-zero pins it does not
/// care about; an empty string is the all-zero hash.
fn hash_from_json(j: &Json) -> Hash {
    let bytes = hex_to_bytes(j.str());
    let mut h = [0u8; 32];
    for (i, b) in bytes.iter().take(32).enumerate() {
        h[i] = *b;
    }
    h
}

fn stratum_prefix_from_json(j: &Json) -> StratumPrefix {
    let level = j.get("level").unwrap().int() as u32;
    let predicates = j
        .get("predicates")
        .unwrap()
        .arr()
        .iter()
        .map(|p| Symbol::new(p.str().as_bytes().to_vec()))
        .collect::<Vec<_>>();
    // Verbatim, NOT StratumPrefix::new: the harness must carry the vector's collection
    // order as authored, or a non-canonical case (issue #839) is silently repaired
    // before it can reach the gate it exists to pin.
    StratumPrefix { level, predicates }
}

fn finite_domain_from_json(j: &Json) -> FiniteDomain {
    let type_tag = Symbol::new(j.get("type_tag").unwrap().str().as_bytes().to_vec());
    let values = j
        .get("values")
        .unwrap()
        .arr()
        .iter()
        .map(|v| {
            term_from_json(v)
                .erase_ground()
                .expect("domain value must be ground")
        })
        .collect::<Vec<_>>();
    // Verbatim, NOT FiniteDomain::new (see stratum_prefix_from_json).
    FiniteDomain { type_tag, values }
}

fn relation_table_from_json(j: &Json) -> RelationTable {
    let pred = Symbol::new(j.get("pred").unwrap().str().as_bytes().to_vec());
    let arity = j.get("arity").unwrap().int() as u32;
    let rows = j
        .get("rows")
        .unwrap()
        .arr()
        .iter()
        .map(ground_from_json)
        .collect::<Vec<_>>();
    // Verbatim, NOT RelationTable::new (see stratum_prefix_from_json).
    RelationTable { pred, arity, rows }
}

fn support_ref_from_json(j: &Json) -> SupportRef {
    if let Some(s) = j.get("same_stratum") {
        SupportRef::SameStratum {
            fact: ground_from_json(s.get("fact").unwrap()),
            rank: s.get("rank").unwrap().int() as u32,
        }
    } else if let Some(s) = j.get("lower_stratum") {
        SupportRef::LowerStratum {
            cert: CertId::from(s.get("cert").unwrap().int() as u64),
            atom: ground_from_json(s.get("atom").unwrap()),
        }
    } else if let Some(s) = j.get("builtin") {
        SupportRef::Builtin {
            atom: ground_from_json(s.get("atom").unwrap()),
        }
    } else if let Some(s) = j.get("neg_lower") {
        SupportRef::NegLower {
            cert: CertId::from(s.get("cert").unwrap().int() as u64),
            atom: ground_from_json(s.get("atom").unwrap()),
        }
    } else if let Some(s) = j.get("count_lower") {
        SupportRef::CountLower {
            cert: CertId::from(s.get("cert").unwrap().int() as u64),
        }
    } else {
        panic!(
            "support ref must be same_stratum/lower_stratum/builtin/neg_lower/count_lower: {j:?}"
        );
    }
}

fn support_edge_from_json(j: &Json) -> SupportEdge {
    SupportEdge {
        fact: ground_from_json(j.get("fact").unwrap()),
        clause: ClauseId::new(j.get("clause").unwrap().str()),
        subst: subst_from_json(j.get("subst").unwrap()),
        body_refs: j
            .get("body_refs")
            .unwrap()
            .arr()
            .iter()
            .map(support_ref_from_json)
            .collect(),
        rank: j.get("rank").unwrap().int() as u32,
    }
}

fn cert_size_decl_from_json(j: &Json) -> CertSizeDecl {
    CertSizeDecl {
        cert_facts: (j.get("cert_facts").unwrap().int()) as u64,
        domain_values: (j.get("domain_values").unwrap().int()) as u64,
        support_edges: (j.get("support_edges").unwrap().int()) as u64,
        rule_groundings: (j.get("rule_groundings").unwrap().int()) as u64,
        join_steps: (j.get("join_steps").unwrap().int()) as u64,
        cert_bytes: j.get("cert_bytes").unwrap().int() as u64,
    }
}

fn closed_model_cert_from_json(j: &Json) -> ClosedModelCert {
    let hashes = |key: &str| {
        j.get(key)
            .map(|a| a.arr().iter().map(hash_from_json).collect::<Vec<_>>())
            .unwrap_or_default()
    };
    ClosedModelCert {
        scope: stratum_prefix_from_json(j.get("scope").unwrap()),
        program_hash: j
            .get("program_hash")
            .map(hash_from_json)
            .unwrap_or([0u8; 32]),
        profile_hash: j
            .get("profile_hash")
            .map(hash_from_json)
            .unwrap_or([0u8; 32]),
        ctx_hash: j.get("ctx_hash").map(hash_from_json).unwrap_or([0u8; 32]),
        theory_config_hash: j
            .get("theory_config_hash")
            .map(hash_from_json)
            .unwrap_or([0u8; 32]),
        edb_snapshot_hashes: hashes("edb_snapshot_hashes"),
        domains: j
            .get("domains")
            .unwrap()
            .arr()
            .iter()
            .map(finite_domain_from_json)
            .collect(),
        extensions: j
            .get("extensions")
            .unwrap()
            .arr()
            .iter()
            .map(relation_table_from_json)
            .collect(),
        supports: SupportWitness(
            j.get("supports")
                .unwrap()
                .arr()
                .iter()
                .map(support_edge_from_json)
                .collect(),
        ),
        closure: ClosureWitness,
        // ADR 0029 D10: the slice seal, read from the vector when present.
        decomposition_witness: j.get("decomposition_witness").map(hash_from_json),
        // ADR 0030 D1: the partial sub-scope, read from the vector when present.
        partial_scope: j.get("partial_scope").map(stratum_prefix_from_json),
        limits_decl: cert_size_decl_from_json(j.get("limits_decl").unwrap()),
    }
}

/// Read the top-level `edb` map: `{ "<pred>": [ <lit>, ... ], ... }` — the EDB-of-
/// record the negation profile attests snapshots over (ADR 0007 §3.6).
fn edb_from_json(j: Option<&Json>) -> std::collections::BTreeMap<Vec<u8>, Vec<GroundLiteral>> {
    let mut edb: std::collections::BTreeMap<Vec<u8>, Vec<GroundLiteral>> =
        std::collections::BTreeMap::new();
    if let Some(m) = j {
        for (pred, rows) in m.obj() {
            edb.insert(
                pred.as_bytes().to_vec(),
                rows.arr().iter().map(ground_from_json).collect(),
            );
        }
    }
    edb
}

/// The negation_v1 profile's theory: `lt` for the builtin support refs, and since #3126 the
/// standard arithmetic theory beside it, so `vectors/theory_not_decided.json` can state a literal
/// the theory does not decide. No negation-family vector names an arithmetic predicate as a
/// relation, so the verdicts of `negation.json` and `exact_claims.json` do not move.
fn negation_theory() -> CompoundTheory {
    CompoundTheory::new(vec![Box::new(LtTheory), Box::new(ArithmeticTheory::new())])
}

/// The fixed non-zero profile/ctx/theory pins the negation_v1 profile binds (the
/// program_hash is recomputed from the live program). Any cert claiming to be
/// honestly bound uses these; a cert that overrides a pin in the vector keeps its
/// override (for the context-mismatch cases).
const NEG_PROFILE_PIN: [u8; 32] = [1u8; 32];
const NEG_CTX_PIN: [u8; 32] = [2u8; 32];
const NEG_THEORY_PIN: [u8; 32] = [3u8; 32];

/// The `negation` family: like `check` but each derivation carries `closed_world`,
/// premises may be `{neg:{...}}`, body literals may be `{neg:<goal>}`. The bound
/// context is DERIVED (recomputed `program_hash` + fixed non-zero pins). A cert with
/// no explicit pins in the vector is auto-bound to the derived context (the honest
/// case); a cert that sets a pin keeps it (the mismatch cases). A case with
/// `"plain_check": true` calls the plain `check()` (zero/unbound context).
fn run_negation(doc: &Json) {
    let program = program_from_json(doc.get("program").unwrap());
    let extensional: PredicateSet = doc
        .get("extensional")
        .map(|a| {
            a.arr()
                .iter()
                .map(|p| Symbol::new(p.str().as_bytes().to_vec()))
                .collect()
        })
        .unwrap_or_default();
    let edb = edb_from_json(doc.get("edb"));
    let derived = CertContext::new(
        logos_contract::program_digest(&program),
        NEG_PROFILE_PIN,
        NEG_CTX_PIN,
        NEG_THEORY_PIN,
    );

    for case in doc.get("cases").unwrap().arr() {
        let name = case.get("name").unwrap().str();
        let claim = ground_from_json(case.get("claim").unwrap());
        let deriv_j = case.get("derivation").unwrap();
        let nodes = deriv_j
            .get("nodes")
            .unwrap()
            .arr()
            .iter()
            .map(node_from_json)
            .collect::<Vec<_>>();
        let root = deriv_j.get("root").unwrap().int();
        let cw_json = deriv_j.get("closed_world");
        let closed_world: Vec<ClosedModelCert> = cw_json
            .map(|cw| {
                cw.arr()
                    .iter()
                    .map(|cj| {
                        let mut cert = closed_model_cert_from_json(cj);
                        // Auto-bind to the derived context unless the vector pins it.
                        if cj.get("program_hash").is_none() {
                            cert.program_hash = derived.program_hash;
                        }
                        if cj.get("profile_hash").is_none() {
                            cert.profile_hash = derived.profile_hash;
                        }
                        if cj.get("ctx_hash").is_none() {
                            cert.ctx_hash = derived.ctx_hash;
                        }
                        if cj.get("theory_config_hash").is_none() {
                            cert.theory_config_hash = derived.theory_config_hash;
                        }
                        cert
                    })
                    .collect()
            })
            .unwrap_or_default();
        // #2602 (`seat:caa`'s condition 3): the length reading equals the encoding it measures.
        for cert in &closed_world {
            let mut zeroed = cert.clone();
            zeroed.limits_decl.cert_bytes = 0;
            assert_eq!(
                logos_contract::cert_encoded_bytes(cert),
                ontos_codec::encode(
                    &logos_contract::derivation_wire::closed_model_cert_as_value(&zeroed)
                )
                .len() as u64,
                "negation {name}: the length reading disagrees with the encoding it measures"
            );
        }
        let deriv = Derivation::with_closed_world(nodes, root as u64, closed_world);
        let limits = limits_from_json(case.get("limits"));
        let profile = negation_profile(limits, extensional.clone(), edb.clone());

        let plain = matches!(case.get("plain_check"), Some(Json::Bool(true)));
        // A per-case context override (rare — the mismatch-on-context cases).
        let cx = match case.get("cert_context") {
            Some(c) => {
                let mut cx = derived;
                if let Some(v) = c.get("program_hash") {
                    cx.program_hash = hash_from_json(v);
                }
                if let Some(v) = c.get("profile_hash") {
                    cx.profile_hash = hash_from_json(v);
                }
                if let Some(v) = c.get("ctx_hash") {
                    cx.ctx_hash = hash_from_json(v);
                }
                if let Some(v) = c.get("theory_config_hash") {
                    cx.theory_config_hash = hash_from_json(v);
                }
                // ADR 0029 D10: a case that declares its decomposition binds the context to it.
                if let Some(v) = c.get("decomposition_witness") {
                    cx = cx.with_decomposition(hash_from_json(v));
                }
                cx
            }
            None => derived,
        };

        let result = if plain {
            check(&program, &claim, &deriv, &(), &profile)
        } else {
            check_with_cert_context(&program, &claim, &deriv, &(), &profile, &cx)
        };
        // #2565 term 1: every certifying case also goes through the checker's world memo, once to
        // fill it (a miss) and once more to be served from it (a hit). Both must be the fresh
        // verdict to the byte, or the replay stops: the memo may skip work, never change a verdict.
        if !plain {
            let mut memo = WorldMemo::new();
            for pass in ["miss", "hit"] {
                let memoized =
                    check_with_cert_memo(&program, &claim, &deriv, &(), &profile, &cx, &mut memo);
                assert_eq!(
                    memoized, result,
                    "#2565: case {name}: the world memo's {pass} diverged from the fresh check"
                );
            }
            let verified = memo.certificates_verified();
            assert!(
                verified == 0 || verified == deriv.closed_world.len(),
                "#2565: case {name}: two checks of one world must verify it at most once, verified {verified}"
            );
        }
        let outcome = match result {
            Outcome::Accept => "\"accept\"".to_string(),
            Outcome::Reject { code, .. } => format!("{{\"reject\":{}}}", jstr(code.code())),
        };
        println!("{{\"name\":{},\"outcome\":{}}}", jstr(name), outcome);
    }
}

// ===================== theory-decision families (ADR 0006 / #95, #154) ==============
// arithmetic / list / term / text / compound — each drives a standard checkable Theory's
// `decide` over the shared vectors/<family>.json `decisions` array. The arg builder mirrors
// the unit replays' build_arg (core/rs/tests/arithmetic_vectors.rs) byte-for-byte, so the
// black-box CLI agrees with the in-process oracle.

/// Build the ontos `Value` (carried as a `Term`) an arg object denotes, matching the
/// structural encoding in `vectors/{arithmetic,list,term,text,compound}.json` (and the
/// Go/TS builders) EXACTLY:
///
/// * `{"int": N}`                 → the ontos-data `int` embedding of `N`;
/// * `{"bigint": "<digits>"}`     → the `int` embedding of a value beyond the JSON int range;
/// * `{"decimal": "<d.dddd>"}`    → the ontos-data `decimal` embedding of that literal (#331);
/// * `{"text": "<s>"}`            → the ontos-data `utf8-text` embedding;
/// * `{"atom": "<utf8>"}`         → a bare `Atom` of those UTF-8 bytes;
/// * `{"op": "<op>", "args": []}` → an operator compound `Tuple(Atom(op), arg…)`;
/// * `{"list": [..]}`             → the ontos-data `list` embedding of the encoded children;
/// * `{"tuple": [..]}`            → a raw `Tuple` of the encoded children.
fn build_theory_arg(j: &Json) -> Term {
    if let Some(n) = j.get("int") {
        return BigInt::from_i128(i128::from(n.int_i64())).to_int_term();
    }
    if let Some(d) = j.get("bigint") {
        return BigInt::from_decimal_str(d.str())
            .unwrap_or_else(|| panic!("bigint {:?} is not a base-10 integer", d.str()))
            .to_int_term();
    }
    if let Some(d) = j.get("decimal") {
        return BigDecimal::from_decimal_str(d.str())
            .unwrap_or_else(|| panic!("decimal {:?} is not a decimal literal", d.str()))
            .to_decimal_term();
    }
    if let Some(t) = j.get("text") {
        return Term::from_value(&ontos_data::encode_text(t.str()));
    }
    if let Some(a) = j.get("atom") {
        return Term::atom(a.str().as_bytes().to_vec());
    }
    if let Some(op) = j.get("op") {
        let args = j.get("args").map(Json::arr).unwrap_or(&[]);
        let mut children = Vec::with_capacity(args.len() + 1);
        children.push(Term::atom(op.str().as_bytes().to_vec()));
        children.extend(args.iter().map(build_theory_arg));
        return Term::tuple(children);
    }
    if let Some(list) = j.get("list") {
        let elems = list
            .arr()
            .iter()
            .map(|c| {
                build_theory_arg(c)
                    .erase_ground()
                    .expect("list element must be ground")
            })
            .collect::<Vec<_>>();
        return Term::from_value(&ontos_data::encode_list(&elems));
    }
    if let Some(children) = j.get("tuple") {
        return Term::tuple(
            children
                .arr()
                .iter()
                .map(build_theory_arg)
                .collect::<Vec<_>>(),
        );
    }
    panic!("unrecognized arg shape: {j:?}");
}

/// The standard checkable [`Theory`] a family names. `compound` composes
/// `[arithmetic, text]` in that order (mirroring the unit replays' `build_compound`).
fn theory_by_name(name: &str) -> Box<dyn Theory> {
    match name {
        "arithmetic" => Box::new(ArithmeticTheory::new()),
        "list" => Box::new(ListTheory::new()),
        "term" => Box::new(TermTheory::new()),
        "text" => Box::new(TextTheory::new()),
        "compound" => Box::new(CompoundTheory::new(vec![
            Box::new(ArithmeticTheory::new()),
            Box::new(TextTheory::new()),
        ])),
        other => panic!("unknown theory family {other:?}"),
    }
}

/// A lowercase-hex rendering of a 32-byte digest.
fn hex_of(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn run_theory(name: &str, doc: &Json) {
    let theory = theory_by_name(name);
    for case in doc.get("decisions").unwrap().arr() {
        let case_name = case.get("name").unwrap().str();
        let pred = case.get("pred").unwrap().str();
        let args = case
            .get("args")
            .unwrap()
            .arr()
            .iter()
            .map(|a| {
                build_theory_arg(a)
                    .erase_ground()
                    .expect("a decision-vector arg must be ground")
            })
            .collect::<Vec<_>>();
        let atom = GroundLiteral::new(pred.as_bytes().to_vec(), args);
        // #3126: the ground verdict, which can say "not decided" (`{"not_completed": <kind>}`).
        use logos_contract::completion::{Completion, NonCompletionKind, TheoryDecision};
        let outcome = match theory.decide_ground(&atom) {
            Completion::Completed(TheoryDecision::Holds) => "\"holds\"".to_string(),
            Completion::Completed(TheoryDecision::Fails { code }) => {
                format!("{{\"fails\":{}}}", jstr(&code))
            }
            Completion::LimitExceeded(never) => match never {},
            // The decision vectors only carry owned predicates, so a routed atom is never
            // disowned; if it is, the vector or the theory's owns set is wrong.
            Completion::NotCompleted(cause)
                if cause.kind() == NonCompletionKind::InconsistentTheory =>
            {
                panic!("{name} {case_name:?}: theory does not own predicate {pred:?}")
            }
            Completion::NotCompleted(cause) => {
                format!("{{\"not_completed\":{}}}", jstr(cause.kind().tag()))
            }
        };
        println!("{{\"name\":{},\"outcome\":{}}}", jstr(case_name), outcome);
    }
    // Pin the theory's identity config digest as a synthetic case so the harness asserts
    // the composed/ordered identity (the compound digest commits to membership AND order),
    // uniformly across every theory family.
    let digest = hex_of(&theory.identity().config_digest);
    println!(
        "{{\"name\":\"__identity__\",\"outcome\":{}}}",
        jstr(&digest)
    );
}

fn main() {
    let family = std::env::args().nth(1).unwrap_or_default();
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .expect("read stdin");
    let doc = P::new(&input).value();
    match family.as_str() {
        "check" => run_check(&doc),
        "account" => run_account(&doc),
        "negation" => run_negation(&doc),
        "arithmetic" | "list" | "term" | "text" | "compound" => run_theory(&family, &doc),
        other => {
            eprintln!(
                "usage: conformance <check|account|negation|arithmetic|list|term|text|compound>  (got {other:?})"
            );
            std::process::exit(2);
        }
    }
}
