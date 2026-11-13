//! Rust replay of the cross-core agreement vector `vectors/semiring.json` (ADR 0031 D1, D2,
//! G3; v2 §14.3).
//!
//! Every core builds the core semiring `Counting` and the four fixture semirings the vector's
//! note defines, and must reproduce each semiring's declared identity, laws, computed identity
//! digest, `zero` and `one`; the element test; every `add`/`mul` row; and every audit verdict,
//! witness included. It builds every product the `products` table names from its members, and
//! must reproduce each product's identity, laws, `zero` and `one`, every `product_ops` row and
//! every `product_audits` verdict. The SAME file is replayed by Go
//! (`contract/go/semiring_vectors_test.go`) and TS (`contract/ts/test/semiring_vectors.test.ts`).
//!
//! The vector is hand-authored from the algebra, and its identity digests were computed with
//! coreutils `sha256sum` (the products' with Python `hashlib`) over the byte layout the note
//! states, so no core is its own oracle.

use logos_contract::decval::{BigDecimal, DecimalError};
use logos_contract::intval::BigInt;
use logos_contract::{
    audit_semiring, semiring_identity, semiring_identity_of, ComponentIdentity, CountingSemiring,
    LawDeclaration, LawTally, ProbabilitySemiring, ProductSemiring, ProvenanceSemiring, Semiring,
    SemiringAnswer, SemiringAudit, SemiringLaw, Term, TropicalSemiring, PRODUCT_SEMIRING_PREFIX,
    SEMIRING_AUDIT_SAMPLE_LIMIT, SEMIRING_IDENTITY_PREFIX,
};
use ontos_core::Value;
use serde_json::Value as Json;
use std::collections::BTreeMap;

const VECTORS: &str = include_str!("../../../vectors/semiring.json");

fn vectors() -> Json {
    serde_json::from_str(VECTORS).expect("vectors/semiring.json parses")
}

/// The ontos value an object of the vector's structural grammar denotes.
fn value(j: &Json) -> Value {
    let obj = j
        .as_object()
        .unwrap_or_else(|| panic!("value is not an object: {j}"));
    if let Some(n) = obj.get("int") {
        let n = n.as_i64().unwrap_or_else(|| panic!("int not an i64: {n}"));
        return int_value(&BigInt::from_i128(i128::from(n)));
    }
    if let Some(digits) = obj.get("bigint") {
        let digits = digits.as_str().expect("bigint is a string");
        let n = BigInt::from_decimal_str(digits).expect("bigint is a decimal integer");
        return int_value(&n);
    }
    if let Some(parts) = obj.get("decimal") {
        let parts = parts.as_array().expect("decimal is [mantissa, exponent]");
        let label = Value::atom(b"decimal".to_vec());
        return Value::tuple(vec![label, small_int(&parts[0]), small_int(&parts[1])]);
    }
    if let Some(a) = obj.get("atom") {
        return atom(a.as_str().expect("atom is a string"));
    }
    if let Some(items) = obj.get("tuple") {
        let items = items.as_array().expect("tuple is an array");
        return Value::tuple(items.iter().map(value).collect::<Vec<_>>());
    }
    panic!("unrecognized value shape: {j}");
}

fn int_value(n: &BigInt) -> Value {
    n.to_int_term()
        .erase_ground()
        .expect("an int term is ground")
}

/// The int embedding of a JSON integer.
fn small_int(j: &Json) -> Value {
    let n = j.as_i64().expect("an i64 integer");
    int_value(&BigInt::from_i128(i128::from(n)))
}

fn decimal_value(d: &BigDecimal) -> Value {
    d.to_decimal_term()
        .erase_ground()
        .expect("a decimal term is ground")
}

fn atom(s: &str) -> Value {
    Value::atom(s.as_bytes().to_vec())
}

fn values(j: &Json) -> Vec<Value> {
    j.as_array()
        .expect("an array of values")
        .iter()
        .map(value)
        .collect()
}

fn law_names(j: &Json) -> Vec<String> {
    j.as_array()
        .expect("an array of law names")
        .iter()
        .map(|l| l.as_str().expect("a law name").to_string())
        .collect()
}

fn names(laws: &[SemiringLaw]) -> Vec<String> {
    laws.iter().map(|l| l.name().to_string()).collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

// ---- the fixture semirings, as the vector's note defines them ----

/// An element, or no answer because an operand is outside the carrier.
fn answer(result: Option<Value>) -> SemiringAnswer {
    match result {
        Some(value) => SemiringAnswer::Element(value),
        None => SemiringAnswer::NotAnElement,
    }
}

/// `atom false` / `atom true` as a boolean, or `None` outside the carrier.
fn truth(v: &Value) -> Option<bool> {
    if *v == atom("true") {
        Some(true)
    } else if *v == atom("false") {
        Some(false)
    } else {
        None
    }
}

fn truth_value(b: bool) -> Value {
    atom(if b { "true" } else { "false" })
}

fn boolean_add(left_add: bool, a: &Value, b: &Value) -> Option<Value> {
    let (x, y) = (truth(a)?, truth(b)?);
    Some(truth_value(if left_add { x } else { x || y }))
}

fn boolean_mul(a: &Value, b: &Value) -> Option<Value> {
    let (x, y) = (truth(a)?, truth(b)?);
    Some(truth_value(x && y))
}

/// `boolean` (⊕ or), or `left_add` (⊕ the left projection), over `{false, true}`.
struct BooleanFixture {
    id: &'static str,
    left_add: bool,
}

impl Semiring for BooleanFixture {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(self.id.as_bytes().to_vec(), b"1".to_vec(), [0u8; 32])
    }

    fn laws(&self) -> LawDeclaration {
        LawDeclaration {
            idempotent: true,
            bounded: true,
            monotone: true,
            commutative: true,
            supports_retraction: false,
        }
    }

    fn zero(&self) -> Value {
        truth_value(false)
    }

    fn one(&self) -> Value {
        truth_value(true)
    }

    fn is_element(&self, value: &Value) -> bool {
        truth(value).is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        answer(boolean_add(self.left_add, a, b))
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        answer(boolean_mul(a, b))
    }
}

/// `string_set`'s element, or `None`: a Tuple of Atoms strictly increasing by bytes.
fn words(v: &Value) -> Option<Vec<Vec<u8>>> {
    let items = v.as_tuple()?.items();
    let mut out: Vec<Vec<u8>> = Vec::with_capacity(items.len());
    for item in items {
        let bytes = item.as_atom()?.bytes().to_vec();
        if out.last().is_some_and(|prev| *prev >= bytes) {
            return None;
        }
        out.push(bytes);
    }
    Some(out)
}

fn word_set(mut ws: Vec<Vec<u8>>) -> Value {
    ws.sort();
    ws.dedup();
    Value::tuple(ws.into_iter().map(Value::atom).collect::<Vec<_>>())
}

fn words_add(a: &Value, b: &Value) -> Option<Value> {
    let (mut x, y) = (words(a)?, words(b)?);
    x.extend(y);
    Some(word_set(x))
}

fn words_mul(a: &Value, b: &Value) -> Option<Value> {
    let (x, y) = (words(a)?, words(b)?);
    let mut out = Vec::with_capacity(x.len() * y.len());
    for p in &x {
        for q in &y {
            let mut pq = p.clone();
            pq.extend_from_slice(q);
            out.push(pq);
        }
    }
    Some(word_set(out))
}

/// `string_set`: finite sets of atoms, ⊕ union, ⊗ pairwise concatenation.
struct StringSetFixture;

impl Semiring for StringSetFixture {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"fixture/string-set-semiring".to_vec(),
            b"1".to_vec(),
            [0u8; 32],
        )
    }

    fn laws(&self) -> LawDeclaration {
        LawDeclaration {
            idempotent: true,
            bounded: false,
            monotone: true,
            commutative: true,
            supports_retraction: false,
        }
    }

    fn zero(&self) -> Value {
        word_set(Vec::new())
    }

    fn one(&self) -> Value {
        word_set(vec![Vec::new()])
    }

    fn is_element(&self, value: &Value) -> bool {
        words(value).is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        answer(words_add(a, b))
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        answer(words_mul(a, b))
    }
}

/// `counting_declared_idempotent` (Counting with `idempotent` also declared), or `stopping`
/// (Counting's carrier, every operation on elements stopped at the capacity bound).
struct CountingVariant {
    declared_idempotent: bool,
    stopping: bool,
}

impl Semiring for CountingVariant {
    fn declared_identity(&self) -> ComponentIdentity {
        if self.stopping {
            ComponentIdentity::new(
                b"fixture/stopping-semiring".to_vec(),
                b"1".to_vec(),
                [0u8; 32],
            )
        } else {
            CountingSemiring::new().declared_identity()
        }
    }

    fn laws(&self) -> LawDeclaration {
        LawDeclaration {
            idempotent: self.declared_idempotent,
            ..CountingSemiring::new().laws()
        }
    }

    fn zero(&self) -> Value {
        CountingSemiring::new().zero()
    }

    fn one(&self) -> Value {
        CountingSemiring::new().one()
    }

    fn is_element(&self, value: &Value) -> bool {
        CountingSemiring::new().is_element(value)
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        self.stop_or(CountingSemiring::new().add(a, b))
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        self.stop_or(CountingSemiring::new().mul(a, b))
    }
}

impl CountingVariant {
    /// Counting's answer, or, for `stopping`, the capacity stop in place of every element.
    fn stop_or(&self, counted: SemiringAnswer) -> SemiringAnswer {
        match counted {
            SemiringAnswer::Element(_) if self.stopping => SemiringAnswer::capacity(),
            other => other,
        }
    }
}

/// A decimal in `[0, 1]`, `noisy_or`'s carrier.
fn unit(v: &Value) -> Option<BigDecimal> {
    let d = BigDecimal::from_decimal_term(&Term::from_value(v))?;
    let one = BigDecimal::from_bigint(BigInt::from_i128(1));
    (!d.is_negative() && d <= one).then_some(d)
}

fn decimal_result(result: Result<BigDecimal, DecimalError>) -> SemiringAnswer {
    match result {
        Ok(d) => SemiringAnswer::Element(decimal_value(&d)),
        Err(_) => SemiringAnswer::capacity(),
    }
}

/// `noisy_or`: decimals in `[0, 1]`, ⊕ `a + b - ab`, ⊗ `ab`. Not distributive, so not a
/// semiring.
struct NoisyOrFixture;

impl Semiring for NoisyOrFixture {
    fn declared_identity(&self) -> ComponentIdentity {
        ComponentIdentity::new(
            b"fixture/noisy-or-semiring".to_vec(),
            b"1".to_vec(),
            [0u8; 32],
        )
    }

    fn laws(&self) -> LawDeclaration {
        LawDeclaration {
            idempotent: false,
            bounded: false,
            monotone: true,
            commutative: true,
            supports_retraction: false,
        }
    }

    fn zero(&self) -> Value {
        decimal_value(&BigDecimal::zero())
    }

    fn one(&self) -> Value {
        decimal_value(&BigDecimal::from_bigint(BigInt::from_i128(1)))
    }

    fn is_element(&self, value: &Value) -> bool {
        unit(value).is_some()
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        let (Some(x), Some(y)) = (unit(a), unit(b)) else {
            return SemiringAnswer::NotAnElement;
        };
        let sum = x.add(&y).and_then(|s| x.mul(&y).and_then(|p| s.sub(&p)));
        decimal_result(sum)
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        let (Some(x), Some(y)) = (unit(a), unit(b)) else {
            return SemiringAnswer::NotAnElement;
        };
        decimal_result(x.mul(&y))
    }
}

/// A semiring this replay builds. It is `Send + Sync`, so it can be a product's member.
type Built = Box<dyn Semiring + Send + Sync>;

/// The semiring a vector row names, built from this core's own code: `kind` "core" is a
/// contract semiring, "fixture" one of the test fixtures above.
fn semiring(name: &str, kind: &str) -> Built {
    match (kind, name) {
        ("core", "counting") => Box::new(CountingSemiring::new()),
        ("fixture", "counting_declared_idempotent") => Box::new(CountingVariant {
            declared_idempotent: true,
            stopping: false,
        }),
        ("fixture", "stopping") => Box::new(CountingVariant {
            declared_idempotent: false,
            stopping: true,
        }),
        ("fixture", "boolean") => Box::new(BooleanFixture {
            id: "fixture/boolean-semiring",
            left_add: false,
        }),
        ("fixture", "left_add") => Box::new(BooleanFixture {
            id: "fixture/left-projection-add",
            left_add: true,
        }),
        ("fixture", "string_set") => Box::new(StringSetFixture),
        ("core", "tropical") => Box::new(TropicalSemiring::new()),
        ("core", "probability") => Box::new(ProbabilitySemiring::new()),
        ("core", "provenance") => Box::new(ProvenanceSemiring::new()),
        ("fixture", "noisy_or") => Box::new(NoisyOrFixture),
        (kind, name) => panic!("vectors/semiring.json names an unknown {kind} semiring {name:?}"),
    }
}

/// The semiring a row refers to by name, with its `kind` from the `semirings` table.
fn semiring_named(v: &Json, name: &str) -> Built {
    let row = v["semirings"]
        .as_array()
        .expect("semirings is an array")
        .iter()
        .find(|r| r["name"] == name)
        .unwrap_or_else(|| panic!("no semiring named {name:?}"));
    semiring(name, row["kind"].as_str().expect("kind is a string"))
}

fn laws_of(j: &Json) -> LawDeclaration {
    let flag = |k: &str| j[k].as_bool().expect("a law flag is a bool");
    LawDeclaration {
        idempotent: flag("idempotent"),
        bounded: flag("bounded"),
        monotone: flag("monotone"),
        commutative: flag("commutative"),
        supports_retraction: flag("supports_retraction"),
    }
}

#[test]
fn the_vector_metadata_is_the_contract_s() {
    let v = vectors();
    let prefix = v["identity_prefix"].as_str().expect("identity_prefix");
    assert_eq!(prefix.as_bytes(), SEMIRING_IDENTITY_PREFIX);
    let product_prefix = v["product_identity_prefix"].as_str().expect("prefix");
    assert_eq!(product_prefix.as_bytes(), PRODUCT_SEMIRING_PREFIX);
    let limit = v["audit_sample_limit"]
        .as_u64()
        .expect("audit_sample_limit");
    assert_eq!(limit, SEMIRING_AUDIT_SAMPLE_LIMIT as u64);
    let order = law_names(&v["audit_order"]);
    assert_eq!(order, names(&SemiringLaw::AUDIT_ORDER), "audit_order");
    let bits = &v["law_bits"];
    for (law, bit) in [
        ("idempotent", LawDeclaration::IDEMPOTENT_BIT),
        ("bounded", LawDeclaration::BOUNDED_BIT),
        ("monotone", LawDeclaration::MONOTONE_BIT),
        ("commutative", LawDeclaration::COMMUTATIVE_BIT),
        (
            "supports_retraction",
            LawDeclaration::SUPPORTS_RETRACTION_BIT,
        ),
    ] {
        assert_eq!(bits[law].as_u64(), Some(u64::from(bit)), "law_bits.{law}");
    }
}

/// `s` reproduces a `semirings` or `products` row: its declared identity, laws, laws byte,
/// computed identity digest, `zero` and `one`.
fn assert_identity_row(name: &str, s: &dyn Semiring, row: &Json) {
    let declared = s.declared_identity();
    let want = &row["declared_identity"];
    let want_id = want["id"].as_str().expect("id");
    let want_version = want["version"].as_str().expect("version");
    let want_config = want["config_digest"].as_str().expect("config");
    assert_eq!(declared.id, want_id.as_bytes(), "{name}");
    assert_eq!(declared.version, want_version.as_bytes(), "{name}");
    assert_eq!(hex(&declared.config_digest), want_config, "{name}");
    let laws = s.laws();
    assert_eq!(laws, laws_of(&row["laws"]), "{name}");
    let laws_byte = row["laws_byte"].as_u64().expect("laws_byte");
    assert_eq!(u64::from(laws.bits()), laws_byte, "{name}");
    let identity = semiring_identity(s);
    assert_eq!(identity, semiring_identity_of(&declared, laws), "{name}");
    assert_eq!(identity.id, declared.id, "{name}: the id is kept");
    assert_eq!(identity.version, declared.version, "{name}");
    let digest = row["identity_digest_hex"].as_str().expect("digest");
    assert_eq!(hex(&identity.config_digest), digest, "{name}");
    assert_eq!(s.zero(), value(&row["zero"]), "{name}: zero");
    assert_eq!(s.one(), value(&row["one"]), "{name}: one");
}

#[test]
fn every_semiring_reproduces_its_identity_laws_zero_and_one() {
    let v = vectors();
    let rows = v["semirings"].as_array().expect("semirings is an array");
    assert!(!rows.is_empty(), "the semirings table is not empty");
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let s = semiring(name, row["kind"].as_str().expect("kind"));
        assert_identity_row(name, &*s, row);
    }
}

#[test]
fn every_element_row_holds() {
    let v = vectors();
    for row in v["elements"].as_array().expect("elements is an array") {
        let name = row["name"].as_str().expect("name");
        let s = semiring_named(&v, row["semiring"].as_str().expect("semiring"));
        let want = row["expected"].as_bool().expect("expected is a bool");
        assert_eq!(s.is_element(&value(&row["value"])), want, "{name}");
    }
}

/// What `s` answers for the row's `op` on its `a` and `b`.
fn run_op(name: &str, s: &dyn Semiring, row: &Json) -> SemiringAnswer {
    let (a, b) = (value(&row["a"]), value(&row["b"]));
    match row["op"].as_str().expect("op") {
        "add" => s.add(&a, &b),
        "mul" => s.mul(&a, &b),
        other => panic!("{name}: unknown op {other:?}"),
    }
}

/// `got` is the row's `expected`: the element, "not_an_element", or a stop of that kind and scope.
fn assert_answer(name: &str, got: SemiringAnswer, want: &Json) {
    if want.as_str() == Some("not_an_element") {
        assert_eq!(got, SemiringAnswer::NotAnElement, "{name}");
    } else if let Some(stop) = want.get("stopped") {
        match got {
            SemiringAnswer::Stopped(cause) => {
                let kind = stop["kind"].as_str().expect("kind");
                assert_eq!(cause.kind().tag(), kind, "{name}");
                let scope = cause.scope().map(|s| s.tag());
                assert_eq!(scope, stop["scope"].as_str(), "{name}");
            }
            other => panic!("{name}: want a stop, got {other:?}"),
        }
    } else {
        assert_eq!(got, SemiringAnswer::Element(value(want)), "{name}");
    }
}

#[test]
fn every_operation_row_holds() {
    let v = vectors();
    for row in v["ops"].as_array().expect("ops is an array") {
        let name = row["name"].as_str().expect("name");
        let s = semiring_named(&v, row["semiring"].as_str().expect("semiring"));
        assert_answer(name, run_op(name, &*s, row), &row["expected"]);
    }
}

/// A verdict's tallies as `(law, decided, undecided)`.
fn tallies(laws: &[LawTally]) -> Vec<(String, u64, u64)> {
    let mut out = Vec::with_capacity(laws.len());
    for t in laws {
        let law = t.law.name().to_string();
        out.push((law, t.decided as u64, t.undecided as u64));
    }
    out
}

/// The vector's tallies as `(law, decided, undecided)`.
fn pinned_tallies(j: &Json) -> Vec<(String, u64, u64)> {
    let mut out = Vec::new();
    for t in j.as_array().expect("laws is an array") {
        let law = t["law"].as_str().expect("law").to_string();
        let decided = t["decided"].as_u64().expect("decided");
        let undecided = t["undecided"].as_u64().expect("undecided");
        out.push((law, decided, undecided));
    }
    out
}

/// `got` is the row's `verdict`, tallies and witness included.
fn assert_verdict(name: &str, got: SemiringAudit, verdict: &Json) {
    if let Some(pass) = verdict.get("no_counterexample") {
        match got {
            SemiringAudit::NoCounterexample { laws } => {
                assert!(!laws.iter().any(LawTally::is_vacuous), "{name}");
                assert_eq!(tallies(&laws), pinned_tallies(&pass["laws"]), "{name}");
            }
            other => panic!("{name}: want no_counterexample, got {other:?}"),
        }
    } else if let Some(vacuous) = verdict.get("vacuous") {
        match got {
            SemiringAudit::Vacuous { laws } => {
                assert!(laws.iter().any(LawTally::is_vacuous), "{name}");
                assert_eq!(tallies(&laws), pinned_tallies(&vacuous["laws"]), "{name}");
            }
            other => panic!("{name}: want vacuous, got {other:?}"),
        }
    } else if let Some(refuted) = verdict.get("counterexample") {
        match got {
            SemiringAudit::Counterexample { law, witness } => {
                assert_eq!(law.name(), refuted["law"].as_str().expect("law"), "{name}");
                assert_eq!(witness, values(&refuted["witness"]), "{name}: witness");
            }
            other => panic!("{name}: want counterexample, got {other:?}"),
        }
    } else if let Some(limit) = verdict.get("sample_limit") {
        match got {
            SemiringAudit::SampleLimit { given, limit: cap } => {
                assert_eq!(Some(given as u64), limit["given"].as_u64(), "{name}");
                assert_eq!(Some(cap as u64), limit["limit"].as_u64(), "{name}");
            }
            other => panic!("{name}: want sample_limit, got {other:?}"),
        }
    } else {
        panic!("{name}: unknown verdict {verdict}");
    }
}

#[test]
fn every_audit_row_reproduces_its_verdict() {
    let v = vectors();
    let rows = v["audits"].as_array().expect("audits is an array");
    assert!(!rows.is_empty(), "the audits table is not empty");
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let s = semiring_named(&v, row["semiring"].as_str().expect("semiring"));
        let got = audit_semiring(&*s, &values(&row["samples"]));
        assert_verdict(name, got, &row["verdict"]);
    }
}

#[test]
fn every_decimal_parts_row_holds() {
    let v = vectors();
    let rows = v["decimal_parts"].as_array().expect("decimal_parts");
    assert!(!rows.is_empty(), "the decimal_parts table is not empty");
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let parts = row["parts"].as_array().expect("parts");
        let mantissa = BigInt::from_i128(i128::from(parts[0].as_i64().expect("mantissa")));
        let exponent = i128::from(parts[1].as_i64().expect("exponent"));
        let built = BigDecimal::from_parts(mantissa, exponent);
        let got = built.as_ref().map(decimal_value);
        let want = &row["expected"];
        if want.as_str() == Some("out_of_band") {
            assert_eq!(got, None, "{name}");
        } else {
            assert_eq!(got, Some(value(want)), "{name}");
        }
    }
}

#[test]
fn every_decimal_decode_row_holds() {
    let v = vectors();
    let rows = v["decimal_decode"].as_array().expect("decimal_decode");
    assert!(!rows.is_empty(), "the decimal_decode table is not empty");
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let term = Term::from_value(&value(&row["value"]));
        let decoded = BigDecimal::from_decimal_term(&term);
        let got = decoded.as_ref().map(decimal_value);
        let want = &row["expected"];
        if want.as_str() == Some("not_a_canonical_decimal") {
            assert_eq!(got, None, "{name}");
        } else {
            assert_eq!(got, Some(value(want)), "{name}");
        }
    }
}

// ---- the product semiring (v2 §14.2), each one as its `products` row defines it ----

/// The laws a product fixture declares beyond its members' AND: exactly the named ones. An
/// unknown law name panics.
fn declared(names: &[String]) -> LawDeclaration {
    let mut laws = LawDeclaration::default();
    for name in names {
        match name.as_str() {
            "idempotent" => laws.idempotent = true,
            "bounded" => laws.bounded = true,
            "monotone" => laws.monotone = true,
            "commutative" => laws.commutative = true,
            "supports_retraction" => laws.supports_retraction = true,
            other => panic!("declares_also names an unknown law {other:?}"),
        }
    }
    laws
}

/// A product fixture: the product of its members, declaring also the laws its row names.
/// Everything but `laws` is the product's own, its declared identity included.
struct DeclaresAlso {
    product: ProductSemiring,
    also: LawDeclaration,
}

impl Semiring for DeclaresAlso {
    fn declared_identity(&self) -> ComponentIdentity {
        self.product.declared_identity()
    }

    fn laws(&self) -> LawDeclaration {
        let (own, also) = (self.product.laws(), self.also);
        LawDeclaration {
            idempotent: own.idempotent || also.idempotent,
            bounded: own.bounded || also.bounded,
            monotone: own.monotone || also.monotone,
            commutative: own.commutative || also.commutative,
            supports_retraction: own.supports_retraction || also.supports_retraction,
        }
    }

    fn zero(&self) -> Value {
        self.product.zero()
    }

    fn one(&self) -> Value {
        self.product.one()
    }

    fn is_element(&self, value: &Value) -> bool {
        self.product.is_element(value)
    }

    fn add(&self, a: &Value, b: &Value) -> SemiringAnswer {
        self.product.add(a, b)
    }

    fn mul(&self, a: &Value, b: &Value) -> SemiringAnswer {
        self.product.mul(a, b)
    }
}

/// The two member names a `products` row lists, in order.
fn members(row: &Json) -> [&str; 2] {
    let listed = row["members"].as_array().expect("members is an array");
    let [first, second] = listed.as_slice() else {
        panic!("a product has exactly two members, not {listed:?}");
    };
    [first, second].map(|m| m.as_str().expect("a name"))
}

/// The product a `products` row defines, built from this core's own semirings: its two
/// `members` in order (an unknown member panics) and, for the one fixture, the laws its row
/// `declares_also`. An unknown kind or fixture panics.
fn build_product(v: &Json, row: &Json) -> Built {
    let name = row["name"].as_str().expect("name");
    let [first, second] = members(row);
    let product = ProductSemiring::new(semiring_named(v, first), semiring_named(v, second));
    match (row["kind"].as_str().expect("kind"), name) {
        ("core", _) => Box::new(product),
        ("fixture", "counting_x_tropical_declared_bounded") => {
            let also = declared(&law_names(&row["declares_also"]));
            Box::new(DeclaresAlso { product, also })
        }
        (kind, name) => panic!("vectors/semiring.json names an unknown {kind} product {name:?}"),
    }
}

/// The product a row refers to by name, from the `products` table.
fn product_named(v: &Json, name: &str) -> Built {
    let rows = v["products"].as_array().expect("products is an array");
    let Some(row) = rows.iter().find(|r| r["name"] == name) else {
        panic!("no product named {name:?}");
    };
    build_product(v, row)
}

/// The names of the `semirings` table's core rows, in table order.
fn core_names(v: &Json) -> Vec<String> {
    let mut cores = Vec::new();
    for row in v["semirings"].as_array().expect("semirings is an array") {
        if row["kind"] == "core" {
            let name = row["name"].as_str().expect("name");
            cores.push(name.to_string());
        }
    }
    cores
}

#[test]
fn every_product_reproduces_its_identity_laws_zero_and_one() {
    let v = vectors();
    let rows = v["products"].as_array().expect("products is an array");
    assert!(!rows.is_empty(), "the products table is not empty");
    let mut identities = BTreeMap::new();
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let s = build_product(&v, row);
        assert_identity_row(name, &*s, row);
        if row["kind"] == "core" {
            let [first, second] = members(row);
            let pair = (first.to_string(), second.to_string());
            let earlier = identities.insert(pair, semiring_identity(&*s));
            assert!(earlier.is_none(), "{name}: a repeated pair");
        }
    }
    let cores = core_names(&v);
    assert_eq!(cores.len(), 4, "the four core semirings");
    let mut pairs = Vec::new();
    for first in &cores {
        for second in &cores {
            pairs.push((first.clone(), second.clone()));
        }
    }
    pairs.sort();
    let carried: Vec<_> = identities.keys().cloned().collect();
    assert_eq!(carried, pairs, "every ordered pair of the cores, once");
    for ((a, b), ab) in &identities {
        let ba = &identities[&(b.clone(), a.clone())];
        if a != b {
            assert_ne!(ab, ba, "{a}_x_{b} and {b}_x_{a} share an identity");
        }
    }
}

#[test]
fn every_product_operation_row_holds() {
    let v = vectors();
    let rows = v["product_ops"].as_array().expect("product_ops");
    assert!(!rows.is_empty(), "the product_ops table is not empty");
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let s = product_named(&v, row["product"].as_str().expect("product"));
        assert_answer(name, run_op(name, &*s, row), &row["expected"]);
    }
}

#[test]
fn every_product_audit_row_reproduces_its_verdict() {
    let v = vectors();
    let rows = v["product_audits"].as_array().expect("product_audits");
    assert!(!rows.is_empty(), "the product_audits table is not empty");
    for row in rows {
        let name = row["name"].as_str().expect("name");
        let s = product_named(&v, row["product"].as_str().expect("product"));
        let got = audit_semiring(&*s, &values(&row["samples"]));
        assert_verdict(name, got, &row["verdict"]);
    }
}
