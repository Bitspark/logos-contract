//! #2258 (a): STACKED certificates. A sealed clause may read a predicate its own certificate
//! does not seal when a certificate at a STRICTLY LOWER scope level seals it: uniquely, exactly
//! (not in that certificate's `partial_scope`, ADR 0030 D2), and Valid. The citing certificate
//! then reads that lower table: a negated literal is true iff the atom is absent from it, a
//! positive literal binds over its rows.
//!
//! Soundness rests on the order [`verification_order`] fixes: a certificate is verified only
//! after every certificate at a lower level, so a lower table is read only once its own support,
//! closure and EDB obligations have made it the exact least model of its predicate. References
//! go strictly down in level, so the citation graph is acyclic by construction, and an invalid
//! certificate nothing resolves against stays inert (seat:caa's C3 amendment).

use super::cert::CertStatus;
use super::RejectionCode;
use crate::cert::{ClosedModelCert, RelationTable};
use crate::fragment::{ScopeReads, SealContext};
use crate::literal::{GroundLiteral, Symbol};
use crate::program::CompleteProgram;
use crate::spi::Theory;
use ontos_core::Value;
use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet};

/// The order the certificates of a `closed_world` are verified in: ascending scope level, ties
/// by index. Every certificate a cert at level `L` can resolve against sits at a level below
/// `L`, so its status is final before that cert is verified.
pub(super) fn verification_order(world: &[ClosedModelCert]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..world.len()).collect();
    order.sort_by_key(|&i| (world[i].scope.level, i));
    order
}

/// One certificate's view of the tables its sealed clauses read: its OWN sealed tables, and each
/// predicate it reads from a strictly lower certificate, resolved to that certificate. The
/// closure join, the body-literal evaluation and the support gate all read tables through it.
pub(super) struct CertView<'a> {
    /// The certificate being verified.
    pub(super) cert: &'a ClosedModelCert,
    /// Predicates read from a lower certificate: its index in `closed_world`, and the cert.
    lower: BTreeMap<Symbol, (usize, &'a ClosedModelCert)>,
    /// #3067 increment 3: what the certificate's sealed clauses read without sealing, the one
    /// computation the seal plan shares ([`ScopeReads`]); `lower` resolves each of them.
    reads: ScopeReads,
    /// #2511: each table this view has been asked about, as the set of its rows, keyed by the
    /// table's address. Built on first use and kept for the view's life (see [`Self::contains`]).
    ///
    /// ⚠ The ADDRESS is a sound key only while the view's immutable borrow (`'a`) of every table it
    /// serves holds: no table can move, be mutated or be freed under it, so one address is one
    /// table with one set of rows for as long as the entry exists. The borrow checker enforces
    /// that for the view's lifetime; an index that outlived the view, or a table reached through
    /// anything but a `&'a` borrow, would lose the guarantee and must not reuse this key.
    members: RefCell<HashMap<usize, HashSet<&'a GroundLiteral>>>,
    /// #2511: every value of the certificate's finite domains, as a set built on first use (see
    /// [`Self::in_domain`]).
    domain: OnceCell<HashSet<&'a Value>>,
    /// #3111 `theory_decisions`: the `decide_ground` calls the support and closure gates made
    /// through this view, which `verify_cert` adds to the check's report once the gates end. The
    /// view is the one context both gates already share down to the deciding site.
    decisions: Cell<u64>,
}

impl<'a> CertView<'a> {
    /// A view that reads only the certificate's own tables: every certificate before #2258 (a),
    /// and the producer's cost model, which measures one certificate.
    pub(super) fn own(cert: &'a ClosedModelCert) -> Self {
        CertView {
            cert,
            lower: BTreeMap::new(),
            reads: ScopeReads::new(),
            members: RefCell::new(HashMap::new()),
            domain: OnceCell::new(),
            decisions: Cell::new(0),
        }
    }

    /// #3111 `theory_decisions`: one `decide_ground` call made through this view.
    pub(super) fn count_decision(&self) {
        self.decisions.set(self.decisions.get() + 1);
    }

    /// The `decide_ground` calls made through this view so far.
    pub(super) fn theory_decisions(&self) -> u64 {
        self.decisions.get()
    }

    /// Does one of the certificate's finite domains hold `v` (#2511)? The answer
    /// `ClosedModelCert::domain_containing` gives, by value equality, which is the relation its
    /// codec-byte binary search decides (the encoding is injective); `verify_cert` has rejected a
    /// non-canonical domain before any caller runs. A set is built once per view, so a head's
    /// argument costs a hash rather than a search that encodes a value at each step.
    pub(super) fn in_domain(&self, v: &Value) -> bool {
        self.domain
            .get_or_init(|| {
                self.cert
                    .domains
                    .iter()
                    .flat_map(|d| d.values.iter())
                    .collect()
            })
            .contains(v)
    }

    /// Is `fact` a row of `table` (#2511)? The answer [`RelationTable::contains`] gives, by the
    /// relation it decides: equal canonical keys, which is structural equality, since the
    /// canonical encoding is injective. Every caller runs after `verify_cert`'s canonicity gate,
    /// where the binary search is exact too. A set of the table's rows is built once per view, so
    /// a probe costs a hash; the binary search encoded a row at each of its log C steps, on every
    /// verified head, filter and support reference.
    pub(super) fn contains(&self, table: &'a RelationTable, fact: &GroundLiteral) -> bool {
        let id = std::ptr::from_ref(table) as usize;
        self.members
            .borrow_mut()
            .entry(id)
            .or_insert_with(|| table.rows.iter().collect())
            .contains(fact)
    }

    /// The table a sealed clause reads for `pred`: the certificate's own if it seals `pred`,
    /// else the resolved lower certificate's. `None` for a predicate neither provides.
    pub(super) fn table(&self, pred: &Symbol) -> Option<&'a RelationTable> {
        if self.cert.scope.seals(pred) {
            return self.cert.table(pred);
        }
        self.lower.get(pred).and_then(|(_, cert)| cert.table(pred))
    }

    /// A view that reads `preds` from `lower`, stated directly rather than resolved from a world:
    /// `vectors/fragment.json`'s replay (#3067) names a clause's context by hand.
    #[cfg(test)]
    pub(super) fn with_lower(
        cert: &'a ClosedModelCert,
        lower: &'a ClosedModelCert,
        preds: &[Symbol],
    ) -> Self {
        let mut view = CertView::own(cert);
        for pred in preds {
            view.lower.insert(pred.clone(), (0, lower));
        }
        // The context is stated by hand, so the reads are exactly the relations read lower.
        view.reads = ScopeReads::stated(preds.to_vec());
        view
    }

    /// The context this certificate's sealed clauses are classified in (#3067, research 0028 row
    /// A15): the relations it seals, and the reads a strictly lower certificate resolved, through
    /// the one computation the seal plan shares ([`ScopeReads::context`], increment 3).
    pub(super) fn seal_context(&self) -> SealContext {
        self.reads.context(
            self.cert.scope.predicates.iter().cloned().collect(),
            &|pred: &Symbol| self.lower.contains_key(pred),
        )
    }

    /// True iff `pred` is read from a strictly lower certificate.
    pub(super) fn reads_lower(&self, pred: &Symbol) -> bool {
        self.lower.contains_key(pred)
    }

    /// The `closed_world` index of the lower certificate `pred` resolved to, if any.
    pub(super) fn lower_index(&self, pred: &Symbol) -> Option<usize> {
        self.lower.get(pred).map(|(index, _)| *index)
    }
}

/// Resolve every predicate the certificate at `own` reads without sealing it: a body literal of
/// a defining clause of one of its sealed predicates (a counted literal's relation included,
/// #2258 L3.3b), on a predicate it does not seal and no theory owns. For each, the certificates
/// at a strictly lower level that seal it:
///
/// - none: left unresolved; the scope gate refuses the literal, as it always has;
/// - more than one: `cert_scope_incomplete`, ambiguous (decided on structure alone, so the
///   verdict never depends on another certificate's);
/// - one, sealing it in its `partial_scope`: `cert_scope_incomplete`, since a lower bound read by
///   a sealed clause makes that clause's closure (or its negation) vacuous;
/// - one, Invalid: that certificate's own code, the detail naming the chain, so the root cause is
///   what the verdict reports;
/// - one, exact and Valid: resolved.
///
/// `status` holds the final status of every certificate at a lower level (the
/// [`verification_order`] guarantees it). `None` resolves on structure alone, for the producer's
/// cost model, which measures a certificate before anything is verified.
pub(super) fn resolve_lower_seals<'a>(
    cert: &'a ClosedModelCert,
    own: usize,
    world: &'a [ClosedModelCert],
    status: Option<&[Option<CertStatus>]>,
    program: &dyn CompleteProgram,
    theory: &dyn Theory,
) -> Result<CertView<'a>, (RejectionCode, String)> {
    let mut view = CertView::own(cert);
    // #3067 increment 3: the reads are the one computation the seal plan shares, in the order
    // this loop has always met them (clause order, then body order).
    let mut reads = ScopeReads::new();
    let seals = |pred: &Symbol| cert.scope.seals(pred);
    let owns = |pred: &Symbol| theory.owns(pred);
    program.for_each_clause(&mut |_id, clause| reads.add(clause, &seals, &owns));
    let mut err: Option<(RejectionCode, String)> = None;
    for pred in reads.iter() {
        // #2258 L3.3b: a count's counted predicate resolves like any other literal's, so a
        // count over a strictly lower seal is readable and the scope gate can admit it.
        let sealers: Vec<usize> = (0..world.len())
            .filter(|&j| world[j].scope.level < cert.scope.level && world[j].scope.seals(pred))
            .collect();
        let name = String::from_utf8_lossy(pred.bytes());
        match sealers.as_slice() {
            [] => {}
            [j] => {
                let j = *j;
                if world[j].is_partial(pred) {
                    err = Some((
                        RejectionCode::CertScopeIncomplete,
                        format!(
                            "certificate {own} reads predicate {name:?}, which certificate {j} seals PARTIAL (a lower bound cannot be read by a sealed clause, ADR 0030 D2)"
                        ),
                    ));
                    break;
                }
                let Some(status) = status else {
                    view.lower.insert(pred.clone(), (j, &world[j]));
                    continue;
                };
                match &status[j] {
                    Some(CertStatus::Valid) => {
                        view.lower.insert(pred.clone(), (j, &world[j]));
                    }
                    Some(CertStatus::Invalid(code, detail)) => {
                        err = Some((
                            *code,
                            format!(
                                "certificate {own} rests on certificate {j} for predicate {name:?}, which is invalid: {detail}"
                            ),
                        ));
                        break;
                    }
                    // The verification order makes every lower status final first; a
                    // missing one is a checker defect, refused rather than read as Valid.
                    None => {
                        err = Some((
                            RejectionCode::CertScopeIncomplete,
                            format!(
                                "certificate {own} would read predicate {name:?} from certificate {j} before it is verified"
                            ),
                        ));
                        break;
                    }
                }
            }
            many => {
                err = Some((
                    RejectionCode::CertScopeIncomplete,
                    format!(
                        "predicate {name:?} is sealed by more than one strictly lower certificate ({many:?}); a stacked read needs a unique lower seal"
                    ),
                ));
                break;
            }
        }
    }
    view.reads = reads;
    match err {
        Some(e) => Err(e),
        None => Ok(view),
    }
}

/// #3067 increment 3 (research 0028 row A15; `seat:caa`'s ruling Q2): the clause context `check`
/// reconstructs for every certificate of `world`, in world order: the relations each certificate
/// seals, and the relations its sealed clauses read from a strictly lower certificate, resolved
/// exactly as `check` resolves them ([`resolve_lower_seals`], on structure alone, since a producer
/// asks before anything is verified). The certifying producer compares it with the seal plan's
/// contexts before it returns a stack.
///
/// A PRODUCER-FACING rs helper, like [`super::closure_join_cost_in_world`]: it is not interface.
/// The SPI's wire and verdicts do not change, and there is no go or ts producer to call it
/// (research 0021: interface parity binds the wire, not an internal helper), so its rs-only
/// existence is not parity debt.
pub fn seal_contexts(
    world: &[ClosedModelCert],
    program: &dyn CompleteProgram,
    theory: &dyn Theory,
) -> Result<Vec<SealContext>, (RejectionCode, String)> {
    (0..world.len())
        .map(|i| {
            resolve_lower_seals(&world[i], i, world, None, program, theory)
                .map(|view| view.seal_context())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    //! #2551 (`seat:caa`'s condition 1): the view's hash membership against the encode-and-binary-
    //! search it replaces, over tables and a domain built from NEAR-COLLIDING values, so the
    //! injectivity the equivalence rests on is pinned by a test rather than argued.
    use super::*;
    use crate::cert::{CertSizeDecl, ClosureWitness, FiniteDomain, StratumPrefix, SupportWitness};

    fn a(bytes: &[u8]) -> Value {
        Value::atom(bytes.to_vec())
    }

    /// Values that differ by as little as the value model allows: an int against the atom of its
    /// digits, `null()` against the atom `null`, the empty tuple against the empty atom, a tuple
    /// against its only element, and nesting shifted between positions.
    fn near_collisions() -> Vec<Value> {
        vec![
            a(b""),
            a(b"1"),
            a(b"0"),
            a(b"null"),
            a(b"\0"),
            ontos_data::encode_int(1),
            ontos_data::encode_int(-1),
            ontos_data::encode_int(0),
            ontos_data::encode_bool(true),
            ontos_data::encode_bool(false),
            ontos_data::encode_list(&[]),
            ontos_data::encode_list(&[ontos_data::encode_int(1)]),
            Value::tuple([]),
            Value::tuple([a(b"null")]),
            Value::tuple([a(b"")]),
            Value::tuple([a(b"1")]),
            Value::tuple([Value::tuple([])]),
            Value::tuple([a(b"a"), a(b"b")]),
            Value::tuple([Value::tuple([a(b"a")]), a(b"b")]),
            Value::tuple([a(b"a"), Value::tuple([a(b"b")])]),
        ]
    }

    fn cert(tables: Vec<RelationTable>, domain: FiniteDomain) -> ClosedModelCert {
        let preds: Vec<Symbol> = tables.iter().map(|t| t.pred.clone()).collect();
        ClosedModelCert {
            scope: StratumPrefix::new(1, preds),
            program_hash: [0; 32],
            profile_hash: [0; 32],
            ctx_hash: [0; 32],
            theory_config_hash: [0; 32],
            edb_snapshot_hashes: vec![],
            domains: vec![domain],
            extensions: tables,
            supports: SupportWitness(vec![]),
            closure: ClosureWitness,
            decomposition_witness: None,
            partial_scope: None,
            limits_decl: CertSizeDecl {
                cert_facts: 0,
                domain_values: 0,
                support_edges: 0,
                rule_groundings: 0,
                join_steps: 0,
                cert_bytes: 0,
            },
        }
    }

    #[test]
    fn hash_membership_is_the_binary_search_over_near_colliding_values_2551() {
        let values = near_collisions();
        // ⭐ The control, FIRST: the pool really is distinct values with distinct canonical
        // encodings, near-collisions included, so the rows below compare a real partition.
        for (i, x) in values.iter().enumerate() {
            for y in &values[i + 1..] {
                assert_ne!(x, y, "the pool holds a duplicate value");
                assert_ne!(
                    ontos_codec::encode(x),
                    ontos_codec::encode(y),
                    "two distinct values share an encoding: {x:?} and {y:?}"
                );
            }
        }
        assert_ne!(ontos_data::encode_int(1), a(b"1"), "int 1 is not atom 1");
        assert_ne!(
            Value::tuple([a(b"null")]),
            a(b"null"),
            "null() is not the atom null"
        );

        // Unary and binary rows over the pool; every other candidate is a member, so each table
        // holds near-collisions on both sides of the partition.
        let unary: Vec<GroundLiteral> = values
            .iter()
            .map(|v| GroundLiteral::new("p", [v.clone()]))
            .collect();
        let binary: Vec<GroundLiteral> = values
            .iter()
            .flat_map(|x| {
                values
                    .iter()
                    .map(move |y| GroundLiteral::new("q", [x.clone(), y.clone()]))
            })
            .collect();
        let members = |rows: &[GroundLiteral]| -> Vec<GroundLiteral> {
            rows.iter()
                .enumerate()
                .filter(|(i, _)| i % 2 == 0)
                .map(|(_, r)| r.clone())
                .collect()
        };
        let p = RelationTable::new("p", 1, members(&unary));
        let q = RelationTable::new("q", 2, members(&binary));
        let domain = FiniteDomain::new(
            Symbol::new(b"d".to_vec()),
            values
                .iter()
                .enumerate()
                .filter(|(i, _)| i % 3 != 0)
                .map(|(_, v)| v.clone()),
        );
        let c = cert(vec![p, q], domain);
        let view = CertView::own(&c);
        let (p, q) = (&c.extensions[0], &c.extensions[1]);

        let (mut hits, mut misses) = (0, 0);
        for (table, probes) in [(p, &unary), (q, &binary)] {
            for probe in probes {
                let hashed = view.contains(table, probe);
                assert_eq!(hashed, table.contains(probe), "membership of {probe:?}");
                if hashed {
                    hits += 1;
                } else {
                    misses += 1;
                }
                // The literal of another predicate or arity is never a member, by either path.
                let other = GroundLiteral::new("r", probe.args.clone());
                assert!(!view.contains(table, &other) && !table.contains(&other));
            }
        }
        assert!(
            hits > 0 && misses > 0,
            "{hits} members and {misses} non-members probed"
        );

        let (mut inside, mut outside) = (0, 0);
        for v in &values {
            let hashed = view.in_domain(v);
            assert_eq!(
                hashed,
                c.domains[0].contains(v),
                "domain membership of {v:?}"
            );
            if hashed {
                inside += 1;
            } else {
                outside += 1;
            }
        }
        assert!(
            inside > 0 && outside > 0,
            "{inside} in the domain and {outside} out"
        );
    }
}
