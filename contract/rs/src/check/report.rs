//! `check()`'s report of the work it actually performed (checker SPI v2, ADR 0036 D8 change 5;
//! design 0006 P1, #1932, `seat:caa`'s decision of 2026-10-04 (shape O) and the coordinator's
//! ruling of 2026-11-12 (O-struct)).
//!
//! The report rides beside the verdict in [`Outcome`](super::Outcome) and never decides it: an
//! outcome's equality is its verdict's, so a counter can never turn a verdict test red. It counts
//! the work done up to and including a rejecting node.
//!
//! **Counters are defined per checker version.** [`CHECK_REPORT_COUNTERS_VERSION`] names the
//! checker version whose counting rules these are, and a kernel test pins it equal to
//! `CHECKER_VERSION` in every core: a change to what a counter counts is a checker-version bump.
//! The tri-core pin is the rows of `vectors/check.json` and `vectors/negation.json` that state a
//! `report` (#4206): every counter hand-computed from the rules below, and asserted exactly by each
//! core's replay of those files (every core's conformance CLI under `conformance/harness.mjs`, and
//! the go and ts negation replays in process). The three `check_report_3111` tests
//! (`contract/rs/tests/check_report_3111.rs`, `contract/go/check_report_3111_test.go` and
//! `contract/ts/test/check_report_3111.test.ts`) are worked examples of the same rules on tiny
//! hand-built derivations.
//!
//! # The counting rules (normative; the go and ts cores mirror this list)
//!
//! One report accumulator is threaded through the check (rs: the private `Tally`, passed as
//! `&mut`), never held in ambient state. Each increment site carries a comment naming its counter.
//! Every counter below is `Counted` in rs.
//!
//! - **`nodes_walked`**: +1 when the forward pass begins a derivation node, before any of the
//!   node's own checks, so a node that then rejects counts. The pass runs in node order and stops
//!   at the first rejecting node, so the nodes after it are not walked; an accepted check walks
//!   every node.
//! - **`rule_nodes` / `builtin_nodes` / `leaf_nodes`**: +1 for that node, by its kind, at the same
//!   point. The three sum to `nodes_walked` ([`CheckReport::node_kinds_sum`]).
//! - **`premises_pos` / `premises_neg`**: +1 when a `Rule` node's step (f) begins matching premise
//!   `k` against body literal `k`, counted by the PREMISE's own kind: a `Pos` premise is positive,
//!   a `Neg` premise negative, and a `Count` premise POSITIVE. A premise is counted before its
//!   checks, so a premise that rejects (a polarity mismatch included) counts. The premises of a
//!   node that rejects before step (f) (an unknown clause, a premise naming no earlier node, the
//!   depth cap, the head, the premise count) are not counted, and nor are the premises after a
//!   rejecting one.
//! - **`theory_decisions`**: +1 for each call the checker makes to a theory's `decide_ground`,
//!   anywhere: a `Builtin` node's decision, a certificate support edge's `Builtin` reference, and
//!   a closure filter on a theory-owned literal of either polarity. `owns` is not counted.
//! - **`leaf_verifications`**: +1 for each `LeafVerifier::verify` call (a `Leaf` node that passed
//!   its partition checks). `edb_snapshot` is not counted.
//! - **`admissibility_checks`**: +1 for each `RuleAdmissibility::admissible` call (a `Rule` node's
//!   step (h)).
//! - **`certs_verified`**: +1 for each closed-model certificate whose verification runs, whatever
//!   status it ends in. A certificate refused as a whole by the unbound-context gate, without its
//!   verification running, is not counted, and nor is one a [`WorldMemo`](super::WorldMemo)
//!   served. The chain check counts each certificate it verifies, in its verification order, up to
//!   and including the first invalid one.
//! - **`certs_memo_hits`**: +1 for each certificate of a closed world whose statuses the
//!   [`WorldMemo`](super::WorldMemo) served instead of verifying them. A miss verifies the world,
//!   and its certificates count under `certs_verified`.
//! - **`cert_tables_read` / `cert_rows_read`**: the unit is one certificate TABLE, one predicate's
//!   sealed extension (`ClosedModelCert::extensions`), and its rows. When a verification's
//!   canonical-form gate (step 1b, the first gate to read the rows) begins a table:
//!   `cert_tables_read` +1 and `cert_rows_read` + that table's row count. Each table counts once
//!   per verification: the later gates' re-reads, and a `Neg` or `Count` premise's lookup in a
//!   verified table, are not counted. A certificate refused before the gate reaches its tables
//!   (the budget gate, or a non-canonical scope or domain) reads none, and the tables after the
//!   first non-canonical one are not read.
//! - **`join_steps_used` / `groundings_enumerated`**: per verified certificate, the closure gate's
//!   own two budget meters (the join steps metered against `max_join_steps`, and the rule
//!   groundings metered against `max_rule_groundings`) as they stand when the gate ends, summed
//!   over the certificates. A meter that trips reports the count it tripped at. A certificate
//!   whose verification ends before the closure gate adds nothing.
//! - **`max_depth_reached`**: the largest derivation depth the forward pass computed and compared
//!   against `max_depth` (a `Rule` node's step (c), and 1 for a `Builtin` or `Leaf` node),
//!   including the depth that trips `too_deep`. 0 when no node got that far.
//! - **`max_term_depth_reached`**: the largest term depth the term-depth cap (step 3b, and the
//!   chain check's per-certificate cap) measured against `max_term_depth`. An atom is 1, and the
//!   measurement stops at the first level past the cap, so a `term_too_deep` refusal reports
//!   `max_term_depth + 1`.
//!
//! **A check refused before the walk reports zeros plus what was genuinely done.** Invalid limits,
//! an empty derivation, the node cap and a root out of range report [`CheckReport::zero`]; a
//! `term_too_deep` refusal reports zeros except `max_term_depth_reached`, since the cap measured
//! terms. The chain check refuses an invalid configuration and an empty chain with zeros, and an
//! unbound context with only the term depths it measured.

use super::{Outcome, Verdict};
use crate::derivation::Premise;
use crate::term::Term;
use ontos_core::Value;

/// The checker version whose counting rules [`CheckReport`]'s counters follow. A kernel test
/// asserts it equals `CHECKER_VERSION`.
pub const CHECK_REPORT_COUNTERS_VERSION: u32 = 24;

/// One counter: a count the checker kept, or `Unsupported` where this core does not count it.
/// `Unsupported` is never a zero (omit, never fake).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReportCount {
    Counted(u64),
    Unsupported,
}

impl ReportCount {
    /// The count, or `None` where it is not supported.
    pub fn get(self) -> Option<u64> {
        match self {
            ReportCount::Counted(n) => Some(n),
            ReportCount::Unsupported => None,
        }
    }
}

impl Default for ReportCount {
    fn default() -> Self {
        ReportCount::Counted(0)
    }
}

/// The work one `check` performed. Each field's increment event is stated on it; the three node
/// kinds sum to `nodes_walked`, a checked invariant.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct CheckReport {
    /// The checker version whose counting rules these counters follow.
    pub counters_version: u32,
    /// Each derivation node visited, up to and including a rejecting node.
    pub nodes_walked: ReportCount,
    /// Each `Rule` node visited.
    pub rule_nodes: ReportCount,
    /// Each `Builtin` node visited.
    pub builtin_nodes: ReportCount,
    /// Each `Leaf` node visited.
    pub leaf_nodes: ReportCount,
    /// Each positive premise examined.
    pub premises_pos: ReportCount,
    /// Each negative premise examined.
    pub premises_neg: ReportCount,
    /// Each call to a theory's `decide_ground`.
    pub theory_decisions: ReportCount,
    /// Each leaf-verifier call.
    pub leaf_verifications: ReportCount,
    /// Each rule-admissibility test.
    pub admissibility_checks: ReportCount,
    /// Each closed-model certificate verified (a memo hit is not a verification).
    pub certs_verified: ReportCount,
    /// Each certificate whose verification was answered by the world memo instead.
    pub certs_memo_hits: ReportCount,
    /// Each certificate table read during verification.
    pub cert_tables_read: ReportCount,
    /// Each certificate row read during verification.
    pub cert_rows_read: ReportCount,
    /// The closure join steps actually spent (beside the declared `max_join_steps` budget).
    pub join_steps_used: ReportCount,
    /// The rule groundings actually enumerated (beside the declared `max_rule_groundings`).
    pub groundings_enumerated: ReportCount,
    /// The deepest derivation depth reached.
    pub max_depth_reached: ReportCount,
    /// The deepest term depth reached.
    pub max_term_depth_reached: ReportCount,
}

impl CheckReport {
    /// A report under the current counting rules with every counter at zero: what a check refused
    /// before its walk reports.
    pub fn zero() -> Self {
        CheckReport {
            counters_version: CHECK_REPORT_COUNTERS_VERSION,
            ..CheckReport::default()
        }
    }

    /// `rule_nodes + builtin_nodes + leaf_nodes == nodes_walked`, where all four are counted.
    pub fn node_kinds_sum(&self) -> bool {
        match (
            self.nodes_walked.get(),
            self.rule_nodes.get(),
            self.builtin_nodes.get(),
            self.leaf_nodes.get(),
        ) {
            (Some(n), Some(r), Some(b), Some(l)) => r + b + l == n,
            (None, None, None, None) => true,
            (_, _, _, _) => false,
        }
    }
}

/// One check's running counts (#3111): plain counters the checker bumps at the points the module
/// doc names, turned into the [`CheckReport`] of the [`Outcome`] once the check ends. Private to
/// the checker, and threaded through it as `&mut Tally`.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Tally {
    pub(super) nodes_walked: u64,
    pub(super) rule_nodes: u64,
    pub(super) builtin_nodes: u64,
    pub(super) leaf_nodes: u64,
    pub(super) premises_pos: u64,
    pub(super) premises_neg: u64,
    pub(super) theory_decisions: u64,
    pub(super) leaf_verifications: u64,
    pub(super) admissibility_checks: u64,
    pub(super) certs_verified: u64,
    pub(super) certs_memo_hits: u64,
    pub(super) cert_tables_read: u64,
    pub(super) cert_rows_read: u64,
    pub(super) join_steps_used: u64,
    pub(super) groundings_enumerated: u64,
    pub(super) max_depth_reached: u64,
    pub(super) max_term_depth_reached: u64,
}

impl Tally {
    /// `premises_pos` / `premises_neg`: one premise examined, by its kind (a count is positive).
    pub(super) fn premise(&mut self, premise: &Premise) {
        match premise {
            Premise::Pos { .. } | Premise::Count { .. } => self.premises_pos += 1,
            Premise::Neg { .. } => self.premises_neg += 1,
        }
    }

    /// `max_depth_reached`: one derivation depth compared against `max_depth`.
    pub(super) fn reach_depth(&mut self, depth: usize) {
        self.max_depth_reached = self.max_depth_reached.max(depth as u64);
    }

    /// `max_term_depth_reached`: measure `term` against `max`; `true` when it is within.
    pub(super) fn term_within(&mut self, term: &Term, max: usize) -> bool {
        self.reach_term_depth(term.depth_capped(max), max)
    }

    /// `max_term_depth_reached`: measure `value` against `max`; `true` when it is within.
    pub(super) fn value_within(&mut self, value: &Value, max: usize) -> bool {
        self.reach_term_depth(crate::term::value_depth_capped(value, max), max)
    }

    fn reach_term_depth(&mut self, depth: usize, max: usize) -> bool {
        self.max_term_depth_reached = self.max_term_depth_reached.max(depth as u64);
        depth <= max
    }

    /// The check's result: `verdict`, with the report of the work counted so far.
    pub(super) fn outcome(&self, verdict: Verdict) -> Outcome {
        Outcome {
            verdict,
            report: self.report(),
        }
    }

    /// The report: every counter `Counted`, since rs counts all of them. Destructured with no
    /// `..`, so a new counter does not compile until it is placed here.
    fn report(&self) -> CheckReport {
        let Tally {
            nodes_walked,
            rule_nodes,
            builtin_nodes,
            leaf_nodes,
            premises_pos,
            premises_neg,
            theory_decisions,
            leaf_verifications,
            admissibility_checks,
            certs_verified,
            certs_memo_hits,
            cert_tables_read,
            cert_rows_read,
            join_steps_used,
            groundings_enumerated,
            max_depth_reached,
            max_term_depth_reached,
        } = *self;
        CheckReport {
            counters_version: CHECK_REPORT_COUNTERS_VERSION,
            nodes_walked: ReportCount::Counted(nodes_walked),
            rule_nodes: ReportCount::Counted(rule_nodes),
            builtin_nodes: ReportCount::Counted(builtin_nodes),
            leaf_nodes: ReportCount::Counted(leaf_nodes),
            premises_pos: ReportCount::Counted(premises_pos),
            premises_neg: ReportCount::Counted(premises_neg),
            theory_decisions: ReportCount::Counted(theory_decisions),
            leaf_verifications: ReportCount::Counted(leaf_verifications),
            admissibility_checks: ReportCount::Counted(admissibility_checks),
            certs_verified: ReportCount::Counted(certs_verified),
            certs_memo_hits: ReportCount::Counted(certs_memo_hits),
            cert_tables_read: ReportCount::Counted(cert_tables_read),
            cert_rows_read: ReportCount::Counted(cert_rows_read),
            join_steps_used: ReportCount::Counted(join_steps_used),
            groundings_enumerated: ReportCount::Counted(groundings_enumerated),
            max_depth_reached: ReportCount::Counted(max_depth_reached),
            max_term_depth_reached: ReportCount::Counted(max_term_depth_reached),
        }
    }
}
