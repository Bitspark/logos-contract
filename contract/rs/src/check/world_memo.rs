//! #2565 term 1 (`seat:caa`'s ruling on #2565, 2026-09-25): a memo of one closed world's
//! certificate verification, so a gate that checks many answers citing the SAME certificates
//! verifies them once rather than once per answer.
//!
//! Measured before this (#2565, negtree n = 1000): 490 answers each re-verified the one boundary
//! certificate their `\+` leaf cites, and the gate was 56.6% of the run.
//!
//! **Why the unit is the whole world.** A stacked certificate's verdict reads the statuses of the
//! lower certificates in the same world (`verify_cert`'s `world` and `status`), so a key per
//! certificate would have to bind its world anyway.
//!
//! **Why it lives in the checker.** A memo kept by a caller would need `check` to accept statuses
//! from that caller, which is a caller-supplied verdict. [`WorldMemo`]'s fields are private and only
//! the checker fills them: a caller can present a memo, never a verdict.

use super::cert::CertStatus;
use super::{verify_world, CertContext, CheckLimits, CheckProfile};
use crate::program::Program;
use crate::ClosedModelCert;

/// One closed world's verified certificate statuses, and everything they were computed under.
///
/// A lookup is a HIT only when ALL of these hold, and anything else re-verifies and replaces the
/// single slot:
///
/// - the derivation's `closed_world` is **structurally equal** to the memoized one: every
///   certificate, in order. That is exact equality, not a digest, so no collision assumption; and
///   structural equality is canonical-byte equality, since the canonical encoding is injective;
/// - the `program`, `profile` and `ctx` are the **same objects** as the call that filled it. The
///   memo BORROWS all three for its whole lifetime (`'a`), so an address it compares cannot be
///   reused by another object while it exists (the #2177 C rule). A pointer comparison can only
///   miss spuriously, never match wrongly;
/// - the [`CertContext`] and the profile's [`CheckLimits`] are equal by value. Both are bound by
///   the identities above already; they are compared anyway, because it is cheap;
/// - the checker version is bound by construction: the memo lives for one run in one process, and
///   `CHECKER_VERSION` is a constant of the one binary that fills and reads it.
///
/// ⚠ It rests on `verify_cert` being a pure function of those inputs, and so on every theory's
/// `decide` and the caller's leaf verifier being deterministic within a run. The contract states
/// that obligation (`docs/spec/logos-contract.md`, the leaf verifier and theory sections); a
/// non-deterministic decider would already break dual conformance, and this memo makes the
/// obligation load-bearing.
pub struct WorldMemo<'a, C> {
    last: Option<Entry<'a, C>>,
    /// Certificates verified through this memo: the size of every world it verified on a miss.
    verified: usize,
}

struct Entry<'a, C> {
    program: &'a dyn Program,
    profile: &'a CheckProfile<C>,
    ctx: &'a C,
    cert_context: CertContext,
    limits: CheckLimits,
    world: Vec<ClosedModelCert>,
    status: Vec<CertStatus>,
}

impl<C> Default for WorldMemo<'_, C> {
    fn default() -> Self {
        WorldMemo {
            last: None,
            verified: 0,
        }
    }
}

impl<'a, C> WorldMemo<'a, C> {
    /// An empty memo; the first derivation citing a certificate fills it.
    pub fn new() -> Self {
        Self::default()
    }

    /// How many certificates have been verified through this memo, counting each world it
    /// verified on a miss in full. N derivations citing one world of k certificates give k.
    #[doc(hidden)]
    pub fn certificates_verified(&self) -> usize {
        self.verified
    }

    /// The statuses of `world` under these inputs: served from the slot on a hit, verified and
    /// stored on a miss. An EMPTY world (a positive derivation) needs no verification and does not
    /// touch the slot, so positive answers between two that cite a world do not evict it.
    #[allow(ambiguous_wide_pointer_comparisons)] // the vtable is part of the identity on purpose
    pub(super) fn statuses(
        &mut self,
        program: &'a dyn Program,
        profile: &'a CheckProfile<C>,
        ctx: &'a C,
        cert_context: &CertContext,
        world: &[ClosedModelCert],
    ) -> &[CertStatus] {
        if world.is_empty() {
            return &[];
        }
        let hit = self.last.as_ref().is_some_and(|entry| {
            std::ptr::eq(entry.program, program)
                && std::ptr::eq(entry.profile, profile)
                && std::ptr::eq(entry.ctx, ctx)
                && entry.cert_context == *cert_context
                && entry.limits == profile.limits
                && entry.world.as_slice() == world
        });
        if !hit {
            let status = verify_world(world, program, profile, ctx, cert_context);
            self.verified += world.len();
            self.last = Some(Entry {
                program,
                profile,
                ctx,
                cert_context: *cert_context,
                limits: profile.limits,
                world: world.to_vec(),
                status,
            });
        }
        &self.last.as_ref().expect("filled above").status
    }
}
