//! Operation counters for #2511's cost measurements (`seat:caa`'s restated done-when (b′)):
//! canonical ground-key encodes and key comparisons, counted process-wide so a test can attribute
//! them to the seal's and the gate's stages by reading them at each span's open and close.
//!
//! A time exponent can rise because a C log C pass outgrows each cache level, and that is not
//! algorithmic; an operation COUNT cannot be bent by the cache. So a count that grows faster than
//! the work it stands for is an algorithmic term, a redundant pass for instance, and it shows here
//! even where the wall clock would hide it under the memory hierarchy.
//!
//! Compiled in only under the `op-counters` feature, which only a test turns on. Without it every
//! hook is an empty inline function and [`snapshot`] is `None`, so the trusted build carries no
//! shared state and no cost.

#[cfg(feature = "op-counters")]
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};

#[cfg(feature = "op-counters")]
static ENCODES: AtomicU64 = AtomicU64::new(0);
#[cfg(feature = "op-counters")]
static COMPARES: AtomicU64 = AtomicU64::new(0);
/// Whether counting is on, OFF until a measurement turns it on. A counted increment is an atomic
/// read-modify-write, and a run that is TIMED must not pay for it, so a measurement counts in a run
/// of its own and times the others with counting off, where each hook costs one relaxed load. Off
/// by default because a workspace test build unifies the feature into every crate's tests, and
/// those must not pay for a count nobody reads.
#[cfg(feature = "op-counters")]
static ENABLED: AtomicBool = AtomicBool::new(false);

/// One canonical ground-key encode ([`ground_key`](crate::cert::ground_key) counts itself).
#[inline]
pub fn count_encode() {
    #[cfg(feature = "op-counters")]
    if ENABLED.load(Relaxed) {
        ENCODES.fetch_add(1, Relaxed);
    }
}

/// One comparison of two canonical keys, in a sort, a dedupe or an ordered search.
#[inline]
pub fn count_compare() {
    #[cfg(feature = "op-counters")]
    if ENABLED.load(Relaxed) {
        COMPARES.fetch_add(1, Relaxed);
    }
}

/// Turn counting on or off (off by default). A no-op when counting is compiled out.
pub fn set_enabled(on: bool) {
    #[cfg(feature = "op-counters")]
    ENABLED.store(on, Relaxed);
    #[cfg(not(feature = "op-counters"))]
    let _ = on;
}

/// The counts so far, as `(encodes, compares)`. `None` when counting is compiled out, so a reader
/// can tell "no count" from "zero".
#[cfg(feature = "op-counters")]
pub fn snapshot() -> Option<(u64, u64)> {
    Some((ENCODES.load(Relaxed), COMPARES.load(Relaxed)))
}

/// The counts so far: `None`, since counting is compiled out.
#[cfg(not(feature = "op-counters"))]
pub fn snapshot() -> Option<(u64, u64)> {
    None
}
