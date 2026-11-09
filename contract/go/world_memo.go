package contract

import (
	"reflect"
	"sync"
)

// WorldMemo is the go port of the checker's closed-world memo (#2569, the go/ts rung of #2565
// term 1; seat:caa's ruling on #2569): a run that checks many derivations citing the SAME
// closed-model certificates verifies them once, not once per derivation.
//
// Its inputs are BOUND AT CONSTRUCTION, and the whole check runs under them: program, profile,
// ctx and CertContext are the memo's own, so a caller cannot pass a different one with it and
// there is no identity to compare. (The rs memo compares borrowed pointers per call; go passes
// ctx by value and an interface comparison can panic, so the binding is structural here.)
//
// The per-call key is the derivation's WHOLE ClosedWorld, compared with reflect.DeepEqual:
// exact representation equality, never a digest, so a hit can only be a world equal to the one
// verified. A spurious difference (a nil slice against an empty one) can only miss. The unit is
// the whole world because a stacked certificate's verdict reads the lower certificates' statuses
// in the same world. CheckLimits are snapshotted when a world is verified and compared with the
// live profile's on every call, so a limit changed through the profile pointer re-verifies.
//
// OBLIGATION (docs/spec/logos-contract.md §6): the program, profile components and ctx a memo is
// built with MUST NOT be mutated while it is in use. A mutated program leaves the bound
// CertContext stale, and the memo would then serve a WRONG verdict, not a slow one. The kernel
// gate meets this by construction: its drive loop holds program, profile and ctx fixed for the
// run. Limits are the one input checked rather than assumed.
type WorldMemo[C any] struct {
	program     Program
	profile     *CheckProfile[C]
	ctx         C
	certContext CertContext

	mu       sync.Mutex
	filled   bool
	limits   CheckLimits
	world    []ClosedModelCert
	status   []certStatus
	verified int
}

// NewWorldMemo binds a memo to the inputs every check through it runs under.
func NewWorldMemo[C any](program Program, profile *CheckProfile[C], ctx C, certContext CertContext) *WorldMemo[C] {
	return &WorldMemo[C]{program: program, profile: profile, ctx: ctx, certContext: captureCertContext(certContext)}
}

// CertificatesVerified is how many certificates have been verified through this memo, counting
// each world it verified on a miss in full. N derivations citing one world of k certificates
// give k.
func (m *WorldMemo[C]) CertificatesVerified() int {
	m.mu.Lock()
	defer m.mu.Unlock()
	return m.verified
}

// CheckWithWorldMemo is CheckWithCertContext under the memo's bound program, profile, ctx and
// CertContext, with the derivation's closed world verified through the memo. The verdict is
// exactly CheckWithCertContext's: only step 3a, the per-certificate verification, can be served
// from the memo; the prechecks, the forward pass over the derivation's own nodes and every
// premise's own checks run on every call.
func CheckWithWorldMemo[C any](m *WorldMemo[C], claim GroundLiteral, deriv Derivation) Outcome {
	return checkNative(m.program, claim, deriv, m.ctx, *m.profile, m.certContext, m)
}

// captureWorld runs before any program or verifier callback. On a hit the
// immutable slot already owns the exact input, so the checker shares both
// the world and its statuses without copying the chain again.
func (m *WorldMemo[C]) captureWorld(world []ClosedModelCert, limits CheckLimits) ([]ClosedModelCert, []certStatus) {
	m.mu.Lock()
	if m.filled && m.limits == limits && reflect.DeepEqual(m.world, world) {
		owned, status := m.world, m.status
		m.mu.Unlock()
		return owned, status
	}
	m.mu.Unlock()
	return cloneWorld(world), nil
}

// Verifiers may reenter the same memo. Only publishing the completed slot
// takes its lock. Overlapping misses count the work each actually performed.
func (m *WorldMemo[C]) rememberWorld(world []ClosedModelCert, status []certStatus, limits CheckLimits) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.world, m.status = world, status
	m.limits = limits
	m.filled = true
	m.verified += len(world)
}
