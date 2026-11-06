package contract

import "reflect"

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

	filled   bool
	limits   CheckLimits
	world    []ClosedModelCert
	status   []certStatus
	verified int
}

// NewWorldMemo binds a memo to the inputs every check through it runs under.
func NewWorldMemo[C any](program Program, profile *CheckProfile[C], ctx C, certContext CertContext) *WorldMemo[C] {
	return &WorldMemo[C]{program: program, profile: profile, ctx: ctx, certContext: certContext}
}

// CertificatesVerified is how many certificates have been verified through this memo, counting
// each world it verified on a miss in full. N derivations citing one world of k certificates
// give k.
func (m *WorldMemo[C]) CertificatesVerified() int { return m.verified }

// CheckWithWorldMemo is CheckWithCertContext under the memo's bound program, profile, ctx and
// CertContext, with the derivation's closed world verified through the memo. The verdict is
// exactly CheckWithCertContext's: only step 3a, the per-certificate verification, can be served
// from the memo; the prechecks, the forward pass over the derivation's own nodes and every
// premise's own checks run on every call.
func CheckWithWorldMemo[C any](m *WorldMemo[C], claim GroundLiteral, deriv Derivation) Outcome {
	if out, ok := derivationPrechecks(m.program, claim, deriv, m.profile); !ok {
		return out
	}
	return checkNodes(m.program, claim, deriv, m.ctx, m.profile, m.statuses(deriv.ClosedWorld))
}

// statuses serves world's statuses from the slot on a hit and verifies and stores them on a
// miss. An EMPTY world (a positive derivation) needs no verification and does not touch the
// slot, so positive answers between two that cite a world do not evict it.
func (m *WorldMemo[C]) statuses(world []ClosedModelCert) []certStatus {
	if len(world) == 0 {
		return nil
	}
	hit := m.filled && m.limits == m.profile.Limits && reflect.DeepEqual(m.world, world)
	if !hit {
		m.status = verifyWorld(world, m.program, m.profile, m.ctx, m.certContext)
		m.world = cloneWorld(world)
		m.limits = m.profile.Limits
		m.filled = true
		m.verified += len(world)
	}
	return m.status
}

// cloneWorld deep-copies a world's own containers (slices, maps, pointers, structs), so a caller
// that later mutates its derivation in place cannot change what the memo compares against: a
// shallow copy would share the rows, and an in-place edit would then compare EQUAL to the stale
// world it replaced. Values held through an interface (ontos core.Value, contract Term) are
// immutable and are kept as they are. It runs on a miss only, never on a hit.
func cloneWorld(world []ClosedModelCert) []ClosedModelCert {
	return deepCopy(reflect.ValueOf(world)).Interface().([]ClosedModelCert)
}

func deepCopy(v reflect.Value) reflect.Value {
	switch v.Kind() {
	case reflect.Slice:
		if v.IsNil() {
			return v
		}
		out := reflect.MakeSlice(v.Type(), v.Len(), v.Len())
		for i := 0; i < v.Len(); i++ {
			out.Index(i).Set(deepCopy(v.Index(i)))
		}
		return out
	case reflect.Map:
		if v.IsNil() {
			return v
		}
		out := reflect.MakeMapWithSize(v.Type(), v.Len())
		for it := v.MapRange(); it.Next(); {
			out.SetMapIndex(it.Key(), deepCopy(it.Value()))
		}
		return out
	case reflect.Pointer:
		if v.IsNil() {
			return v
		}
		out := reflect.New(v.Elem().Type())
		out.Elem().Set(deepCopy(v.Elem()))
		return out
	case reflect.Struct, reflect.Array:
		out := reflect.New(v.Type()).Elem()
		out.Set(v)
		if v.Kind() == reflect.Array {
			for i := 0; i < v.Len(); i++ {
				out.Index(i).Set(deepCopy(v.Index(i)))
			}
			return out
		}
		for i := 0; i < v.NumField(); i++ {
			if out.Field(i).CanSet() {
				out.Field(i).Set(deepCopy(v.Field(i)))
			}
		}
		return out
	default:
		return v
	}
}
