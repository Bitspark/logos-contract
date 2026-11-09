package contract

import (
	"fmt"
	"maps"
	"reflect"
)

// CaptureSubst takes ownership of an untrusted substitution before its terms
// are applied to a goal. Only immutable native terms can enter a retained map.
// Success establishes shape and depth, without making a logical judgment.
func CaptureSubst(subst Subst, limits CheckLimits) (Subst, Outcome) {
	if err := limits.Validate(); err != nil {
		return nil, reject(InvalidCheckLimits, err.Error())
	}
	for name, term := range subst {
		if why := wellFormedTerm(term, limits.MaxTermDepth, "substitution image of "+name.String()); why != "" {
			return nil, reject(UnknownNodeKind, why)
		}
		if !TermDepthLE(term, limits.MaxTermDepth) {
			return nil, reject(TermTooDeep, fmt.Sprintf("substitution image of %s exceeds max_term_depth %d", name.String(), limits.MaxTermDepth))
		}
	}
	return maps.Clone(subst), Accept()
}

// CaptureDerivation isolates a native proposal before verification calls
// application code. The ordinary checker and the capturing path apply the same
// header refusals before inspecting nodes. Logical checking still follows.
func CaptureDerivation(proof Derivation, limits CheckLimits) (Derivation, Outcome) {
	if out := checkDerivationShape(proof, limits); !out.IsAccept() {
		return Derivation{}, out
	}
	return CloneDerivation(proof), Accept()
}

func checkDerivationShape(proof Derivation, limits CheckLimits) Outcome {
	if out := derivationHeader(proof, limits); !out.IsAccept() {
		return out
	}
	return checkWellFormed(proof, limits)
}

func derivationHeader(proof Derivation, limits CheckLimits) Outcome {
	if err := limits.Validate(); err != nil {
		return reject(InvalidCheckLimits, err.Error())
	}
	n := len(proof.Nodes)
	if n == 0 {
		return reject(EmptyDerivation, "derivation has no nodes")
	}
	if n > limits.MaxNodes {
		return reject(TooManyNodes, fmt.Sprintf("%d nodes exceeds max_nodes %d", n, limits.MaxNodes))
	}
	if _, ok := proof.RootOffset(); !ok {
		return reject(RootOutOfRange, fmt.Sprintf("root %d out of range (len %d)", proof.Root, n))
	}
	return Accept()
}

// CloneDerivation returns a detached in-process proof, preserving node and premise
// representations, opaque clause handles and native nil containers. Mutable model
// containers in the original and result can be edited independently. Term and
// Ontos values have immutable value semantics. Opaque verifier evidence retains
// its receiver-defined meaning under the same fixed-input obligation as Check.
func CloneDerivation(proof Derivation) Derivation {
	return deepCopy(reflect.ValueOf(proof)).Interface().(Derivation)
}

// cloneWorld detaches the complete proposed certificate chain before an
// independent component is consulted about any one of its members.
func cloneWorld(world []ClosedModelCert) []ClosedModelCert {
	return deepCopy(reflect.ValueOf(world)).Interface().([]ClosedModelCert)
}

func deepCopy(v reflect.Value) reflect.Value {
	switch v.Kind() {
	case reflect.Interface:
		// Recurse into the closed account records that can own mutable Go data.
		// Terms and Ontos values are immutable. Foreign implementations remain
		// opaque, and copying cannot turn an unrecognized case into a valid one.
		switch v.Interface().(type) {
		case RuleNode, BuiltinNode, LeafNode, PosPremise, NegPremise, CountPremise,
			SameStratumRef, LowerStratumRef, BuiltinRef, NegLowerRef, CountLowerRef:
			out := reflect.New(v.Type()).Elem()
			out.Set(deepCopy(v.Elem()))
			return out
		default:
			return v
		}
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
