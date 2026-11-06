// ADR 0029 D10 — the SLICE SEAL, go arm.
//
// These are the go twins of the six `d10_g5_*` tests in contract/rs/tests/negation.rs. They exist
// because of a hazard specific to this language: adding `DecompositionWitness` to ClosedModelCert
// broke NOTHING in go — every existing literal kept compiling and silently received nil — where
// the identical change in rs surfaced 29 construction sites loudly. `go build` and `go test ./...`
// passing therefore proved only that nothing REGRESSED; without this file the D10 branch would be
// shipped unexercised. Silence is the alarm, not the all-clear.
//
// They target checkCertContext directly rather than a full CheckWithCertContext round trip: that
// function is precisely what D10 changed, and a unit test over it exercises all four branches plus
// the slice digest without rebuilding the whole negation fixture.
package contract

import "testing"

// The two-clause program the rs twin uses: `denied` is the sealed component, `permit` is the
// upper stratum and outside it. `revoked` is a pure EDB leaf and contributes no clause, so the
// SLICE of the ideal {denied, revoked} is exactly {deniedRule}.
func d10Program() *MapProgram {
	return NewMapProgram().
		With(NewClauseId("denied_rule"), NewClause(
			NewGoal("denied", Var("S")),
			NewGoal("revoked", Var("S")),
		)).
		With(NewClauseId("permit_rule"), NewClause(
			NewGoal("permit", Var("S")),
			NewGoal("granted", Var("S")),
		))
}

func d10Scope() StratumPrefix {
	return NewStratumPrefix(1, []Symbol{NewSymbol([]byte("denied")), NewSymbol([]byte("revoked"))})
}

var (
	d10WitnessA = Hash{0xD1}
	d10WitnessB = Hash{0xD2}
)

// A cert whose four pins are honest for `program`, sealed over whichever clause set `sliced` says.
func d10Cert(program Program, sliced bool, witness *Hash) ClosedModelCert {
	cert := ClosedModelCert{
		Scope:            d10Scope(),
		ProgramHash:      ProgramDigestOf(program),
		ProfileHash:      Hash{0x01},
		CtxHash:          Hash{0x02},
		TheoryConfigHash: Hash{0x03},
	}
	if sliced {
		cert.ProgramHash = programDigestOverScope(program, cert)
	}
	cert.DecompositionWitness = witness
	return cert
}

func d10Context(program Program, witness *Hash) CertContext {
	cx := NewCertContext(ProgramDigestOf(program), Hash{0x01}, Hash{0x02}, Hash{0x03})
	cx.DecompositionWitness = witness
	return cx
}

// ANTI-VACUITY. Every case below is meaningless unless the slice and the complete program digest
// apart — if they collided, a checker that never read DecompositionWitness would pass them all.
func TestD10SliceDigestDiffersFromCompleteDigest(t *testing.T) {
	program := d10Program()
	complete := ProgramDigestOf(program)
	slice := programDigestOverScope(program, d10Cert(program, false, nil))
	if complete == slice {
		t.Fatal("the D10 go arm is vacuous unless the slice and the complete program digest apart")
	}
}

// THE GREEN TWIN: a slice seal replays under the decomposition that authorized it.
func TestD10SliceSealReplaysUnderItsOwnDecomposition(t *testing.T) {
	program := d10Program()
	cert := d10Cert(program, true, &d10WitnessA)
	if e := checkCertContext(cert, program, d10Context(program, &d10WitnessA)); e != nil {
		t.Fatalf("a slice seal must replay under its own decomposition; got %v: %s", e.code, e.detail)
	}
}

// CONTROL: the pin is load-bearing. A DIFFERENT decomposition is refused.
func TestD10SliceSealUnderADifferentDecompositionIsRefused(t *testing.T) {
	program := d10Program()
	cert := d10Cert(program, true, &d10WitnessA)
	e := checkCertContext(cert, program, d10Context(program, &d10WitnessB))
	if e == nil || e.code != CertContextMismatch {
		t.Fatalf("a slice seal under a different decomposition must be refused; got %v", e)
	}
}

// CONTROL: a slice seal cannot discharge in a run that declares no decomposition. This is what
// keeps a component's cert from leaking into a whole-program check.
func TestD10SliceSealCannotDischargeInAWholeProgramRun(t *testing.T) {
	program := d10Program()
	cert := d10Cert(program, true, &d10WitnessA)
	e := checkCertContext(cert, program, d10Context(program, nil))
	if e == nil || e.code != CertContextMismatch {
		t.Fatalf("a slice seal must not discharge in a whole-program run; got %v", e)
	}
}

// CONTROL: D10 does not disturb the whole-program path. An ordinary cert is still accepted even
// when the CALLER declares a decomposition — otherwise D10 would have made every existing cert
// conditional on the caller not decomposing.
func TestD10WholeProgramCertIsUnaffectedByADecomposedContext(t *testing.T) {
	program := d10Program()
	cert := d10Cert(program, false, nil)
	if e := checkCertContext(cert, program, d10Context(program, &d10WitnessA)); e != nil {
		t.Fatalf("a whole-program cert must be unaffected by the caller's decomposition; got %v: %s", e.code, e.detail)
	}
}

// CONTROL: the pre-D10 reading is untouched — an honest whole-program cert under an ordinary
// context still passes, and a wrong program pin still fails.
func TestD10PreExistingBehaviourIsUnchanged(t *testing.T) {
	program := d10Program()
	if e := checkCertContext(d10Cert(program, false, nil), program, d10Context(program, nil)); e != nil {
		t.Fatalf("an honest whole-program cert must still pass; got %v: %s", e.code, e.detail)
	}
	// a cert pinning the SLICE while declaring no decomposition is refused, which is exactly the
	// pre-D10 behaviour and the assertion unit 1 (#1618) landed in rs.
	e := checkCertContext(d10Cert(program, true, nil), program, d10Context(program, nil))
	if e == nil || e.code != CertContextMismatch {
		t.Fatalf("slicing alone must never buy admission; got %v", e)
	}
}

// WIRE: the 11th element is TRAILING-OPTIONAL, so a cert that seals the complete program encodes
// to the same TEN-element tuple it always did — and a slice-sealed one round-trips its pin.
func TestD10WireIsTrailingOptional(t *testing.T) {
	program := d10Program()

	plain := ClosedModelCertAsValue(d10Cert(program, false, nil))
	pt, err := decItems(plain, "plain")
	if err != nil {
		t.Fatalf("plain cert did not encode as a tuple: %v", err)
	}
	if len(pt) != 10 {
		t.Fatalf("a cert with no slice seal must encode to TEN elements, got %d", len(pt))
	}

	sealed := ClosedModelCertAsValue(d10Cert(program, true, &d10WitnessA))
	st, err := decItems(sealed, "sealed")
	if err != nil {
		t.Fatalf("sealed cert did not encode as a tuple: %v", err)
	}
	if len(st) != 11 {
		t.Fatalf("a slice-sealed cert must encode to ELEVEN elements, got %d", len(st))
	}

	// both round-trip, and the pin survives
	back, err := ClosedModelCertFromValue(plain)
	if err != nil {
		t.Fatalf("plain round trip: %v", err)
	}
	if back.DecompositionWitness != nil {
		t.Fatal("a ten-element cert must decode to a nil witness")
	}
	back, err = ClosedModelCertFromValue(sealed)
	if err != nil {
		t.Fatalf("sealed round trip: %v", err)
	}
	if back.DecompositionWitness == nil || *back.DecompositionWitness != d10WitnessA {
		t.Fatalf("the slice-seal pin must survive the round trip; got %v", back.DecompositionWitness)
	}
}
