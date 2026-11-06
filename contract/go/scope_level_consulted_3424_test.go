package contract

// #3424 (research 0035 lane 8, row B17): where a certificate's scope `level` is inert, and where
// it is consulted. `level` is not read for a single certificate with a full scope. Since #1708 a
// partial scope must sit at its certificate's own level, and since #2344 stacked certificates are
// verified in level order and a certificate reads only a strictly lower seal. There, a wrong level
// changes the verdict. The fixtures are vectors/negation.json's own cases, replayed through the
// setup TestNegationVectors uses, with only the certificates' scope levels changed. The rs
// counterparts are contract/rs/tests/negation.rs (the inert case), adr0030_partial_scope_guard.rs
// and stacked_scope_level_3424.rs.

import "testing"

// replayNegWithLevels replays the negation vector `name` with certificate i's scope level set to
// levels[i], and returns its outcome ("accept" or "reject:<code>").
func replayNegWithLevels(t *testing.T, name string, levels []uint32) string {
	t.Helper()
	vf := loadNegVectors(t)
	var c *negCase
	for i := range vf.Cases {
		if vf.Cases[i].Name == name {
			c = &vf.Cases[i]
		}
	}
	if c == nil {
		t.Fatalf("vectors/negation.json carries no case %q", name)
	}
	if c.PlainCheck || c.CertContext != nil || c.Limits != nil {
		t.Fatalf("case %q needs a setup this replay does not make", name)
	}
	if len(levels) != len(c.Derivation.ClosedWorld) {
		t.Fatalf("case %q has %d certificates, %d levels given", name, len(c.Derivation.ClosedWorld), len(levels))
	}
	program := NewMapProgram()
	for id, clause := range vf.Program {
		body := make([]BodyLit, len(clause.Body))
		for i, b := range clause.Body {
			body[i] = b.build(t)
		}
		program.Insert(NewClauseId(id), NewClauseLits(clause.Head.buildGoal(t), body...))
	}
	extensional := NewPredicateSet()
	for _, p := range vf.Extensional {
		extensional.Insert(SymbolFromString(p))
	}
	edb := make(map[string][]GroundLiteral, len(vf.Edb))
	for pred, rows := range vf.Edb {
		grounds := make([]GroundLiteral, len(rows))
		for i, r := range rows {
			grounds[i] = r.buildGround(t)
		}
		edb[pred] = grounds
	}
	derived := NewCertContext(ProgramDigestOf(program), negVectorPin(1), negVectorPin(2), negVectorPin(3))
	nodes := make([]Node, len(c.Derivation.Nodes))
	for i, nj := range c.Derivation.Nodes {
		nodes[i] = nj.build(t)
	}
	world := make([]ClosedModelCert, len(c.Derivation.ClosedWorld))
	for i, cj := range c.Derivation.ClosedWorld {
		cj.Scope.Level = levels[i] // a copy: the loaded vector is untouched
		world[i] = cj.build(t, derived)
	}
	profile := &CheckProfile[unitCtx]{
		Theory: ltTheory{},
		Leaves: negVectorLeaves{extensional: extensional, edb: edb},
		Admit:  AlwaysAdmit[unitCtx]{},
		Limits: DefaultLimits(),
	}
	deriv := NewDerivationWithClosedWorld(nodes, uint64(c.Derivation.Root), world)
	return negOutcomeString(CheckWithCertContext[unitCtx](program, c.Claim.buildGround(t), deriv, unitCtx{}, profile, derived))
}

// A single certificate with a full scope: `level` is not read, so a wrong level in either
// direction accepts as the vector's own level does.
func TestScopeLevelIsInertForASingleFullScopeCertificate3424(t *testing.T) {
	for _, level := range []uint32{1, 0, 7} {
		if got := replayNegWithLevels(t, "accept_negation_of_absent_atom", []uint32{level}); got != "accept" {
			t.Fatalf("level %d: got %q, want accept (the vector's level is 1)", level, got)
		}
	}
}

// A partial scope (#1708): the certificate's own level is read against its partial scope's.
func TestScopeLevelIsReadOnceACertificateCarriesAPartialScope3424(t *testing.T) {
	const name = "adr0030_lower_bound_table_not_closed_but_marked_partial"
	if got := replayNegWithLevels(t, name, []uint32{1}); got != "accept" {
		t.Fatalf("control, level 1 (its partial scope's): got %q, want accept", got)
	}
	for _, level := range []uint32{0, 7} {
		if got := replayNegWithLevels(t, name, []uint32{level}); got != "reject:cert_partial_scope_invalid" {
			t.Fatalf("level %d under a level-1 partial scope: got %q, want reject:cert_partial_scope_invalid", level, got)
		}
	}
}

// Stacked certificates (#2344): verified in level order whatever their index, and a certificate
// reads only a strictly lower seal, so a wrong level changes the verdict.
func TestScopeLevelOrdersAndResolvesStackedCertificates3424(t *testing.T) {
	const upperFirst = "stacked_2258_the_order_of_the_world_does_not_matter_accepts" // [upper, base]
	const baseFirst = "stacked_2258_the_edb_sealed_once_below_accepts"               // [base, upper]
	if got := replayNegWithLevels(t, baseFirst, []uint32{1, 2}); got != "accept" {
		t.Fatalf("control, the base listed first: got %q, want accept", got)
	}
	if got := replayNegWithLevels(t, upperFirst, []uint32{2, 1}); got != "accept" {
		t.Fatalf("the upper certificate listed first is still verified after the base: got %q, want accept", got)
	}
	// the base at the upper's level, or above it: in either order the upper has no strictly lower seal
	for _, c := range []struct {
		name   string
		levels []uint32
	}{{upperFirst, []uint32{1, 1}}, {upperFirst, []uint32{2, 3}}, {baseFirst, []uint32{1, 1}}, {baseFirst, []uint32{3, 2}}} {
		if got := replayNegWithLevels(t, c.name, c.levels); got != "reject:cert_scope_incomplete" {
			t.Fatalf("%s at levels %v: got %q, want reject:cert_scope_incomplete", c.name, c.levels, got)
		}
	}
}
