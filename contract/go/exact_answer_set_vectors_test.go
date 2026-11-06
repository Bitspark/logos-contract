// Go replay of the shared cross-language vectors/exact_answer_set.json (#3022, research 0028 rows
// 1, 3, 4, 5 and 6): G4 compares the emitted answers with the sealed rows STRUCTURALLY. #3023
// (research 0028 A16): G4 is CheckAnswerSet, so the replay runs it here, through the contract entry
// point, and asserts its structured result: the kind of mismatch, and the literal the normative
// precedence names. Replayed identically by rs (contract/rs/tests/exact_answer_set_vectors.rs) and
// ts (contract/ts/test/exact_answer_set_vectors.test.ts).
//
// Denominator first: the file must carry exactly the named cases, so a case added to the file and
// not replayed, or dropped from it, reds here rather than silently thinning the replay.
package contract

import (
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"testing"
)

var exactAnswerSetCaseNames = []string{
	"control_the_sealed_set_emitted_accepts",
	"row1_one_spelling_emitted_of_two_sealed_rows_is_refused",
	"row1_both_sealed_rows_emitted_accepts",
	"row3_a_flat_ground_goal_has_no_cons_instance_accepts_the_empty_set",
	"row3_the_cons_row_emitted_for_a_flat_ground_goal_is_refused",
	"row4_an_open_cons_pattern_matches_its_cons_row_accepts",
	"row5_an_open_flat_pattern_has_no_cons_instance_accepts_the_empty_set",
	"row6_a_repeated_variable_does_not_join_two_spellings_accepts_the_empty_set",
	"precedence_an_extra_is_reported_before_a_missing_row",
	"precedence_the_first_extra_is_in_claim_order",
	"precedence_the_first_missing_row_is_in_key_order",
}

type answerSetTerm struct {
	AtomStr *string         `json:"atom_str"`
	Tuple   []answerSetTerm `json:"tuple"`
	Var     *string         `json:"var"`
}

func (j answerSetTerm) build(t *testing.T) Term {
	t.Helper()
	switch {
	case j.AtomStr != nil:
		return Atom([]byte(*j.AtomStr))
	case j.Var != nil:
		return Var(*j.Var)
	case j.Tuple != nil:
		children := make([]Term, len(j.Tuple))
		for i, c := range j.Tuple {
			children[i] = c.build(t)
		}
		return Tuple(children...)
	default:
		t.Fatalf("term must be atom_str/var/tuple: %+v", j)
		return nil
	}
}

type answerSetLiteral struct {
	Pred string          `json:"pred"`
	Args []answerSetTerm `json:"args"`
}

func (j answerSetLiteral) goal(t *testing.T) Goal {
	t.Helper()
	args := make([]Term, len(j.Args))
	for i, a := range j.Args {
		args[i] = a.build(t)
	}
	return NewGoal(j.Pred, args...)
}

func (j answerSetLiteral) ground(t *testing.T) GroundLiteral {
	t.Helper()
	g, ok := j.goal(t).AsGround()
	if !ok {
		t.Fatalf("a sealed row or an emitted claim is ground: %+v", j)
	}
	return g
}

func answerSetGroundAll(t *testing.T, lits []answerSetLiteral) []GroundLiteral {
	t.Helper()
	out := make([]GroundLiteral, len(lits))
	for i, l := range lits {
		out[i] = l.ground(t)
	}
	return out
}

func TestExactAnswerSetVectors3023(t *testing.T) {
	raw, err := os.ReadFile(filepath.Join("..", "..", "vectors", "exact_answer_set.json"))
	if err != nil {
		t.Fatalf("read vectors/exact_answer_set.json: %v", err)
	}
	var doc struct {
		Cases []struct {
			Name    string             `json:"name"`
			Goal    answerSetLiteral   `json:"goal"`
			Sealed  []answerSetLiteral `json:"sealed"`
			Emitted []answerSetLiteral `json:"emitted"`
			Outcome json.RawMessage    `json:"outcome"`
		} `json:"cases"`
	}
	if err := json.Unmarshal(raw, &doc); err != nil {
		t.Fatalf("parse vectors/exact_answer_set.json: %v", err)
	}
	names := make([]string, len(doc.Cases))
	for i, c := range doc.Cases {
		names[i] = c.Name
	}
	if !reflect.DeepEqual(names, exactAnswerSetCaseNames) {
		t.Fatalf("the file's cases are not exactly the replayed ones: %v", names)
	}

	for _, c := range doc.Cases {
		got := CheckAnswerSet(c.Goal.goal(t), answerSetGroundAll(t, c.Sealed), answerSetGroundAll(t, c.Emitted))
		var accept string
		if json.Unmarshal(c.Outcome, &accept) == nil {
			if accept != "accept" || got != nil {
				t.Errorf("%s: expected accept, got %+v", c.Name, got)
			}
			continue
		}
		var refused struct {
			Reject   string `json:"reject"`
			Mismatch struct {
				Extra   *answerSetLiteral `json:"extra"`
				Missing *answerSetLiteral `json:"missing"`
			} `json:"mismatch"`
		}
		if err := json.Unmarshal(c.Outcome, &refused); err != nil || refused.Reject != "completeness_set_mismatch" {
			t.Fatalf("%s: the only G4 refusal is completeness_set_mismatch, the vector says %s", c.Name, c.Outcome)
		}
		var want AnswerSetMismatch
		switch {
		case refused.Mismatch.Extra != nil && refused.Mismatch.Missing == nil:
			want = AnswerSetMismatch{Kind: AnswerSetExtra, Literal: refused.Mismatch.Extra.ground(t)}
		case refused.Mismatch.Missing != nil && refused.Mismatch.Extra == nil:
			want = AnswerSetMismatch{Kind: AnswerSetMissing, Literal: refused.Mismatch.Missing.ground(t)}
		default:
			t.Fatalf("%s: a mismatch names exactly one of extra or missing: %s", c.Name, c.Outcome)
		}
		if got == nil || got.Kind != want.Kind || !got.Literal.Equal(want.Literal) {
			t.Errorf("%s: got %+v, want %+v", c.Name, got, want)
		}
	}
}
