package typed

import "unicode/utf8"

type budget struct {
	remaining uint32
	spent     uint32
	depth     uint32
	err       *failure
	location  Location
}

func (b *budget) fail(f *failure) {
	if b.err == nil {
		f.location = b.location
		b.err = f
	}
}

func (b *budget) tick(depth uint32) bool {
	if b.err != nil {
		return false
	}
	if depth > b.depth {
		b.fail(incomplete(Depth))
		return false
	}
	if b.remaining == 0 {
		b.fail(incomplete(Work))
		return false
	}
	b.remaining--
	b.spent++
	return true
}

func (b *budget) charge(amount uint64) bool {
	if b.err != nil {
		return false
	}
	if amount > uint64(b.remaining) {
		b.fail(incomplete(Work))
		return false
	}
	b.remaining -= uint32(amount)
	b.spent += uint32(amount)
	return true
}

// Preflight is iterative and borrows immutable Expr nodes. It never recursively
// copies malformed/deep input or trusts host allocation to supply a valid AST.
type preflight struct {
	budget  *budget
	limits  Limits
	nodes   uint32
	entries uint32
}

func (p *preflight) identity(s string) bool {
	if !p.budget.tick(0) {
		return false
	}
	if uint64(len(s)) > uint64(p.limits.NameBytes) {
		p.budget.fail(incomplete(NameBytes))
		return false
	}
	if !p.budget.charge(uint64(len(s))) {
		return false
	}
	if !utf8.ValidString(s) {
		p.budget.fail(invalid(MalformedInput))
		return false
	}
	return true
}

func (p *preflight) collection(n int) bool {
	if !p.budget.tick(0) {
		return false
	}
	if uint64(n) > uint64(p.limits.CollectionEntries-p.entries) {
		p.budget.fail(incomplete(CollectionEntries))
		return false
	}
	p.entries += uint32(n)
	return true
}

func arity(k Kind) (int, bool) {
	switch k {
	case SortKind, VarKind, ConstKind, NatKind, ZeroKind, BoolKind, FalseKind, TrueKind:
		return 0, true
	case FstKind, SndKind, SuccKind:
		return 1, true
	case PiKind, LamKind, AppKind, SigmaKind, ReflKind:
		return 2, true
	case PairKind, IDKind:
		return 3, true
	case NatElimKind, BoolElimKind:
		return 4, true
	case TransportKind:
		return 6, true
	default:
		return 0, false
	}
}

func (p *preflight) expression(root Expr) bool {
	type frame struct {
		expr  Expr
		depth uint32
		exit  bool
	}
	stack := []frame{{expr: root, depth: 1}}
	active := make(map[*expression]bool)
	maxDepth := min(p.limits.InputDepth, MaxInputDepth)
	for len(stack) != 0 && p.budget.err == nil {
		at := len(stack) - 1
		f := stack[at]
		stack = stack[:at]
		if f.exit {
			delete(active, f.expr.node)
			continue
		}
		if !p.budget.tick(0) {
			break
		}
		if f.expr.node == nil {
			p.budget.fail(invalid(MalformedInput))
			break
		}
		if active[f.expr.node] {
			p.budget.fail(invalid(MalformedInput))
			break
		}
		if f.depth > maxDepth {
			p.budget.fail(incomplete(InputDepth))
			break
		}
		if p.nodes == p.limits.InputNodes {
			p.budget.fail(incomplete(InputNodes))
			break
		}
		p.nodes++
		n := f.expr.node
		count, ok := arity(n.kind)
		if !ok || len(n.args) != count || (n.kind != SortKind && n.kind != VarKind && n.index != 0) || (n.kind != ConstKind && n.name != "") {
			p.budget.fail(invalid(MalformedInput))
			break
		}
		if n.kind == ConstKind {
			if !p.identity(n.name) {
				break
			}
			if n.name == "" {
				p.budget.fail(invalid(EmptyConstantName))
				break
			}
		}
		active[n] = true
		stack = append(stack, frame{expr: f.expr, exit: true})
		for i := len(n.args) - 1; i >= 0; i-- {
			stack = append(stack, frame{expr: n.args[i], depth: f.depth + 1})
		}
	}
	return p.budget.err == nil
}

func (p *preflight) all(s Statement, candidate Expr, policy Policy) bool {
	if !p.identity(s.Foundation) || !p.collection(len(s.Declarations)) || !p.collection(len(s.Context)) {
		return false
	}
	for i, d := range s.Declarations {
		p.budget.location = Location{Phase: PreflightPhase, Index: uint32(i), HasIndex: true}
		if !p.identity(d.name) {
			return false
		}
		if d.name == "" {
			p.budget.fail(invalid(EmptyConstantName))
			return false
		}
		if d.kind != assumed && d.kind != defined {
			p.budget.fail(invalid(MalformedInput))
			return false
		}
		if !p.collection(len(d.dependencies)) {
			return false
		}
		if d.kind == assumed && len(d.dependencies) == 0 {
			p.budget.fail(invalid(MissingAssumptions))
			return false
		}
		for _, dep := range d.dependencies {
			if !p.identity(dep) {
				return false
			}
			if dep == "" {
				p.budget.fail(invalid(MissingAssumptions))
				return false
			}
		}
		if d.kind == defined && len(d.dependencies) != 0 {
			p.budget.fail(invalid(MalformedInput))
			return false
		}
		if !p.expression(d.typ) {
			return false
		}
		if d.kind == defined && !p.expression(d.value) {
			return false
		}
	}
	for i, e := range s.Context {
		p.budget.location = Location{Phase: PreflightPhase, Index: uint32(i), HasIndex: true}
		if !p.expression(e) {
			return false
		}
	}
	p.budget.location = Location{Phase: PreflightPhase}
	if !p.expression(s.Expected) || !p.expression(candidate) {
		return false
	}
	if !p.identity(policy.Foundation) || !p.identity(policy.Checker) || !p.collection(len(policy.Dependencies)) {
		return false
	}
	for _, dep := range policy.Dependencies {
		if !p.identity(dep) {
			return false
		}
		if dep == "" {
			p.budget.fail(invalid(MalformedInput))
			return false
		}
	}
	return p.budget.err == nil
}
