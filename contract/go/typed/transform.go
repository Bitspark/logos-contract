package typed

const maxNatural = ^uint32(0)

func (m *machine) copy(e Expr, depth uint32) Expr { return m.shift(e, 0, depth) }

func (m *machine) shift(e Expr, amount, depth uint32) Expr {
	return m.walk(e, 0, depth, func(index, bound, d uint32) Expr {
		if !m.tick(d) {
			return Expr{}
		}
		if index < bound {
			return Var(index)
		}
		if amount > maxNatural-index {
			m.budget.fail(incomplete(IndexCapacity))
			return Expr{}
		}
		return Var(index + amount)
	})
}

// instantiate removes the outermost free slot. Crossing a binder lifts the
// argument, preventing free variables in it from being captured.
func (m *machine) instantiate(body, argument Expr, depth uint32) Expr {
	return m.walk(body, 0, depth, func(index, bound, d uint32) Expr {
		if !m.tick(d) {
			return Expr{}
		}
		if index == bound {
			return m.shift(argument, bound, d+1)
		}
		if index > bound {
			return Var(index - 1)
		}
		return Var(index)
	})
}

func (m *machine) walk(e Expr, bound, depth uint32, variable func(uint32, uint32, uint32) Expr) Expr {
	if !m.tick(depth) {
		return Expr{}
	}
	if e.node == nil {
		m.fail(MalformedInput)
		return Expr{}
	}
	switch e.Kind() {
	case VarKind:
		return variable(e.Index(), bound, depth+1)
	case SortKind:
		return Sort(e.Index())
	case ConstKind:
		return Const(e.Name())
	case PiKind, LamKind, AppKind, SigmaKind, PairKind, FstKind, SndKind,
		NatKind, ZeroKind, SuccKind, NatElimKind, BoolKind, FalseKind, TrueKind,
		BoolElimKind, IDKind, ReflKind, TransportKind:
		// Rebuild every operand below, adjusting the scope at binders.
	default:
		m.fail(MalformedInput)
		return Expr{}
	}
	args := make([]Expr, len(e.node.args))
	for i, arg := range e.node.args {
		inside := bound
		if i == 1 && (e.Kind() == PiKind || e.Kind() == LamKind || e.Kind() == SigmaKind) {
			if bound == maxNatural {
				m.budget.fail(incomplete(IndexCapacity))
				return Expr{}
			}
			inside++
		}
		args[i] = m.walk(arg, inside, depth+1, variable)
		if m.budget.err != nil {
			return Expr{}
		}
	}
	return expr(e.Kind(), args...)
}
