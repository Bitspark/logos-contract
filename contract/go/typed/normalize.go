package typed

func (m *machine) normalize(e Expr, depth uint32) Expr {
	if !m.tick(depth) {
		return Expr{}
	}
	if e.node == nil {
		m.fail(MalformedInput)
		return Expr{}
	}
	d := depth + 1
	a := e.node.args
	switch e.Kind() {
	case SortKind:
		return Sort(e.Index())
	case VarKind:
		return Var(e.Index())
	case ConstKind:
		entry, ok := m.entry(e.Name(), d)
		if !ok {
			return Expr{}
		}
		if entry.defined {
			return m.normalize(entry.definition, d)
		}
		return Const(e.Name())
	case AppKind:
		fun := m.normalize(a[0], d)
		arg := m.normalize(a[1], d)
		if fun.Kind() == LamKind {
			reduced := m.instantiate(fun.node.args[1], arg, d)
			return m.normalize(reduced, d)
		}
		return App(fun, arg)
	case FstKind, SndKind:
		pair := m.normalize(a[0], d)
		if pair.Kind() == PairKind {
			if e.Kind() == FstKind {
				return pair.node.args[1]
			}
			return pair.node.args[2]
		}
		return expr(e.Kind(), pair)
	case NatElimKind:
		scrutinee := m.normalize(a[3], d)
		if scrutinee.Kind() == ZeroKind {
			return m.normalize(a[1], d)
		}
		if scrutinee.Kind() == SuccKind {
			n := scrutinee.node.args[0]
			recursion := NatElim(m.copy(a[0], d), m.copy(a[1], d), m.copy(a[2], d), m.copy(n, d))
			reduced := App(App(m.copy(a[2], d), n), recursion)
			return m.normalize(reduced, d)
		}
		return NatElim(m.normalize(a[0], d), m.normalize(a[1], d), m.normalize(a[2], d), scrutinee)
	case BoolElimKind:
		scrutinee := m.normalize(a[3], d)
		if scrutinee.Kind() == FalseKind {
			return m.normalize(a[1], d)
		}
		if scrutinee.Kind() == TrueKind {
			return m.normalize(a[2], d)
		}
		return BoolElim(m.normalize(a[0], d), m.normalize(a[1], d), m.normalize(a[2], d), scrutinee)
	case TransportKind:
		equality := m.normalize(a[3], d)
		if equality.Kind() == ReflKind {
			return m.normalize(a[5], d)
		}
		return Transport(m.normalize(a[0], d), m.normalize(a[1], d), m.normalize(a[2], d), equality, m.normalize(a[4], d), m.normalize(a[5], d))
	case PiKind, LamKind, SigmaKind, PairKind, NatKind, ZeroKind, SuccKind,
		BoolKind, FalseKind, TrueKind, IDKind, ReflKind:
		args := make([]Expr, len(a))
		for i, arg := range a {
			args[i] = m.normalize(arg, d)
			if m.budget.err != nil {
				return Expr{}
			}
		}
		return expr(e.Kind(), args...)
	default:
		m.fail(MalformedInput)
		return Expr{}
	}
}
