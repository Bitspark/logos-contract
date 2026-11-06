package typed

func (m *machine) infer(e Expr, ctx []Expr, depth uint32) Expr {
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
		if e.Index() == maxNatural {
			m.budget.fail(incomplete(UniverseCapacity))
			return Expr{}
		}
		return Sort(e.Index() + 1)
	case VarKind:
		index := e.Index()
		if uint64(index) >= uint64(len(ctx)) {
			m.fail(EscapedVariable)
			return Expr{}
		}
		if index == maxNatural {
			m.budget.fail(incomplete(IndexCapacity))
			return Expr{}
		}
		return m.shift(ctx[len(ctx)-1-int(index)], index+1, d)
	case ConstKind:
		entry, ok := m.entry(e.Name(), d)
		if !ok {
			return Expr{}
		}
		return m.copy(entry.typ, d)
	case PiKind, SigmaKind:
		left := m.universe(a[0], ctx, d)
		inner := append(ctx, m.copy(a[0], d))
		right := m.universe(a[1], inner, d)
		return Sort(max(left, right))
	case LamKind:
		m.universe(a[0], ctx, d)
		inner := append(ctx, m.copy(a[0], d))
		body := m.infer(a[1], inner, d)
		return Pi(m.copy(a[0], d), body)
	case AppKind:
		typ := m.infer(a[0], ctx, d)
		normal := m.normalize(typ, d)
		if normal.Kind() != PiKind {
			m.fail(ExpectedFunction)
			return Expr{}
		}
		m.expect(a[1], normal.node.args[0], ctx, d)
		return m.instantiate(normal.node.args[1], a[1], d)
	case PairKind:
		m.universe(a[0], ctx, d)
		normal := m.normalize(a[0], d)
		if normal.Kind() != SigmaKind {
			m.fail(ExpectedSigma)
			return Expr{}
		}
		m.expect(a[1], normal.node.args[0], ctx, d)
		secondType := m.instantiate(normal.node.args[1], a[1], d)
		m.expect(a[2], secondType, ctx, d)
		return m.copy(a[0], d)
	case FstKind, SndKind:
		typ := m.infer(a[0], ctx, d)
		normal := m.normalize(typ, d)
		if normal.Kind() != SigmaKind {
			m.fail(ExpectedSigma)
			return Expr{}
		}
		if e.Kind() == FstKind {
			return normal.node.args[0]
		}
		return m.instantiate(normal.node.args[1], Fst(m.copy(a[0], d)), d)
	case NatKind, BoolKind:
		return Sort(0)
	case ZeroKind:
		return Nat()
	case SuccKind:
		m.expect(a[0], Nat(), ctx, d)
		return Nat()
	case FalseKind, TrueKind:
		return Bool()
	case NatElimKind:
		return m.inferNatElim(a, ctx, d)
	case BoolElimKind:
		m.motive(a[0], Bool(), ctx, d)
		m.expect(a[3], Bool(), ctx, d)
		m.expect(a[1], App(m.copy(a[0], d), False()), ctx, d)
		m.expect(a[2], App(m.copy(a[0], d), True()), ctx, d)
		return App(m.copy(a[0], d), m.copy(a[3], d))
	case IDKind:
		level := m.universe(a[0], ctx, d)
		m.expect(a[1], a[0], ctx, d)
		m.expect(a[2], a[0], ctx, d)
		return Sort(level)
	case ReflKind:
		m.universe(a[0], ctx, d)
		m.expect(a[1], a[0], ctx, d)
		return ID(m.copy(a[0], d), m.copy(a[1], d), m.copy(a[1], d))
	case TransportKind:
		m.universe(a[0], ctx, d)
		m.expect(a[1], a[0], ctx, d)
		m.expect(a[2], a[0], ctx, d)
		equalityType := ID(m.copy(a[0], d), m.copy(a[1], d), m.copy(a[2], d))
		m.expect(a[3], equalityType, ctx, d)
		m.motive(a[4], a[0], ctx, d)
		m.expect(a[5], App(m.copy(a[4], d), m.copy(a[1], d)), ctx, d)
		return App(m.copy(a[4], d), m.copy(a[2], d))
	default:
		m.fail(MalformedInput)
		return Expr{}
	}
}

func (m *machine) inferNatElim(a []Expr, ctx []Expr, depth uint32) Expr {
	m.motive(a[0], Nat(), ctx, depth)
	m.expect(a[3], Nat(), ctx, depth)
	m.expect(a[1], App(m.copy(a[0], depth), Zero()), ctx, depth)
	ihType := App(m.shift(a[0], 1, depth), Var(0))
	stepResult := App(m.shift(a[0], 2, depth), Succ(Var(1)))
	stepType := Pi(Nat(), Pi(ihType, stepResult))
	m.expect(a[2], stepType, ctx, depth)
	return App(m.copy(a[0], depth), m.copy(a[3], depth))
}
