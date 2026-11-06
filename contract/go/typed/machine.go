package typed

type entry struct {
	typ          Expr
	definition   Expr
	defined      bool
	used         map[string]struct{}
	dependencies map[string]struct{}
}

type machine struct {
	budget       *budget
	signature    map[string]entry
	used         map[string]struct{}
	dependencies map[string]struct{}
}

func (m *machine) tick(depth uint32) bool { return m.budget.tick(depth) }
func (m *machine) fail(code Code)         { m.budget.fail(invalid(code)) }

func (m *machine) resetUsage() {
	m.used = make(map[string]struct{})
	m.dependencies = make(map[string]struct{})
}

func (m *machine) entry(name string, depth uint32) (entry, bool) {
	if !m.tick(depth) || !m.budget.charge(uint64(len(name))*2) {
		return entry{}, false
	}
	e, ok := m.signature[name]
	if !ok {
		m.fail(UnknownConstant)
		return entry{}, false
	}
	m.used[name] = struct{}{}
	if !mergeNames(m.used, e.used, m.budget) || !mergeNames(m.dependencies, e.dependencies, m.budget) {
		return entry{}, false
	}
	return e, true
}

// Cached closures are maps. Reserve metadata traversal, then aggregate byte and
// insertion work before mutating a destination, so exhaustion is independent of
// their iteration order even when names have different byte lengths.
func mergeNames(destination, source map[string]struct{}, b *budget) bool {
	if !b.charge(uint64(len(source))) {
		return false
	}
	amount := uint64(len(source))
	for name := range source {
		amount += uint64(len(name))
	}
	if !b.charge(amount) {
		return false
	}
	for name := range source {
		destination[name] = struct{}{}
	}
	return true
}

func (m *machine) declare(d Declaration) {
	if !m.tick(0) || !m.budget.charge(uint64(len(d.name))*2) {
		return
	}
	if _, exists := m.signature[d.name]; exists {
		m.fail(DuplicateConstant)
		return
	}
	m.resetUsage()
	m.universe(d.typ, nil, 0)
	if d.kind == defined {
		m.expect(d.value, d.typ, nil, 0)
	}
	if m.budget.err != nil {
		return
	}
	// Scan all syntax in addition to typing. Dependencies in a branch erased by
	// conversion remain part of the declared rule's basis.
	m.reachable(d.typ)
	if d.kind == defined {
		m.reachable(d.value)
	}
	for _, dependency := range d.dependencies {
		if !m.tick(0) || !m.budget.charge(uint64(len(dependency))) {
			return
		}
		m.dependencies[dependency] = struct{}{}
	}
	if m.budget.err != nil {
		return
	}
	m.signature[d.name] = entry{typ: d.typ, definition: d.value, defined: d.kind == defined, used: m.used, dependencies: m.dependencies}
}

func (m *machine) reachable(root Expr) {
	stack := []Expr{root}
	for len(stack) > 0 && m.budget.err == nil {
		i := len(stack) - 1
		e := stack[i]
		stack = stack[:i]
		if !m.tick(0) {
			return
		}
		if e.Kind() == ConstKind {
			if _, ok := m.entry(e.Name(), 0); !ok {
				return
			}
		}
		stack = append(stack, e.node.args...)
	}
}

func (m *machine) context(types []Expr) []Expr {
	if !m.budget.charge(uint64(len(types))) {
		return nil
	}
	ctx := make([]Expr, 0, len(types))
	for i, typ := range types {
		m.budget.location = Location{Phase: ContextPhase, Index: uint32(i), HasIndex: true}
		if !m.tick(uint32(len(ctx))) {
			return nil
		}
		m.universe(typ, ctx, 0)
		ctx = append(ctx, m.copy(typ, 0))
		if m.budget.err != nil {
			return nil
		}
	}
	return ctx
}

func (m *machine) universe(e Expr, ctx []Expr, depth uint32) uint32 {
	if !m.tick(depth) {
		return 0
	}
	inferred := m.infer(e, ctx, depth+1)
	normal := m.normalize(inferred, depth+1)
	if normal.Kind() != SortKind {
		m.fail(ExpectedUniverse)
		return 0
	}
	return normal.Index()
}

func (m *machine) expect(e, expected Expr, ctx []Expr, depth uint32) {
	if !m.tick(depth) {
		return
	}
	actual := m.infer(e, ctx, depth+1)
	m.convert(actual, expected, depth+1)
}

func (m *machine) motive(e, domain Expr, ctx []Expr, depth uint32) {
	if !m.tick(depth) {
		return
	}
	typ := m.infer(e, ctx, depth+1)
	normal := m.normalize(typ, depth+1)
	if normal.Kind() != PiKind {
		m.fail(ExpectedFunction)
		return
	}
	m.convert(normal.node.args[0], domain, depth+1)
	if normal.node.args[1].Kind() != SortKind {
		m.fail(ExpectedUniverse)
	}
}

func (m *machine) convert(left, right Expr, depth uint32) {
	if !m.tick(depth) {
		return
	}
	a := m.normalize(left, depth+1)
	b := m.normalize(right, depth+1)
	if !m.same(a, b, depth+1) {
		m.fail(TypeMismatch)
	}
}

func (m *machine) same(a, b Expr, depth uint32) bool {
	if !m.tick(depth) {
		return false
	}
	if a.Kind() != b.Kind() {
		return false
	}
	if a.node == nil || b.node == nil {
		m.fail(MalformedInput)
		return false
	}
	if !m.budget.charge(uint64(len(a.Name())) + uint64(len(b.Name()))) {
		return false
	}
	if a.Index() != b.Index() || a.Name() != b.Name() || len(a.node.args) != len(b.node.args) {
		return false
	}
	for i := range a.node.args {
		if !m.same(a.node.args[i], b.node.args[i], depth+1) {
			return false
		}
	}
	return true
}
