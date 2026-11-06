package typed

// Check validates supplied proof syntax against the receiver's exact statement.
// The statement and policy are borrowed for this synchronous call; callers must
// not concurrently mutate their slices. Expr and Declaration are immutable.
// No parsing, search, semantic extraction or asynchronous cancellation is done.
func Check(statement Statement, candidate Expr, policy Policy, limits Limits) Outcome {
	b := &budget{remaining: limits.Work, depth: min(limits.Depth, uint32(512)), location: Location{Phase: PreflightPhase}}
	p := preflight{budget: b, limits: limits}
	if !p.all(statement, candidate, policy) {
		return failed(b)
	}
	b.location = Location{Phase: PolicyPhase}
	if !b.charge(uint64(len(statement.Foundation)) + uint64(len(policy.Foundation)) + uint64(len(policy.Checker))) {
		return failed(b)
	}
	switch {
	case statement.Foundation != Foundation:
		b.fail(unsupported(UnsupportedFoundation, statement.Foundation))
	case policy.Foundation != Foundation:
		b.fail(unsupported(UnadmittedFoundation, policy.Foundation))
	case policy.Checker != Checker:
		b.fail(unsupported(UnadmittedChecker, policy.Checker))
	}
	if b.err != nil {
		return failed(b)
	}
	m := machine{budget: b, signature: make(map[string]entry)}
	for i, d := range statement.Declarations {
		b.location = Location{Phase: DeclarationPhase, Index: uint32(i), HasIndex: true}
		m.declare(d)
		if b.err != nil {
			return failed(b)
		}
	}
	m.resetUsage()
	ctx := m.context(statement.Context)
	if b.err != nil {
		return failed(b)
	}
	b.location = Location{Phase: ExpectedPhase}
	m.universe(statement.Expected, ctx, 0)
	if b.err != nil {
		return failed(b)
	}
	b.location = Location{Phase: CandidatePhase}
	actual := m.infer(candidate, ctx, 0)
	m.convert(actual, statement.Expected, 0)
	if b.err != nil {
		return failed(b)
	}
	// The closure is syntactic, including unused hypotheses and arguments that
	// beta/projection/eliminator conversion may discard.
	for _, e := range statement.Context {
		m.reachable(e)
	}
	m.reachable(statement.Expected)
	m.reachable(candidate)
	if b.err != nil {
		return failed(b)
	}
	b.location = Location{Phase: PolicyPhase}
	if !b.charge(uint64(len(policy.Dependencies))) {
		return failed(b)
	}
	allowed := make(map[string]struct{}, len(policy.Dependencies))
	for _, dep := range policy.Dependencies {
		if !b.tick(0) || !b.charge(uint64(len(dep))) {
			return failed(b)
		}
		allowed[dep] = struct{}{}
	}
	dependencies := sortedKeys(m.dependencies, b)
	for _, dep := range dependencies {
		if !b.tick(0) || !b.charge(uint64(len(dep))) {
			return failed(b)
		}
		if _, ok := allowed[dep]; !ok {
			b.fail(unsupported(UnadmittedDependency, dep))
			return failed(b)
		}
	}
	if b.err != nil {
		return failed(b)
	}
	b.location = Location{Phase: SnapshotPhase}
	used := sortedKeys(m.used, b)
	snapshot := snapshotStatement(statement, b)
	admitted := snapshotPolicy(policy, b)
	if !b.tick(0) {
		return failed(b)
	}
	a := &acceptanceState{valid: true, statement: snapshot, candidate: candidate, policy: admitted, used: used, dependencies: dependencies, steps: b.spent}
	return Outcome{status: AcceptedStatus, accepted: a, steps: b.spent}
}

func failed(b *budget) Outcome {
	if b.err == nil {
		return Outcome{status: InvalidStatus, code: MalformedInput, steps: b.spent, location: b.location}
	}
	return Outcome{status: b.err.status, code: b.err.code, detail: b.err.detail, steps: b.spent, location: b.err.location}
}

func sortedKeys(set map[string]struct{}, b *budget) []string {
	// Reserve the metadata traversal before inspecting any key. Byte content is
	// untouched while finding its maximum length, independently of map order.
	if !b.charge(uint64(len(set))) {
		return nil
	}
	var longest uint64
	for key := range set {
		longest = max(longest, uint64(len(key)))
	}
	count := uint64(len(set))
	height := uint64(0)
	for n := count; n > 0; n >>= 1 {
		height++
	}
	// Heap construction and extraction together use fewer than 4*n*height
	// primitive operations/comparisons. Reserve their worst-case byte cost
	// before allocating or sorting, avoiding map-order-dependent work charges.
	reserve := count
	if count > 1 {
		for _, factor := range []uint64{4, height, 1 + longest} {
			if reserve > uint64(maxNatural)/factor {
				reserve = uint64(maxNatural) + 1
				break
			}
			reserve *= factor
		}
	}
	if !b.charge(reserve) {
		return nil
	}
	keys := make([]string, 0, len(set))
	for key := range set {
		keys = append(keys, key)
	}
	// The complete bounded sort has already been charged, including comparison
	// byte scans. Its output is UTF-8 byte order for every initial heap order.
	for start := len(keys)/2 - 1; start >= 0; start-- {
		siftKeys(keys, start, len(keys))
	}
	for end := len(keys) - 1; end > 0; end-- {
		keys[0], keys[end] = keys[end], keys[0]
		siftKeys(keys, 0, end)
	}
	return keys
}

func siftKeys(keys []string, root, end int) {
	for root < end/2 {
		child := root*2 + 1
		if child+1 < end {
			if keys[child] < keys[child+1] {
				child++
			}
		}
		if keys[root] >= keys[child] {
			break
		}
		keys[root], keys[child] = keys[child], keys[root]
		root = child
	}
}

func snapshotStatement(s Statement, b *budget) Statement {
	result := Statement{Foundation: s.Foundation, Expected: s.Expected}
	if !b.charge(uint64(len(s.Declarations)) + uint64(len(s.Context))) {
		return Statement{}
	}
	result.Declarations = make([]Declaration, 0, len(s.Declarations))
	for _, d := range s.Declarations {
		if !b.tick(0) {
			return Statement{}
		}
		// Declaration's dependency storage is private and immutable. Expr also
		// exposes no mutable node storage, so these values can safely be shared.
		result.Declarations = append(result.Declarations, d)
	}
	result.Context = make([]Expr, 0, len(s.Context))
	for _, e := range s.Context {
		if !b.tick(0) {
			return Statement{}
		}
		result.Context = append(result.Context, e)
	}
	return result
}

func snapshotPolicy(p Policy, b *budget) Policy {
	if !b.charge(uint64(len(p.Dependencies))) {
		return Policy{}
	}
	result := Policy{Foundation: p.Foundation, Checker: p.Checker}
	result.Dependencies = make([]string, 0, len(p.Dependencies))
	for _, dependency := range p.Dependencies {
		if !b.tick(0) {
			return Policy{}
		}
		result.Dependencies = append(result.Dependencies, dependency)
	}
	return result
}
