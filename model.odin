package loki

// AT_MOST_ONE_PAIRWISE_MAX is the largest group add_at_most_one encodes pairwise.
// Bigger groups use the sequential counter, which needs fewer clauses.
AT_MOST_ONE_PAIRWISE_MAX :: 10

// Model owns the variables and clauses of a SAT problem.
// Its zero value is an empty model.
Model :: struct {
	formula: Formula,
}

// new_bool_var creates a Boolean variable and returns its positive literal.
new_bool_var :: proc(m: ^Model) -> Literal {
	l := lit_pos(Var(m.formula.num_vars))
	m.formula.num_vars += 1
	return l
}

// add_clause adds a clause that requires at least one of lits to be true.
// The model copies the literals. An empty clause makes the model unsatisfiable.
add_clause :: proc(m: ^Model, lits: ..Literal) {
	c := make([]Literal, len(lits), clause_allocator(&m.formula))
	copy(c, lits)
	append(&m.formula.clauses, c)
}


// add_at_most_one adds "at most one of lits is true".
// Up to AT_MOST_ONE_PAIRWISE_MAX literals it forbids every pair, with no extra variables.
// Above that it uses add_at_most(m, lits, 1), the sequential counter.
add_at_most_one :: proc(m: ^Model, lits: []Literal) {
	if len(lits) > AT_MOST_ONE_PAIRWISE_MAX {
		add_at_most(m, lits, 1)
		return
	}
	for l, i in lits {
		for j in i + 1 ..< len(lits) {
			add_clause(m, lit_not(lits[j]), lit_not(l))
		}
	}
}

// add_at_most adds "at most k of lits are true", using Sinz's sequential counter.
// It creates (n-1)*k auxiliary variables when 1 <= k < n. A negative k makes
// the model unsatisfiable.
add_at_most :: proc(m: ^Model, lits: []Literal, k: int) {
	n := len(lits)
	switch {
	case k < 0:
		add_clause(m)
		return
	case k >= n:
		return
	case k == 0:
		for l in lits {
			add_clause(m, lit_not(l))
		}
		return
	}

	// at_least returns the counter variable meaning "at least j+1 of `lits[0..i]` are true".
	// The counter variables are numbered consecutively from base, k per position.
	at_least :: proc(base: u32, k, i, j: int) -> Literal {
		return lit_pos(Var(base + u32(i * k + j)))
	}


	base := m.formula.num_vars
	for _ in 0 ..< (n - 1) * k {
		_ = new_bool_var(m)
	}

	// First literal: it alone makes the tally 1, never more.
	add_clause(m, lit_not(lits[0]), at_least(base, k, 0, 0))
	for j in 1 ..< k {
		add_clause(m, lit_not(at_least(base, k, 0, j)))
	}

	// Middle literals: update the tally, and forbid going past k.
	for i in 1 ..< n - 1 {
		// this one true -> tally >= 1
		add_clause(m, lit_not(lits[i]), at_least(base, k, i, 0))
		// tally >= 1 before -> still >= 1
		add_clause(m, lit_not(at_least(base, k, i - 1, 0)), at_least(base, k, i, 0))

		for j in 1 ..< k {
			// this one true and tally >= j before -> tally >= j+1
			add_clause(
				m,
				lit_not(lits[i]),
				lit_not(at_least(base, k, i - 1, j - 1)),
				at_least(base, k, i, j),
			)
			// tally >= j+1 before -> still >= j+1
			add_clause(m, lit_not(at_least(base, k, i - 1, j)), at_least(base, k, i, j))
		}

		// this one true and tally already k -> too many
		add_clause(m, lit_not(lits[i]), lit_not(at_least(base, k, i - 1, k - 1)))
	}

	// Last literal: only the "too many" check, since nothing reads its tally.
	add_clause(m, lit_not(lits[n - 1]), lit_not(at_least(base, k, n - 2, k - 1)))

}

// add_at_least adds "at least k of lits are true". k <= 0 adds nothing, and
// k > len(lits) makes the model unsatisfiable.
add_at_least :: proc(m: ^Model, lits: []Literal, k: int) {
	if k <= 0 {
		return
	}
	if k == 1 {
		add_clause(m, ..lits)
		return
	}

	neg := make([]Literal, len(lits))
	defer delete(neg)
	for l, i in lits {
		neg[i] = lit_not(l)
	}
	add_at_most(m, neg, len(lits) - k)
}

// add_exactly adds "exactly k of lits are true". A k below 0 or above len(lits)
// makes the model unsatisfiable.
add_exactly :: proc(m: ^Model, lits: []Literal, k: int) {
	add_at_most(m, lits, k)
	add_at_least(m, lits, k)
}

// add_exactly_one adds "exactly one of lits is true".
add_exactly_one :: proc(m: ^Model, lits: []Literal) {
	add_clause(m, ..lits)
	add_at_most_one(m, lits)
}


// model_destroy frees the storage owned by m.
model_destroy :: proc(m: ^Model) {
	formula_destroy(&m.formula)
}

// model_solve solves m. The formula is left unchanged.
// On .Sat, solution[v] gives the value of variable v (zero-based).
// The caller owns the solution and frees it with delete.
model_solve :: proc(
	m: ^Model,
	allocator := context.allocator,
) -> (
	result: Result,
	solution: []bool,
) {

	s := solver_make(&m.formula)
	defer solver_destroy(&s)

	result = solve(&s)

	if result == .Sat {
		solution = make([]bool, m.formula.num_vars, allocator)
		for v, i in s.values {
			solution[i] = v == .True
		}
	}
	return result, solution
}
