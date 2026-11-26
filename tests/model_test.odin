package tests

import loki ".."
import "core:testing"

@(test)
model_variable_numbering :: proc(t: ^testing.T) {
	m: loki.Model
	defer loki.model_destroy(&m)

	for i in 0 ..< 3 {
		lit := loki.new_bool_var(&m)
		testing.expect_value(t, lit, loki.lit_pos(loki.Var(i)))
	}
}

@(test)
model_copies_clause_literals :: proc(t: ^testing.T) {
	m: loki.Model
	defer loki.model_destroy(&m)

	x := loki.new_bool_var(&m)
	lits := [1]loki.Literal{x}
	loki.add_clause(&m, ..lits[:])
	lits[0] = loki.lit_not(x)
	loki.add_clause(&m, x)

	// If the first clause still points into lits, the two clauses conflict.
	result, solution := loki.model_solve(&m)
	defer delete(solution)
	testing.expect_value(t, result, loki.Result.Sat)
	if testing.expect_value(t, len(solution), 1) {
		testing.expect(t, loki.lit_is_true(x, solution))
	}
}

@(test)
model_empty_clause :: proc(t: ^testing.T) {
	m: loki.Model
	defer loki.model_destroy(&m)

	loki.add_clause(&m)
	result, solution := loki.model_solve(&m)
	defer delete(solution)
	testing.expect_value(t, result, loki.Result.Unsat)
	testing.expect(t, solution == nil)
}

@(test)
model_at_most_one :: proc(t: ^testing.T) {
	// Each mask fixes all four variables in a fresh model.
	for mask in 0 ..< 16 {
		m: loki.Model
		defer loki.model_destroy(&m)

		lits: [4]loki.Literal
		num_true := 0
		for _, i in lits {
			x := loki.new_bool_var(&m)
			lits[i] = x
			if mask & (1 << uint(i)) != 0 {
				loki.add_clause(&m, x)
				num_true += 1
			} else {
				loki.add_clause(&m, loki.lit_not(x))
			}
		}
		loki.add_at_most_one(&m, lits[:])

		result, solution := loki.model_solve(&m)
		defer delete(solution)
		want := loki.Result.Sat if num_true <= 1 else loki.Result.Unsat
		testing.expectf(t, result == want, "assignment mask %04b: got %v, want %v", mask, result, want)
	}
}

@(test)
at_most_sizes :: proc(t: ^testing.T) {
	m: loki.Model
	defer loki.model_destroy(&m)

	// 4 ordinary variables
	lits: [4]loki.Literal
	for &l in lits {
		l = loki.new_bool_var(&m)
	}
	testing.expect_value(t, m.formula.num_vars, 4)
	testing.expect_value(t, len(m.formula.clauses), 0)

	// at most 2 of 4: 3 tally rows x 2 columns = 6 new variables,
	// and 2 + 5 + 5 + 1 = 13 clauses
	loki.add_at_most(&m, lits[:], 2)
	testing.expect_value(t, m.formula.num_vars, 10)
	testing.expect_value(t, len(m.formula.clauses), 13)
}

// Cardinality_Kind picks which constraint cardinality_brute_force adds.
@(private = "file")
Cardinality_Kind :: enum {
	At_Most,
	At_Least,
	Exactly,
}

@(test)
cardinality_brute_force :: proc(t: ^testing.T) {
	// For every n, k and assignment, fix the literals with unit clauses, add the
	// constraint, and check Sat exactly when the number of true literals fits.
	for kind in Cardinality_Kind {
		for n in 1 ..= 6 {
			for k in -1 ..= n + 1 {
				for mask in 0 ..< 1 << uint(n) {
					m: loki.Model
					defer loki.model_destroy(&m)

					lits: [6]loki.Literal
					num_true := 0
					for i in 0 ..< n {
						lits[i] = loki.new_bool_var(&m)
						if mask & (1 << uint(i)) != 0 {
							loki.add_clause(&m, lits[i])
							num_true += 1
						} else {
							loki.add_clause(&m, loki.lit_not(lits[i]))
						}
					}

					fits: bool
					switch kind {
					case .At_Most:
						loki.add_at_most(&m, lits[:n], k)
						fits = num_true <= k
					case .At_Least:
						loki.add_at_least(&m, lits[:n], k)
						fits = num_true >= k
					case .Exactly:
						loki.add_exactly(&m, lits[:n], k)
						fits = num_true == k
					}

					result, solution := loki.model_solve(&m)
					delete(solution)
					want := loki.Result.Sat if fits else loki.Result.Unsat
					if !testing.expectf(
						t,
						result == want,
						"%v n=%d k=%d mask=%b: got %v, want %v",
						kind, n, k, mask, result, want,
					) {
						return
					}
				}
			}
		}
	}
}

@(test)
exactly_one_brute_force :: proc(t: ^testing.T) {
	for n in 1 ..= 6 {
		for mask in 0 ..< 1 << uint(n) {
			m: loki.Model
			defer loki.model_destroy(&m)

			lits: [6]loki.Literal
			num_true := 0
			for i in 0 ..< n {
				lits[i] = loki.new_bool_var(&m)
				if mask & (1 << uint(i)) != 0 {
					loki.add_clause(&m, lits[i])
					num_true += 1
				} else {
					loki.add_clause(&m, loki.lit_not(lits[i]))
				}
			}
			loki.add_exactly_one(&m, lits[:n])

			result, solution := loki.model_solve(&m)
			delete(solution)
			want := loki.Result.Sat if num_true == 1 else loki.Result.Unsat
			if !testing.expectf(t, result == want, "n=%d mask=%b: got %v, want %v", n, mask, result, want) {
				return
			}
		}
	}
}

@(test)
at_most_one_switch :: proc(t: ^testing.T) {
	// Up to the cutoff: pairwise, n(n-1)/2 clauses and no new variables.
	// Above it: the counter, 3n-4 clauses and n-1 new variables.
	Case :: struct {
		n, clauses, new_vars: int,
	}
	n_max := loki.AT_MOST_ONE_PAIRWISE_MAX
	cases := [?]Case {
		{n_max, n_max * (n_max - 1) / 2, 0},
		{n_max + 1, 3 * (n_max + 1) - 4, n_max},
	}
	for c in cases {
		m: loki.Model
		defer loki.model_destroy(&m)

		lits := make([]loki.Literal, c.n)
		defer delete(lits)
		for &l in lits {
			l = loki.new_bool_var(&m)
		}
		loki.add_at_most_one(&m, lits)
		testing.expectf(t, len(m.formula.clauses) == c.clauses, "n=%d: %d clauses, want %d", c.n, len(m.formula.clauses), c.clauses)
		testing.expectf(t, int(m.formula.num_vars) - c.n == c.new_vars, "n=%d: %d new variables, want %d", c.n, int(m.formula.num_vars) - c.n, c.new_vars)
	}
}

@(test)
at_most_one_above_cutoff :: proc(t: ^testing.T) {
	// Every assignment with 0, 1, 2 or 3 true literals, on a group past the cutoff.
	n := loki.AT_MOST_ONE_PAIRWISE_MAX + 2
	for mask in 0 ..< 1 << uint(n) {
		num_true := 0
		for i in 0 ..< n {
			if mask & (1 << uint(i)) != 0 {num_true += 1}
		}
		if num_true > 3 {continue}

		m: loki.Model
		defer loki.model_destroy(&m)
		lits := make([]loki.Literal, n)
		defer delete(lits)
		for i in 0 ..< n {
			lits[i] = loki.new_bool_var(&m)
			loki.add_clause(&m, lits[i] if mask & (1 << uint(i)) != 0 else loki.lit_not(lits[i]))
		}
		loki.add_at_most_one(&m, lits)

		result, solution := loki.model_solve(&m)
		delete(solution)
		want := loki.Result.Sat if num_true <= 1 else loki.Result.Unsat
		if !testing.expectf(t, result == want, "mask=%b: got %v, want %v", mask, result, want) {
			return
		}
	}
}
