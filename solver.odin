package loki


// NO_REASON is the sentinel for "no clause": no implying reason or no conflict.
NO_REASON :: -1

// The Lifted Boolean type is used to represent a boolean value that can also be undefined.
LBool :: enum u8 {
	Undef,
	True,
	False,
}

Result :: enum {
	Sat,
	Unsat,
}


// Solver represents a SAT solver that operates on a given formula, maintains variable assignments, and tracks the trail of decisions made during the solving process.
Solver :: struct {
	formula:   ^Formula,
	values:    []LBool,
	trail:     [dynamic]Literal,
	trail_lim: [dynamic]int,
	watches:   [][dynamic]int,
	qhead:     int,
	levels:    []int,
	reasons:   []int,
	seen:      []bool,
}

// solver_init creates a solver for f. The solver keeps a pointer to f, so f
// must outlive it; release the solver with solver_destroy.
solver_init :: proc(f: ^Formula) -> Solver {
	s := Solver {
		formula = f,
		watches = make([][dynamic]int, 2 * f.num_vars),
		values  = make([]LBool, f.num_vars),
		seen    = make([]bool, f.num_vars),
		levels  = make([]int, f.num_vars),
		reasons = make([]int, f.num_vars),
	}
	for c, i in f.clauses {
		if len(c) >= 2 {
			append(&s.watches[c[0]], i)
			append(&s.watches[c[1]], i)
		}
	}
	return s
}

// solver_destroy frees the solver's internal state. It does not free the formula.
solver_destroy :: proc(s: ^Solver) {
	delete(s.values)
	delete(s.trail)
	delete(s.trail_lim)
	// delete the inner before the outer
	for v in s.watches {
		delete(v)
	}
	delete(s.watches)
	delete(s.reasons)
	delete(s.levels)
	delete(s.seen)
}


// clause_satisfied reports whether any literal in c is true under assignment,
// which is indexed by variable.
clause_satisfied :: proc(c: Clause, assignment: []bool) -> bool {
	for v in c {
		if lit_is_true(v, assignment) {
			return true
		}
	}
	return false
}


// assign makes l true at the current decision level and records why: a clause
// index in reason, or NO_REASON for decisions and root units.
assign :: proc(s: ^Solver, l: Literal, reason: int) {
	v := lit_var(l)
	s.reasons[v] = reason
	s.levels[v] = decision_level(s)
	if lit_is_neg(l) {
		s.values[v] = LBool.False
	} else {
		s.values[v] = LBool.True
	}
	append(&s.trail, l)
}

// propagate performs unit propagation on the trail. It returns the index of a
// conflicting clause, or NO_REASON if none was found.
propagate :: proc(s: ^Solver) -> int {
	for s.qhead < len(s.trail) {
		p := s.trail[s.qhead]
		s.qhead += 1
		false_lit := lit_neg(p)

		ws := &s.watches[false_lit]
		i := 0
		for i < len(ws) {
			ci := ws[i]
			c := s.formula.clauses[ci]

			// Normalise: Make sure false_lit is in c[1]
			if c[0] == false_lit {
				c[0], c[1] = c[1], c[0]
			}
			// Case 1: other watched lit is True -> Clause Satisfied
			if lit_value(s, c[0]) == .True {
				i += 1
				continue
			}
			// Case 2: Look for replacement watch in c[2], c[3], ...
			found := false
			for k in 2 ..< len(c) {
				if lit_value(s, c[k]) != .False {
					c[1], c[k] = c[k], c[1] // literal goes to watch pos 1
					append(&s.watches[c[1]], ci) // register clause under new watch
					unordered_remove(ws, i) //remove it from old watch list
					found = true
					break
				}
			}
			if found {
				continue
			}
			// Case 3: No replacement, clause stays watching false_lit
			if lit_value(s, c[0]) == .False {
				return ci
			} else {
				assign(s, c[0], ci)
			}
			i += 1
		}
	}

	return NO_REASON
}

// decision_level returns the number of active decisions; 0 is the root level.
decision_level :: proc(s: ^Solver) -> int {
	return len(s.trail_lim)
}

// new_decision_level starts a new decision level at the current trail length.
// It must be called before assigning the decision literal.
new_decision_level :: proc(s: ^Solver) {
	current_trail_len := len(s.trail)
	append(&s.trail_lim, current_trail_len)
}


// backtrack returns the solver to the given decision level, unassigning
// everything above it.
backtrack :: proc(s: ^Solver, level: int) {
	if level >= decision_level(s) {
		return
	}
	target_trail_length := s.trail_lim[level]
	for len(s.trail) > target_trail_length {
		l := pop(&s.trail)
		s.values[lit_var(l)] = .Undef
	}
	resize(&s.trail_lim, level)
	s.qhead = target_trail_length
}

// pick_unassigned returns the unassigned variable with the highest activity,
// or false if every variable is assigned.
pick_unassigned :: proc(s: ^Solver) -> (Var, bool) {
	for v, i in s.values {
		if v == .Undef {
			return Var(i), true
		}
	}
	return Var(0), false
}


// solve runs conflict-driven clause learning. On .Sat, the satisfying
// assignment is in s.values. Non-unit learned clauses are appended to
// s.formula.clauses.
solve :: proc(s: ^Solver) -> Result {
	for c in s.formula.clauses {
		switch len(c) {
		case 0:
			return .Unsat
		case 1:
			v := lit_value(s, c[0])
			switch v {
			case .False:
				return .Unsat
			case .True:
				continue
			case .Undef:
				assign(s, c[0], NO_REASON)
			}
		}
	}

	for {
		confl := propagate(s)

		switch confl {
		case NO_REASON:
			v, ok := pick_unassigned(s)
			if !ok {
				return .Sat
			}
			new_decision_level(s)
			assign(s, lit_pos(v), NO_REASON)
		case:
			if decision_level(s) == 0 {
				return .Unsat
			}
			learnt, bj_level := analyze(s, confl)
			backtrack(s, bj_level)
			if len(learnt) == 1 {
				assign(s, learnt[0], NO_REASON)
				delete(learnt)
			} else {
				append(&s.formula.clauses, learnt[:])
				ci := len(s.formula.clauses) - 1
				append(&s.watches[learnt[0]], ci)
				append(&s.watches[learnt[1]], ci)
				assign(s, learnt[0], ci)
			}
		}
	}
	return .Unsat
}

// analyze performs conflict analysis on the conflict clause `confl` using the
// first Unique Implication Point (1UIP) scheme. It walks the implication graph
// backwards from the conflict, resolving the reason clauses of trail literals
// until only one literal from the current decision level remains (the UIP).
//
// Returns the learnt clause and the level to backjump to:
//   learnt   - slot 0 holds the negated UIP literal, which the clause asserts
//              after backjumping; slots 1.. hold falsified literals from
//              earlier decision levels, with the highest-level one swapped
//              into slot 1 so the two watched literals are the asserting one
//              and the latest-level one.
//   bj_level - highest decision level among learnt[1:], or 0 for a unit clause.
//
// As a side effect, bump (VSIDS) is applied to every newly seen literal above
// decision level 0, so variables involved in recent conflicts are preferred by
// pick_unassigned.
//
// The caller owns the returned dynamic array.
analyze :: proc(s: ^Solver, confl: int) -> (learnt: [dynamic]Literal, bj_level: int) {
	append(&learnt, Literal(0)) // reserves slot 0

	counter := 0
	p: Literal
	p_set := false
	idx := len(s.trail) - 1
	confl := confl
	current := decision_level(s)

	// each time around the loop, look at one clause.
	// first the conflict clause, then the reason clauses.
	for {
		c := s.formula.clauses[confl]
		start := 1 if p_set else 0

		for k in start ..< len(c) {
			q := c[k]
			v := lit_var(q)

			if !s.seen[v] && s.levels[v] > 0 {
				s.seen[v] = true
				if s.levels[v] == current {
					counter += 1
				} else {
					append(&learnt, q)
				}
			}
		}

		for !s.seen[lit_var(s.trail[idx])] {
			idx -= 1
		}
		p = s.trail[idx]
		p_set = true
		idx -= 1
		s.seen[lit_var(p)] = false
		counter -= 1

		if counter == 0 {
			break // p is the 1UIP
		}
		confl = s.reasons[lit_var(p)] // next time expand p's reason
	}

	learnt[0] = lit_neg(p)

	// backjump level = highest level among learnt[1:], move that literal into slot 1
	bj_level = 0
	max_i := 1
	for i in 1 ..< len(learnt) {
		lvl := s.levels[lit_var(learnt[i])]
		if lvl > bj_level {
			bj_level = lvl
			max_i = i
		}
	}
	if len(learnt) > 1 {
		learnt[1], learnt[max_i] = learnt[max_i], learnt[1]
	}

	// clear seen for older level literals. current level literals were already cleared
	for i in 1 ..< len(learnt) {
		s.seen[lit_var(learnt[i])] = false
	}

	return learnt, bj_level
}

// bump adds var_inc to activity[v]; if the result exceeds 1e100, it rescales
// all activities and var_inc by 1e-100 to avoid overflow.
bump :: proc(s: ^Solver, v: Var) {
	s.activity[v] += s.var_inc
	if s.activity[v] > 1e100 {
		// rescale activity and var_inc by 1e-100
		for &a in s.activity {
			a *= 1e-100
		}
		s.var_inc *= 1e-100
	}
}
