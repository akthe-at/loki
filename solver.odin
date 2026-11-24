package loki

import "core:slice"

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

Restart_Schedule :: enum {
	Geometric,
	Luby,
}

Clause_Info :: struct {
	learned: bool,
	lbd:     int,
	deleted: bool,
}

Victim_Candidate :: struct {
	ci:  int,
	lbd: int,
}


// Solver represents a SAT solver that operates on a given formula, maintains variable assignments, and tracks the trail of decisions made during the solving process.
Solver :: struct {
	formula:          ^Formula,
	values:           []LBool,
	trail:            [dynamic]Literal,
	trail_lim:        [dynamic]int,
	infos:            [dynamic]Clause_Info,
	watches:          [][dynamic]int,
	qhead:            int,
	levels:           []int,
	reasons:          []int,
	seen:             []bool,
	level_seen:       []bool,
	polarity:         []bool,
	activity:         []f64,
	phase_saving:     bool,
	var_inc:          f64,
	conflicts:        int,
	decisions:        int,
	restarts:         int,
	deleted:          int,
	reduce_first:     int,
	reduce_inc:       int,
	reductions:       int,
	restart_schedule: Restart_Schedule,
	restart_unit:     int,
}

// solver_init creates a solver for f. The solver keeps a pointer to f, so f
// must outlive it; release the solver with solver_destroy.
solver_init :: proc(f: ^Formula) -> Solver {
	s := Solver {
		formula          = f,
		var_inc          = 1.0,
		reduce_first     = 2000,
		reduce_inc       = 300,
		restart_schedule = .Geometric,
		restart_unit     = 100,
		phase_saving     = true,
		watches          = make([][dynamic]int, 2 * f.num_vars),
		values           = make([]LBool, f.num_vars),
		seen             = make([]bool, f.num_vars),
		level_seen       = make([]bool, f.num_vars + 1),
		levels           = make([]int, f.num_vars),
		reasons          = make([]int, f.num_vars),
		activity         = make([]f64, f.num_vars),
		polarity         = make([]bool, f.num_vars),
	}
	for c, i in f.clauses {
		append(&s.infos, Clause_Info{})
		if len(c) >= 2 {
			append(&s.watches[c[0]], i)
			append(&s.watches[c[1]], i)
		}
	}
	for &v in s.polarity {
		v = true
	}
	assert(len(s.infos) == len(s.formula.clauses))
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
	delete(s.level_seen)
	delete(s.seen)
	delete(s.activity)
	delete(s.infos)
	delete(s.polarity)
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
			assert(!s.infos[ci].deleted)
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
		if s.phase_saving {
			s.polarity[lit_var(l)] = !lit_is_neg(l)
		}
		s.values[lit_var(l)] = .Undef
	}
	resize(&s.trail_lim, level)
	s.qhead = target_trail_length
}

// pick_unassigned returns the unassigned variable with the highest activity,
// or false if every variable is assigned.
pick_unassigned :: proc(s: ^Solver) -> (Var, bool) {
	best_score := -1.0
	best_index := -1

	for v, i in s.values {
		if v != .Undef {
			continue
		}
		if s.activity[i] > best_score {
			best_score = s.activity[i]
			best_index = i
		}
	}
	if best_index != -1 {
		return Var(best_index), true
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

	restart_limit := s.restart_unit
	interval := s.reduce_first
	next_reduce := s.reduce_first
	conflicts_since_restart := 0

	for {
		confl := propagate(s)

		switch confl {
		case NO_REASON:
			if s.conflicts >= next_reduce {
				reduce_db(s)
				interval += s.reduce_inc
				next_reduce += interval
			}
			if conflicts_since_restart >= restart_limit {
				backtrack(s, 0)
				conflicts_since_restart = 0
				s.restarts += 1
				switch s.restart_schedule {
				case .Geometric:
					restart_limit = restart_limit * 3 / 2
				case .Luby:
					restart_limit = s.restart_unit * luby(s.restarts + 1)
				}
				continue
			}
			v, ok := pick_unassigned(s)
			if !ok {
				return .Sat
			}
			s.decisions += 1
			new_decision_level(s)
			decision: Literal
			if s.polarity[v] {
				decision = lit_pos(v)
			} else {
				decision = lit_neg(lit_pos(v))
			}
			assign(s, decision, NO_REASON)
		case:
			if decision_level(s) == 0 {
				return .Unsat
			}
			learnt, bj_level := analyze(s, confl)
			s.var_inc /= 0.95
			s.conflicts += 1
			conflicts_since_restart += 1
			lbd := compute_lbd(s, learnt[:])
			backtrack(s, bj_level)
			if len(learnt) == 1 {
				assign(s, learnt[0], NO_REASON)
				delete(learnt)
			} else {
				append(&s.formula.clauses, learnt[:])
				ci := len(s.formula.clauses) - 1
				append(&s.infos, Clause_Info{learned = true, lbd = lbd})
				assert(len(s.infos) == len(s.formula.clauses))
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
	append(&learnt, Literal(0)) // reserves slot 0 for the negated UIP

	counter := 0 // seen literals at the current level still to resolve
	p: Literal
	p_set := false
	idx := len(s.trail) - 1
	confl := confl // mutable copy of the parameter
	current := decision_level(s)

	// each time around the loop, look at one clause.
	// first the conflict clause, then the reason clauses.
	for {
		c := s.formula.clauses[confl]
		// skip c[0] once resolving reasons: it is p itself, the literal this
		// clause propagated. the conflict clause asserts nothing, so the
		// first pass scans every literal.
		start := 1 if p_set else 0

		for k in start ..< len(c) {
			q := c[k]
			v := lit_var(q)

			// ignore duplicates and level-0 facts (permanent assignments)
			if !s.seen[v] && s.levels[v] > 0 {
				s.seen[v] = true
				bump(s, v)
				if s.levels[v] == current {
					counter += 1
				} else {
					append(&learnt, q)
				}
			}
		}

		// reverse trail order is reverse implication order
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

	// after backjumping, all other learnt literals are still false, so the
	// clause propagates lit_neg(p)
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

// compute_lbd returns the number or distinct decision levels among lits.
compute_lbd :: proc(s: ^Solver, lits: []Literal) -> int {
	lbd := 0
	for l in lits {
		v := lit_var(l)
		lvl := s.levels[v]

		if !s.level_seen[lvl] {
			s.level_seen[lvl] = true
			lbd += 1
		}
	}

	for l in lits {
		v := lit_var(l)
		lvl := s.levels[v]
		s.level_seen[lvl] = false
	}
	assert(1 <= lbd && lbd <= len(lits))

	return lbd
}

locked :: proc(s: ^Solver, ci: int) -> bool {
	c := s.formula.clauses[ci]

	return lit_value(s, c[0]) == .True && s.reasons[lit_var(c[0])] == ci
}

// Victim rules: a clause can be deleted only if it's learned, has LBD > 2 (glue clauses are kept),
// and is not locked.
// Among those, sort by LBD, highest first, and pick the first half.
//  - Locked clauses: a clause is locked while it's the reason for a literal that's currently assigned.
//    Deleting it would leave analyze following reasons[v] to a clause that no longer exists.
//  - Fast locked test: in your code, a clause only ever assigns its slot-0 literal, so the test is "c[0] is
//    true now and reasons[var] == ci". You need both halves because backtrack leaves old reasons entries
//    behind, the same way it leaves levels behind, which ties back to the decision_level() vs s.levels[v]
//    mix-up from earlier.
collect_victims :: proc(s: ^Solver) -> [dynamic]int {
	candidates: [dynamic]Victim_Candidate
	defer delete(candidates)

	result: [dynamic]int

	for info, ci in s.infos {
		// every clause index that is learned, has LBD > 2, and is not locked, each paired with its LBD
		// if it passes all 3 tests, append a pair.
		if info.learned && info.lbd > 2 && !info.deleted && !locked(s, ci) {
			append(&candidates, Victim_Candidate{ci = ci, lbd = info.lbd})
		}
	}

	// sort it worst-first (highest LBD first)
	slice.sort_by(candidates[:], proc(a, b: Victim_Candidate) -> bool {
		return a.lbd > b.lbd
	})

	// declare victims
	// loop over first half of candidates: append each one's ci to victims
	for k in 0 ..< len(candidates) / 2 {
		append(&result, candidates[k].ci)
		assert(
			s.infos[candidates[k].ci].learned &&
			!s.infos[candidates[k].ci].deleted &&
			s.infos[candidates[k].ci].lbd > 2 &&
			!locked(s, candidates[k].ci),
		)
	}


	// return the clause indices of the first half. The caller owns the returned array, and the temporary list is freed inside the proc.
	return result
}

reduce_db :: proc(s: ^Solver) {
	// Mark. Set s.infos[ci].deleted = true for every victim.
	// Clean the watch lists. Walk every watch list and drop the entries whose clause is marked deleted.
	// Free. delete each victim's literals, and set its slot to nil.
	// Count. s.deleted += len(victims).
	victims := collect_victims(s)
	defer delete(victims)
	for ci in victims {
		s.infos[ci].deleted = true
	}

	for &ws in s.watches {
		j := 0
		for ci in ws {

			if !s.infos[ci].deleted {
				ws[j] = ci
				j += 1
			}
		}
		resize(&ws, j)
	}

	for ci in victims {
		delete(s.formula.clauses[ci])
		s.formula.clauses[ci] = nil
	}
	s.deleted += len(victims)
	s.reductions += 1
}

luby :: proc(i: int) -> int {
	assert(i >= 1)
	n := i
	for {
		size := 1

		for size < n {
			size = 2 * size + 1
		}
		if n == size {
			return (size + 1) / 2
		}
		n -= (size - 1) / 2
	}
}
