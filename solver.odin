package loki

import "base:runtime"
import "core:slice"
import "core:time"

// LOKI_PROFILE turns on timing of propagate, pick_unassigned and analyze.
// Build with -define:LOKI_PROFILE=true; normal builds compile no timing code.
LOKI_PROFILE :: #config(LOKI_PROFILE, false)

// NO_REASON is the sentinel for "no clause": no implying reason or no conflict.
@(private)
NO_REASON :: Cref(max(u32))

// Cref names a clause by its offset into Solver.arena.
@(private)
Cref :: distinct u32

// Every clause in the arena is a 2-word header followed by its literals.
// Word 0 holds the size and three flags.
// Word 1 holds the LBD, or while `arena_compact` runs, the clause's new Cref.
@(private)
HEADER_WORDS :: 2

@(private)
SIZE_MASK :: u32(1 << 29) - 1

@(private)
LEARNED_BIT :: u32(1) << 29

@(private)
DELETED_BIT :: u32(1) << 30

@(private)
RELOCATED_BIT :: u32(1) << 31

// COMPACT_FRAC is the share of wasted arena words that triggers arena_compact
// (MiniSat's garbage_frac).
@(private)
COMPACT_FRAC :: 0.20

// LBool is a lifted Boolean: True, False, or Undef (the zero value, unassigned).
LBool :: enum u8 {
	Undef,
	True,
	False,
}

// Result is the outcome of a solve attempt. Unknown (zero value) means no
// answer was produced (e.g. the input failed to parse).
Result :: enum {
	Unknown,
	Sat,
	Unsat,
}

// Restart_Schedule chooses when the solver restarts. Geometric restarts
// after restart_unit conflicts, then grows by 1.5x each time.
// Luby restarts after restart_unit * luby(i) conflicts: (ie: 1, 1, 2, 1, 1, 2, 4)...
Restart_Schedule :: enum {
	Geometric,
	Luby,
}

// Minimize_Mode chooses how analyze shortens each learned clause (MiniSat's
// ccmin-mode 0/1/2). None keeps the 1UIP clause, Local drops literals whose
// reason is already covered by the clause, and Recursive follows reasons
// further back.
Minimize_Mode :: enum {
	None,
	Local,
	Recursive,
}

// Watch is one entry in a literal's watch list: clause cref watches this literal,
// and propagate visits it when the literal becomes false. blocker is another
// literal of the clause; if it is true, the clause is satisfied and propagate
// skips it without reading the arena. binary marks a 2-literal clause, whose
// blocker is its only other literal. Packed into 8 bytes, so cref has 31 bits.
@(private)
Watch :: bit_field u64 {
	cref:    Cref    | 31,
	binary:  bool    | 1,
	blocker: Literal | 32,
}
#assert(size_of(Watch) == 8)

@(private)
Victim_Candidate :: struct {
	cr:  Cref,
	lbd: int,
}


// Solver holds the state of one CDCL search over a Formula.
//
// Settings (set after solver_make, before solve): phase_saving,
// restart_schedule, restart_unit, reduce_first, reduce_inc, and minimize.
// Statistics (read after solve): conflicts, decisions, restarts, clauses_deleted,
// reductions, max_literals, and tot_literals; len(learnts) is the number of
// live learned clauses, and learned_lbd_stats summarizes them.
// prop_time, pick_time and analyze_time are filled in only in LOKI_PROFILE builds.
// On .Sat, values hold the assignment.
// All other fields are internal.
Solver :: struct {
	// Internal
	formula:          ^Formula,
	allocator:        runtime.Allocator, // for the solver's own state
	values:           []LBool,
	analyze_stack:    [dynamic]Literal,
	arena:            [dynamic]u32,
	seen_to_clear:    [dynamic]Literal,
	trail:            [dynamic]Literal,
	level_starts:     [dynamic]int,
	watches:          [][dynamic]Watch,
	learnts:          [dynamic]Cref,
	learnt_buffer:    [dynamic]Literal,
	wasted:           int,
	qhead:            int,
	levels:           []int,
	reasons:          []Cref,
	seen:             []bool,
	lbd_levels:       []bool,
	polarity:         []bool,
	activity:         []f64,
	order:            Var_Heap, // unassigned variables by activity; see heap.odin
	var_inc:          f64,
	//Statistics
	conflicts:        int,
	decisions:        int,
	restarts:         int,
	clauses_deleted:  int,
	reductions:       int,
	max_literals:     int,
	tot_literals:     int,
	prop_time:        time.Duration,
	pick_time:        time.Duration,
	analyze_time:     time.Duration,
	// Settings
	phase_saving:     bool,
	restart_schedule: Restart_Schedule,
	restart_unit:     int,
	reduce_first:     int,
	reduce_inc:       int,
	minimize:         Minimize_Mode,
}

// solver_make creates a solver for f. The solver keeps a pointer to f, so f
// must outlive it; release the solver with solver_destroy. Everything the
// solver allocates, including the clause arena that holds a copy of f's clauses
// and every learned clause, uses allocator. solve never changes f.
solver_make :: proc(f: ^Formula, allocator := context.allocator) -> Solver {
	s := Solver {
		formula          = f,
		allocator        = allocator,
		var_inc          = 1.0,
		reduce_first     = 2000,
		reduce_inc       = 300,
		restart_schedule = .Geometric,
		minimize         = .Recursive,
		restart_unit     = 100,
		phase_saving     = true,
		watches          = make([][dynamic]Watch, 2 * f.num_vars, allocator),
		values           = make([]LBool, f.num_vars, allocator),
		seen             = make([]bool, f.num_vars, allocator),
		lbd_levels       = make([]bool, f.num_vars + 1, allocator),
		levels           = make([]int, f.num_vars, allocator),
		reasons          = make([]Cref, f.num_vars, allocator),
		activity         = make([]f64, f.num_vars, allocator),
		polarity         = make([]bool, f.num_vars, allocator),
		arena            = make([dynamic]u32, allocator),
		analyze_stack    = make([dynamic]Literal, allocator),
		seen_to_clear    = make([dynamic]Literal, allocator),
		trail            = make([dynamic]Literal, allocator),
		level_starts     = make([dynamic]int, allocator),
		learnts          = make([dynamic]Cref, allocator),
		learnt_buffer    = make([dynamic]Literal, allocator),
	}
	for &w in s.watches {
		w = make([dynamic]Watch, allocator)
	}

	for c in f.clauses {
		if len(c) >= 2 {
			attach(&s, clause_alloc(&s, c, learned = false, lbd = 0))
		}
	}

	for &v in s.polarity {
		v = true
	}

	// Every variable starts unassigned, so every variable starts in the heap.
	heap_init(&s.order, f.num_vars, allocator)
	for v in 0 ..< f.num_vars {
		heap_insert(&s.order, s.activity, Var(v))
	}
	return s
}

// solver_destroy frees the solver's internal state. It does not free the formula.
solver_destroy :: proc(s: ^Solver) {
	// Slices don't remember their allocator, so they're freed with s.allocator.
	// Dynamic arrays do, so a plain delete is enough.
	delete(s.values, s.allocator)
	delete(s.trail)
	delete(s.level_starts)
	// delete the inner before the outer
	for v in s.watches {
		delete(v)
	}
	delete(s.watches, s.allocator)
	delete(s.reasons, s.allocator)
	delete(s.levels, s.allocator)
	delete(s.lbd_levels, s.allocator)
	delete(s.seen, s.allocator)
	delete(s.activity, s.allocator)
	delete(s.polarity, s.allocator)
	delete(s.learnts)
	delete(s.learnt_buffer)
	delete(s.seen_to_clear)
	delete(s.analyze_stack)
	delete(s.arena)
	heap_destroy(&s.order)
}

// clause_alloc copies lits into the arena behind a two-word header (size and
// flags, then the LBD) and returns the new clause's
// Cref. Appending can move the arena, so any slice from clause_lits is
// invalid afterwards.
@(private)
clause_alloc :: proc(s: ^Solver, lits: []Literal, learned: bool, lbd: int) -> Cref {
	assert(len(s.arena) < 1 << 31, "arena too big for a Watch's 31-bit cref")

	cr := Cref(len(s.arena))
	word0 := u32(len(lits))
	if learned {
		word0 |= LEARNED_BIT
	}
	append(&s.arena, word0)
	append(&s.arena, u32(lbd))
	for l in lits {
		append(&s.arena, u32(l))
	}
	return cr
}

// attach watches cr's first two literals, so propagate visits cr when either becomes false.
// A binary clause's watches are marked binary, so propagate can use
// the blocker alone and skip reading the arena.
@(private)
attach :: proc(s: ^Solver, cr: Cref) {
	lits := clause_lits(s, cr)
	binary := len(lits) == 2
	append(&s.watches[lits[0]], Watch{cref = cr, blocker = lits[1], binary = binary})
	append(&s.watches[lits[1]], Watch{cref = cr, blocker = lits[0], binary = binary})

}

// clause_lits returns cr's literals as a view into the arena, not a copy.
// The slice is invalid after the next clause_alloc or arena_compact, which
// can move the arena.
@(private)
clause_lits :: proc(s: ^Solver, cr: Cref) -> []Literal {
	size := int(s.arena[cr] & SIZE_MASK)
	start := int(cr) + HEADER_WORDS
	return transmute([]Literal)s.arena[start:start + size]
}

// clause_learned reports whether cr was learned during the search vs copied from the formula.
@(private)
clause_learned :: proc(s: ^Solver, cr: Cref) -> bool {
	return s.arena[cr] & LEARNED_BIT != 0
}

// clause_deleted reports whether reduce_db has deleted cr. Its words stay in
// the arena, marked, until arena_compact squeezes them out.
@(private)
clause_deleted :: proc(s: ^Solver, cr: Cref) -> bool {
	return s.arena[cr] & DELETED_BIT != 0
}

// clause_lbd returns the LBD stored in cr's header: 0 for original clauses.
@(private)
clause_lbd :: proc(s: ^Solver, cr: Cref) -> int {
	return int(s.arena[cr + 1])
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


// assign makes l true at the current decision level and records why: the
// Cref of the implying clause in reason, or NO_REASON for decisions and root
// units.
@(private)
assign :: proc(s: ^Solver, l: Literal, reason: Cref) {
	v := lit_var(l)
	s.reasons[v] = reason
	s.levels[v] = decision_level(s)
	if lit_is_neg(l) {
		s.values[v] = .False
	} else {
		s.values[v] = .True
	}
	append(&s.trail, l)
}

// propagate performs unit propagation on the trail. It returns the Cref of a
// conflicting clause, or NO_REASON if none was found.
@(private)
propagate :: proc(s: ^Solver) -> Cref {
	for s.qhead < len(s.trail) {
		p := s.trail[s.qhead]
		s.qhead += 1
		false_lit := lit_not(p)

		ws := &s.watches[false_lit]
		i := 0
		for i < len(ws) {
			w := ws[i]

			bv := lit_value(s, w.blocker)
			if bv == .True {
				i += 1
				continue
			}

			if w.binary {

				c := clause_lits(s, w.cref)
				if c[0] == false_lit {
					c[0], c[1] = c[1], c[0]
				}

				if bv == .False {
					return w.cref
				}

				assign(s, w.blocker, w.cref)
				i += 1
				continue
			}
			cr := w.cref
			c := clause_lits(s, cr)

			// Normalise: Make sure false_lit is in c[1]
			if c[0] == false_lit {
				c[0], c[1] = c[1], c[0]
			}
			// Case 1: other watched lit is True -> Clause Satisfied
			if lit_value(s, c[0]) == .True {
				ws[i].blocker = c[0]
				i += 1
				continue
			}
			// Case 2: Look for replacement watch in c[2], c[3], ...
			found := false
			for k in 2 ..< len(c) {
				if lit_value(s, c[k]) != .False {
					c[1], c[k] = c[k], c[1] // literal goes to watch pos 1
					append(&s.watches[c[1]], Watch{cref = cr, blocker = c[0], binary = false}) // register clause under new watch
					unordered_remove(ws, i) // remove it from old watch list
					found = true
					break
				}
			}
			if found {
				continue
			}
			// Case 3: No replacement, clause stays watching false_lit
			if lit_value(s, c[0]) == .False {
				return cr
			} else {
				ws[i].blocker = c[0]
				assign(s, c[0], cr)
			}
			i += 1
		}
	}

	return NO_REASON
}

// decision_level returns the number of active decisions; 0 is the root level.
@(private)
decision_level :: proc(s: ^Solver) -> int {
	return len(s.level_starts)
}

// new_decision_level starts a new decision level at the current trail length.
// It must be called before assigning the decision literal.
@(private)
new_decision_level :: proc(s: ^Solver) {
	current_trail_len := len(s.trail)
	append(&s.level_starts, current_trail_len)
}


// backtrack returns the solver to the given decision level, unassigning
// everything above it.
@(private)
backtrack :: proc(s: ^Solver, level: int) {
	if level >= decision_level(s) {
		return
	}
	target_trail_length := s.level_starts[level]
	for len(s.trail) > target_trail_length {
		l := pop(&s.trail)
		if s.phase_saving {
			s.polarity[lit_var(l)] = !lit_is_neg(l)
		}
		s.values[lit_var(l)] = .Undef
		// Keep the invariant: every unassigned variable is in the heap.
		heap_insert(&s.order, s.activity, lit_var(l))
	}
	resize(&s.level_starts, level)
	s.qhead = target_trail_length
}

// pick_unassigned returns the unassigned variable with the highest activity,
// or false if every variable is assigned. Ties go to the lower-numbered
// variable. Assigned variables left in the heap are discarded as they surface.
@(private)
pick_unassigned :: proc(s: ^Solver) -> (Var, bool) {
	for len(s.order.heap) > 0 {
		v := heap_pop_max(&s.order, s.activity)
		if s.values[v] == .Undef {
			return v, true
		}
	}
	return Var(0), false
}


// solve runs conflict-driven clause learning. On .Sat, the satisfying
// assignment is in s.values. Learned clauses go into the solver's arena; the
// formula is left unchanged.
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
		when LOKI_PROFILE {t0 := time.tick_now()}
		confl := propagate(s)
		when LOKI_PROFILE {s.prop_time += time.tick_since(t0)}

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
			when LOKI_PROFILE {t1 := time.tick_now()}
			v, ok := pick_unassigned(s)
			when LOKI_PROFILE {s.pick_time += time.tick_since(t1)}
			if !ok {
				return .Sat
			}
			s.decisions += 1
			new_decision_level(s)
			decision: Literal
			if s.polarity[v] {
				decision = lit_pos(v)
			} else {
				decision = lit_not(lit_pos(v))
			}
			assign(s, decision, NO_REASON)
		case:
			if decision_level(s) == 0 {
				return .Unsat
			}
			when LOKI_PROFILE {t2 := time.tick_now()}
			learnt, backjump_level := analyze(s, confl)
			when LOKI_PROFILE {s.analyze_time += time.tick_since(t2)}
			s.var_inc /= 0.95
			s.conflicts += 1
			conflicts_since_restart += 1
			lbd := compute_lbd(s, learnt[:])
			backtrack(s, backjump_level)
			if len(learnt) == 1 {
				assign(s, learnt[0], NO_REASON)
			} else {
				cr := clause_alloc(s, learnt[:], learned = true, lbd = lbd)
				append(&s.learnts, cr)
				attach(s, cr)
				assign(s, learnt[0], cr)
			}
		}
	}
}

// analyze performs conflict analysis on the conflict clause `confl` using the
// first Unique Implication Point (1UIP) scheme. It walks the implication graph
// backwards from the conflict, resolving the reason clauses of trail literals
// until only one literal from the current decision level remains (the UIP).
//
// Returns the learnt clause and the level to backjump to:
//   clause   - slot 0 holds the negated UIP literal, which the clause asserts
//              after backjumping; slots 1.. hold falsified literals from
//              earlier decision levels, with the highest-level one swapped
//              into slot 1 so the two watched literals are the asserting one
//              and the latest-level one.
//   backjump_level - highest decision level among clause[1:], or 0 for a unit clause.
//
// The clause is then minimized according to s.minimize (see Minimize_Mode), and
// its length before and after minimizing is added to s.max_literals and
// s.tot_literals.
//
// As a side effect, every newly seen variable above decision level 0 is bumped
// (VSIDS), so variables involved in recent conflicts are preferred by
// pick_unassigned.
//
// clause is a view of s.learnt_buffer: valid until the next analyze, and the
// caller must not delete it.
@(private)
analyze :: proc(s: ^Solver, confl: Cref) -> (clause: []Literal, backjump_level: int) {
	learnt := &s.learnt_buffer
	clear(learnt)
	append(learnt, Literal(0)) // reserves slot 0 for the negated UIP

	counter := 0 // seen literals at the current level still to resolve
	p: Literal
	p_set := false
	idx := len(s.trail) - 1
	confl := confl // mutable copy of the parameter
	current := decision_level(s)

	// each time around the loop, look at one clause.
	// first the conflict clause, then the reason clauses.
	for {
		c := clause_lits(s, confl)
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
					append(learnt, q)
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
	// clause propagates lit_not(p)
	learnt[0] = lit_not(p)
	clear(&s.seen_to_clear)
	append(&s.seen_to_clear, ..learnt[1:])
	s.max_literals += len(learnt)
	switch s.minimize {
	case .None:
	// Nothing: keep the clause as it is
	case .Local:
		j := 1
		for i in 1 ..< len(learnt) {
			v := lit_var(learnt[i])
			keep := s.reasons[v] == NO_REASON
			if !keep {
				c := clause_lits(s, s.reasons[v])
				for k in 1 ..< len(c) {
					u := lit_var(c[k])
					if !s.seen[u] && s.levels[u] > 0 {
						keep = true
						break
					}
				}
			}
			if keep {
				learnt[j] = learnt[i]
				j += 1
			}
		}
		resize(learnt, j)
	case .Recursive:
		levels: u32
		for i in 1 ..< len(learnt) {
			levels |= abstract_level(s, lit_var(learnt[i]))
		}
		j := 1
		for i in 1 ..< len(learnt) {
			v := lit_var(learnt[i])
			keep := s.reasons[v] == NO_REASON || !lit_redundant(s, learnt[i], levels)
			if keep {
				learnt[j] = learnt[i]
				j += 1
			}
		}
		resize(learnt, j)
	}


	s.tot_literals += len(learnt)

	// backjump level = highest level among learnt[1:], move that literal into slot 1
	max_i := 1
	for i in 1 ..< len(learnt) {
		lvl := s.levels[lit_var(learnt[i])]
		if lvl > backjump_level {
			backjump_level = lvl
			max_i = i
		}
	}
	if len(learnt) > 1 {
		learnt[1], learnt[max_i] = learnt[max_i], learnt[1]
	}

	// clear seen for older level literals. current level literals were already cleared
	for l in s.seen_to_clear {
		s.seen[lit_var(l)] = false
	}

	return learnt[:], backjump_level
}

// bump adds var_inc to activity[v]; if the result exceeds 1e100, it rescales
// all activities and var_inc by 1e-100 to avoid overflow.
@(private)
bump :: proc(s: ^Solver, v: Var) {
	s.activity[v] += s.var_inc
	heap_increase(&s.order, s.activity, v)
	if s.activity[v] > 1e100 {
		// rescale activity and var_inc by 1e-100
		for &a in s.activity {
			a *= 1e-100
		}
		s.var_inc *= 1e-100
	}
}

// compute_lbd returns the number of distinct decision levels among lits.
@(private)
compute_lbd :: proc(s: ^Solver, lits: []Literal) -> int {
	lbd := 0
	for l in lits {
		v := lit_var(l)
		lvl := s.levels[v]

		if !s.lbd_levels[lvl] {
			s.lbd_levels[lvl] = true
			lbd += 1
		}
	}

	for l in lits {
		v := lit_var(l)
		lvl := s.levels[v]
		s.lbd_levels[lvl] = false
	}

	return lbd
}

// locked reports whether clause cr is the reason for a literal that is assigned
// now. Deleting a locked clause would leave analyze following reasons[v] to a
// clause that no longer exists. A clause only ever implies its c[0], and
// backtrack leaves stale reasons behind, so both halves of the test are needed.
@(private)
locked :: proc(s: ^Solver, cr: Cref) -> bool {
	c := clause_lits(s, cr)

	return lit_value(s, c[0]) == .True && s.reasons[lit_var(c[0])] == cr
}

// collect_victims returns the Crefs of the learned clauses to delete: of those
// in s.learnts with LBD > 2 (glue clauses are kept) that are not locked, the
// worse half by LBD. The caller owns the returned array and frees it with delete.
@(private)
collect_victims :: proc(s: ^Solver) -> [dynamic]Cref {
	candidates: [dynamic]Victim_Candidate
	defer delete(candidates)

	result: [dynamic]Cref

	for cr in s.learnts {
		lbd := clause_lbd(s, cr)
		// learned clauses with LBD > 2 that aren't locked, each paired with its LBD
		if lbd > 2 && !locked(s, cr) {
			append(&candidates, Victim_Candidate{cr = cr, lbd = lbd})
		}
	}

	// sort it worst-first (highest LBD first)
	slice.sort_by(candidates[:], proc(a, b: Victim_Candidate) -> bool {
		return a.lbd > b.lbd
	})

	// declare victims
	// loop over first half of candidates: append each one's cr to victims
	for k in 0 ..< len(candidates) / 2 {
		append(&result, candidates[k].cr)
	}

	return result
}

@(private)
reduce_db :: proc(s: ^Solver) {
	victims := collect_victims(s)
	defer delete(victims)
	for cr in victims {
		s.arena[cr] |= DELETED_BIT
		s.wasted += HEADER_WORDS + len(clause_lits(s, cr))
	}

	// Drop watches of deleted clauses.
	for &ws in s.watches {
		j := 0
		for w in ws {
			if !clause_deleted(s, w.cref) {
				ws[j] = w
				j += 1
			}
		}
		resize(&ws, j)
	}

	// Drop deleted clauses from learnts, so the next reduce_db never picks them again.
	j := 0
	for cr in s.learnts {
		if !clause_deleted(s, cr) {
			s.learnts[j] = cr
			j += 1
		}
	}
	resize(&s.learnts, j)

	s.clauses_deleted += len(victims)
	s.reductions += 1
	if f64(s.wasted) > COMPACT_FRAC * f64(len(s.arena)) {
		arena_compact(s)
	}
}

// arena_compact copies the live clauses, in order, into a new arena, and
// moves every Cref the solver holds (watches, reasons of assigned variables,
// learnts) to its clause's new position. reduce_db calls it once wasted words
// pass COMPACT_FRAC of the arena. Any slice from clause_lits is invalid
// afterwards, so it must not run while propagate or analyze holds one.
@(private)
arena_compact :: proc(s: ^Solver) {
	// Part 1 - copy
	to := make([dynamic]u32, 0, len(s.arena) - s.wasted, s.allocator)
	pos := 0
	for pos < len(s.arena) {
		header := s.arena[pos]
		words := HEADER_WORDS + int(header & SIZE_MASK)

		if header & DELETED_BIT == 0 {
			new_cr := u32(len(to))
			append(&to, ..s.arena[pos:pos + words])
			s.arena[pos] = header | RELOCATED_BIT
			s.arena[pos + 1] = new_cr
		}

		pos += words
	}

	// Part 2 - relocate
	relocate :: proc(old: []u32, cr: Cref) -> Cref {
		assert(old[cr] & RELOCATED_BIT != 0, "a Cref to a deleted clause")
		return Cref(old[int(cr) + 1])
	}
	for &ws in s.watches {
		for &w in ws {
			w.cref = relocate(s.arena[:], w.cref)
		}
	}

	for l in s.trail {
		v := lit_var(l)
		if s.reasons[v] != NO_REASON {
			s.reasons[v] = relocate(s.arena[:], s.reasons[v])
		}
	}

	for &cr in s.learnts {
		cr = relocate(s.arena[:], cr)
	}
	// Part 3 - swap
	delete(s.arena)
	s.arena = to
	s.wasted = 0
}

@(private)
luby :: proc(i: int) -> int {
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

@(private)
abstract_level :: proc(s: ^Solver, v: Var) -> u32 {
	return u32(1) << uint(s.levels[v] & 31)
}

@(private)
lit_redundant :: proc(s: ^Solver, p: Literal, abstract_levels: u32) -> bool {
	clear(&s.analyze_stack)
	append(&s.analyze_stack, p)

	top := len(s.seen_to_clear)
	for len(s.analyze_stack) > 0 {
		q := pop(&s.analyze_stack)
		c := clause_lits(s, s.reasons[lit_var(q)])
		for l in c[1:] {
			v := lit_var(l)
			if s.seen[v] || s.levels[v] == 0 {
				continue
			}
			if s.reasons[v] != NO_REASON && abstract_level(s, v) & abstract_levels != 0 {
				s.seen[v] = true
				append(&s.analyze_stack, l)
				append(&s.seen_to_clear, l)
			} else {
				for i in top ..< len(s.seen_to_clear) {
					s.seen[lit_var(s.seen_to_clear[i])] = false
				}
				resize(&s.seen_to_clear, top)
				return false
			}
		}
	}

	return true
}

// learned_lbd_stats returns the average LBD of the learned clauses the solver
// still holds, and how many of them are glue clauses (LBD <= 2). With no
// learned clauses, the average is 0.
learned_lbd_stats :: proc(s: ^Solver) -> (avg_lbd: f64, glue: int) {
	sum := 0
	for cr in s.learnts {
		lbd := clause_lbd(s, cr)
		sum += lbd
		if lbd <= 2 {
			glue += 1
		}
	}

	if len(s.learnts) > 0 {
		avg_lbd = f64(sum) / f64(len(s.learnts))
	}
	return avg_lbd, glue
}
