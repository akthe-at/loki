#+private
package loki

import "core:strings"
import "core:testing"

// Tests for the solver's private procs. They live in package loki so they can
// call backtrack, propagate and analyze directly. Run with `odin test .`.

// L turns a DIMACS literal into a Literal, to keep the tests readable.
@(private = "file")
L :: proc(x: int) -> Literal {
	return lit_from_dimacs(x)
}

// fixture parses text into a heap-allocated formula (the solver keeps a
// pointer to it, so it must not live in a stack frame that returns) and
// builds a solver for it. Free both with teardown.
@(private = "file")
fixture :: proc(t: ^testing.T, text: string, loc := #caller_location) -> (f: ^Formula, s: Solver) {
	f = new(Formula)
	err: Parse_Error
	f^, err = parse_dimacs_string(text)
	testing.expect_value(t, err, Parse_Error.None, loc = loc)
	s = solver_init(f)
	return
}

@(private = "file")
teardown :: proc(f: ^Formula, s: ^Solver) {
	solver_destroy(s)
	formula_destroy(f)
	free(f)
}

// decide opens a new decision level and assigns l there, as solve does.
@(private = "file")
decide :: proc(s: ^Solver, l: Literal) {
	new_decision_level(s)
	assign(s, l, NO_REASON)
}

// backtrack had a bug in Lesson 10: it saved polarity[level] instead of
// polarity[lit_var(l)]. This test catches that, and checks everything else
// backtrack is responsible for.
@(test)
backtrack_undoes_levels_and_saves_phases :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 4 0\n")
	defer teardown(f, &s)

	decide(&s, L(1)) // level 1: x1
	decide(&s, L(-2)) // level 2: ¬x2, then x3 as if implied
	assign(&s, L(3), NO_REASON)
	decide(&s, L(-4)) // level 3: ¬x4
	s.qhead = len(s.trail)
	// In a real solve the decided variables were popped from the heap by
	// pick_unassigned. Empty it, so backtrack has to put them back.
	for len(s.order.heap) > 0 {
		heap_pop_max(&s.order, s.activity)
	}

	backtrack(&s, 1)

	testing.expect_value(t, decision_level(&s), 1)
	testing.expect_value(t, len(s.trail), 1)
	testing.expect_value(t, s.trail[0], L(1))
	testing.expect_value(t, s.qhead, 1)
	testing.expect_value(t, s.values[0], LBool.True)
	for v in 1 ..< 4 {
		testing.expectf(t, s.values[v] == .Undef, "var %d still assigned after backtrack", v)
		// invariant from Lesson 11b: every unassigned variable is in the heap
		testing.expectf(t, heap_contains(&s.order, Var(v)), "unassigned var %d missing from heap", v)
	}
	// saved phases: the sign each variable had when it was unassigned
	testing.expect_value(t, s.polarity[1], false) // was ¬x2
	testing.expect_value(t, s.polarity[2], true) // was x3
	testing.expect_value(t, s.polarity[3], false) // was ¬x4
	testing.expect_value(t, s.polarity[0], true) // x1 still assigned: untouched

	// backtracking to the current level (or above) changes nothing
	backtrack(&s, 1)
	backtrack(&s, 5)
	testing.expect_value(t, len(s.trail), 1)
}

@(test)
backtrack_without_phase_saving :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 2 0\n")
	defer teardown(f, &s)
	s.phase_saving = false

	decide(&s, L(-1))
	decide(&s, L(-2))
	backtrack(&s, 0)

	// solver_init starts every phase as true, and nothing may change it
	testing.expect_value(t, s.polarity[0], true)
	testing.expect_value(t, s.polarity[1], true)
}

// A chain of implications: x1 forces x2 forces x3, each with its reason clause.
@(test)
propagate_unit_chain :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 3 2\n-1 2 0\n-2 3 0\n")
	defer teardown(f, &s)

	decide(&s, L(1))
	confl := propagate(&s)

	testing.expect_value(t, confl, NO_REASON)
	testing.expect_value(t, len(s.trail), 3)
	testing.expect_value(t, s.values[1], LBool.True)
	testing.expect_value(t, s.values[2], LBool.True)
	testing.expect_value(t, s.reasons[1], 0) // x2 because of clause 0
	testing.expect_value(t, s.reasons[2], 1) // x3 because of clause 1
	testing.expect_value(t, s.levels[1], 1)
	testing.expect_value(t, s.levels[2], 1)
}

// x1 forces both x2 and ¬x2: propagate must report a conflict clause that is
// entirely false.
@(test)
propagate_reports_conflict :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 2 2\n-1 2 0\n-1 -2 0\n")
	defer teardown(f, &s)

	decide(&s, L(1))
	confl := propagate(&s)

	if !testing.expect(t, confl != NO_REASON) {
		return
	}
	for l in f.clauses[confl] {
		testing.expectf(t, lit_value(&s, l) == .False, "conflict clause %d has non-false literal %d", confl, l)
	}
}

// With a replacement available, the watch moves and nothing is assigned.
@(test)
propagate_moves_watch :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 3 1\n1 2 3 0\n")
	defer teardown(f, &s)

	decide(&s, L(-1)) // falsifies watched literal x1
	confl := propagate(&s)

	testing.expect_value(t, confl, NO_REASON)
	testing.expect_value(t, len(s.trail), 1) // x2 and x3 stay unassigned
	testing.expect_value(t, len(s.watches[L(1)]), 0)
	testing.expect_value(t, len(s.watches[L(3)]), 1)
}

// A conflict worked out by hand. Level 1 decides x4. Level 2 decides x1, which
// forces x2 (clause 0) and x3 (clause 1, since x4 is true), and clause 2 forbids
// x2 and x3 together. Resolving gives ¬x1 ∨ ¬x4. The first UIP is x1 (both x2
// and x3 follow from it), so the backjump goes to level 1, where the clause
// will force ¬x1.
@(test)
analyze_hand_example :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 4 3\n-1 2 0\n-1 -4 3 0\n-2 -3 0\n")
	defer teardown(f, &s)

	decide(&s, L(4))
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(1))
	confl := propagate(&s)
	if !testing.expect(t, confl != NO_REASON) {
		return
	}

	learnt, bj_level := analyze(&s, confl)
	defer delete(learnt)

	testing.expect_value(t, bj_level, 1)
	if testing.expect_value(t, len(learnt), 2) {
		testing.expect_value(t, learnt[0], L(-1)) // asserting literal first
		testing.expect_value(t, learnt[1], L(-4)) // highest-level other literal second
	}
	// analyze must leave seen[] clean for the next conflict
	for v in 0 ..< 4 {
		testing.expectf(t, !s.seen[v], "seen[%d] left set after analyze", v)
	}
	// every variable in the conflict was bumped
	for v in 0 ..< 4 {
		testing.expectf(t, s.activity[v] > 0, "var %d not bumped", v)
	}
	// LBD: levels 2 and 1
	testing.expect_value(t, compute_lbd(&s, learnt[:]), 2)
}

// pick_unassigned (the heap) must choose exactly what the old linear scan
// chose: highest activity, lower variable on ties. Lesson 11b relies on this.
@(test)
pick_matches_linear_scan :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 40 0\n")
	defer teardown(f, &s)

	// deterministic pseudo-random bumps, with plenty of ties
	seed: u32 = 12345
	for _ in 0 ..< 200 {
		seed = seed * 1664525 + 1013904223
		bump(&s, Var((seed >> 8) % 40))
	}

	for round in 0 ..< 40 {
		want, want_ok := scan_unassigned(&s)
		got, ok := pick_unassigned(&s)
		testing.expect_value(t, ok, want_ok)
		if !testing.expectf(t, got == want, "round %d: heap picked %d, scan picks %d", round, got, want) {
			return
		}
		decide(&s, lit_pos(got))
	}
	_, ok := pick_unassigned(&s)
	testing.expect(t, !ok) // everything assigned
}

// scan_unassigned is the Lesson 7-10 pick_unassigned, kept as a reference.
@(private = "file")
scan_unassigned :: proc(s: ^Solver) -> (Var, bool) {
	best := -1
	for v, i in s.values {
		if v == .Undef && (best == -1 || s.activity[i] > s.activity[best]) {
			best = i
		}
	}
	return Var(max(best, 0)), best != -1
}

// collect_victims on clauses whose LBDs are set by hand. Deletable means:
// learned, LBD > 2 (glue clauses are kept), not already deleted, not locked.
// Of those, the worst half by LBD goes.
@(test)
collect_victims_rules :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 16 8\n1 2 0\n3 4 0\n5 6 0\n7 8 0\n9 10 0\n11 12 0\n13 14 0\n15 16 0\n")
	defer teardown(f, &s)

	s.infos[0] = {learned = false, lbd = 10} // original clause: never deleted
	s.infos[1] = {learned = true, lbd = 2} // glue: kept
	s.infos[2] = {learned = true, lbd = 3}
	s.infos[3] = {learned = true, lbd = 4}
	s.infos[4] = {learned = true, lbd = 5}
	s.infos[5] = {learned = true, lbd = 6}
	s.infos[6] = {learned = true, lbd = 9} // locked below: kept
	s.infos[7] = {learned = true, lbd = 7}
	assign(&s, f.clauses[6][0], 6) // clause 6 is now the reason for x13

	// deletable: clauses 2, 3, 4, 5, 7. Half of 5 is 2: the worst two by LBD.
	victims := collect_victims(&s)
	defer delete(victims)
	if testing.expect_value(t, len(victims), 2) {
		testing.expect_value(t, victims[0], 7) // lbd 7
		testing.expect_value(t, victims[1], 5) // lbd 6
	}
}

// The asserts removed in Lesson 11b, as one test. A pigeonhole formula with a
// tiny reduction schedule forces many learned clauses and several reduce_db
// calls, then every invariant is checked.
@(test)
invariants_after_solve_with_reductions :: proc(t: ^testing.T) {
	text := pigeonhole(7, 6)
	defer delete(text)
	f, s := fixture(t, text)
	defer teardown(f, &s)
	s.reduce_first = 50
	s.reduce_inc = 10

	testing.expect_value(t, solve(&s), Result.Unsat)
	testing.expect(t, s.reductions > 0)
	testing.expect(t, s.deleted > 0)

	// infos and clauses stay the same length
	testing.expect_value(t, len(s.infos), len(f.clauses))

	// no watch list points at a deleted clause
	for ws, lit in s.watches {
		for ci in ws {
			testing.expectf(t, !s.infos[ci].deleted, "watches[%d] holds deleted clause %d", lit, ci)
		}
	}

	for info, ci in s.infos {
		c := f.clauses[ci]
		if info.deleted {
			// only learned, non-glue clauses are ever deleted
			testing.expectf(t, info.learned && info.lbd > 2, "clause %d deleted but learned=%v lbd=%d", ci, info.learned, info.lbd)
			testing.expectf(t, c == nil, "deleted clause %d not freed", ci)
		} else if info.learned {
			// LBD counts distinct levels: at least 1, at most one per literal
			testing.expectf(t, 1 <= info.lbd && info.lbd <= len(c), "clause %d: lbd %d, %d literals", ci, info.lbd, len(c))
		}
	}

	// collect_victims picks only deletable clauses
	victims := collect_victims(&s)
	defer delete(victims)
	for ci in victims {
		info := s.infos[ci]
		testing.expectf(
			t,
			info.learned && !info.deleted && info.lbd > 2 && !locked(&s, ci),
			"victim %d is not deletable",
			ci,
		)
	}
}

// pigeonhole writes PHP(pigeons, holes) as DIMACS text; the caller deletes it.
@(private = "file")
pigeonhole :: proc(pigeons, holes: int) -> string {
	// strings.write_int rather than printf-style formatting: root test files are
	// compiled into the library package, which has no formatting import.
	b := strings.builder_make()
	strings.write_string(&b, "p cnf ")
	strings.write_int(&b, pigeons * holes)
	strings.write_string(&b, " ")
	strings.write_int(&b, pigeons + holes * pigeons * (pigeons - 1) / 2)
	strings.write_string(&b, "\n")
	for p in 0 ..< pigeons {
		for h in 0 ..< holes {
			strings.write_int(&b, p * holes + h + 1)
			strings.write_string(&b, " ")
		}
		strings.write_string(&b, "0\n")
	}
	for h in 0 ..< holes {
		for p1 in 0 ..< pigeons {
			for p2 in p1 + 1 ..< pigeons {
				strings.write_int(&b, -(p1 * holes + h + 1))
				strings.write_string(&b, " ")
				strings.write_int(&b, -(p2 * holes + h + 1))
				strings.write_string(&b, " 0\n")
			}
		}
	}
	return strings.to_string(b)
}
