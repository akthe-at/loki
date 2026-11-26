#+private
package loki

import "core:slice"
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
	s = solver_make(f)
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

// backtrack once had a bug: it saved polarity[level] instead of
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
		//  every unassigned variable is in the heap
		testing.expectf(
			t,
			heap_contains(&s.order, Var(v)),
			"unassigned var %d missing from heap",
			v,
		)
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

	// solver_make starts every phase as true, and nothing may change it
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
		testing.expectf(
			t,
			lit_value(&s, l) == .False,
			"conflict clause %d has non-false literal %d",
			confl,
			l,
		)
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

	learnt, backjump_level := analyze(&s, confl)
	defer delete(learnt)

	testing.expect_value(t, backjump_level, 1)
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
// chose: highest activity, lower variable on ties.
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
		if !testing.expectf(
			t,
			got == want,
			"round %d: heap picked %d, scan picks %d",
			round,
			got,
			want,
		) {
			return
		}
		decide(&s, lit_pos(got))
	}
	_, ok := pick_unassigned(&s)
	testing.expect(t, !ok) // everything assigned
}

// scan_unassigned is the earlier pick_unassigned, kept as a reference.
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
	f, s := fixture(
		t,
		"p cnf 16 8\n1 2 0\n3 4 0\n5 6 0\n7 8 0\n9 10 0\n11 12 0\n13 14 0\n15 16 0\n",
	)
	defer teardown(f, &s)

	s.infos[0] = {
		learned = false,
		lbd     = 10,
	} // original clause: never deleted
	s.infos[1] = {
		learned = true,
		lbd     = 2,
	} // glue: kept
	s.infos[2] = {
		learned = true,
		lbd     = 3,
	}
	s.infos[3] = {
		learned = true,
		lbd     = 4,
	}
	s.infos[4] = {
		learned = true,
		lbd     = 5,
	}
	s.infos[5] = {
		learned = true,
		lbd     = 6,
	}
	s.infos[6] = {
		learned = true,
		lbd     = 9,
	} // locked below: kept
	s.infos[7] = {
		learned = true,
		lbd     = 7,
	}
	assign(&s, f.clauses[6][0], 6) // clause 6 is now the reason for x13

	// deletable: clauses 2, 3, 4, 5, 7. Half of 5 is 2: the worst two by LBD.
	victims := collect_victims(&s)
	defer delete(victims)
	if testing.expect_value(t, len(victims), 2) {
		testing.expect_value(t, victims[0], 7) // lbd 7
		testing.expect_value(t, victims[1], 5) // lbd 6
	}
}

// The invariant checks that used to be asserts inside the solver, as one test.
// A pigeonhole formula with a tiny reduction schedule forces many learned
// clauses and several reduce_db calls, then every invariant is checked.
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
	testing.expect(t, s.clauses_deleted > 0)

	// infos and clauses stay the same length
	testing.expect_value(t, len(s.infos), len(f.clauses))

	// every watch entry: live clause, filed under one of its two watched
	// literals, blocker taken from the clause, binary flag matching its length
	for ws, lit in s.watches {
		for w in ws {
			if !testing.expectf(
				t,
				!s.infos[w.ci].deleted,
				"watches[%d] holds deleted clause %d",
				lit,
				w.ci,
			) {
				continue
			}
			c := f.clauses[w.ci]
			testing.expectf(
				t,
				c[0] == Literal(lit) || c[1] == Literal(lit),
				"watches[%d] holds clause %d, which doesn't watch it",
				lit,
				w.ci,
			)
			testing.expectf(
				t,
				slice.contains(c, w.blocker),
				"watches[%d]: clause %d's blocker %d is not in the clause",
				lit,
				w.ci,
				w.blocker,
			)
			// an entry filed under x is visited only when x is false, so x
			// itself could never let it skip
			testing.expectf(
				t,
				w.blocker != Literal(lit),
				"watches[%d]: clause %d uses its own literal as blocker",
				lit,
				w.ci,
			)
			testing.expectf(
				t,
				w.binary == (len(c) == 2),
				"watches[%d]: clause %d has binary=%v but %d literals",
				lit,
				w.ci,
				w.binary,
				len(c),
			)
		}
	}

	for info, ci in s.infos {
		c := f.clauses[ci]
		if info.deleted {
			// only learned, non-glue clauses are ever deleted
			testing.expectf(
				t,
				info.learned && info.lbd > 2,
				"clause %d deleted but learned=%v lbd=%d",
				ci,
				info.learned,
				info.lbd,
			)
			testing.expectf(t, c == nil, "deleted clause %d not freed", ci)
		} else if info.learned {
			// LBD counts distinct levels: at least 1, at most one per literal
			testing.expectf(
				t,
				1 <= info.lbd && info.lbd <= len(c),
				"clause %d: lbd %d, %d literals",
				ci,
				info.lbd,
				len(c),
			)
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


// A binary clause whose blocker is true is skipped without being loaded, so
// nothing is assigned and its literal order is untouched (a load would have
// normalised it to [2, 1]).
@(test)
propagate_binary_blocker_true :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 2 1\n1 2 0\n")
	defer teardown(f, &s)

	decide(&s, L(2))
	decide(&s, L(-1)) // visits watches[x1]; its blocker x2 is true
	testing.expect_value(t, propagate(&s), NO_REASON)

	testing.expect_value(t, len(s.trail), 2)
	testing.expect_value(t, f.clauses[0][0], L(1))
	testing.expect_value(t, f.clauses[0][1], L(2))
}

// A binary clause whose blocker is unassigned implies it, and the reason
// clause has the implied literal in slot 0 (analyze skips c[0], locked
// tests it).
@(test)
propagate_binary_blocker_unassigned :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 2 1\n1 2 0\n")
	defer teardown(f, &s)

	decide(&s, L(-1))
	testing.expect_value(t, propagate(&s), NO_REASON)

	testing.expect_value(t, s.values[1], LBool.True)
	testing.expect_value(t, s.reasons[1], 0)
	testing.expect_value(t, f.clauses[0][0], L(2))
	testing.expect_value(t, f.clauses[0][1], L(1))
	testing.expect(t, locked(&s, 0))
}

// A binary clause whose blocker is false is a conflict.
@(test)
propagate_binary_blocker_false :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 2 1\n1 2 0\n")
	defer teardown(f, &s)

	// assign both without propagating in between, so the blocker is already
	// false when watches[x1] is visited
	decide(&s, L(-2))
	decide(&s, L(-1))
	s.qhead = 1 // x2's own watch list has been handled; x1's has not
	testing.expect_value(t, propagate(&s), 0)
}

// The blocker of a long clause goes stale when the other watch moves. A true
// stale blocker still skips the clause: the watch stays where it is. (Without
// the blocker, the visit would load the clause and move the watch to x2.)
@(test)
propagate_stale_blocker_true_skips :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 4 1\n1 2 3 4 0\n")
	defer teardown(f, &s)

	// ¬x2 moves the x2 watch to x3. watches[x1] keeps blocker x2: now stale.
	decide(&s, L(-2))
	testing.expect_value(t, propagate(&s), NO_REASON)
	testing.expect_value(t, len(s.watches[L(3)]), 1)
	backtrack(&s, 0)

	decide(&s, L(2)) // the stale blocker is true now
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(-1))
	testing.expect_value(t, propagate(&s), NO_REASON)

	testing.expect_value(t, len(s.watches[L(1)]), 1)
	testing.expect_value(t, len(s.watches[L(2)]), 0)
	testing.expect_value(t, len(s.watches[L(3)]), 1)
}

// A long clause whose blocker is false is loaded; when c[0] turns out to be
// true, the clause is skipped and the entry's blocker becomes c[0].
@(test)
propagate_refreshes_blocker_when_c0_true :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 4 1\n1 2 3 4 0\n")
	defer teardown(f, &s)

	decide(&s, L(-2)) // x2 watch moves to x3; watches[x1] keeps blocker x2
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(3))
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(-1)) // blocker x2 is false: load; c[0] = x3 is true
	testing.expect_value(t, propagate(&s), NO_REASON)

	testing.expect_value(t, len(s.trail), 3) // nothing implied
	if testing.expect_value(t, len(s.watches[L(1)]), 1) {
		testing.expect_value(t, s.watches[L(1)][0].blocker, L(3))
	}
}

// A long clause that becomes unit through an entry with a stale blocker
// assigns c[0], and the entry's blocker becomes c[0].
@(test)
propagate_refreshes_blocker_when_unit :: proc(t: ^testing.T) {
	f, s := fixture(t, "p cnf 4 1\n1 2 3 4 0\n")
	defer teardown(f, &s)

	decide(&s, L(-2)) // x2 watch moves to x3; watches[x1] keeps blocker x2
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(-4))
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(-1)) // only x3 is left
	testing.expect_value(t, propagate(&s), NO_REASON)

	testing.expect_value(t, s.values[2], LBool.True)
	testing.expect_value(t, s.reasons[2], 0)
	testing.expect_value(t, f.clauses[0][0], L(3))
	if testing.expect_value(t, len(s.watches[L(1)]), 1) {
		testing.expect_value(t, s.watches[L(1)][0].blocker, L(3))
	}
}

// propagation_complete reports whether propagate reached a fixpoint: every
// clause is satisfied or still has two literals that aren't false. A clause
// with one non-false literal is a missed unit; with none, a missed conflict.
@(private = "file")
propagation_complete :: proc(s: ^Solver) -> bool {
	for c, ci in s.formula.clauses {
		if s.infos[ci].deleted || len(c) < 2 {
			continue
		}
		open := 0
		for l in c {
			v := lit_value(s, l)
			if v == .True {
				open = 2
				break
			}
			if v == .Undef {
				open += 1
			}
		}
		if open < 2 {
			return false
		}
	}
	return true
}

// Random decisions and backtracks on random 3-SAT and pigeonhole formulas.
// After every propagate that finds no conflict, nothing may be left to
// propagate. This is what catches a blocker that isn't in its clause: the
// answers stay right, because the clause's other watch still finds conflicts
// late, but units get missed.
@(test)
propagate_reaches_fixpoint :: proc(t: ^testing.T) {
	texts := [?]string {
		random_3sat(60, 255, 1),
		random_3sat(60, 255, 2),
		random_3sat(100, 420, 3),
		pigeonhole(6, 5),
	}
	defer for text in texts {
		delete(text)
	}

	for text, n in texts {
		f, s := fixture(t, text)
		defer teardown(f, &s)
		rng := u64(n + 1)

		for _ in 0 ..< 3000 {
			if propagate(&s) != NO_REASON {
				if decision_level(&s) == 0 {
					break
				}
				backtrack(&s, decision_level(&s) - 1)
				continue
			}
			if !testing.expectf(
				t,
				propagation_complete(&s),
				"formula %d: missed propagation at level %d",
				n,
				decision_level(&s),
			) {
				break
			}
			// pick a random unassigned variable and a random sign
			nv := int(f.num_vars)
			start := int(next_random(&rng) % u64(nv))
			v := -1
			for k in 0 ..< nv {
				if s.values[(start + k) % nv] == .Undef {
					v = (start + k) % nv
					break
				}
			}
			if v < 0 {
				backtrack(&s, 0) // everything assigned: start over
				continue
			}
			l := lit_pos(Var(v))
			if next_random(&rng) % 2 == 0 {
				l = lit_not(l)
			}
			decide(&s, l)
		}
	}
}

// next_random is a small xorshift generator, so the test is the same every run.
@(private = "file")
next_random :: proc(state: ^u64) -> u64 {
	x := state^ * 0x9E3779B97F4A7C15 + 1
	x ~= x >> 31
	x ~= x << 17
	x ~= x >> 23
	state^ = x
	return x
}

// random_3sat writes a random 3-SAT formula as DIMACS text; the caller deletes it.
@(private = "file")
random_3sat :: proc(num_vars, num_clauses: int, seed: u64) -> string {
	rng := seed
	b := strings.builder_make()
	strings.write_string(&b, "p cnf ")
	strings.write_int(&b, num_vars)
	strings.write_string(&b, " ")
	strings.write_int(&b, num_clauses)
	strings.write_string(&b, "\n")
	for _ in 0 ..< num_clauses {
		vars: [3]int
		for k in 0 ..< 3 {
			for {
				vars[k] = int(next_random(&rng) % u64(num_vars)) + 1
				if k == 0 || (vars[k] != vars[0] && (k == 1 || vars[k] != vars[1])) {
					break
				}
			}
			x := vars[k]
			if next_random(&rng) % 2 == 0 {
				x = -x
			}
			strings.write_int(&b, x)
			strings.write_string(&b, " ")
		}
		strings.write_string(&b, "0\n")
	}
	return strings.to_string(b)
}


// With a=1 b=2 c=3 d=4 u=5 x=6. Deciding a, then u, gives one conflict whose 1UIP clause is
// (¬u ∨ ¬a ∨ ¬d ∨ ¬c). d's reason (d ∨ ¬a) is covered by the clause, so local
// minimization drops ¬d. c is forced by b, which is forced by a, so only
// recursive minimization drops ¬c as well.
@(private = "file")
MINIMIZE_EXAMPLE :: "p cnf 6 5\n-1 2 0\n-2 3 0\n-1 4 0\n-5 -3 6 0\n-5 -1 -4 -6 0\n"

// The same example, except d's reason also needs x7, a level-0 fact:
// (d ∨ ¬a ∨ ¬x7). A false level-0 literal counts as covered, so ¬d is still
// redundant in both modes.
@(private = "file")
MINIMIZE_LEVEL0_EXAMPLE :: "p cnf 7 6\n7 0\n-1 2 0\n-2 3 0\n-1 -7 4 0\n-5 -3 6 0\n-5 -1 -4 -6 0\n"

@(private = "file")
Minimize_Case :: struct {
	text: string,
	mode: Minimize_Mode,
	want: []int, // DIMACS literals expected in learnt[1:], in any order
}

// Each case decides a (=1) then u (=5), analyzes the conflict, and checks the
// learned clause, the literal stats and the seen cleanup.
@(test)
minimize_modes_on_example :: proc(t: ^testing.T) {
	cases := [?]Minimize_Case {
		{MINIMIZE_EXAMPLE, .None, {-1, -4, -3}},
		{MINIMIZE_EXAMPLE, .Local, {-1, -3}},
		{MINIMIZE_EXAMPLE, .Recursive, {-1}},
		{MINIMIZE_LEVEL0_EXAMPLE, .Local, {-1, -3}},
		{MINIMIZE_LEVEL0_EXAMPLE, .Recursive, {-1}},
	}
	for tc, n in cases {
		f, s := fixture(t, tc.text)
		defer teardown(f, &s)
		s.minimize = tc.mode

		// the level-0 unit, if there is one, as solve would assign it
		for c in f.clauses {
			if len(c) == 1 {
				assign(&s, c[0], NO_REASON)
			}
		}
		testing.expect_value(t, propagate(&s), NO_REASON)
		decide(&s, L(1))
		testing.expect_value(t, propagate(&s), NO_REASON)
		decide(&s, L(5))
		confl := propagate(&s)
		if !testing.expectf(t, confl != NO_REASON, "case %d: no conflict", n) {
			continue
		}

		learnt, backjump_level := analyze(&s, confl)
		defer delete(learnt)

		testing.expectf(t, learnt[0] == L(-5), "case %d: slot 0 is %d, want ¬u", n, learnt[0])
		testing.expectf(
			t,
			backjump_level == 1,
			"case %d: backjump level %d, want 1",
			n,
			backjump_level,
		)
		if testing.expectf(
			t,
			len(learnt) == 1 + len(tc.want),
			"case %d (%v): %d literals, want %d",
			n,
			tc.mode,
			len(learnt),
			1 + len(tc.want),
		) {
			for x in tc.want {
				testing.expectf(
					t,
					slice.contains(learnt[1:], L(x)),
					"case %d (%v): %d missing",
					n,
					tc.mode,
					x,
				)
			}
		}
		// the stats count the 1UIP clause before minimizing, and what's left after
		testing.expectf(
			t,
			s.max_literals == 4,
			"case %d: max_literals %d, want 4",
			n,
			s.max_literals,
		)
		testing.expectf(
			t,
			s.tot_literals == len(learnt),
			"case %d: tot_literals %d, want %d",
			n,
			s.tot_literals,
			len(learnt),
		)
		// every mark minimization made must be gone for the next conflict
		for v in 0 ..< int(f.num_vars) {
			testing.expectf(t, !s.seen[v], "case %d (%v): seen[%d] left set", n, tc.mode, v)
		}
	}
}

// Nothing to remove: analyze_hand_example's clause is (¬x1 ∨ ¬x4), and x4 is a
// decision, so every mode must return it unchanged.
@(test)
minimize_keeps_decisions :: proc(t: ^testing.T) {
	for mode in Minimize_Mode {
		f, s := fixture(t, "p cnf 4 3\n-1 2 0\n-1 -4 3 0\n-2 -3 0\n")
		defer teardown(f, &s)
		s.minimize = mode

		decide(&s, L(4))
		testing.expect_value(t, propagate(&s), NO_REASON)
		decide(&s, L(1))
		confl := propagate(&s)
		if !testing.expect(t, confl != NO_REASON) {
			continue
		}
		learnt, _ := analyze(&s, confl)
		defer delete(learnt)

		testing.expectf(t, len(learnt) == 2, "%v: %d literals, want 2", mode, len(learnt))
		testing.expectf(
			t,
			s.max_literals == s.tot_literals,
			"%v: %d -> %d literals",
			mode,
			s.max_literals,
			s.tot_literals,
		)
		for v in 0 ..< 4 {
			testing.expectf(t, !s.seen[v], "%v: seen[%d] left set", mode, v)
		}
	}
}

// rup_implied reports whether clause c follows from clauses plus the unit
// literals by unit propagation alone: assume every literal of c is false, then
// propagate to a fixpoint and look for a clause with every literal false. It is
// deliberately simple and independent of propagate, so it can check it.
@(private = "file")
rup_implied :: proc(num_vars: int, clauses: []Clause, units: []Literal, c: Clause) -> bool {
	values := make([]LBool, num_vars)
	defer delete(values)
	value :: proc(values: []LBool, l: Literal) -> LBool {
		v := values[lit_var(l)]
		if v == .Undef || !lit_is_neg(l) {
			return v
		}
		return .False if v == .True else .True
	}
	set :: proc(values: []LBool, l: Literal) -> (conflict: bool) {
		switch value(values, l) {
		case .True:
		case .False:
			return true
		case .Undef:
			values[lit_var(l)] = .False if lit_is_neg(l) else .True
		}
		return false
	}
	for l in units {
		if set(values, l) {
			return true
		}
	}
	for l in c {
		if set(values, lit_not(l)) {
			return true
		}
	}
	for changed := true; changed; {
		changed = false
		for d in clauses {
			if d == nil {
				continue
			}
			unassigned := 0
			last: Literal
			satisfied := false
			for l in d {
				switch value(values, l) {
				case .True:
					satisfied = true
				case .Undef:
					unassigned += 1
					last = l
				case .False:
				}
				if satisfied {
					break
				}
			}
			if satisfied {
				continue
			}
			if unassigned == 0 {
				return true
			}
			if unassigned == 1 {
				set(values, last)
				changed = true
			}
		}
	}
	return false
}

// Every clause loki learns must follow from the formula. Check each one by unit
// propagation (the RUP check that proof checkers use) against the original
// clauses, the clauses learned before it, and the level-0 facts. Clause deletion
// is turned off so that every learned clause is still there to check.
@(test)
minimized_clauses_are_implied :: proc(t: ^testing.T) {
	texts := [?]string {
		random_3sat(50, 215, 11),
		random_3sat(50, 215, 12),
		random_3sat(60, 258, 13),
		pigeonhole(5, 4),
	}
	defer for text in texts {
		delete(text)
	}

	for text, n in texts {
		for mode in ([]Minimize_Mode{.Local, .Recursive}) {
			f, s := fixture(t, text)
			defer teardown(f, &s)
			s.minimize = mode
			s.reduce_first = max(int) / 2 // no deletion
			n_original := len(f.clauses)

			solve(&s)
			testing.expectf(
				t,
				s.conflicts >= 20,
				"formula %d: only %d conflicts, test checks too little",
				n,
				s.conflicts,
			)

			level0_end := s.level_starts[0] if len(s.level_starts) > 0 else len(s.trail)
			units := s.trail[:level0_end]
			for ci in n_original ..< len(f.clauses) {
				if !testing.expectf(
					t,
					rup_implied(int(f.num_vars), f.clauses[:ci], units, f.clauses[ci]),
					"formula %d (%v): learned clause %d is not implied",
					n,
					mode,
					ci,
				) {
					break
				}
			}
		}
	}
}

// A failed check must undo its marks. z=1 y=2 q=3 a=4 p1=5 p2=6 u=7 x=8.
// Level 1 decides z, which forces y and q. Level 2 decides a, which forces p1
// and p2 (each from a and y). Level 3 decides u, which forces x, and the clause
// (¬x ∨ ¬u ∨ ¬a ∨ ¬p1 ∨ ¬p2 ∨ ¬q) is all false. The 1UIP clause is
// (¬u ∨ ¬a ∨ ¬p1 ∨ ¬p2 ∨ ¬q), and nothing in it is redundant: every chain ends
// at z, a decision that isn't in the clause. Checking p1 marks y before it
// fails at z. If that mark isn't undone, p2's check stops at y as if it were
// covered, and p2 is wrongly removed.
@(test)
minimize_undoes_failed_check :: proc(t: ^testing.T) {
	f, s := fixture(
		t,
		"p cnf 8 6\n-1 2 0\n-1 3 0\n-2 -4 5 0\n-2 -4 6 0\n-7 8 0\n-8 -7 -4 -5 -6 -3 0\n",
	)
	defer teardown(f, &s)
	s.minimize = .Recursive

	decide(&s, L(1))
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(4))
	testing.expect_value(t, propagate(&s), NO_REASON)
	decide(&s, L(7))
	confl := propagate(&s)
	if !testing.expect(t, confl != NO_REASON) {
		return
	}
	learnt, _ := analyze(&s, confl)
	defer delete(learnt)

	testing.expectf(t, len(learnt) == 5, "%d literals, want 5 (nothing is redundant)", len(learnt))
	for x in ([]int{-7, -4, -5, -6, -3}) {
		testing.expectf(
			t,
			slice.contains(learnt[:], L(x)),
			"%d missing from the learned clause",
			x,
		)
	}
	for v in 0 ..< 8 {
		testing.expectf(t, !s.seen[v], "seen[%d] left set", v)
	}
}
