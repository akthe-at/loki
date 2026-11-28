#+private
package loki

import "core:slice"
import "core:testing"

// clause_alloc writes a 2-word header (size and learned flag, then LBD) and the
// literals, and returns the clause's offset. clause_lits and the header
// accessors read it back.
@(test)
arena_round_trip :: proc(t: ^testing.T) {
	f: Formula
	s := solver_make(&f)
	defer solver_destroy(&s)

	a := [3]Literal{lit_from_dimacs(1), lit_from_dimacs(-2), lit_from_dimacs(3)}
	b := [2]Literal{lit_from_dimacs(-4), lit_from_dimacs(5)}
	ca := clause_alloc(&s, a[:], learned = false, lbd = 0)
	cb := clause_alloc(&s, b[:], learned = true, lbd = 2)

	// a starts at 0; b starts after a's header and 3 literals
	testing.expect_value(t, ca, Cref(0))
	testing.expect_value(t, cb, Cref(HEADER_WORDS + 3))
	testing.expect_value(t, len(s.arena), 2 * HEADER_WORDS + 5)

	testing.expect(t, slice.equal(clause_lits(&s, ca), a[:]), "clause a's literals")
	testing.expect(t, slice.equal(clause_lits(&s, cb), b[:]), "clause b's literals")
	testing.expect(t, !clause_learned(&s, ca), "clause a is original")
	testing.expect(t, clause_learned(&s, cb), "clause b is learned")
	testing.expect(t, !clause_deleted(&s, ca) && !clause_deleted(&s, cb), "nothing deleted")
	testing.expect_value(t, clause_lbd(&s, cb), 2)
}

// clause_lits is a view into the arena, not a copy: propagate swaps watched
// literals through it.
@(test)
arena_lits_are_a_view :: proc(t: ^testing.T) {
	f: Formula
	s := solver_make(&f)
	defer solver_destroy(&s)

	a := [3]Literal{lit_from_dimacs(1), lit_from_dimacs(2), lit_from_dimacs(3)}
	cr := clause_alloc(&s, a[:], learned = false, lbd = 0)
	c := clause_lits(&s, cr)
	c[0], c[2] = c[2], c[0]

	again := clause_lits(&s, cr)
	testing.expect_value(t, again[0], lit_from_dimacs(3))
	testing.expect_value(t, again[2], lit_from_dimacs(1))
	testing.expect_value(t, a[0], lit_from_dimacs(1)) // the caller's array is untouched
}

// solver_make copies every clause with 2+ literals into the arena, in order,
// and leaves units and the formula alone.
@(test)
arena_holds_the_formula :: proc(t: ^testing.T) {
	f, err := parse_dimacs_string("p cnf 4 4\n1 2 0\n-3 0\n2 3 4 0\n-1 -4 0\n")
	defer formula_destroy(&f)
	testing.expect_value(t, err, Parse_Error.None)
	s := solver_make(&f)
	defer solver_destroy(&s)

	want := [?][]Literal{f.clauses[0], f.clauses[2], f.clauses[3]} // the unit is skipped
	cr := Cref(0)
	for w in want {
		testing.expect(t, slice.equal(clause_lits(&s, cr), w), "arena clause differs from the formula")
		testing.expect(t, !clause_learned(&s, cr), "original clause marked learned")
		cr += Cref(HEADER_WORDS + len(w))
	}
	testing.expect_value(t, len(s.arena), int(cr))
	testing.expect_value(t, len(f.clauses), 4)
}

// arena_compact on a hand example. The arena starts as
//   A = (x1 ∨ x2) at 0, B = (¬x1 ∨ x3 ∨ x4) at 4, C = (x2 ∨ ¬x3) at 9,
//   and a learned D = (¬x2 ∨ x4), LBD 2, at 13.
// C is the reason for x2. Deleting B leaves a 5-word hole, so compacting
// moves C from 9 to 4 and D from 13 to 8, and every Cref must follow.
@(test)
arena_compact_moves_clauses :: proc(t: ^testing.T) {
	f, err := parse_dimacs_string("p cnf 4 3\n1 2 0\n-1 3 4 0\n2 -3 0\n")
	defer formula_destroy(&f)
	testing.expect_value(t, err, Parse_Error.None)
	s := solver_make(&f)
	defer solver_destroy(&s)

	d := [2]Literal{lit_from_dimacs(-2), lit_from_dimacs(4)}
	cd := clause_alloc(&s, d[:], learned = true, lbd = 2)
	append(&s.learnts, cd)
	attach(&s, cd)
	testing.expect_value(t, cd, Cref(13))
	assign(&s, lit_from_dimacs(2), Cref(9)) // C implies x2

	// delete B the way reduce_db does: mark it, count it, drop its watches
	s.arena[4] |= DELETED_BIT
	s.wasted += HEADER_WORDS + 3
	for &ws in s.watches {
		j := 0
		for w in ws {
			if w.cref != 4 {
				ws[j] = w
				j += 1
			}
		}
		resize(&ws, j)
	}

	arena_compact(&s)

	// A, C, D, packed: 4 + 4 + 4 words, and nothing wasted
	testing.expect_value(t, len(s.arena), 12)
	testing.expect_value(t, s.wasted, 0)
	testing.expect(t, slice.equal(clause_lits(&s, 0), f.clauses[0]), "A stays at 0")
	testing.expect(t, slice.equal(clause_lits(&s, 4), f.clauses[2]), "C moves to 4")
	testing.expect(t, slice.equal(clause_lits(&s, 8), d[:]), "D moves to 8")
	testing.expect(t, clause_learned(&s, 8) && !clause_learned(&s, 4), "learned flags move with the clauses")
	testing.expect_value(t, clause_lbd(&s, 8), 2)
	for cr in ([]Cref{0, 4, 8}) {
		testing.expectf(t, s.arena[cr] & (RELOCATED_BIT | DELETED_BIT) == 0, "clause %d copied with a stale flag", cr)
	}

	// every Cref the solver holds followed its clause
	testing.expect_value(t, len(s.learnts), 1)
	testing.expect_value(t, s.learnts[0], Cref(8))
	testing.expect_value(t, s.reasons[lit_var(lit_from_dimacs(2))], Cref(4))
	n_watches := 0
	for ws, lit in s.watches {
		for w in ws {
			n_watches += 1
			testing.expectf(t, w.cref == 0 || w.cref == 4 || w.cref == 8, "watch on clause %d, not a clause start", w.cref)
			c := clause_lits(&s, w.cref)
			testing.expectf(t, c[0] == Literal(lit) || c[1] == Literal(lit), "watches[%d] holds clause %d, which doesn't watch it", lit, w.cref)
		}
	}
	testing.expect_value(t, n_watches, 6) // two per clause
}
