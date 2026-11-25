package tests

import loki ".."
import "core:testing"

// DIMACS x -> variable |x| - 1 -> literal 2v (positive) or 2v + 1 (negative).
// lit_from_dimacs had a bug history (the switch to 0-based variables), so the
// table covers both signs, the first variable, and a large one.
@(test)
lit_from_dimacs_cases :: proc(t: ^testing.T) {
	cases := []struct {
		dimacs: int,
		want:   loki.Literal,
	}{{1, 0}, {-1, 1}, {3, 4}, {-3, 5}, {250, 498}, {-250, 499}}

	for c in cases {
		got := loki.lit_from_dimacs(c.dimacs)
		testing.expectf(t, got == c.want, "lit_from_dimacs(%d) = %d, want %d", c.dimacs, got, c.want)
	}
}

// lit_var strips the sign; lit_is_neg reports it.
@(test)
lit_var_and_sign :: proc(t: ^testing.T) {
	for x in ([]int{1, -1, 2, -2, 7, -7, 250, -250}) {
		l := loki.lit_from_dimacs(x)
		want_var := loki.Var(abs(x) - 1)
		testing.expectf(t, loki.lit_var(l) == want_var, "lit_var(lit(%d)) = %d, want %d", x, loki.lit_var(l), want_var)
		testing.expectf(t, loki.lit_is_neg(l) == (x < 0), "lit_is_neg(lit(%d)) = %v, want %v", x, loki.lit_is_neg(l), x < 0)
	}
}

// lit_pos gives the positive literal of a variable, which is lit_from_dimacs(v + 1).
@(test)
lit_pos_cases :: proc(t: ^testing.T) {
	for v in 0 ..< 10 {
		got := loki.lit_pos(loki.Var(v))
		want := loki.lit_from_dimacs(v + 1)
		testing.expectf(t, got == want, "lit_pos(%d) = %d, want %d", v, got, want)
	}
}

// lit_neg flips the sign: twice is the identity, and it matches negating in DIMACS.
@(test)
lit_neg_cases :: proc(t: ^testing.T) {
	for x in ([]int{1, -1, 3, -3, 250, -250}) {
		l := loki.lit_from_dimacs(x)
		testing.expectf(t, loki.lit_neg(loki.lit_neg(l)) == l, "lit_neg(lit_neg(lit(%d))) != lit(%d)", x, x)
		testing.expectf(
			t,
			loki.lit_neg(l) == loki.lit_from_dimacs(-x),
			"lit_neg(lit(%d)) = %d, want lit(%d) = %d",
			x,
			loki.lit_neg(l),
			-x,
			loki.lit_from_dimacs(-x),
		)
	}
}

// lit_is_true reads an assignment indexed by variable.
@(test)
lit_is_true_cases :: proc(t: ^testing.T) {
	assignment := []bool{true, false} // var 0 true, var 1 false
	testing.expect(t, loki.lit_is_true(loki.lit_from_dimacs(1), assignment))
	testing.expect(t, !loki.lit_is_true(loki.lit_from_dimacs(-1), assignment))
	testing.expect(t, !loki.lit_is_true(loki.lit_from_dimacs(2), assignment))
	testing.expect(t, loki.lit_is_true(loki.lit_from_dimacs(-2), assignment))
}
