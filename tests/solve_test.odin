package tests

import loki ".."
import "core:fmt"
import "core:strings"
import "core:testing"

// solve_text parses text, solves it with the given settings, and for a Sat
// answer checks the solution against the ORIGINAL clauses (solve appends learned
// clauses to the formula, so those are left out).
solve_text :: proc(
	t: ^testing.T,
	text: string,
	phase_saving := true,
	restarts := loki.Restart_Schedule.Geometric,
	loc := #caller_location,
) -> loki.Result {
	f, err := loki.parse_dimacs_string(text)
	defer loki.formula_destroy(&f)
	if !testing.expect_value(t, err, loki.Parse_Error.None, loc = loc) {
		return .Unknown
	}
	n_original := len(f.clauses)

	s := loki.solver_init(&f)
	defer loki.solver_destroy(&s)
	s.phase_saving = phase_saving
	s.restart_schedule = restarts

	result := loki.solve(&s)
	if result == .Sat {
		solution := make([]bool, f.num_vars)
		defer delete(solution)
		for v, i in s.values {
			solution[i] = v == .True
		}
		for c, ci in f.clauses[:n_original] {
			testing.expectf(t, loki.clause_satisfied(c, solution), "Sat solution breaks clause %d", ci, loc = loc)
		}
	}
	return result
}

// Small formulas whose answers are known by hand.
@(test)
solve_small_formulas :: proc(t: ^testing.T) {
	cases := []struct {
		name: string,
		text: string,
		want: loki.Result,
	} {
		{"no clauses", "p cnf 3 0\n", .Sat},
		{"one unit", "p cnf 1 1\n1 0\n", .Sat},
		{"x and not x", "p cnf 1 2\n1 0\n-1 0\n", .Unsat},
		{"empty clause", "p cnf 1 1\n0\n", .Unsat},
		{"unit chain to conflict", "p cnf 3 4\n1 0\n-1 2 0\n-2 3 0\n-3 0\n", .Unsat},
		{"needs a decision", "p cnf 3 2\n1 -2 0\n2 3 -1 0\n", .Sat},
		// all four sign combinations of two variables: no assignment survives
		{"all 2-var clauses", "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n", .Unsat},
		// exactly one of 1, 2, 3
		{"exactly one of three", "p cnf 3 4\n1 2 3 0\n-1 -2 0\n-1 -3 0\n-2 -3 0\n", .Sat},
	}
	for c in cases {
		got := solve_text(t, c.text)
		testing.expectf(t, got == c.want, "%s: got %v, want %v", c.name, got, c.want)
	}
}

// Pigeonhole: n+1 pigeons into n holes is Unsat, n into n is Sat. Small, but
// it needs real conflict analysis, learning and restarts.
@(test)
solve_pigeonhole :: proc(t: ^testing.T) {
	for holes in 2 ..= 5 {
		for pigeons in ([]int{holes, holes + 1}) {
			text := pigeonhole_dimacs(pigeons, holes)
			defer delete(text)
			want := loki.Result.Sat if pigeons <= holes else loki.Result.Unsat
			for ps in ([]bool{true, false}) {
				for rs in ([]loki.Restart_Schedule{.Geometric, .Luby}) {
					got := solve_text(t, text, ps, rs)
					testing.expectf(
						t,
						got == want,
						"php(%d, %d) phase_saving=%v restarts=%v: got %v, want %v",
						pigeons,
						holes,
						ps,
						rs,
						got,
						want,
					)
				}
			}
		}
	}
}

// The one-call API, on the two small files in tests/data.
@(test)
solve_file_cases :: proc(t: ^testing.T) {
	result, solution, err := loki.solve_file("tests/data/test.cnf")
	defer delete(solution)
	testing.expect_value(t, err, loki.Parse_Error.None)
	testing.expect_value(t, result, loki.Result.Sat)
	testing.expect_value(t, len(solution), 3)

	r2, m2, e2 := loki.solve_file("tests/data/prop.cnf")
	testing.expect_value(t, e2, loki.Parse_Error.None)
	testing.expect_value(t, r2, loki.Result.Unsat)
	testing.expect(t, m2 == nil)
}

// A parse error gives Unknown and no solution, never a Sat.
@(test)
solve_file_missing :: proc(t: ^testing.T) {
	result, solution, err := loki.solve_file("tests/data/no-such-file.cnf")
	testing.expect_value(t, err, loki.Parse_Error.File_Read)
	testing.expect_value(t, result, loki.Result.Unknown)
	testing.expect(t, solution == nil)
}

// pigeonhole_dimacs writes PHP(pigeons, holes) as DIMACS text. Variable
// p*holes + h + 1 means "pigeon p sits in hole h". The caller deletes the text.
pigeonhole_dimacs :: proc(pigeons, holes: int) -> string {
	b := strings.builder_make()
	n_clauses := pigeons + holes * pigeons * (pigeons - 1) / 2
	fmt.sbprintf(&b, "p cnf %d %d\n", pigeons * holes, n_clauses)
	// every pigeon sits in some hole
	for p in 0 ..< pigeons {
		for h in 0 ..< holes {
			fmt.sbprintf(&b, "%d ", p * holes + h + 1)
		}
		strings.write_string(&b, "0\n")
	}
	// no hole holds two pigeons
	for h in 0 ..< holes {
		for p1 in 0 ..< pigeons {
			for p2 in p1 + 1 ..< pigeons {
				fmt.sbprintf(&b, "-%d -%d 0\n", p1 * holes + h + 1, p2 * holes + h + 1)
			}
		}
	}
	return strings.to_string(b)
}
