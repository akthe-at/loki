package tests

import loki ".."
import "core:testing"

// A well-formed file: comments are skipped, the header sets num_vars, and each
// clause keeps its literals in order.
@(test)
parse_good_input :: proc(t: ^testing.T) {
	f, err := loki.parse_dimacs_string("c a comment\np cnf 3 2\n1 -2 0\n2 3 0\n")
	defer loki.formula_destroy(&f)

	testing.expect_value(t, err, loki.Parse_Error.None)
	testing.expect_value(t, f.num_vars, 3)
	if !testing.expect_value(t, len(f.clauses), 2) {
		return
	}
	expect_clause(t, f.clauses[0], {1, -2})
	expect_clause(t, f.clauses[1], {2, 3})
}

// A clause may span lines: only the 0 ends it.
@(test)
parse_clause_across_lines :: proc(t: ^testing.T) {
	f, err := loki.parse_dimacs_string("p cnf 3 1\n1 2\n3 0\n")
	defer loki.formula_destroy(&f)

	testing.expect_value(t, err, loki.Parse_Error.None)
	if testing.expect_value(t, len(f.clauses), 1) {
		expect_clause(t, f.clauses[0], {1, 2, 3})
	}
}

// SATLIB files end with "%" and then "0". Both are ignored.
@(test)
parse_satlib_trailer :: proc(t: ^testing.T) {
	f, err := loki.parse_dimacs_string("p cnf 2 1\n1 2 0\n%\n0\n")
	defer loki.formula_destroy(&f)

	testing.expect_value(t, err, loki.Parse_Error.None)
	testing.expect_value(t, len(f.clauses), 1)
}

// "0" on its own line is the empty clause, which makes the formula Unsat.
@(test)
parse_empty_clause :: proc(t: ^testing.T) {
	f, err := loki.parse_dimacs_string("p cnf 1 1\n0\n")
	defer loki.formula_destroy(&f)

	testing.expect_value(t, err, loki.Parse_Error.None)
	if testing.expect_value(t, len(f.clauses), 1) {
		testing.expect_value(t, len(f.clauses[0]), 0)
	}
}

// Every Parse_Error case, from the same inputs as Lesson 11 part 1's bad files.
// After an error the returned formula must be empty, and destroying it must be
// harmless: this is the double free from Lesson 11 part 2. With
// -define:ODIN_TEST_FAIL_ON_BAD_MEMORY=true a leak or bad free fails the test.
@(test)
parse_errors :: proc(t: ^testing.T) {
	cases := []struct {
		name: string,
		text: string,
		want: loki.Parse_Error,
	} {
		{"clause before header", "1 2 0\n-1 0\n", .Missing_Header},
		{"literal out of range", "p cnf 2 1\n1 5 0\n", .Literal_Out_Of_Range},
		{"negative out of range", "p cnf 2 1\n-3 0\n", .Literal_Out_Of_Range},
		{"unterminated clause", "p cnf 2 2\n1 2 0\n-1\n", .Unterminated_Clause},
		{"non-numeric var count", "p cnf two 1\n1 0\n", .Bad_Header},
		{"short header", "p cnf\n1 0\n", .Bad_Header},
		{"negative var count", "p cnf -2 1\n1 0\n", .Bad_Header},
		{"bad token", "p cnf 2 2\n1 x 0\n", .Bad_Literal},
	}

	for c in cases {
		f, err := loki.parse_dimacs_string(c.text)
		testing.expectf(t, err == c.want, "%s: got %v, want %v", c.name, err, c.want)
		testing.expectf(t, len(f.clauses) == 0 && f.num_vars == 0, "%s: formula not empty after error", c.name)
		loki.formula_destroy(&f) // must not double free
	}
}

@(test)
parse_missing_file :: proc(t: ^testing.T) {
	f, err := loki.parse_dimacs("tests/data/no-such-file.cnf")
	testing.expect_value(t, err, loki.Parse_Error.File_Read)
	loki.formula_destroy(&f)
}

// expect_clause checks a clause against DIMACS literals.
expect_clause :: proc(t: ^testing.T, got: loki.Clause, want: []int, loc := #caller_location) {
	if !testing.expectf(t, len(got) == len(want), "clause has %d literals, want %d", len(got), len(want), loc = loc) {
		return
	}
	for x, i in want {
		testing.expectf(
			t,
			got[i] == loki.lit_from_dimacs(x),
			"literal %d is %d, want lit(%d) = %d",
			i,
			got[i],
			x,
			loki.lit_from_dimacs(x),
			loc = loc,
		)
	}
}
