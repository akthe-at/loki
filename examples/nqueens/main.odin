package nqueens

import loki "../.."
import "core:fmt"
import "core:os"
import "core:strconv"

// Place n queens on an n x n board so no two attack each other.
//
//	odin run examples/nqueens -- 8   (Sat)
//	odin run examples/nqueens -- 3   (Unsat)
main :: proc() {
	n := 8
	if len(os.args) > 1 {
		ok: bool
		n, ok = strconv.parse_int(os.args[1])
		if !ok || n < 1 {
			fmt.eprintln("usage: nqueens [board size >= 1]")
			os.exit(2)
		}
	}

	m: loki.Model
	defer loki.model_destroy(&m)

	// q[r * n + c]: a queen on row r, column c
	q := make([]loki.Literal, n * n)
	defer delete(q)
	for &l in q {
		l = loki.new_bool_var(&m)
	}

	line := make([dynamic]loki.Literal)
	defer delete(line)

	// Exactly one queen in each row.
	for r in 0 ..< n {
		clear(&line)
		for c in 0 ..< n {
			append(&line, q[r * n + c])
		}
		loki.add_exactly_one(&m, line[:])
	}

	// Exactly one queen in each column.
	for c in 0 ..< n {
		clear(&line)
		for r in 0 ..< n {
			append(&line, q[r * n + c])
		}
		loki.add_exactly_one(&m, line[:])
	}

	// At most one queen on each diagonal going down-right (same r - c).
	for d in -(n - 1) ..= n - 1 {
		clear(&line)
		for r in 0 ..< n {
			c := r - d
			if c >= 0 && c < n {
				append(&line, q[r * n + c])
			}
		}
		loki.add_at_most_one(&m, line[:])
	}

	// At most one queen on each diagonal going down-left (same r + c).
	for d in 0 ..= 2 * (n - 1) {
		clear(&line)
		for r in 0 ..< n {
			c := d - r
			if c >= 0 && c < n {
				append(&line, q[r * n + c])
			}
		}
		loki.add_at_most_one(&m, line[:])
	}

	fmt.printf("%d clauses, %d variables\n", len(m.formula.clauses), m.formula.num_vars)
	result, solution := loki.model_solve(&m)
	defer delete(solution)
	fmt.printf("result: %v\n", result)
	if result != .Sat {
		return
	}

	// cols[r]: the column of row r's queen
	cols := make([]int, n)
	defer delete(cols)
	for r in 0 ..< n {
		for c in 0 ..< n {
			if loki.lit_is_true(q[r * n + c], solution) {
				cols[r] = c
			}
		}
	}
	if n <= 20 {
		fmt.println("queen columns, row by row:", cols)
	}
	fmt.println("check:", "ok" if check(cols) else "FAILED")
}

// check uses only the queen positions: no two share a column or a diagonal.
// (One queen per row is built into cols.)
check :: proc(cols: []int) -> bool {
	for a in 0 ..< len(cols) {
		for b in a + 1 ..< len(cols) {
			if cols[a] == cols[b] || abs(cols[a] - cols[b]) == b - a {
				return false
			}
		}
	}
	return true
}
