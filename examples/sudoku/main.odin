package sudoku

import loki "../.."
import "core:fmt"

// The puzzle from Wikipedia's "Sudoku" article, row by row. 0 = empty.
PUZZLE :: "530070000600195000098000060800060003400803001700020006060000280000419005000080079"

main :: proc() {
	m: loki.Model
	defer loki.model_destroy(&m)

	// x[r][c][d]: the cell at row r, column c holds digit d+1
	x: [9][9][9]loki.Literal
	for r in 0 ..< 9 {
		for c in 0 ..< 9 {
			for d in 0 ..< 9 {
				x[r][c][d] = loki.new_bool_var(&m)
			}
		}
	}

	// Each cell holds exactly one digit.
	for r in 0 ..< 9 {
		for c in 0 ..< 9 {
			loki.add_exactly_one(&m, x[r][c][:])
		}
	}

	// Each digit appears exactly once in each row, column and box.
	group: [9]loki.Literal
	for d in 0 ..< 9 {
		for r in 0 ..< 9 {
			for c in 0 ..< 9 {
				group[c] = x[r][c][d]
			}
			loki.add_exactly_one(&m, group[:])
		}
		for c in 0 ..< 9 {
			for r in 0 ..< 9 {
				group[r] = x[r][c][d]
			}
			loki.add_exactly_one(&m, group[:])
		}
		for b in 0 ..< 9 {
			// box b's top-left cell is (b / 3 * 3, b % 3 * 3)
			for i in 0 ..< 9 {
				group[i] = x[b / 3 * 3 + i / 3][b % 3 * 3 + i % 3][d]
			}
			loki.add_exactly_one(&m, group[:])
		}
	}

	// The givens.
	for ch, i in PUZZLE {
		if ch != '0' {
			loki.add_clause(&m, x[i / 9][i % 9][int(ch - '1')])
		}
	}

	fmt.printf("%d clauses, %d variables\n", len(m.formula.clauses), m.formula.num_vars)
	result, solution := loki.model_solve(&m)
	defer delete(solution)
	fmt.printf("result: %v\n", result)
	if result != .Sat {
		return
	}

	grid: [9][9]int
	for r in 0 ..< 9 {
		for c in 0 ..< 9 {
			for d in 0 ..< 9 {
				if loki.lit_is_true(x[r][c][d], solution) {
					grid[r][c] = d + 1
				}
			}
		}
	}
	for row in grid {
		fmt.println(row)
	}
	fmt.println("check:", "ok" if check(grid, PUZZLE) else "FAILED")
}

// check uses only the digits: every given is kept, and every row, column and
// box holds 1-9 once each. It knows nothing about the model or its clauses.
check :: proc(g: [9][9]int, puzzle: string) -> bool {
	for i in 0 ..< 81 {
		if puzzle[i] != '0' && g[i / 9][i % 9] != int(puzzle[i] - '0') {
			return false
		}
	}
	ALL :: bit_set[1 ..= 9]{1, 2, 3, 4, 5, 6, 7, 8, 9}
	for i in 0 ..< 9 {
		row, col, box: bit_set[1 ..= 9]
		for j in 0 ..< 9 {
			row += {g[i][j]}
			col += {g[j][i]}
			box += {g[i / 3 * 3 + j / 3][i % 3 * 3 + j % 3]}
		}
		if row != ALL || col != ALL || box != ALL {
			return false
		}
	}
	return true
}
