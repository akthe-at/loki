package loki

// solve_file parses and solves a DIMACS file. On .Sat, `solution[v]` is the value
// of variable v (0-based); the caller owns solution and frees it with delete.
// On a parse error, result is .Unknown and solution is nil.
solve_file :: proc(
	path: string,
	allocator := context.allocator,
) -> (
	result: Result,
	solution: []bool,
	err: Parse_Error,
) {
	f := parse_dimacs(path) or_return
	defer formula_destroy(&f)

	s := solver_make(&f)
	defer solver_destroy(&s)

	result = solve(&s)

	if result == .Sat {
		solution = make([]bool, f.num_vars, allocator)
		for v, i in s.values {
			solution[i] = v == .True
		}
	}

	return result, solution, err
}
