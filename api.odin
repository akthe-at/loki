package loki

// solve_file parses and solves a DIMACS file. On .Sat, `model[v]` is the value
// of variable v (0-based); the caller owns model and frees it with delete.
// On a parse error, result is .Unknown and model is nil.
solve_file :: proc(
	path: string,
	allocator := context.allocator,
) -> (
	result: Result,
	model: []bool,
	err: Parse_Error,
) {
	f := parse_dimacs(path) or_return
	defer formula_destroy(&f)

	s := solver_init(&f)
	defer solver_destroy(&s)

	result = solve(&s)

	if result == .Sat {
		model = make([]bool, f.num_vars, allocator)
		for v, i in s.values {
			if v == .True {
				model[i] = true
			} else {
				model[i] = false
			}
		}
	}

	return result, model, err
}
