package main

import loki "../.."
import "core:fmt"

main :: proc() {
	f, ok := loki.parse_dimacs("./bench/uf50-218/uf50-0131.cnf")
	if !ok {
		fmt.println("Failed to parse DIMACS file")
		return
	}
	fmt.println(f)
	defer loki.formula_destroy(&f)

	s := loki.solver_init(&f)
	defer loki.solver_destroy(&s)
	fmt.println(s.watches)


	the_result := loki.solve(&s)
	if the_result == .Sat {
		fmt.println("The result: ", the_result)
	}

	other_test := make([]bool, f.num_vars)
	defer delete(other_test)
	for v, i in s.values {
		if v == .True {
			other_test[i] = true
		} else {
			other_test[i] = false
		}
	}

	fmt.println(loki.formula_satisfied(f, other_test))

}
