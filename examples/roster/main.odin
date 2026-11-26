package roster

import loki "../.."
import "core:fmt"
import "core:os"

main :: proc() {
	doctors := [3]string{"A", "B", "C"}
	shifts := [2]string{"day", "night"}
	b_on_leave := len(os.args) > 1 && os.args[1] == "--b-on-leave"

	m: loki.Model
	defer loki.model_destroy(&m)

	works: [len(doctors)][len(shifts)]loki.Literal
	for _, d in doctors {
		for _, s in shifts {
			works[d][s] = loki.new_bool_var(&m)
		}
	}

	// Each shift needs exactly one doctor.
	for _, s in shifts {
		cover := [len(doctors)]loki.Literal{works[0][s], works[1][s], works[2][s]}
		loki.add_exactly_one(&m, cover[:])
	}

	// Each doctor can work at most one shift.
	for assignments in works {
		loki.add_clause(&m, loki.lit_not(assignments[0]), loki.lit_not(assignments[1]))
	}

	loki.add_clause(&m, loki.lit_not(works[0][1])) // A doesn't work nights.
	for shift in works[2] { 	// C is on leave.
		loki.add_clause(&m, loki.lit_not(shift))
	}
	if b_on_leave {
		for shift in works[1] {
			loki.add_clause(&m, loki.lit_not(shift))
		}
	}

	fmt.printf("%d clauses, %d variables\n", len(m.formula.clauses), m.formula.num_vars)
	result, solution := loki.model_solve(&m)
	defer delete(solution)
	fmt.printf("result: %v\n", result)

	if result == .Sat {
		for doctor, d in doctors {
			for shift, s in shifts {
				if loki.lit_is_true(works[d][s], solution) {
					fmt.printf("  %s works %s\n", doctor, shift)
				}
			}
		}
	}
}
