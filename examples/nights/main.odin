package nights

import loki "../.."
import "core:fmt"
import "core:os"
import "core:strconv"

// Two doctors cover 7 nights, one doctor per night, and each may work at most
// k nights, where k comes from the command line.
//
//	odin run examples/nights -- 3   (Unsat: 2 x 3 < 7)
//	odin run examples/nights -- 4   (Sat)
main :: proc() {
	if len(os.args) != 2 {
		fmt.eprintln("usage: nights <max nights per doctor>")
		os.exit(2)
	}
	k, ok := strconv.parse_int(os.args[1])
	if !ok {
		fmt.eprintln("not a number:", os.args[1])
		os.exit(2)
	}

	doctors := [2]string{"A", "B"}
	NIGHTS :: 7

	m: loki.Model
	defer loki.model_destroy(&m)

	works: [len(doctors)][NIGHTS]loki.Literal // works[d][n]: doctor d works night n
	for d in 0 ..< len(doctors) {
		for n in 0 ..< NIGHTS {
			works[d][n] = loki.new_bool_var(&m)
		}
	}

	// Each night needs exactly one doctor.
	for n in 0 ..< NIGHTS {
		cover := [len(doctors)]loki.Literal{works[0][n], works[1][n]}
		loki.add_exactly_one(&m, cover[:])
	}

	// Each doctor works at most k nights.
	for d in 0 ..< len(doctors) {
		loki.add_at_most(&m, works[d][:], k)
	}

	fmt.printf("%d clauses, %d variables\n", len(m.formula.clauses), m.formula.num_vars)
	result, solution := loki.model_solve(&m)
	defer delete(solution)
	fmt.printf("result: %v\n", result)

	if result == .Sat {
		for doctor, d in doctors {
			fmt.printf("  %s:", doctor)
			for n in 0 ..< NIGHTS {
				fmt.print(" X" if loki.lit_is_true(works[d][n], solution) else " .")
			}
			fmt.println()
		}
	}
}
