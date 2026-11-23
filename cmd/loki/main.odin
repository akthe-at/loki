package main

import loki "../.."
import "core:fmt"
import "core:mem"
import "core:os"
import "core:time"

main :: proc() {
	// In debug builds (-debug), report any memory that was never freed.
	when ODIN_DEBUG {
		track: mem.Tracking_Allocator
		mem.tracking_allocator_init(&track, context.allocator)
		context.allocator = mem.tracking_allocator(&track)
		defer {
			if len(track.allocation_map) > 0 {
				fmt.eprintf("=== %v allocations not freed: ===\n", len(track.allocation_map))
				for _, entry in track.allocation_map {
					fmt.eprintf("- %v bytes @ %v\n", entry.size, entry.location)
				}
			}
			mem.tracking_allocator_destroy(&track)
		}
	}

	if len(os.args) < 2 {
		fmt.eprintln("usage: loki <file.cnf>")
		os.exit(1)
	}

	f, ok := loki.parse_dimacs(os.args[1])
	if !ok {
		fmt.eprintln("Failed to parse DIMACS file")
		os.exit(1)
	}
	defer loki.formula_destroy(&f)

	// solve() appends learned clauses to f.clauses, so remember how many
	// clauses came from the file; the self-check only uses those.
	n_original := len(f.clauses)

	s := loki.solver_init(&f)
	defer loki.solver_destroy(&s)

	start := time.now()
	result := loki.solve(&s)
	elapsed := time.since(start)

	fmt.println("result:   ", result)

	// Self-check: a Sat answer must satisfy every ORIGINAL clause.
	if result == .Sat {
		assignment := make([]bool, f.num_vars)
		defer delete(assignment)
		for v, i in s.values {
			assignment[i] = v == .True
		}

		check_ok := true
		for c in f.clauses[:n_original] {
			if !loki.clause_satisfied(c, assignment) {
				check_ok = false
				break
			}
		}
		fmt.println("check:    ", "ok" if check_ok else "FAILED")
	}

	fmt.printf("time:      %.2f ms\n", time.duration_milliseconds(elapsed))
	fmt.println("conflicts:", s.conflicts)
	fmt.println("decisions:", s.decisions)
	fmt.println("restarts: ", s.restarts)
	fmt.println("learned:  ", len(f.clauses) - n_original)
}
