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

	// Settings from the environment (CLI only; the library takes struct fields).
	// LOKI_PHASE_SAVING=0 turns phase saving off.
	if value, found := os.lookup_env("LOKI_PHASE_SAVING", context.temp_allocator);
	   found && value == "0" {
		s.phase_saving = false
	}
	fmt.println("phase saving:", "on" if s.phase_saving else "off")
	// LOKI_RESTARTS
	if value, found := os.lookup_env("LOKI_RESTARTS", context.temp_allocator);
	   found && value == "luby" {
		s.restart_schedule = .Luby
	}
	if value, found := os.lookup_env("LOKI_RESTARTS", context.temp_allocator);
	   found && value == "geometric" {
		s.restart_schedule = .Geometric
	}
	fmt.println("restart schedule:", s.restart_schedule)

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

	learned := len(f.clauses) - n_original
	fmt.printf("time:      %.2f ms\n", time.duration_milliseconds(elapsed))
	fmt.println("conflicts:", s.conflicts)
	fmt.println("decisions:", s.decisions)
	fmt.println("restarts: ", s.restarts)
	fmt.println("learned:  ", learned)
	fmt.println("deleted:", s.deleted)
	fmt.println("alive:", learned - s.deleted)
	fmt.println("reductions:", s.reductions)

	// Clause quality: average LBD and glue count (LBD <= 2) over learned clauses.
	n_learned, lbd_sum, glue := 0, 0, 0
	for info in s.infos {
		if !info.learned {
			continue
		}
		n_learned += 1
		lbd_sum += info.lbd
		if info.lbd <= 2 {
			glue += 1
		}
	}
	avg_lbd := f64(lbd_sum) / f64(n_learned) if n_learned > 0 else 0
	fmt.printf("avg lbd:   %.2f\n", avg_lbd)
	fmt.println("glue:     ", glue)
}
