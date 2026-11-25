package tests

import loki ".."
import "core:fmt"
import "core:log"
import "core:testing"

// A few real SATLIB files, solved end to end through the public API, with the
// model checked for every Sat answer. bench/ is gitignored (fetch it with
// scripts/fetch_bench.sh), so a missing file is skipped, not failed.
@(test)
bench_files_self_check :: proc(t: ^testing.T) {
	sets := []struct {
		pattern: string,
		want:    loki.Result,
	} {
		{"bench/uf50-218/uf50-0%d.cnf", .Sat},
		{"bench/uuf50-218/UUF50.218.1000/uuf50-0%d.cnf", .Unsat},
	}
	solved := 0
	for set in sets {
		for i in 1 ..= 5 {
			path := fmt.aprintf(set.pattern, i)
			defer delete(path)

			f, err := loki.parse_dimacs(path)
			defer loki.formula_destroy(&f)
			if err == .File_Read {
				continue
			}
			if !testing.expectf(t, err == nil, "%s: parse error %v", path, err) {
				continue
			}
			n_original := len(f.clauses)
			s := loki.solver_init(&f)
			defer loki.solver_destroy(&s)

			result := loki.solve(&s)
			testing.expectf(t, result == set.want, "%s: got %v, want %v", path, result, set.want)
			if result == .Sat {
				model := make([]bool, f.num_vars)
				defer delete(model)
				for v, k in s.values {
					model[k] = v == .True
				}
				for c in f.clauses[:n_original] {
					if !testing.expectf(t, loki.clause_satisfied(c, model), "%s: model breaks a clause", path) {
						break
					}
				}
			}
			solved += 1
		}
	}
	if solved == 0 {
		log.warn("bench/ not found: skipped (run scripts/fetch_bench.sh)")
	}
}
