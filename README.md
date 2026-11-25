# loki

Howdy, I bet you're wondering how you got here and what this is? Honestly, I am too. This repo is me playing with the Odin language while also trying to learn about SAT solvers at the same time. My programming background is pretty much all higher level languages (Go, Python, R, SQL) where I never had to manage memory...probably going to be a few learning experiences here. 

My long-term (very long-term) dream is a CP-SAT style constraint solver written in plain Odin. Step one was getting a real CDCL SAT solver working, and that's done now: it's a tested, reasonably fast SAT library, which I'm calling milestone 1 / v0.1.0.

> **heads up:** this is a learning project and not production ready...yet...don't trust it with anything important yet. The API *will* change once I start working on the CP stuff (soon)...

## where it's at

loki reads a DIMACS `.cnf` file and tells you SAT or UNSAT (and gives you the answer if it's SAT). You can use it from the command line or as an Odin package.

what's in it, roughly in the order I built it:

- literal encoding: `2v` for x, `2v+1` for NOT x, so flipping a literal is just `l ~ 1`. 0-based vars internally (same trick CP-SAT uses, turns out)
- a DIMACS parser that returns errors instead of crashing on bad files
- unit propagation with two watched literals
- conflict analysis (1UIP) w/ clause learning and backjumping
- VSIDS decision heuristic, on a binary heap (picking a variable used to be a full scan)
- restarts (geometric by default, Luby is there too) and phase saving
- learned clause cleanup using LBD
- blocking literals in the watch lists, plus a fast path for binary clauses
- learned clause minimization (MiniSat-style recursive, from [Sörensson & Biere 2009](https://fmv.jku.at/papers/SoerenssonBiere-SAT09.pdf)): drops literals the rest of the clause already implies, which cuts about 20–40% of learned literals
- tests: unit tests for the internals, plus whole solves against the benchmark files

### how fast?

Compared to [gophersat](https://github.com/crillab/gophersat) (a Go CDCL solver) and [MiniSat](https://github.com/niklasso/minisat) 2.2 (the classic C++ one, run with `-no-pre` since loki doesn't preprocess either) on my not-very-fast machine, median of 10 runs, one solve at a time:

| benchmark set | loki | gophersat | MiniSat |
|---|---|---|---|
| bmc (13 hardware verification files) | 5.2 s | 9.2 s | 2.3 s |
| uuf250 (5 hard random Unsat files) | 9.4 s | 16.9 s | 14.7 s |
| qg (3 quasigroup files) | 3.8 s | 5.7 s | 3.1 s |

Clause minimization made loki about 18% faster overall (22.5 s → 18.4 s for all 21 files). bmc is still where MiniSat leaves me in the dust.


## using it

You need [Odin](https://odin-lang.org/) (I'm currently using `dev-2026-11` nightly).

### command line

```sh
odin build cmd/loki -o:speed -out:loki
./loki some_problem.cnf
```

It prints the result, checks any SAT answer against the original clauses, and shows some stats (conflicts, decisions, restarts, learned clauses, how many learned literals minimization removed...). Build with `-define:LOKI_PROFILE=true` to also see where the time goes.

### as an Odin package

Odin doesn't have a package manager, so the easy way is to clone loki into your project and import the folder:

```sh
git clone https://github.com/akthe-at/loki.git
```

```odin
package main

import "core:fmt"
import loki "loki"

main :: proc() {
	result, solution, err := loki.solve_file("puzzle.cnf")
	if err != nil {
		fmt.eprintln("couldn't read it:", err)
		return
	}
	defer delete(solution)

	fmt.println(result) // Sat or Unsat
	if result == .Sat {
		fmt.println("x1 =", solution[0]) // solution is 0-based: DIMACS var 1 is solution[0]
	}
}
```

If you want more control (settings like restarts, phase saving or clause minimization, or stats after the solve), use `parse_dimacs` + `solver_init` + `solve` directly. `api.odin` shows how they fit together.

### tests and benchmarks

```sh
odin test . -define:ODIN_TEST_FAIL_ON_BAD_MEMORY=true      # internals
odin test tests -define:ODIN_TEST_FAIL_ON_BAD_MEMORY=true  # public API

scripts/fetch_bench.sh            # download the SATLIB random sets into bench/
scripts/fetch_bench.sh structured # and the structured ones (bmc, qg, ...)
scripts/bench.sh                  # run them all and check every answer
```

## what I'm working on / towards

- [x] a real CDCL SAT solver (milestone 1, v0.1.0)
- [ ] The CP side: "exactly k of these" constraints, optimization (best answer, not just any answer), integer variables with lazy clause generation
- [ ] a C API, so it can be used from other languages

I've got a couple real-world use cases for this at work and in personal projects that I want an alternative to CP-SAT to use with.

Currently, in my head...the plan is for this to be a general library other people can use too, not just from Odin: eventually from Python, R, Go (no cgo way?), and maybe others but I know I would use it from those languages at least.

## license

zlib licensed, see [LICENSE](LICENSE).
