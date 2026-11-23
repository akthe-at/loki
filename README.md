# loki

Howdy, I bet you're wondering how you got here and what this is? Honestly, I am too. This repo is me playing with the Odin language while also trying to learn about SAT solvers at the same time. My programming background is pretty much all higher level languages (Go, Python, R, SQL) where I never had to manage memory...probably going to be a few learning experiences here. 

My long-term (very long-term) dream is a CP-SAT style constraint solver written in plain Odin. My first step/goal was just getting a real CDCL SAT solver working, which is about the state we are in now.

## where it's at

it's all one `main.odin` file at the moment. it reads a DIMACS `.cnf` file and tells you SAT or UNSAT. it works! it's just not organized yet.

stuff I've built so far, roughly in order:

- literal encoding: `2v` for x, `2v+1` for NOT x, so flipping a literal is just `l ~ 1`. 0-based vars internally (same trick CP-SAT uses, turns out)
- a check that an assignment actually satisfies the formula. 
- a DIMACS parser
- unit propagation
- decisions + backtracking with a trail and decision levels (plain DPLL)
- watched literals
- conflict analysis (1UIP), clause learning and backjumping...so it's actually CDCL now I guess.


## what I'm working on / towards

- **next up:** VSIDS (smarter choice of which variable to guess) and restarts. right now it always guesses the first unassigned variable.
- splitting this into a proper Odin library package, with a small CLI and real tests instead of me eyeballing printouts
- cleaning out old learned clauses so memory doesn't grow forever
- phase saving
- then the CP side: "exactly k of these" constraints, optimization (best answer, not just any answer), integer variables with lazy clause generation

I've got a couple real-world use cases for this at work and in personal projects that I want an alternative to CP-SAT to use with.

