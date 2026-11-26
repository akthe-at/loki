package loki

import "base:runtime"

// Formula represents a CNF formula with a number of variables and a list of clauses.
Formula :: struct {
	clauses:  [dynamic]Clause,
	num_vars: u32,
}

// formula_satisfied reports whether every clause in f is true under assignment.
formula_satisfied :: proc(f: Formula, assignment: []bool) -> bool {
	for c in f.clauses {
		if !clause_satisfied(c, assignment) {
			return false
		}
	}
	return true
}

// formula_destroy frees the formula's clauses, with the allocator they were made with.
formula_destroy :: proc(f: ^Formula) {
	allocator := clause_allocator(f)
	for c in f.clauses {
		delete(c, allocator)
	}
	delete(f.clauses)
}

// clause_allocator returns the allocator f's clauses are made with: the one its
// clause list was created with, or context.allocator if it has none yet (the
// list then adopts context.allocator on its first append).
@(private)
clause_allocator :: proc(f: ^Formula) -> runtime.Allocator {
	if f.clauses.allocator.procedure == nil {
		return context.allocator
	}
	return f.clauses.allocator
}
