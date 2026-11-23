package loki


// Formula represents a CNF formula with a number of variables and a list of clauses.
Formula :: struct {
	num_vars: u32,
	clauses:  [dynamic]Clause,
}

formula_satisfied :: proc(f: Formula, assignment: []bool) -> bool {
	for c in f.clauses {
		if !clause_satisfied(c, assignment) {
			return false
		}
	}
	return true
}

formula_destroy :: proc(f: ^Formula) {
	for c in f.clauses {
		delete(c)
	}
	delete(f.clauses)
}
