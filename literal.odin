package loki


// Var is a variable index, 0-based: DIMACS variable x is Var(x-1).
Var :: distinct u32

// Literal is a variable or its negation, encoded as 2*v (positive) or
// 2*v + 1 (negative). Build one with lit_from_dimacs or lit_pos.
Literal :: distinct u32

// Clause is a disjunction of literals: it is true when at least one of
// its literals is true.
Clause :: []Literal

// lit_from_dimacs converts a signed 1-based DIMACS literal to the internal
// encoding: zero-based variable with the sign in the least significant bit.
lit_from_dimacs :: proc(x: int) -> Literal {
	v := abs(x) - 1
	if x < 0 {
		return Literal(2 * v + 1)
	} else {
		return Literal(2 * v)
	}
}

// lit_var returns the variable of l, ignoring its sign.
lit_var :: proc(l: Literal) -> Var {
	result := l / 2
	return Var(result)
}

// lit_pos returns the positive literal of variable v.
lit_pos :: proc(v: Var) -> Literal {
	return Literal(2 * v)
}

// lit_not returns the negation of l: the same variable with the opposite sign.
lit_not :: proc(l: Literal) -> Literal {
	return l ~ 1
}

// lit_is_true reports whether l is true under assignment, which is indexed by variable.
lit_is_true :: proc(l: Literal, assignment: []bool) -> bool {
	return assignment[lit_var(l)] != lit_is_neg(l)
}

// lit_value returns the value of l under s's current assignment, or .Undef.
lit_value :: proc(s: ^Solver, l: Literal) -> LBool {
	v := lit_var(l)
	value := s.values[v]
	if value == .Undef {
		return .Undef
	}
	if lit_is_neg(l) {
		if value == .True {
			return .False
		} else {
			return .True
		}
	} else {
		return value
	}
}

// lit_is_neg reports whether l is a negative literal.
lit_is_neg :: proc(l: Literal) -> bool {
	return l % 2 == 1
}
