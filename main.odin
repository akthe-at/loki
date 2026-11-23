package loki

import "core:fmt"
import "core:os"
import "core:strconv"
import "core:strings"


Var :: distinct u32
Literal :: distinct u32
Clause :: []Literal
NO_REASON :: -1

// The Lifted Boolean type is used to represent a boolean value that can also be undefined.
LBool :: enum u8 {
	Undef,
	True,
	False,
}

Result :: enum {
	Sat,
	Unsat,
}

// Formula represents a CNF formula with a number of variables and a list of clauses.
Formula :: struct {
	num_vars: u32,
	clauses:  [dynamic]Clause,
}

// Solver represents a SAT solver that operates on a given formula, maintains variable assignments, and tracks the trail of decisions made during the solving process.
Solver :: struct {
	formula:   ^Formula,
	values:    []LBool,
	trail:     [dynamic]Literal,
	trail_lim: [dynamic]int,
	watches:   [][dynamic]int,
	qhead:     int,
	levels:    []int,
	reasons:   []int,
	seen:      []bool,
}


lit_from_dimacs :: proc(x: int) -> Literal {
	// switch to 0-based indexing and encode the sign in the least significant bit
	v := abs(x) - 1
	if x < 0 {
		return Literal(2 * v + 1)
	} else {
		return Literal(2 * v)
	}
}

lit_var :: proc(l: Literal) -> Var {
	result := l / 2
	return Var(result)
}

lit_pos :: proc(v: Var) -> Literal {
	return Literal(2 * v)
}

lit_neg :: proc(l: Literal) -> Literal {
	return l ~ 1
}

lit_is_true :: proc(l: Literal, assignment: []bool) -> bool {
	value := assignment[lit_var(l)]
	negated := l % 2 == 1
	return value != negated
}

clause_satisfied :: proc(c: Clause, assignment: []bool) -> bool {
	for v in c {
		if lit_is_true(v, assignment) {
			return true
		}
	}
	return false
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

parse_dimacs :: proc(path: string) -> (f: Formula, ok: bool) {
	// Read the file. If it fails, return {}, false.
	data, err := os.read_entire_file(path, context.allocator)
	if err != nil {
		fmt.println("Error reading file:", err)
		return {}, false
	}
	defer delete(data)

	text := string(data)
	rest := text
	current: [dynamic]Literal
	defer delete(current)
	defer if !ok {formula_destroy(&f)}
	//      - For each line:
	//        - empty or starts with c: skip it (continue)
	for line in strings.split_lines_iterator(&rest) {
		if len(line) == 0 || strings.starts_with(line, "c") {
			// skip header
			continue
		}

		if strings.starts_with(line, "%") {
			break
		}
		// Parse the third word into f.num_vars.
		//- starts with p: the words are p, cnf, 3, 2.
		//	You'll need a conversion, since parse_int gives an int
		//  and the field is u32.
		if strings.starts_with(line, "p") {
			// parse the third word into f.num_vars
			header := line
			count := 0
			for w in strings.fields_iterator(&header) {
				count += 1
				if count == 3 {
					n, ok := strconv.parse_int(w)
					if !ok {return f, false}
					f.num_vars = u32(n)
					break
				}
			}
			continue
		}
		words := line
		for word in strings.fields_iterator(&words) {
			lit, ok := strconv.parse_int(word)
			if !ok {return f, false}
			if lit == 0 {
				// finish the current clause
				append(&f.clauses, current[:])
				current = {}
			} else {
				append(&current, lit_from_dimacs(lit))
			}
		}
	}
	return f, true
}

solver_init :: proc(f: ^Formula) -> Solver {
	s := Solver {
		formula = f,
		watches = make([][dynamic]int, 2 * f.num_vars),
		values  = make([]LBool, f.num_vars),
		seen    = make([]bool, f.num_vars),
		levels  = make([]int, f.num_vars),
		reasons = make([]int, f.num_vars),
	}
	for c, i in f.clauses {
		if len(c) >= 2 {
			append(&s.watches[c[0]], i)
			append(&s.watches[c[1]], i)
		}
	}
	return s
}

solver_destroy :: proc(s: ^Solver) {
	delete(s.values)
	delete(s.trail)
	delete(s.trail_lim)
	// delete the inner before the outer
	for v in s.watches {
		delete(v)
	}
	delete(s.watches)
	delete(s.reasons)
	delete(s.levels)
	delete(s.seen)
}

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

lit_is_neg :: proc(l: Literal) -> bool {
	return l % 2 == 1
}

assign :: proc(s: ^Solver, l: Literal, reason: int) {
	v := lit_var(l)
	s.reasons[v] = reason
	s.levels[v] = decision_level(s)
	if lit_is_neg(l) {
		s.values[v] = LBool.False
	} else {
		s.values[v] = LBool.True
	}
	append(&s.trail, l)
}


// The new propagate:
//
// while qhead < len(trail):
//     p := trail[qhead]; qhead += 1
//     false_lit := lit_neg(p)          // p just became True, so NOT p just became False
//     visit each clause in watches[false_lit], using the three cases above
propagate :: proc(s: ^Solver) -> int {
	for s.qhead < len(s.trail) {
		p := s.trail[s.qhead]
		s.qhead += 1
		false_lit := lit_neg(p)

		ws := &s.watches[false_lit]
		i := 0
		for i < len(ws) {
			ci := ws[i]
			c := s.formula.clauses[ci]

			// Normalise: Make sure false_lit is in c[1]
			if c[0] == false_lit {
				c[0], c[1] = c[1], c[0]
			}
			// Case 1: other watched lit is True -> Clause Satisfied
			if lit_value(s, c[0]) == .True {
				i += 1
				continue
			}
			// Case 2: Look for replacement watch in c[2], c[3], ...
			found := false
			for k in 2 ..< len(c) {
				if lit_value(s, c[k]) != .False {
					c[1], c[k] = c[k], c[1] // literal goes to watch pos 1
					append(&s.watches[c[1]], ci) // register clause under new watch
					unordered_remove(ws, i) //remove it from old watch list
					found = true
					break
				}
			}
			if found {
				continue
			}
			// Case 3: No replacement, clause stays watching false_lit
			if lit_value(s, c[0]) == .False {
				return ci
			} else {
				assign(s, c[0], ci)
			}
			i += 1
		}
	}

	return NO_REASON
}

// decision_level tells us the current decision level
decision_level :: proc(s: ^Solver) -> int {
	return len(s.trail_lim)
}

// appends current trail length to trail_lim, this sets the new decision level.
// You must call it before assigning the decision literal.
new_decision_level :: proc(s: ^Solver) {
	current_trail_len := len(s.trail)
	append(&s.trail_lim, current_trail_len)
}


backtrack :: proc(s: ^Solver, level: int) {
	if level >= decision_level(s) {
		return
	}
	target_trail_length := s.trail_lim[level]
	for len(s.trail) > target_trail_length {
		l := pop(&s.trail)
		s.values[lit_var(l)] = .Undef
	}
	resize(&s.trail_lim, level)
	s.qhead = target_trail_length
}

pick_unassigned :: proc(s: ^Solver) -> (Var, bool) {
	for v, i in s.values {
		if v == .Undef {
			return Var(i), true
		}
	}
	return Var(0), false
}


solve :: proc(s: ^Solver) -> Result {
	for c in s.formula.clauses {
		switch len(c) {
		case 0:
			return .Unsat
		case 1:
			v := lit_value(s, c[0])
			switch v {
			case .False:
				return .Unsat
			case .True:
				continue
			case .Undef:
				assign(s, c[0], NO_REASON)
			}
		}
	}

	for {
		confl := propagate(s)

		switch confl {
		case NO_REASON:
			v, ok := pick_unassigned(s)
			if !ok {
				return .Sat
			}
			new_decision_level(s)
			assign(s, lit_pos(v), NO_REASON)
		case:
			if decision_level(s) == 0 {
				return .Unsat
			}
			learnt, bj_level := analyze(s, confl)
			backtrack(s, bj_level)
			if len(learnt) == 1 {
				assign(s, learnt[0], NO_REASON)
				delete(learnt)
			} else {
				append(&s.formula.clauses, learnt[:])
				ci := len(s.formula.clauses) - 1
				append(&s.watches[learnt[0]], ci)
				append(&s.watches[learnt[1]], ci)
				assign(s, learnt[0], ci)
			}
		}
	}
	return .Unsat
}

analyze :: proc(s: ^Solver, confl: int) -> (learnt: [dynamic]Literal, bj_level: int) {
	append(&learnt, Literal(0)) // reserves slot 0

	counter := 0
	p: Literal
	p_set := false
	idx := len(s.trail) - 1
	confl := confl
	current := decision_level(s)

	// each time around the loop, look at one clause.
	// first the conflict clause, then the reason clauses.
	for {
		c := s.formula.clauses[confl]
		start := 1 if p_set else 0

		for k in start ..< len(c) {
			q := c[k]
			v := lit_var(q)

			if !s.seen[v] && s.levels[v] > 0 {
				s.seen[v] = true
				if s.levels[v] == current {
					counter += 1
				} else {
					append(&learnt, q)
				}
			}
		}

		for !s.seen[lit_var(s.trail[idx])] {
			idx -= 1
		}
		p = s.trail[idx]
		p_set = true
		idx -= 1
		s.seen[lit_var(p)] = false
		counter -= 1

		if counter == 0 {
			break // p is the 1UIP
		}
		confl = s.reasons[lit_var(p)] // next time expand p's reason
	}

	learnt[0] = lit_neg(p)

	// backjump level = highest level among learnt[1:], move that literal into slot 1
	bj_level = 0
	max_i := 1
	for i in 1 ..< len(learnt) {
		lvl := s.levels[lit_var(learnt[i])]
		if lvl > bj_level {
			bj_level = lvl
			max_i = i
		}
	}
	if len(learnt) > 1 {
		learnt[1], learnt[max_i] = learnt[max_i], learnt[1]
	}

	// clear seen for older level literals. current level literals were already cleared
	for i in 1 ..< len(learnt) {
		s.seen[lit_var(learnt[i])] = false
	}

	return learnt, bj_level
}
