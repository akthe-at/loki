package loki

import "core:fmt"
import "core:os"
import "core:strconv"
import "core:strings"

// parse_dimacs reads a DIMACS CNF file. On success the caller owns the returned
// formula and must free it with formula_destroy.
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
