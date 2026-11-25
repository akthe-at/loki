package loki

import "core:os"
import "core:strconv"
import "core:strings"


// Parse_Error is the reason parsing failed. None (zero value) means
// success, so callers can test err != nil
Parse_Error :: enum {
	None,
	File_Read,
	Missing_Header,
	Bad_Header,
	Bad_Literal,
	Literal_Out_Of_Range,
	Unterminated_Clause,
}

// parses DIMACS CNF text. On success the caller owns the returned formula
// and frees it with formula_destroy. On error the returned formula is empty.
parse_dimacs_string :: proc(text: string) -> (f: Formula, err: Parse_Error) {
	seen_header := false
	rest := text
	current: [dynamic]Literal
	defer delete(current)
	// On any error, free the clauses parsed so far.
	defer if err != nil {formula_destroy(&f)}

	for line in strings.split_lines_iterator(&rest) {
		if len(line) == 0 || strings.starts_with(line, "c") {
			// skip blank lines and comments
			continue
		}

		if strings.starts_with(line, "%") {
			break
		}
		// Header: "p cnf <num_vars> <num_clauses>". The third word is num_vars.
		if strings.starts_with(line, "p") {
			header := line
			count := 0
			for w in strings.fields_iterator(&header) {
				count += 1
				if count == 3 {
					n, ok := strconv.parse_int(w)
					if !ok || n < 0 {return f, .Bad_Header}
					f.num_vars = u32(n)
					break
				}
			}
			if count < 3 {return f, .Bad_Header}
			seen_header = true
			continue
		}
		// Every line that reaches here is a clause line.
		if !seen_header {return f, .Missing_Header}

		words := line
		for word in strings.fields_iterator(&words) {
			lit, ok := strconv.parse_int(word)
			if !ok {return f, .Bad_Literal}
			if lit == 0 {
				// finish the current clause
				append(&f.clauses, current[:])
				current = {}
			} else {
				if abs(lit) > int(f.num_vars) {return f, .Literal_Out_Of_Range}
				append(&current, lit_from_dimacs(lit))
			}
		}
	}
	if len(current) > 0 {
		return f, .Unterminated_Clause
	}
	return f, nil
}

// parse_dimacs reads a DIMACS CNF file. On success the caller owns the returned
// formula and must free it with formula_destroy. On error the returned formula is empty.
parse_dimacs :: proc(path: string) -> (f: Formula, err: Parse_Error) {
	data, read_error := os.read_entire_file(path, context.allocator)
	if read_error != nil {
		return {}, .File_Read
	}
	defer delete(data)

	return parse_dimacs_string(string(data))
}
