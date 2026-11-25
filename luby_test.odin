#+private
package loki

import "core:testing"

// luby is private, so its test lives in package loki (run with `odin test .`).
// The sequence is 1-based: luby(1) = 1. It had a bug history in Lesson 10.
@(test)
luby_first_values :: proc(t: ^testing.T) {
	want := [15]int{1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8}
	for w, i in want {
		testing.expectf(t, luby(i + 1) == w, "luby(%d) = %d, want %d", i + 1, luby(i + 1), w)
	}
}

// Each power of two first appears at i = 2^k - 1.
@(test)
luby_powers_of_two :: proc(t: ^testing.T) {
	for k in 0 ..< 10 {
		i := (1 << uint(k + 1)) - 1
		want := 1 << uint(k)
		testing.expectf(t, luby(i) == want, "luby(%d) = %d, want %d", i, luby(i), want)
	}
	testing.expect_value(t, luby(31), 16)
}
