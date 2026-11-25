#+private
package loki

import "core:testing"

// heap_valid checks both invariants: every parent comes before its children,
// and index agrees with heap.
heap_valid :: proc(h: ^Var_Heap, act: []f64) -> bool {
	for v, i in h.heap {
		if h.index[v] != i {return false}
		if i > 0 && heap_before(act, v, h.heap[(i - 1) / 2]) {return false}
	}
	return true
}

@(test)
heap_pops_in_activity_order :: proc(t: ^testing.T) {
	act := []f64{3, 1, 4, 1, 5, 9, 2, 6}
	h: Var_Heap
	heap_init(&h, u32(len(act)))
	defer heap_destroy(&h)

	for v in 0 ..< len(act) {
		heap_insert(&h, act, Var(v))
	}
	testing.expect(t, heap_valid(&h, act))

	// 9, 6, 5, 4, 3, 2, then the tie at 1: lower variable first.
	want := []Var{5, 7, 4, 2, 0, 6, 1, 3}
	for w in want {
		testing.expect_value(t, heap_pop_max(&h, act), w)
		testing.expect(t, heap_valid(&h, act))
	}
	testing.expect_value(t, len(h.heap), 0)
}

@(test)
heap_increase_moves_var_up :: proc(t: ^testing.T) {
	act := []f64{3, 1, 4, 1, 5}
	h: Var_Heap
	heap_init(&h, u32(len(act)))
	defer heap_destroy(&h)
	for v in 0 ..< len(act) {
		heap_insert(&h, act, Var(v))
	}

	act[3] = 10
	heap_increase(&h, act, 3)
	testing.expect(t, heap_valid(&h, act))
	testing.expect_value(t, heap_pop_max(&h, act), Var(3))
}

@(test)
heap_contains_and_reinsert :: proc(t: ^testing.T) {
	act := []f64{2, 1}
	h: Var_Heap
	heap_init(&h, u32(len(act)))
	defer heap_destroy(&h)
	heap_insert(&h, act, 0)
	heap_insert(&h, act, 1)
	heap_insert(&h, act, 0) // already in: no duplicate
	testing.expect_value(t, len(h.heap), 2)

	top := heap_pop_max(&h, act)
	testing.expect_value(t, top, Var(0))
	testing.expect(t, !heap_contains(&h, 0))
	heap_insert(&h, act, 0)
	testing.expect(t, heap_contains(&h, 0))
	testing.expect(t, heap_valid(&h, act))
}
