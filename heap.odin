#+private
package loki


Var_Heap :: struct {
	heap:  [dynamic]Var,
	index: []int,
}


heap_init :: proc(h: ^Var_Heap, num_vars: u32) {
	h.index = make([]int, num_vars)
	for &i in h.index {
		i = -1
	}
}

heap_destroy :: proc(h: ^Var_Heap) {
	delete(h.heap)
	delete(h.index)
}

heap_contains :: proc(h: ^Var_Heap, v: Var) -> bool {
	return h.index[v] >= 0
}

// before lets us know if a should be closer to the top of the heap than b:
// higher activity first, and on a tie, the lower-numbered variable.
before :: proc(act: []f64, a, b: Var) -> bool {
	return act[a] > act[b] || (act[a] == act[b] && a < b)
}

sift_up :: proc(h: ^Var_Heap, act: []f64, i: int) {
	i := i
	// take v out -- position i is now a "hole"
	v := h.heap[i]
	for i > 0 {
		parent := (i - 1) / 2
		if !before(act, v, h.heap[parent]) {
			break
		}
		// parent slides down into the hole
		h.heap[i] = h.heap[parent]
		// and the index follows it...
		h.index[h.heap[i]] = i
		// hole moves up
		i = parent
	}
	// v fills the hole.
	h.heap[i] = v
	h.index[v] = i
}

sift_down :: proc(h: ^Var_Heap, act: []f64, i: int) {
	i := i
	v := h.heap[i]
	n := len(h.heap)
	for {
		child := 2 * i + 1
		if child >= n {
			break
		}
		if child + 1 < n && before(act, h.heap[child + 1], h.heap[child]) {
			child += 1
		}
		if !before(act, h.heap[child], v) {
			break
		}
		h.heap[i] = h.heap[child]
		h.index[h.heap[i]] = i
		i = child
	}
	h.heap[i] = v
	h.index[v] = i
}

// heap_insert adds v to the heap. It does nothing if v is already in it.
heap_insert :: proc(h: ^Var_Heap, act: []f64, v: Var) {
	if heap_contains(h, v) {
		return
	}
	// v goes in the last slot, then rises to where it belongs.
	append(&h.heap, v)
	sift_up(h, act, len(h.heap) - 1)
}

// heap_increase restores the heap after v's activity went up.
// It does nothing if v is not in the heap.
heap_increase :: proc(h: ^Var_Heap, act: []f64, v: Var) {
	if heap_contains(h, v) {
		sift_up(h, act, h.index[v])
	}
}

// heap_pop_max removes and returns the best variable. The heap must not be empty.
heap_pop_max :: proc(h: ^Var_Heap, act: []f64) -> Var {
	top := h.heap[0]
	last := pop(&h.heap)
	h.index[top] = -1
	// If top was the only variable, last == top and the heap is now empty.
	// Otherwise move last into the top slot and let it sink.
	if len(h.heap) > 0 {
		h.heap[0] = last
		h.index[last] = 0
		sift_down(h, act, 0)
	}
	return top
}
