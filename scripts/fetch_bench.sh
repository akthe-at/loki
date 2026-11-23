#!/usr/bin/env bash
# Download SATLIB uniform random 3-SAT benchmark sets into bench/.
# Usage: scripts/fetch_bench.sh [set ...]     (default: all sets below)
# "uf" sets are all satisfiable, "uuf" sets are all unsatisfiable.
set -euo pipefail

cd "$(dirname "$0")/.."

BASE_URL="https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT"
DEFAULT_SETS=(uf20-91 uf50-218 uuf50-218 uf150-645 uf250-1065 uuf250-1065)
sets=("${@:-${DEFAULT_SETS[@]}}")

for set in "${sets[@]}"; do
	dir="bench/$set"
	if [ -d "$dir" ] && [ -n "$(find "$dir" -name '*.cnf' -print -quit)" ]; then
		echo "$set: already present, skipping"
		continue
	fi
	echo "$set: downloading..."
	mkdir -p "$dir"
	curl -sSL --fail --max-time 120 -o "$dir/$set.tar.gz" "$BASE_URL/$set.tar.gz"
	tar xzf "$dir/$set.tar.gz" -C "$dir"
	rm "$dir/$set.tar.gz"
	echo "$set: $(find "$dir" -name '*.cnf' | wc -l) files"
done
