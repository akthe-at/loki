#!/usr/bin/env bash
# Download SATLIB benchmark sets into bench/ (gitignored).
# Usage: scripts/fetch_bench.sh [set|group ...]   (default: random)
#
# Groups:  random      uniform random 3-SAT (uf* = all Sat, uuf* = all Unsat)
#          structured  bmc ssa bf logistics blocksworld qg (some mixed Sat/Unsat)
#          all         both groups
# Single sets can be named too, e.g. `scripts/fetch_bench.sh bmc qg`.
#
# Structured sets have mixed answers that the set name cannot tell you.
# bench.sh reads them from bench/expected.txt if you create one (see bench.sh).
set -euo pipefail

cd "$(dirname "$0")/.."

BASE_URL="https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT"

RANDOM_SETS=(uf20-91 uf50-218 uuf50-218 uf150-645 uf250-1065 uuf250-1065)
STRUCTURED_SETS=(bmc ssa bf logistics blocksworld qg)

# Path of each set's archive under BASE_URL.
url_path() {
	case "$1" in
		uf*-* | uuf*-*) echo "RND3SAT/$1.tar.gz" ;;
		bmc)         echo "BMC/bmc.tar.gz" ;;
		ssa)         echo "DIMACS/SSA/ssa.tar.gz" ;;
		bf)          echo "DIMACS/BF/bf.tar.gz" ;;
		logistics)   echo "PLANNING/Logistics/logistics.tar.gz" ;;
		blocksworld) echo "PLANNING/BlocksWorld/blocksworld.tar.gz" ;;
		qg)          echo "QG/QG.tar.gz" ;;
		*)           return 1 ;;
	esac
}

sets=()
for arg in "${@:-random}"; do
	case "$arg" in
		random)     sets+=("${RANDOM_SETS[@]}") ;;
		structured) sets+=("${STRUCTURED_SETS[@]}") ;;
		all)        sets+=("${RANDOM_SETS[@]}" "${STRUCTURED_SETS[@]}") ;;
		*)          sets+=("$arg") ;;
	esac
done

for set in "${sets[@]}"; do
	if ! path=$(url_path "$set"); then
		echo "$set: unknown set (known: ${RANDOM_SETS[*]} ${STRUCTURED_SETS[*]})" >&2
		exit 1
	fi
	dir="bench/$set"
	if [ -d "$dir" ] && [ -n "$(find "$dir" -name '*.cnf' -print -quit)" ]; then
		echo "$set: already present, skipping"
		continue
	fi
	echo "$set: downloading..."
	mkdir -p "$dir"
	curl -sSL --fail --max-time 300 -o "$dir/$set.tar.gz" "$BASE_URL/$path"
	tar xzf "$dir/$set.tar.gz" -C "$dir"
	rm "$dir/$set.tar.gz"
	echo "$set: $(find "$dir" -name '*.cnf' | wc -l) files"
done
