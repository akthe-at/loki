#!/usr/bin/env bash
# Build loki with optimizations and run it over benchmark sets in bench/.
# Usage: scripts/bench.sh [set ...]            (default: every set in bench/)
# Env:   TIMEOUT=60   seconds allowed per file
#        LIMIT=0      only run the first N files of each set (0 = all)
#
# Expected answers come from the set name: uf* = Sat, uuf* = Unsat.
set -uo pipefail

cd "$(dirname "$0")/.."

TIMEOUT="${TIMEOUT:-60}"
LIMIT="${LIMIT:-0}"
BIN="build/loki_bench"

mkdir -p build
echo "building $BIN (-o:speed)..."
odin build cmd/loki -o:speed -out:"$BIN" || exit 1

if [ $# -gt 0 ]; then
	sets=("$@")
else
	mapfile -t sets < <(find bench -mindepth 1 -maxdepth 1 -type d -printf '%f\n' | sort)
fi
if [ ${#sets[@]} -eq 0 ]; then
	echo "no benchmark sets found; run scripts/fetch_bench.sh first"
	exit 1
fi

printf '\n%-14s %6s %6s %9s %10s %10s %14s\n' set files wrong timeouts total_ms avg_ms avg_conflicts
any_wrong=0
for set in "${sets[@]}"; do
	case "$set" in
		uuf*) expect=Unsat ;;
		uf*)  expect=Sat ;;
		*)    expect="" ;;
	esac

	mapfile -t files < <(find "bench/$set" -name '*.cnf' | sort)
	if [ "$LIMIT" -gt 0 ]; then files=("${files[@]:0:$LIMIT}"); fi

	n=0 wrong=0 timeouts=0 total_ms=0 conflicts=0 solved=0
	for f in "${files[@]}"; do
		n=$((n + 1))
		start=$(date +%s%N)
		out=$(timeout "$TIMEOUT" "$BIN" "$f" 2>&1)
		rc=$?
		end=$(date +%s%N)
		total_ms=$((total_ms + (end - start) / 1000000))

		if [ $rc -eq 124 ]; then
			timeouts=$((timeouts + 1))
			continue
		fi
		result=$(awk '/^result:/ {print $2}' <<<"$out")
		if grep -q FAILED <<<"$out" || { [ -n "$expect" ] && [ "$result" != "$expect" ]; }; then
			wrong=$((wrong + 1))
			echo "  WRONG: $f (got '$result', expected '$expect')"
		fi
		c=$(awk '/^conflicts:/ {print $2}' <<<"$out")
		conflicts=$((conflicts + ${c:-0}))
		solved=$((solved + 1))
	done

	[ $wrong -gt 0 ] && any_wrong=1
	avg_ms=$(( n > 0 ? total_ms / n : 0 ))
	avg_conf=$(( solved > 0 ? conflicts / solved : 0 ))
	printf '%-14s %6d %6d %9d %10d %10d %14d\n' "$set" "$n" "$wrong" "$timeouts" "$total_ms" "$avg_ms" "$avg_conf"
done

exit $any_wrong
