#!/usr/bin/env bash
# Build loki with optimizations and run it over benchmark sets in bench/,
# one solve at a time.
# Usage: scripts/bench.sh [set ...]            (default: every set in bench/)
# Env:   TIMEOUT=60   seconds allowed per file
#        LIMIT=0      only run the first N files of each set (0 = all)
#
# Expected answers, per file:
#   1. bench/expected.txt, if present (local, gitignored). One line per file:
#        <set>/<file>.cnf  Sat|Unsat      ('#' starts a comment)
#   2. otherwise the set name: uf* = Sat, uuf* = Unsat
#   3. otherwise unknown. A Sat answer is still verified by loki's model
#      self-check; an Unsat answer with no expectation counts as "unverified".
set -uo pipefail

cd "$(dirname "$0")/.."

TIMEOUT="${TIMEOUT:-60}"
LIMIT="${LIMIT:-0}"
BIN="build/loki_bench"
EXPECTED_FILE="bench/expected.txt"

mkdir -p build
echo "building $BIN (-o:speed)..."
odin build cmd/loki -o:speed -out:"$BIN" || exit 1

declare -A expected=()
if [ -f "$EXPECTED_FILE" ]; then
	while read -r key answer _; do
		[[ -z "$key" || "$key" == \#* ]] && continue
		expected["$key"]="$answer"
	done <"$EXPECTED_FILE"
	echo "loaded ${#expected[@]} expected answers from $EXPECTED_FILE"
fi

if [ $# -gt 0 ]; then
	sets=("$@")
else
	mapfile -t sets < <(find bench -mindepth 1 -maxdepth 1 -type d -printf '%f\n' | sort)
fi
if [ ${#sets[@]} -eq 0 ]; then
	echo "no benchmark sets found; run scripts/fetch_bench.sh first"
	exit 1
fi

printf '\n%-14s %6s %5s %5s %6s %10s %9s %10s %10s %14s\n' \
	set files sat unsat wrong unverified timeouts total_ms avg_ms avg_conflicts
any_wrong=0
for set in "${sets[@]}"; do
	case "$set" in
		uuf*) set_expect=Unsat ;;
		uf*)  set_expect=Sat ;;
		*)    set_expect="" ;;
	esac

	mapfile -t files < <(find "bench/$set" -name '*.cnf' | sort)
	if [ "$LIMIT" -gt 0 ]; then files=("${files[@]:0:$LIMIT}"); fi

	n=0 sat=0 unsat=0 wrong=0 unverified=0 timeouts=0 total_ms=0 conflicts=0 solved=0
	for f in "${files[@]}"; do
		n=$((n + 1))
		expect="${expected[${f#bench/}]:-$set_expect}"

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
		case "$result" in
			Sat)   sat=$((sat + 1)) ;;
			Unsat) unsat=$((unsat + 1)) ;;
		esac
		if grep -q FAILED <<<"$out" || { [ -n "$expect" ] && [ "$result" != "$expect" ]; }; then
			wrong=$((wrong + 1))
			echo "  WRONG: $f (got '$result', expected '${expect:-a valid model}')"
		elif [ -z "$expect" ] && [ "$result" != Sat ]; then
			unverified=$((unverified + 1))
		fi
		c=$(awk '/^conflicts:/ {print $2}' <<<"$out")
		conflicts=$((conflicts + ${c:-0}))
		solved=$((solved + 1))
	done

	[ $wrong -gt 0 ] && any_wrong=1
	avg_ms=$(( n > 0 ? total_ms / n : 0 ))
	avg_conf=$(( solved > 0 ? conflicts / solved : 0 ))
	printf '%-14s %6d %5d %5d %6d %10d %9d %10d %10d %14d\n' \
		"$set" "$n" "$sat" "$unsat" "$wrong" "$unverified" "$timeouts" "$total_ms" "$avg_ms" "$avg_conf"
done

exit $any_wrong
