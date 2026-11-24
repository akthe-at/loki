#!/usr/bin/env bash
# Compare loki configurations on benchmark sets, one solve at a time.
# Every config runs on a file before the next file starts, so background
# load on the machine hits all configs equally.
#
# Usage: scripts/compare.sh <label>:<ENV=VAL>[,<ENV=VAL>...] ... -- <set> ...
#   e.g. scripts/compare.sh on:LOKI_PHASE_SAVING=1 off:LOKI_PHASE_SAVING=0 -- uuf250-1065 bmc
# Env:   TIMEOUT=60   seconds allowed per solve (a timeout counts as TIMEOUT in totals)
#        LIMIT=0      only run the first N files of each set (0 = all)
#
# Expected answers are found the same way as in bench.sh (bench/expected.txt,
# then the uf/uuf set name). Per-file results go to build/compare-<time>.tsv.
set -uo pipefail

cd "$(dirname "$0")/.."

TIMEOUT="${TIMEOUT:-60}"
LIMIT="${LIMIT:-0}"
BIN="build/loki_bench"
EXPECTED_FILE="bench/expected.txt"

labels=() envs=()
while [ $# -gt 0 ] && [ "$1" != "--" ]; do
	case "$1" in
		*:*) labels+=("${1%%:*}"); envs+=("${1#*:}") ;;
		*)   echo "bad config '$1' (want label:ENV=VAL[,ENV=VAL])" >&2; exit 1 ;;
	esac
	shift
done
[ "${1:-}" = "--" ] && shift
sets=("$@")
if [ ${#labels[@]} -lt 1 ] || [ ${#sets[@]} -lt 1 ]; then
	sed -n '2,13p' "$0" | sed 's/^# \{0,1\}//'
	exit 1
fi

mkdir -p build
echo "building $BIN (-o:speed)..."
odin build cmd/loki -o:speed -out:"$BIN" || exit 1

declare -A expected=()
if [ -f "$EXPECTED_FILE" ]; then
	while read -r key answer _; do
		[[ -z "$key" || "$key" == \#* ]] && continue
		expected["$key"]="$answer"
	done <"$EXPECTED_FILE"
fi

tsv="build/compare-$(date +%Y%m%d-%H%M%S).tsv"
printf 'set\tfile\tconfig\tresult\tms\tconflicts\n' >"$tsv"

printf '\n%-14s %-10s %6s %10s %9s %6s  %s\n' set config files total_ms timeouts wrong slowest_file
any_wrong=0
for set in "${sets[@]}"; do
	case "$set" in
		uuf*) set_expect=Unsat ;;
		uf*)  set_expect=Sat ;;
		*)    set_expect="" ;;
	esac
	mapfile -t files < <(find "bench/$set" -name '*.cnf' | sort)
	if [ ${#files[@]} -eq 0 ]; then
		echo "$set: no files (run scripts/fetch_bench.sh $set)"
		continue
	fi
	if [ "$LIMIT" -gt 0 ]; then files=("${files[@]:0:$LIMIT}"); fi

	declare -A total=() tmo=() wrong=() slow_ms=() slow_f=()
	for f in "${files[@]}"; do
		expect="${expected[${f#bench/}]:-$set_expect}"
		for i in "${!labels[@]}"; do
			label="${labels[$i]}"
			IFS=',' read -ra kv <<<"${envs[$i]}"
			start=$(date +%s%N)
			out=$(env "${kv[@]}" timeout "$TIMEOUT" "$BIN" "$f" 2>&1)
			rc=$?
			end=$(date +%s%N)
			ms=$(((end - start) / 1000000))
			if [ $rc -eq 124 ]; then
				result=TIMEOUT
				ms=$((TIMEOUT * 1000))
				tmo[$label]=$((${tmo[$label]:-0} + 1))
			else
				result=$(awk '/^result:/ {print $2}' <<<"$out")
				if grep -q FAILED <<<"$out" || { [ -n "$expect" ] && [ "$result" != "$expect" ]; }; then
					wrong[$label]=$((${wrong[$label]:-0} + 1))
					echo "  WRONG [$label]: $f (got '$result', expected '${expect:-a valid model}')"
				fi
			fi
			total[$label]=$((${total[$label]:-0} + ms))
			if [ "$ms" -gt "${slow_ms[$label]:--1}" ]; then
				slow_ms[$label]=$ms
				slow_f[$label]=$(basename "$f")
			fi
			c=$(awk '/^conflicts:/ {print $2}' <<<"$out")
			printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$set" "$(basename "$f")" "$label" "$result" "$ms" "${c:--}" >>"$tsv"
		done
	done

	for label in "${labels[@]}"; do
		[ "${wrong[$label]:-0}" -gt 0 ] && any_wrong=1
		printf '%-14s %-10s %6d %10d %9d %6d  %s (%d ms)\n' "$set" "$label" "${#files[@]}" \
			"${total[$label]:-0}" "${tmo[$label]:-0}" "${wrong[$label]:-0}" "${slow_f[$label]}" "${slow_ms[$label]}"
	done
	unset total tmo wrong slow_ms slow_f
done

echo
echo "per-file results: $tsv"
exit $any_wrong
