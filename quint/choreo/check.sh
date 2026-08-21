#!/usr/bin/env bash
# Check the two Choreo machines.
#
#   ./check.sh
#
# `abstract.qnt` runs the program with one process per invocation; `concrete.qnt`
# fragments the same program across a server and two workers. Both run
# `workflow.qnt` and nothing else, so every difference is a difference in the
# runtime.
set -uo pipefail
cd "$(dirname "$0")"

SAMPLES=${SAMPLES:-20000}
DEPTH=${DEPTH:-25}

echo "== types =="
for m in workflow abstract concrete; do quint typecheck $m.qnt || exit 1; done
echo "  ok"

echo "== the traces =="
quint test abstract.qnt --match executionTest  || exit 1
quint test concrete.qnt --match fragmentedTest || exit 1

echo "== the abstract machine =="
quint run abstract.qnt --verbosity=1 --max-steps=15 --max-samples="$SAMPLES" \
      --invariants noWrongAnswer continuationStaysHome || exit 1
quint run abstract.qnt --verbosity=1 --max-steps=15 --max-samples="$SAMPLES" \
      --witnesses answered || exit 1

echo "== the concrete machine =="
quint run concrete.qnt --verbosity=1 --max-steps="$DEPTH" --max-samples="$SAMPLES" \
      --invariant=noWrongAnswer || exit 1
# What fragmenting an execution buys, and what it costs. The first two are the
# point; the last two are the price, and neither is expressible upstairs.
quint run concrete.qnt --verbosity=1 --max-steps="$DEPTH" --max-samples="$SAMPLES" \
      --witnesses answered fragmentsSplit inTheStoreAndNowhereElse \
                  sameFragmentTwice stranded
