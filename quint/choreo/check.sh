#!/usr/bin/env bash
# Check the two Choreo machines.
#
#   ./check.sh
#
# `abstract.qnt` is the specification: a server that handles a request when one
# arrives and does its background work when that is enabled. `concrete.qnt` is
# one way of running it: a server that keeps the store and workers that keep
# nothing. They share no line of code, and the second one has continuations
# because it has to.
set -uo pipefail
cd "$(dirname "$0")"

SAMPLES=${SAMPLES:-20000}

echo "== types =="
for m in abstract concrete; do quint typecheck $m.qnt || exit 1; done
echo "  ok"

echo "== the specification =="
quint run abstract.qnt --verbosity=1 --max-steps=20 --max-samples="$SAMPLES" \
      --invariants callbacksOnlyOnKnownPromises runnableIsLive || exit 1
quint run abstract.qnt --verbosity=1 --max-steps=20 --max-samples="$SAMPLES" \
      --witnesses someoneSettled someoneWaited someoneDrained || exit 1

echo "== the implementation =="
# The specification's one law, asked of a machine that continues executions on
# machines that never began them.
quint run concrete.qnt --verbosity=1 --max-steps=25 --max-samples="$SAMPLES" \
      --invariant=observationsAreTruthful || exit 1
# What fragmenting an execution looks like, and what it costs.
quint run concrete.qnt --verbosity=1 --max-steps=40 --max-samples="$SAMPLES" \
      --witnesses fragmentsSplit inTheStoreAndNowhereElse \
                  sameFragmentTwice rerunDecidedDifferently stranded
