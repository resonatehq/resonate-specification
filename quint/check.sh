#!/usr/bin/env bash
# Check the Quint machines.
#
#   ./check.sh              types, the written-down traces, then simulation
#   ./check.sh verify 6     the abstract invariants, exhaustively, to depth 6
#
# Simulation samples random behaviours: it is fast, it finds violations, and it
# proves nothing. `verify` calls Apalache, which is exhaustive up to the step
# bound and slow -- the same trade `tla/check.sh` records, for the same reason.
#
# Two checks below are EXPECTED TO FAIL, and the failure is the result.
set -uo pipefail
cd "$(dirname "$0")"

STEPS=${2:-6}
SAMPLES=${SAMPLES:-20000}
DEPTH=${DEPTH:-30}
BACKEND=${QUINT_BACKEND:-rust}     # `typescript` needs no download

sim() {  # sim <file> <invariant> <expect: hold|fail> [samples]
    local file=$1 inv=$2 want=$3 n=${4:-$SAMPLES} out rc
    out=$(quint run "$file" --backend="$BACKEND" --verbosity=1 \
              --max-steps="$DEPTH" --max-samples="$n" --invariant="$inv" 2>&1)
    rc=$?
    if [ "$want" = hold ] && [ $rc -eq 0 ]; then echo "  ok      $inv"
    elif [ "$want" = fail ] && [ $rc -ne 0 ]; then echo "  ok      $inv violated, as expected"
    else echo "  FAILED  $inv (wanted to $want)"; echo "$out" | tail -20; return 1
    fi
}

echo "== types =="
for m in requests abstractAction concrete trans refine witnesses; do
    quint typecheck $m.qnt || exit 1
done
echo "  ok"

if [ "${1:-run}" = "verify" ]; then
    echo "== the protocol, exhaustive to depth $STEPS =="
    quint verify abstractAction.qnt --invariant=allInvariants --max-steps="$STEPS"
    quint verify trans.qnt --invariant=allStepProperties --max-steps="$STEPS"
    exit $?
fi

# Written-down traces. Random search will not walk this far: a dispatched
# message is ten aligned steps from an empty store, and the refinement
# counterexample is nine.
echo "== the traces =="
quint test concrete.qnt || exit 1
quint test refine.qnt   || exit 1

echo "== the protocol =="
sim abstractAction.qnt allInvariants     hold || exit 1
sim trans.qnt          allStepProperties hold || exit 1

echo "== the executor =="
sim concrete.qnt wheelComplete hold || exit 1
# Arming before writing admits an entry for an object that is not there yet.
# That is noise the handler re-checks away, and no fence removes it.
sim concrete.qnt wheelSound    fail || exit 1

echo "== the refinement =="
sim refine.qnt c_invariants   hold || exit 1
# A step sweeps what its document says is due AND handles its own request, and
# lands both in ONE write. Upstairs those are two steps. `quint test` above
# holds the trace, and the control beside it: with an empty sweep it holds.
# Nine steps deep, so it needs a long look -- `quint test` above is the one
# that does not depend on luck.
sim refine.qnt refinesAction  fail 200000 || exit 1

echo "== not vacuity =="
# An invariant over an empty store holds and says nothing. Every line here is a
# state the machine had better reach; a 0% is a handler that never fired.
quint run witnesses.qnt --backend="$BACKEND" --verbosity=1 \
      --max-steps="$DEPTH" --max-samples=8000 \
      --witnesses wAcquired wSuspended wHalted wFulfilled wCallback wListener \
                  wResumes wTimedout wTimerDone wResolved wExecute wUnblock \
                  wVersion2 wTicked wTwoObjects
