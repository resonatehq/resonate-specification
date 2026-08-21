#!/usr/bin/env bash
# Check the Quint machine.
#
#   ./check.sh                     types, then the state invariants, then the
#                                  step properties, by simulation
#   ./check.sh verify              the same invariants, exhaustively, with
#                                  Apalache, up to --max-steps
#   ./check.sh verify 4            ... to a shallower bound
#
# Simulation is the fast pass: it samples random behaviours and reports the
# first violation. `verify` is the real one, and it is slow -- the same story
# `tla/check.sh` tells about Apalache on this machine.
set -uo pipefail
cd "$(dirname "$0")"

STEPS=${2:-6}
BACKEND=${QUINT_BACKEND:-typescript}

echo "== types =="
quint typecheck requests.qnt      || exit 1
quint typecheck abstractAction.qnt || exit 1
quint typecheck trans.qnt          || exit 1
quint typecheck witnesses.qnt      || exit 1
echo "ok"

if [ "${1:-run}" = "verify" ]; then
    echo "== invariants, exhaustive to depth $STEPS =="
    quint verify abstractAction.qnt --invariant=allInvariants --max-steps="$STEPS"
    echo "== step properties, exhaustive to depth $STEPS =="
    quint verify trans.qnt --invariant=allStepProperties --max-steps="$STEPS"
    exit $?
fi

echo "== invariants =="
quint run abstractAction.qnt --backend="$BACKEND" --verbosity=1 \
      --max-steps=12 --max-samples=2000 \
      --invariants typeOk \
                   well_formed_promise_created_at_lte_timeout_at \
                   well_formed_promise_settled_at_iff_not_pending \
                   well_formed_promise_pending_has_no_value \
                   well_formed_promise_settled_at_lte_timeout_at \
                   well_formed_task_pending_iff_has_retry_at \
                   well_formed_task_acquired_iff_has_expires_at \
                   consistent_settled_promise_has_fulfilled_task \
                   consistent_settled_task_promise_settled \
                   consistent_task_iff_targeted_promise \
                   unitCoherent \
                   sameOrigin || exit 1

echo "== step properties =="
quint run trans.qnt --backend="$BACKEND" --verbosity=1 \
      --max-steps=12 --max-samples=2000 \
      --invariants preserved_settled_promise_record \
                   consistent_new_promise_born_clean \
                   consistent_promise_settlement_stamp \
                   consistent_settlement_fulfils_task || exit 1

# An invariant over an empty store holds and says nothing. Every line here is a
# state the machine had better reach; a 0% is a handler that never fired.
echo "== not vacuity =="
quint run witnesses.qnt --backend="$BACKEND" --verbosity=1 \
      --max-steps=16 --max-samples=8000 \
      --witnesses wAcquired wSuspended wHalted wFulfilled wCallback wListener \
                  wResumes wTimedout wTimerDone wResolved wExecute wUnblock \
                  wVersion2 wTicked wTwoObjects
