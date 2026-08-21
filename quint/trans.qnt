/// THE STEP PROPERTIES. Four of the catalogue entries are about a PAIR of
/// consecutive states, not a state: what a step is allowed to do to a promise
/// that was already settled, what a promise is allowed to look like the moment
/// it appears, when a settlement stamp is legal, and what a settlement owes the
/// task beside it.
///
/// TLA+ writes those as `[][P]_vars` and reads `objects'` inside `P`. Quint has
/// no primed READ -- a variable may only be primed on the left of an assignment
/// -- so the previous state is carried in a variable instead. That is the whole
/// of this module: `abstractAction` is untouched, and `prevObjects` is a
/// spectator, written by every step and read by nothing the machine does.
///
/// The Quint reading of the `T_*` properties in `tla/AbstractAction.tla`.
module trans {
  import requests.* from "./requests"
  import abstractAction as A from "./abstractAction"

  var prevObjects: Id -> Object
  var prevNow: int

  action init = all {
    A::init,
    prevObjects' = Map(),
    prevNow'     = 0,
  }

  action step = all {
    A::step,
    prevObjects' = A::objects,
    prevNow'     = A::now,
  }

  // -------------------------------------------------------------------------

  /// A settled promise is a record, not a state: once it says what it came to,
  /// no step may say otherwise.
  pure def keptSettled(before: Object, after: Object): bool = and {
    after.promise.state     == before.promise.state,
    after.promise.settledAt == before.promise.settledAt,
    after.promise.value     == before.promise.value,
  }

  val preserved_settled_promise_record =
    prevObjects.keys().forall(i => or {
      prevObjects.get(i).promise.state == Pending,
      A::objects.keys().contains(i)
        and keptSettled(prevObjects.get(i), A::objects.get(i)),
    })

  /// A promise that has just appeared has no history: nobody is waiting on it,
  /// it carries no value, and it is either pending with its deadline ahead of
  /// it or settled exactly at the deadline it was already past.
  pure def bornClean(q: Promise, t: int): bool = and {
    q.callbacks == Set(),
    q.listeners == Set(),
    q.value == NoValue,
    q.createdAt <= t,
    or {
      and {
        q.state == Pending,
        q.settledAt == NoTime,
        q.createdAt < q.timeoutAt,
      },
      and {
        q.settledAt == q.timeoutAt,
        q.createdAt == q.timeoutAt,
        q.timeoutAt <= t,
        q.state == (if (q.tags.timer) Resolved else RejectedTimedout),
      },
    },
  }

  val consistent_new_promise_born_clean =
    A::objects.keys().forall(i => or {
      prevObjects.keys().contains(i),
      bornClean(A::objects.get(i).promise, prevNow),
    })

  /// A promise settles in exactly one of two ways, and the stamp says which:
  /// a request settled it NOW, before its deadline and not as a timeout -- or
  /// the DEADLINE settled it, at the deadline, with the value untouched.
  pure def settlementStamp(before: Promise, after: Promise, t: int): bool = or {
    after.state == Pending,
    and {
      after.settledAt == t,
      t < after.timeoutAt,
      after.state != RejectedTimedout,
    },
    and {
      after.settledAt == after.timeoutAt,
      after.timeoutAt <= t,
      after.state == (if (after.tags.timer) Resolved else RejectedTimedout),
      after.value == before.value,
    },
  }

  val consistent_promise_settlement_stamp =
    prevObjects.keys().forall(i => or {
      prevObjects.get(i).promise.state != Pending,
      A::objects.keys().contains(i)
        and settlementStamp(prevObjects.get(i).promise,
                            A::objects.get(i).promise, prevNow),
    })

  /// Settling a promise retires its task in the same step. There is no state in
  /// between, because there is no write in between.
  val consistent_settlement_fulfils_task =
    prevObjects.keys().forall(i => or {
      prevObjects.get(i).promise.state != Pending,
      not(A::objects.keys().contains(i)),
      A::objects.get(i).promise.state == Pending,
      Set(TaskNone, TaskFulfilled).contains(A::objects.get(i).task.state),
    })

  val allStepProperties = and {
    preserved_settled_promise_record,
    consistent_new_promise_born_clean,
    consistent_promise_settlement_stamp,
    consistent_settlement_fulfils_task,
  }
}
