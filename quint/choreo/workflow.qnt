/// THE PROGRAM, and nothing else. Both machines below run this and only this,
/// so any difference between them is a difference in the RUNTIME.
///
///     f() { val v = await g(); return v + 1 }
///     g() { return 41 }
module workflow {
  type Id = str

  pure val ROOT:  Id = "f"
  pure val CHILD: Id = "g"
  pure val IDS = Set(ROOT, CHILD)

  /// How far a program has got: the beginning, or the point just after an
  /// await that answered `v`.
  type Pc = Start | Resumed(int)

  /// A CONTINUATION. An invocation and where in it we are -- the whole of what
  /// has to survive from one piece of an execution to the next.
  ///
  /// The two specs run the same program over the same continuation type. All
  /// they disagree about is WHERE IT LIVES, and therefore how many machines one
  /// execution may touch.
  type Cont = { id: Id, pc: Pc }

  type Instr = Await(Id) | Return(int)

  /// What the program does next. (`run` is a Quint keyword, hence the name.)
  pure def proceed(c: Cont): Instr =
    match c.pc {
      | Start      => if (c.id == ROOT) Await(CHILD) else Return(41)
      | Resumed(v) => Return(v + 1)
    }

  pure val ANSWER = 42
}
