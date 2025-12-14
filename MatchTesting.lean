import Lean

open Lean Meta Elab Command

opaque opq : Nat → Nat

/-- A particular tricky inductive type -/
inductive T : Nat → Type where
  | mk1 : T 0
  | mk2 n : T n
  | mk3 n : T (n + 1)
  | mk4 n : T (opq n)
  | mk5 (x : T n) : T (n + 1)

/--
The result of analying a match statement. The constructors are ordered so that later ones should
take precendence, e.g. if there are multiple error messages.
 -/
inductive MatchClassification
  /-- The matcher was successfully generated and compiled, and equations were generated. -/
  | ok
  /-- The matcher was compiled, but congr equation generation failed. This is a bug. -/
  | congrEqnsFailed
  /-- The matcher was compiled, but equation generation failed. This is a bug. -/
  | eqnsFailed
  /-- The matcher is type correct, but failed to compile. This is a bug. -/
  | matcherFailed
  /-- The matcher is type incorrect. May or may not be a bug. -/
  | typeIncorrect
  /-- Could not classify error. Need to extend `classifyMessage`. -/
  | unexpected (msg : MessageData)

instance : ToMessageData MatchClassification where
  toMessageData
    | .ok => "Ok"
    | .typeIncorrect => "TypeIncorrect"
    | .matcherFailed => "MatcherFailed"
    | .eqnsFailed => "EqnsFailed"
    | .congrEqnsFailed => "CongrEqnsFailed"
    | .unexpected msg => m!"Unexpected: {msg}"

def classifyMessage (msg : MessageData) : BaseIO MatchClassification := do
  let msgStr ← msg.toString
  if msgStr.startsWith "Type mismatch" then
    return .typeIncorrect
  if msgStr.startsWith "failed to synthesize" then
    return .typeIncorrect
  if msgStr.startsWith "typeclass instance" then
    return .typeIncorrect
  if msgStr.startsWith "Tactic `cases` failed with a nested error:" then
    return .matcherFailed
  if msgStr.startsWith "Failed to realize constant test1.match_1.eq_1" then
    return .eqnsFailed
  if msgStr.startsWith "Unknown constant `test1.match_1.eq_1" then
    return .eqnsFailed
  if msgStr.startsWith "Unknown identifier `test1.match_1.eq_1" then
    return .eqnsFailed
  if msgStr.startsWith "Failed to realize constant test1.match_1.congr_eq_1" then
    return .congrEqnsFailed
  if msgStr.startsWith "Unknown identifier `test1.match_1.congr_eq_1" then
    return .congrEqnsFailed
  if msgStr.startsWith "Unknown constant `test1.match_1.congr_eq_1" then
    return .congrEqnsFailed
  return .unexpected msg
/--
Elaborates a command that contains a match statement, reads errors off the log and
categorizes them.
-/
def evalMatchCommand (cmds : TSyntaxArray `command) : CommandElabM MatchClassification := withoutModifyingEnv do
    -- Code cargo-culted from `Lean.Elab.Tactic.GuardMsgs.elabGuardMsgs`
    let messagesBefore := (← get).messages
    modify ({ · with messages := {} })
    -- do not forward snapshot as we don't want messages assigned to it to leak outside
    withReader ({ · with snap? := none }) do
      -- The `#guard_msgs` command is special-cased in `elabCommandTopLevel` to ensure linters only run once.
      cmds.forM elabCommand
    -- collect sync and async messages
    let msgs := (← get).messages ++
      (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) { : MessageLog}) {}
    -- clear async messages as we don't want them to leak outside
    modify ({ · with snapshotTasks := #[] })
    -- restore previous messages
    modify ({ · with messages := messagesBefore })
    let msgs := msgs.toArray.map (·.data)
    -- logInfo m!"msgs: {msgs}" -- useful for debugging
    let res ← msgs.mapM (classifyMessage ·)
    return res.getMax? (·.ctorIdx < ·.ctorIdx) |>.getD .ok

-- A small elaborator to use `evalMatchCommand` interactively

syntax withPosition("#test_match" (colGt command)+) : command
elab_rules : command | `(#test_match $[$cmds]*) => do
  let res ← evalMatchCommand cmds
  logInfo m!"Result: {res}"

-- Example usage, and tests to for the various classifications:

/-- info: Result: Ok -/
#guard_msgs in
#test_match
  def test1 : (n : Nat) → T n → Unit
    | 0, _ => ()
    | _, _ => ()
  def eqns := @test1.match_1.eq_1
  def congreqns := @test1.match_1.congr_eq_1

/-- info: Result: TypeIncorrect -/
#guard_msgs in
#test_match
  def test1 : (n : Nat) → T n → Unit
    | T.mk1, T.mk2 _ => ()
    | _, _ => ()
  def eqns := @test1.match_1.eq_1
  def congreqns := @test1.match_1.congr_eq_1

/-- info: Result: EqnsFailed -/
#guard_msgs in
#test_match
  def test1 : (n : Nat) → T n → Unit
    | 0, _ => ()
    | _, .mk4 _ => ()
    | _, _ => ()
  def eqns := @test1.match_1.eq_1
  def congreqns := @test1.match_1.congr_eq_1

/-- info: Result: MatcherFailed -/
#guard_msgs in
#test_match
   def test1 : (n : Nat) → T n → Unit
      | 0, _ => ()
      | 1, _ => ()
      | _, .mk4 _ => ()
      | _, _ => ()
  def eqns := @test1.match_1.eq_1
  def congreqns := @test1.match_1.congr_eq_1

set_option pp.sanitizeNames false -- we don't want daggers in the output below

-- A starting point for a simple random test generator

def patternFragments : Array (CoreM Term) := #[
    `(term| Nat.zero ),
    `(term| Nat.succ _),
    `(term| _ + 1),
    `(term| 0),
    `(term| 1000),
    `(term| T.mk1),
    `(term| T.mk2 _),
    `(term| T.mk3 _),
    `(term| T.mk4 _),
    `(term| T.mk5 _),
    `(term| x@_)
  ]


def randPat : (depth : Nat) → CoreM Term
  | 0 => `(term| _)
  | n+1 => do
    let patIdx ← IO.rand 0 (patternFragments.size -1)
    let pat ← patternFragments[patIdx]!
    TSyntax.mk <$> pat.raw.replaceM (fun s => match s with
      | `(term|_) => randPat n
      | _ => return s
    )

run_cmd
  let depth ← IO.rand 1 2
  let pat1 ← liftCoreM <| randPat depth
  let pat2 ← liftCoreM <| randPat  depth
  let mut decls := #[]
  decls := decls.push <| ← `(command|
    def test : (n : Nat) → T n → Unit
      | $pat1, $pat2 => ()
      | _, _ => ()
  )
  decls := decls.push <| ← `(command|
    def eqns := @test1.match_1.eq_1
  )
  decls := decls.push <| ← `(command|
    def congreqns := @test1.match_1.congr_eq_1
  )
  logInfo m!"Syntax:\n{m!"\n".joinSep (decls.toList.map toMessageData)}"
  let res ← evalMatchCommand decls
  logInfo m!"Result: {res}"
