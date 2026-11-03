import Lean

/-!
# Test support

`#reject "text" in cmd` elaborates the command `cmd` and succeeds when `cmd`
fails with an error mentioning `text`; the command's messages are dropped. A
test file can thereby state the claims a tactic must not prove next to the ones
it must, and still compile. As with `#guard_msgs`, the messages of the tasks
the command spawns (a theorem's proof, elaborated in parallel) are waited for
and included.
-/

open Lean Elab Command

syntax (name := reject) "#reject " str " in " command : command

@[command_elab reject] def elabReject : CommandElab
  | `(#reject $text in $cmd) => do
    let (messages, tasks) ← modifyGet fun s =>
      ((s.messages, s.snapshotTasks), {s with messages := {}, snapshotTasks := #[]})
    -- (no incremental reporting: the command's messages must not escape)
    withReader ({· with snap? := none}) do
      elabCommand cmd
    let produced := (← get).messages ++
      (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) {}) {}
    modify fun s => {s with messages, snapshotTasks := tasks}
    let errors ← produced.toList.filterMapM fun m => do
      if m.severity == .error then return some (← m.toString) else return none
    if errors.isEmpty then
      throwError "#reject: the command succeeded"
    unless errors.any fun e => (e.splitOn text.getString).length > 1 do
      throwError "#reject: the command failed without mentioning \"{text.getString}\":\n{errors}"
  | _ => throwUnsupportedSyntax
