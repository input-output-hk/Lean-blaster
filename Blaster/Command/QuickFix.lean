import Lean

open Lean Server Lsp RequestM

namespace Blaster

/-- Drop the common leading indentation of `lines` (ignoring blank lines). -/
private def dedent (lines : List String) : List String :=
  let indent := lines.foldl
    (fun acc l => if l.trim.isEmpty then acc else min acc (l.takeWhile (· == ' ')).length)
    1000000
  lines.map (·.drop indent)

/-- Extract the replacement text of a rendered `Try this: <suggestion>`
    message: strip the header and the indentation the message renderer adds
    to the suggestion block. -/
private def suggestionText (msg : String) : String :=
  let body := msg.drop "Try this:".length
  let lines := (body.splitOn "\n").dropWhile (·.trim.isEmpty)
  String.intercalate "\n" (dedent lines) |>.trim

/-- Editor-side quick fix for `Try this:` suggestions.

    The builtin `tryThisProvider` looks for `TryThisInfo` nodes in the
    command's info tree, but commands elaborated inside async snapshot
    tasks (like `#blaster`) do not expose those nodes to the server, so
    only the InfoView link survives. This provider reconstructs the quick
    fix from the reported `Try this:` diagnostic itself: its range is
    exactly the invocation to replace and its rendered message carries the
    replacement text. The action is linked to the diagnostic, so editors
    offer it directly from the diagnostic hover box as well. -/
@[code_action_provider]
def tryThisQuickFixProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let diags ← doc.diagnosticsRef.get
  let mut acts := #[]
  for d in diags do
    unless d.severity? == some .information do continue
    let str := d.message.stripTags
    unless str.startsWith "Try this:" do continue
    -- only offer the fix when the request touches the suggestion's lines
    unless d.range.start.line ≤ params.range.end.line &&
           params.range.start.line ≤ d.range.end.line do continue
    let newText := suggestionText str
    if newText.isEmpty then continue
    let firstLine := (newText.splitOn "\n").headD newText
    let title := s!"Try this: {firstLine}{if newText.contains '\n' then " …" else ""}"
    acts := acts.push {
      eager := {
        title
        kind? := "quickfix"
        isPreferred? := true
        -- link the action to the diagnostic so the editor offers it from
        -- the diagnostic hover box as well
        diagnostics? := some #[{
          range := d.range
          severity? := d.severity?
          message := str
        }]
        edit? := some <| .ofTextEdit doc.versionedIdentifier
          { range := d.range, newText }
      }
    }
  return acts

end Blaster
