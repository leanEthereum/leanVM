module

public meta import RustcIngest.Core
public meta import Lean.Elab.Command
public meta import Lean.Parser.Module

namespace Ingest

open Lean Elab Command

public meta section

/-- Parse the generated module body in the importing module's environment. -/
def elaborateSource (path source : String) : CommandElabM Unit := do
  let input := Parser.mkInputContext source path
  let (_, initial, messages) ← Parser.parseHeader input
  if messages.hasErrors then
    throwError "invalid generated module header: {path}"
  let mut state := initial
  repeat
    let (command, next, messages) := Parser.parseCommand input
      { env := ← getEnv, options := ← getOptions } state {}
    if messages.hasErrors then
      for message in messages.toList do
        logError (← message.data.toString)
      throwError "invalid generated command in {path}"
    if Parser.isTerminalCommand command then break
    withReader (fun context => { context with fileName := path, fileMap := input.fileMap }) do
      elabCommand command
    state := next

/-- Function modules parse only their function; aggregate modules check the whole program. -/
def filesForModule {I C : Type} [ToExpr I] [ToExpr C] [BEq I] [BEq C]
    (arch : Arch I C) (env : Environment) (names : Std.HashMap String String)
    (inputs : Array (String × String)) (path : String) : IO (Array File) := do
  let pieces := (path.splitOn "/").toArray
  if pieces.size ≥ 4 then
    let dir := pieces[2]!
    let name := (pieces[3]!.splitOn ".").head!
    if name != "Names" && name != "Offsets" && name != "Labels" then
      let mut selected : Option (Fn I C) := none
      for (scheme, text) in inputs do
        if dir != "Common" && dir != capitalize scheme then continue
        let functions ← IO.ofExcept (functions (text.splitOn "\n").toArray)
        let some function := functions.find? (fun f => (names[f.name]? <|> shortName f.name) == some name)
          | throw <| IO.userError s!"{scheme}: missing function {name}"
        let function ← ingestFunction arch env names function
        if let some previous := selected then
          unless previous.lines == function.lines && previous.prog == function.prog do
            throw <| IO.userError s!"{function.sym} differs between schemes"
        selected := some function
      let some function := selected | throw <| IO.userError s!"missing function for {path}"
      return (fnModules arch dir function).1
  let schemes ← inputs.mapM fun (scheme, text) => ingestScheme arch env names scheme text
  emit arch env schemes

/-- The assembly is a Lake-tracked input of every reader module. -/
def elaborateModule {I C : Type} [ToExpr I] [ToExpr C] [BEq I] [BEq C]
    (base : Arch I C) (target ns path : String) : CommandElabM Unit := do
  let arch := { base with ns, labels := true }
  let assembly ← IO.FS.readFile s!"rustc/asm/signatures-{target}.s"
  let inputs := #[("sphincs", assembly)]
  let files ← filesForModule arch (← getEnv) {} inputs path
  let some (_, source) := files.find? (fun file => file.1 == path)
    | throwError "assembly no longer produces module {path}; run rustc/ingest/wrappers.sh"
  elaborateSource path source

end

end Ingest
