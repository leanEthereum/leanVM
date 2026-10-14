import Whir
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let environment ← getEnv
  for moduleName in environment.header.moduleNames do
    if (`Whir).isPrefixOf moduleName then
      logInfo m!"Audited import: {moduleName}"
  let mut count : Nat := 0
  for (name, info) in environment.constants.toList do
    if (`Whir).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {name}: {axiomName}"
        logInfo m!"{name}: {axioms}"
        count := count + 1
      | .axiomInfo _ => throwError "project declares an axiom: {name}"
      | _ => pure ()
  unless count > 0 do
    throwError "no project theorems audited"
  logInfo m!"Audited {count} Whir theorems; only propext, Classical.choice and Quot.sound permitted."
