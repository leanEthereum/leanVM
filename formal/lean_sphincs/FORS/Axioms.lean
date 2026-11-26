import FORS

/-!
Axiom guards. The `#print axioms` below pin the main theorem; the last command checks every
declaration of every `FORS` module (`FORS.lean` imports all of them) and fails if one depends on an
axiom other than `propext`, `Classical.choice` and `Quot.sound`, such as the one an unfinished proof
or a compiled decision procedure adds.
-/

/-- info: 'FORS.h26_layered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FORS.h26_layered

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless (`FORS).isPrefixOf env.header.moduleNames[i] do continue
    for name in env.header.moduleData[i]!.constNames do
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do bad := bad.push (name, axiomName)
  unless bad.isEmpty do
    throwError m!"declarations with axioms outside propext, Classical.choice, Quot.sound: {bad.toList}"
