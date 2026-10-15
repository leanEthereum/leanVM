import Sphincs.Lifetimes
import Sphincs.Axioms
import Lean

/-!
Theorem listing for the axiom guards of `Sphincs`. `lake env lean scripts/ForestTheorems.lean`
writes `forest_theorems.txt`: the public theorems of the `Sphincs` modules, one per line with
their module, sorted. `scripts/forest_axioms.py` turns it into `Sphincs/Axioms.lean`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.toString.startsWith "Sphincs." do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternalDetail then continue
    if isPrivateName n then continue
    let last := n.getString!
    if last.startsWith "eq_" || last == "eq_def" || last.startsWith "proof_" || last.startsWith "match_" then
      continue
    rows := rows.push s!"{mod} {n}"
  let sorted := rows.qsort (· < ·)
  IO.FS.writeFile "forest_theorems.txt" (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"{sorted.size} theorems"
