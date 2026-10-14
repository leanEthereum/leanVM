import WhirAeneas.NativeCompose
import Lean.Util.CollectAxioms

/-! Axiom audit of the composed native theorem and everything it rests on: the replay and Merkle
extractions, their proofs, the Merkle opening composition and binding, and the link. -/

#print axioms WhirAeneas.Native.verify_refines_native
#print axioms WhirAeneas.Native.verify_eq_native
#print axioms WhirAeneas.Native.ensure_native
#print axioms WhirAeneas.Native.clone_native
#print axioms WhirAeneas.Native.limbs_injective
#print axioms WhirAeneas.Native.root_shape
#print axioms WhirAeneas.Native.root_shapes
#print axioms WhirAeneas.NativeReads.native_transcript
#print axioms WhirAeneas.NativeReads.check_pow_ok
#print axioms WhirAeneas.NativeReads.queries_ok
#print axioms WhirAeneas.Native.level_hints
#print axioms WhirAeneas.Native.authenticated_native
#print axioms WhirAeneas.Replay.verify_eq
#print axioms WhirAeneas.Replay.nativeVerify_withOracles
#print axioms WhirAeneas.Replay.authenticated_withOracles
#print axioms WhirAeneas.MerkleNative.open_rows_ok
#print axioms WhirAeneas.MerkleNative.hint_binding
#print axioms WhirAeneas.MerkleNative.open_rows_eq
#print axioms WhirAeneas.Merkle.open_eq
#print axioms WhirAeneas.Merkle.expand_eq
#print axioms WhirAeneas.Merkle.push_path_eq
#print axioms WhirAeneas.Merkle.pairSpec_struct
#print axioms WhirAeneas.Merkle.rebuildSpec_struct
#print axioms WhirAeneas.Merkle.rebuildSpec_tree
#print axioms WhirAeneas.Merkle.openSpec_accepts
#print axioms WhirAeneas.Merkle.openSpec_binding
#print axioms ReplaySource.verifier.open_rows_native
#print axioms WhirAeneas.NativeReads.nativeInst
#print axioms ReplaySource.whir.verify.verify

open Lean in
run_cmd do
  let environment ← getEnv
  let prefixes := [`WhirAeneas.Native, `WhirAeneas.NativeReads, `WhirAeneas.Merkle, `WhirAeneas.MerkleNative,
    `WhirAeneas.Replay, `WhirAeneas.Fold, `WhirAeneas.Query, `WhirAeneas.Sampling, `ReplaySource]
  let mut count : Nat := 0
  for (declarationName, declarationInfo) in environment.constants.toList do
    if prefixes.any (·.isPrefixOf declarationName) then
      match declarationInfo with
      | .thmInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
        count := count + 1
      | .axiomInfo _ => throwError "project declares an axiom: {declarationName}"
      | .defnInfo _ =>
        let axioms ← collectAxioms declarationName
        for axiomName in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom in {declarationName}: {axiomName}"
      | _ => pure ()
  unless count > 0 do
    throwError "no theorems audited"
  logInfo m!"Audited {count} replay, Merkle and native theorems; only propext, Classical.choice and Quot.sound permitted."
