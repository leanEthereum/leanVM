import WhirAeneas.Merkle
import WhirAeneas.MerkleNative
import Lean.Util.CollectAxioms

/-! Axiom audit of the Merkle opening extraction and its proofs. `WhirAeneas.NativeAudit` audits
them together with the replay and the composed native theorem. -/

#print axioms ReplaySource.merkle.PrunedMerklePaths.from_hint
#print axioms ReplaySource.merkle.PrunedMerklePaths.open
#print axioms WhirAeneas.Merkle.from_hint_some
#print axioms WhirAeneas.Merkle.from_hint_none
#print axioms WhirAeneas.Merkle.pair_level_loop_eq
#print axioms WhirAeneas.Merkle.rebuild_eq
#print axioms WhirAeneas.Merkle.position_loop_eq
#print axioms WhirAeneas.Merkle.node_position_loop_eq
#print axioms ReplaySource.verifier.open_rows_native
#print axioms WhirAeneas.MerkleNative.from_le_to_le
#print axioms WhirAeneas.MerkleNative.to_le_four
#print axioms WhirAeneas.MerkleNative.decode_prefix
#print axioms WhirAeneas.MerkleNative.next_ok
#print axioms WhirAeneas.MerkleNative.next_none
#print axioms WhirAeneas.MerkleNative.prover_hint_ok
#print axioms WhirAeneas.MerkleNative.prover_hint_missing
#print axioms WhirAeneas.MerkleNative.prover_hint_poisoned
#print axioms WhirAeneas.MerkleNative.prover_hint_with_ok
#print axioms WhirAeneas.MerkleNative.prover_hint_with_err
#print axioms WhirAeneas.MerkleNative.closure_eq
#print axioms WhirAeneas.MerkleNative.image_eq
#print axioms WhirAeneas.MerkleNative.rowsOf_length
#print axioms WhirAeneas.MerkleNative.rows_loop_eq
#print axioms WhirAeneas.MerkleNative.rows_eq
#print axioms WhirAeneas.MerkleNative.shl_one_val
#print axioms WhirAeneas.MerkleNative.decodeOpen_eq
#print axioms WhirAeneas.MerkleNative.authenticate_eq
#print axioms WhirAeneas.MerkleNative.authenticate_err
#print axioms WhirAeneas.MerkleNative.open_rows_eq
#print axioms WhirAeneas.MerkleNative.open_rows_missing
#print axioms WhirAeneas.MerkleNative.open_rows_poisoned

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (declarationName, declarationInfo) in environment.constants.toList do
    if (`WhirAeneas.Merkle).isPrefixOf declarationName || (`WhirAeneas.MerkleNative).isPrefixOf declarationName ||
        (`ReplaySource.merkle).isPrefixOf declarationName || (`ReplaySource.verifier).isPrefixOf declarationName then
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
    throwError "no Merkle theorems audited"
  logInfo m!"Audited {count} Merkle theorems; only propext, Classical.choice and Quot.sound permitted."
