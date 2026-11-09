module

public import LeanDa.RpmCodeBinding
public import LeanDa.HashOracle
public import LeanDa.MerkleM
public import PqDas.Target.Scheme
public import LeanDa.Defs
public import LeanDa.WithHash

@[expose] public section

/-!
# Completeness in the random-permutation model

LeanDA is perfectly complete for every permutation `π` of the Keccak state: with the hash
Keccak-256 over `π` (`keccak256WithPermutation π`), the membership challenges the deployed duplex over `π`, and
the argument's prover and verifier answered by `π`, every position of every message's honest
commitment opens and verifies (`leanDa_perfectlyComplete_rpmH : PerfectlyCompleteRpmH`).

The proof is a transfer of Benedikt Wagner's completeness proof (`PqDas.scheme_perfectlyComplete`):
the honest run verifies from the completeness of the Merkle commitment (`verifyCell_openCell`),
of the membership test (`checker_complete`, so the honest cells satisfy the relation for `π`
whatever the root's challenges) and of the argument, which, its oracles answered by `π`, verifies
an honest proof of a statement true for `π` with probability one.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas
open scoped ENNReal

namespace LeanDa

/-! ## Completeness -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation**
(Benedikt Wagner's completeness, transferred). For a fixed `π` the honest commitment's cells
satisfy the relation for `π` (they commit to the root, and a codeword passes the membership test
on every challenge, `checker_complete`), so the argument's honest proof verifies with probability
one; and the honest opening verifies (`verifyCell_openCell`, `verifyCellM_id`). -/
theorem leanDa_perfectlyComplete_rpmH : PerfectlyCompleteRpmH := by
  intro r π Crs Proof ps hps msg p
  rw [OracleComp.prEvent_eq_one_iff]
  intro b hb
  simp only [completenessExpRpmH, support_bind, Set.mem_iUnion, support_pure,
    Set.mem_singleton_iff, exists_prop] at hb
  obtain ⟨crs, hcrs, ok, hok, rfl⟩ := hb
  set c := (leanDaErasureCode r).encode msg
  have hcode : c ∈ (leanDaErasureCode r).code := ⟨msg, rfl⟩
  have hcomm : commitCellsMWithHash (m := Id) (fun a ↦ pure (keccak256WithPermutation π a)) c =
      pure (commitCellsWithHash (keccak256WithPermutation π) c) :=
    commitCellsM_eval (fun x ↦ x) (fun _ ↦ rfl) (fun _ _ ↦ rfl) _ _ (fun _ ↦ rfl) c
  have hrel : relationForPermutationWithHash r π (commitCellsWithHash (keccak256WithPermutation π) c) c = true := by
    unfold relationForPermutationWithHash relationMWithHash
    rw [hcomm]
    simp only [Id.run_bind, Id.run_pure, decide_true, Bool.true_and]
    exact decide_eq_true_iff.mpr fun i ↦ dot_dual_eq_zero ((mem_code_iff c).mp hcode i) _
  have h1 := hps π crs hcrs _ _ hrel
  rw [OracleComp.prEvent_eq_one_iff] at h1
  rw [h1 ok hok, Bool.true_and, verifyCellM_id]
  exact verifyCell_openCell (keccak256WithPermutation π) c p

end LeanDa
