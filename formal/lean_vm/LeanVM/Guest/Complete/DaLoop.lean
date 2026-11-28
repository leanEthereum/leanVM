module

public import LeanVM.Guest.Complete.DaBlob
import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_loop0»

/-!
# `da_verify`'s blob loop, complete

`da_verify_loop0` takes no words itself; each iteration's blob check takes its region
(`da_verify_blob_completes`), placed one after another. From the counter `g^i`, `i < r`, on the
weights table and the blob roots' slots (`DvLPre`), it pops blobs `i ..< r`'s cells' symbols
(`dv_loop_completes`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Guest.B1.Digest LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value

@[expose] public section

set_option linter.constructorNameAsVariable false

/-- The blob loop's block. -/
def dvLPre : List Stmt := [
  .call "da_verify_blob" [.n 2] [.n 4, .n 5],
  .atom (.mul (.n 6) (.n 0) (.n 0)),
  .atom (.mul (.n 7) (.n 3) (.n 6)),
  .atom (.load (.n 4) (.n 7) 0),
  .atom (.load (.n 5) (.n 7) 1),
  .atom (.const (.n 8) (word 2 0)),
  .atom (.mul (.n 9) (.n 0) (.n 8)),
  .atom (.add (.n 10) (.n 9) (.n 1)),
  .atom (.const (.n 11) (word 2 0)),
  .atom (.mul (.n 12) (.n 0) (.n 11)),
  .callIf (.n 10) name% «da_verify_loop0» [.n 12, .n 1, .n 2, .n 3]]

theorem dvL_body : (fn% «da_verify_loop0»).body = dvLPre ++ [.ret []] := rfl
theorem dvL_params : (fn% «da_verify_loop0»).params = [.n 0, .n 1, .n 2, .n 3] := rfl

set_option maxRecDepth 100000 in
theorem find_dvL : coreProgram.find? name% «da_verify_loop0» = some fn% «da_verify_loop0» :=
  coreProgram_find?_at (j := idx% «da_verify_loop0») rfl

/-- Iteration `i`'s valuation, `root` its blob's. -/
noncomputable def dvLσ (i r : ℕ) (wt roots : E) (root : E × E) : Val := fun v =>
  [gen ^ i, gen ^ r, wt, roots, root.1, root.2, gen ^ i * gen ^ i, roots * (gen ^ i * gen ^ i), word 2 0,
    gen ^ i * word 2 0, gen ^ i * word 2 0 + gen ^ r, word 2 0, gen ^ i * word 2 0].getD v.idx 0

/-- What the blob loop reads: the weights table, and blob `j`'s root at `roots·g^(2j)`. -/
def DvLPre (z : E) (r : ℕ) (syms : ℕ → ℕ → List E) (wt roots : E) (rd : Reader) : Prop :=
  WeightsHold rd z wt ∧
    ∀ j < r, ReadsAt rd (roots * gen ^ (2 * j)) [(blobRoot (syms j)).1, (blobRoot (syms j)).2]

/-- The blobs' entries: each blob's cells' symbols. -/
def dvPops (syms : ℕ → ℕ → List E) (i n : ℕ) : List Pop :=
  (List.range' i n).flatMap fun j => (List.range 128).map fun h => ("da_symbols", syms j h)

/-- The blob loop from `g^i` pops blobs `i ..< r`'s cells' symbols. -/
def DvLPost (syms : ℕ → ℕ → List E) (i r : ℕ) (rd : Reader) (t : Tree) : Prop :=
  t.pops coreProgram rd = dvPops syms i (r - i)

set_option maxRecDepth 100000 in
/-- **One iteration of the blob loop completes**, given its tail's completeness. -/
theorem dvL_step (hwf : coreProgram.Wf) (k : ℕ) (z : E) {r : ℕ} (hr : r < 2 ^ 34) {syms : ℕ → ℕ → List E}
    (hsl : ∀ i h, (syms i h).length = LeanDa.cellSymbols) (horth : ∀ i < r, runSum z (syms i) 128 = 0)
    (wt roots : E) {i : ℕ} (hi : i < r)
    (htail : i + 1 < r → CallCompletes k name% «da_verify_loop0» [gen ^ (i + 1), gen ^ r, wt, roots] []
      (DvLPre z r syms wt roots) (DvLPost syms (i + 1) r)) :
    CallCompletes k name% «da_verify_loop0» [gen ^ i, gen ^ r, wt, roots] [] (DvLPre z r syms wt roots)
      (DvLPost syms i r) := by
  refine callCompletes_straight find_dvL dvL_body rfl fun b => ?_
  set σ := dvLσ i r wt roots (blobRoot (syms i)) with hσ
  have e10 : σ (.n 10) = gen ^ i * word 2 0 + gen ^ r := rfl
  have hargs : [V.n 12, .n 1, .n 2, .n 3].map σ = [gen ^ (i + 1), gen ^ r, wt, roots] := by
    show [gen ^ i * word 2 0, gen ^ r, wt, roots] = _; rw [gen_mul_two]
  have hblob := CallCompletes.monoPP (da_verify_blob_completes hwf k z (hsl i) (horth i hi) wt)
    (Pre' := fun rd => HoldsWords rd [] ∧ DvLPre z r syms wt roots rd) (fun _ hp => hp.2.1) fun _ _ _ h => h
  refine ⟨0, [], σ, [BlobPost (syms i), DvLPost syms (i + 1) r], wordsIn_nil b, rfl, rfl, ?_, ?_, ?_⟩
  · intro rd _ _ hp s hs
    have hR := hp.2 i hi
    simp only [dvLPre, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact rfl
    · exact rfl
    · show LoadHolds rd (roots * (gen ^ i * gen ^ i)) 0 (blobRoot (syms i)).1
      rw [gen_sq]; exact hR 0 (by simp)
    · show LoadHolds rd (roots * (gen ^ i * gen ^ i)) 1 (blobRoot (syms i)).2
      rw [gen_sq]; exact hR 1 (by simp)
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · exact rfl
    · show IsInK (gen ^ i * word 2 0 + gen ^ r); rw [gen_mul_two]; exact gen_pow_add_isInK _ _
  · refine kidsCompl_cons_taken rfl rfl rfl rfl hblob ?_
    by_cases hlt : i + 1 < r
    · have htk : decide (σ (.n 10) ≠ 0) = true := by
        rw [e10, loopGuard_taken hr (by omega)]; exact decide_eq_true (by omega)
      exact kidsCompl_cons_taken htk rfl hargs rfl (CallCompletes.monoPP (htail hlt) (fun _ hp => hp.2) fun _ _ _ h => h) kidsCompl_nil
    · have htk : decide (σ (.n 10) ≠ 0) = false := by
        rw [e10, loopGuard_taken hr (by omega)]; exact decide_eq_false (by omega)
      exact kidsCompl_cons_skip (σ' := dvLσ (i + 1) r wt roots 0) htk find_dvL
        (by rw [dvL_params]; exact hargs.symm) kidsCompl_nil
  · intro rd ts _ _ _ hv hq
    have hlen := kidsValid_len hv
    rw [show ((dvLPre.filterMap Stmt.callS).map (mkCall σ)).length = 2 from rfl] at hlen
    rcases ts with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, ts⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · have h1 : BlobPost (syms i) rd t1 := hq.1 rfl
      have h2 : t2.pops coreProgram rd = dvPops syms (i + 1) (r - (i + 1)) := by
        by_cases hlt : i + 1 < r
        · have htk : decide (σ (.n 10) ≠ 0) = true := by
            rw [e10, loopGuard_taken hr (by omega)]; exact decide_eq_true (by omega)
          exact hq.2.1 htk
        · have htk : decide (σ (.n 10) ≠ 0) = false := by
            rw [e10, loopGuard_taken hr (by omega)]; exact decide_eq_false (by omega)
          have hv2 := hv.2.2.2.1
          simp only [mkCall, htk, Bool.false_eq_true, ↓reduceIte] at hv2
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv2
          rw [Tree.pops, show r - (i + 1) = 0 by omega]; rfl
      show _ = _
      rw [pops_straight_none find_dvL dvL_body rfl rfl hv, Tree.popsKids, Tree.popsKids, Tree.popsKids, h1, h2,
        show r - i = r - (i + 1) + 1 by omega, dvPops, dvPops, List.range'_succ, List.flatMap_cons]
      simp
    · simp at hlen

/-- **The blob loop completes** from every counter below the count `r`, popping each blob's cells'
symbols. -/
theorem dv_loop_completes (hwf : coreProgram.Wf) (k : ℕ) (z : E) {r : ℕ} (hr : r < 2 ^ 34)
    {syms : ℕ → ℕ → List E} (hsl : ∀ i h, (syms i h).length = LeanDa.cellSymbols)
    (horth : ∀ i < r, runSum z (syms i) 128 = 0) (wt roots : E) :
    ∀ i < r, CallCompletes k name% «da_verify_loop0» [gen ^ i, gen ^ r, wt, roots] []
      (DvLPre z r syms wt roots) (DvLPost syms i r) := by
  have key : ∀ t i, i + 1 + t = r → CallCompletes k name% «da_verify_loop0» [gen ^ i, gen ^ r, wt, roots] []
      (DvLPre z r syms wt roots) (DvLPost syms i r) := by
    intro t
    induction t with
    | zero => intro i hi; exact dvL_step hwf k z hr hsl horth wt roots (by omega) fun h' => absurd h' (by omega)
    | succ t ih => intro i hi; exact dvL_step hwf k z hr hsl horth wt roots (by omega) fun _ => ih (i + 1) (by omega)
  intro i hi
  exact key (r - i - 1) i (by omega)

end
end LeanVM.Guest.Complete
