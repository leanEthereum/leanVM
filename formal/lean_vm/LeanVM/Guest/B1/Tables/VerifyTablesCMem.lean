/-
  LeanVM.Guest.B1.Tables.VerifyTablesCMem

  `verify_tables`' completeness: what the honest buffers hold, as the windows read it.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCChain2
public import LeanVM.Guest.B1.VerifySub.CPlaced3
public import Mathlib.Data.List.GetD

/-!
# The honest buffers, read

`vtOwnW`'s buffers at their indices (`vtOwnW_sel` for the selectors'), and from a memory holding
them, what each window reads (`selMem_of` for the selectors).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL)

@[expose] public section

theorem flatMap_range_getD3 {α : Type} (f : ℕ → List α) (hf : ∀ a, (f a).length = 3) (d : α) :
    ∀ (m j k : ℕ), j < m → k < 3 → ((List.range m).flatMap f).getD (3 * j + k) d = (f j).getD k d
  | 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | m + 1, j, k, hj, hk => by
    have hl : ((List.range m).flatMap f).length = 3 * m := by
      rw [List.length_flatMap]; simp [hf, Nat.mul_comm]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hl]; omega)]
      exact flatMap_range_getD3 f hf d m j k h hk
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, show 3 * j + k - 3 * j = k by omega]

section
variable (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E) (cl ch : ℕ → E)
  (chis : List E)

theorem selW_length (i : ℕ) : (selW ks point i).length = 3 := rfl

/-- Selector `i`'s three buffers in `vtOwnW`. -/
theorem vtOwnW_sel {i k : ℕ} (hi : i < 65) (hk : k < 3) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).getD (selBuf i + k) [] = (selW ks point i).getD k [] := by
  unfold vtOwnW
  by_cases h3 : i < 3
  · interval_cases i <;> interval_cases k <;> rfl
  · have hsb : selBuf i + k = 16 + (3 * (i - 3) + k) := by
      simp only [selBuf, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, ↓reduceIte]; omega
    have hF : ((List.range 62).flatMap fun j => selW ks point (j + 3)).length = 186 := by
      rw [List.length_flatMap]; simp [selW_length]
    rw [hsb, List.getD_append _ _ _ _ (by simp [List.length_append, selW_length, hF]; omega),
      List.getD_append_right _ _ _ _ (by simp [selW_length]), show (16 + (3 * (i - 3) + k) -
        ([sortW ks, sideW, offW ks, idxcW, bimW point logMem] ++ selW ks point 0 ++ selW ks point 1 ++
          [idxChainW point logMem] ++ selW ks point 2 ++ [idxChainW point 18]).length) =
        3 * (i - 3) + k by simp [selW_length],
      flatMap_range_getD3 (fun j => selW ks point (j + 3)) (fun _ => rfl) [] 62 (i - 3) k (by omega) hk,
      Nat.sub_add_cancel (by omega)]

theorem vtOwnW_zc :
    (vtOwnW ks point logMem n cvr cur cl ch chis).getD 202 [] = zcRoundsW cvr cur cl n ∧
      (vtOwnW ks point logMem n cvr cur cl ch chis).getD 203 [] = zcCprodW ch n ∧
      (vtOwnW ks point logMem n cvr cur cl ch chis).getD 204 [] = zcPeqW point chis n := by
  have hF : ((List.range 62).flatMap fun j => selW ks point (j + 3)).length = 186 := by
    rw [List.length_flatMap]; simp [selW_length]
  have hP : ([sortW ks, sideW, offW ks, idxcW, bimW point logMem] ++ selW ks point 0 ++ selW ks point 1 ++
      [idxChainW point logMem] ++ selW ks point 2 ++ [idxChainW point 18] ++
      (List.range 62).flatMap fun j => selW ks point (j + 3)).length = 202 := by
    simp [selW_length, hF]
  unfold vtOwnW
  refine ⟨?_, ?_, ?_⟩ <;> rw [List.getD_append_right _ _ _ _ (by omega), hP] <;> rfl

end

/-- A prefix of what a pointer holds, agreeing with it. -/
theorem readsAt_sub {rd : Reader} {p : E} {L l : List E} (h : ReadsAt rd p L) (hl : l.length ≤ L.length)
    (he : ∀ j < l.length, l.getD j 0 = L.getD j 0) : ReadsAt rd p l := fun j hj => by
  have e : l[j] = L[j]'(by omega) := by
    rw [← List.getD_eq_getElem l 0, he j hj, List.getD_eq_getElem]
  rw [e]; exact h j (by omega)

end
end LeanVM.Guest.B1.VerifySub
