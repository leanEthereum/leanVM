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

theorem selBlk_facts : (∀ i < 37, selBlk.getD i 0 = i) ∧ (∀ j < 28, selBlk.getD (37 + j) 0 = 74 + j) := by
  decide +kernel

theorem selBuf_lt : ∀ i < 65, selBuf i + 2 < 205 := by decide

theorem vtSizes_length (n : ℕ) : (vtSizes n).length = 205 := by simp [vtSizes, selSz]

theorem vtOwnW_length (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) : (vtOwnW ks point logMem n cvr cur cl ch chis).length = 205 := by
  rw [← vtSizes_length n]; exact (vtOwnW_fit ks point logMem n cvr cur cl ch chis).length_eq

theorem readsAt_chain {rd : Reader} {m : ℕ} (hm : m < 42) (f : ℕ → E) (L : List E)
    (hL : L = (List.range 42).map (fun t => if t ≤ m then f t else 0)) (p : E) (hp : ReadsAt rd p L) :
    ReadsAt rd p ((List.range (m + 1)).map f) := by
  subst hL
  refine readsAt_sub hp (by simp only [List.length_map, List.length_range]; omega) fun j hj => ?_
  simp only [List.length_map, List.length_range] at hj
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_map, List.getElem_range, List.getElem_range]
  simp only [show j ≤ m by omega, ↓reduceIte]

/-- **What the selectors read**, on a memory holding the honest buffers and `block_kappa`. -/
theorem selMem_of {rd : Reader} {b n logMem : ℕ} {ks : ℕ → ℕ} {point : List E} {cvr : ℕ → Digest}
    {cur : E} {cl ch : ℕ → E} {chis : List E} {bk : E}
    (hB : MemL rd (bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis)))
    (hbk : ∀ b' < 102, LoadHolds rd bk b' (gen ^ ks b'))
    (hfit : ∀ i < 65, ks (selBlk.getD i 0) ≤ point.length ∧ selOff ks i < 2 ^ point.length ∧
      2 ^ ks (selBlk.getD i 0) ∣ selOff ks i) (hpl : point.length < 33) :
    ∀ i < 65, SelMem rd bk (vtPtr b n 2) point ks (selOff ks) (vtPtr b n) i := by
  intro i hi
  obtain ⟨hk, hoff, hdvd⟩ := hfit i hi
  have get : ∀ j < 205, ReadsAt rd (vtPtr b n j) ((vtOwnW ks point logMem n cvr cur cl ch chis).getD j []) :=
    fun j hj => memL_bufL_get (i := j) hB (by rw [vtSizes_length]; exact hj) (by rw [vtOwnW_length]; exact hj)
  have hsel : ∀ k < 3, ReadsAt rd (vtPtr b n (selBuf i + k)) ((selW ks point i).getD k []) := fun k hk =>
    vtOwnW_sel ks point logMem n cvr cur cl ch chis hi hk ▸ get (selBuf i + k) (by have := selBuf_lt i hi; omega)
  have hb102 : selBlk.getD i 0 < 102 := by
    rcases Nat.lt_or_ge i 37 with h | h
    · rw [selBlk_facts.1 i h]; omega
    · rw [show i = 37 + (i - 37) by omega, selBlk_facts.2 _ (by omega)]; omega
  have hoffW : ReadsAt rd (vtPtr b n 2) (offW ks) := get 2 (by norm_num)
  have chain := fun (f : ℕ → E) => readsAt_chain (rd := rd) (m := point.length - ks (selBlk.getD i 0))
    (by omega) f
  refine ⟨hk, hoff, hdvd, hbk _ hb102, ?_, ?_, chain _ _ rfl _ (hsel 1 (by norm_num)),
    chain _ _ rfl _ (hsel 2 (by norm_num))⟩
  · have := hoffW (selBlk.getD i 0) (by rw [offW, List.length_map, List.length_range]; exact hb102)
    simp only [offW, List.getElem_map, List.getElem_range] at this
    convert this using 1
    unfold selOff
    rcases Nat.lt_or_ge i 37 with h | h
    · rw [selBlk_facts.1 i h]; simp only [h, ↓reduceIte]
    · rw [show i = 37 + (i - 37) by omega, selBlk_facts.2 _ (by omega)]
      simp only [show ¬ 37 + (i - 37) < 37 by omega, show ¬ 74 + (i - 37) < 37 by omega,
        show 74 ≤ 74 + (i - 37) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  · have h0 := hsel 0 (by norm_num)
    rw [Nat.add_zero] at h0
    exact h0
end
end LeanVM.Guest.B1.VerifySub
