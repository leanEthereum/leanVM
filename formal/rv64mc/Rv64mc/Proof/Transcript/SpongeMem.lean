/-
  Rv64mc.Proof.Transcript.SpongeMem

  What `Sponge::duplex`'s and `Sponge::new`'s proofs share: a slot of the stack as a number (`slot_toNat`), the
  ground challenge read back from words that agree (`OptionEAt.congr`).
-/

import Rv64mc.Proof.Transcript.Common
import Rv64mc.Model.Extra.Transcript

namespace Rv64mc.Proof.Transcript

open RiscvZkvm.Rv64 Rv64mc.Spec.Transcript

/-- `t - k`, as a stack slot's literal offset. -/
theorem slot_toNat {t c : Word} {k : Nat} (hc : c = BitVec.ofNat 64 (2 ^ 64 - k)) (hk : k ≤ t.toNat) (hk0 : 0 < k) :
    (t + c).toNat = t.toNat - k := by
  rw [hc]; exact toNat_sub_lit hk hk0

/-- **An `Option<E>` read back from words that agree.** -/
theorem OptionEAt.congr {m M : MachineState} {a : Word} {o : Option LeanVM.Parameters.E} (h : OptionEAt m a o)
    (hk : ∀ k, k < 24 → M.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k)) :
    OptionEAt M a o := by
  cases o with
  | none =>
    simp only [OptionEAt, Layouts.OptionE.tagOffset, Layouts.OptionE.None.tag] at h ⊢
    rw [hk 0 (by decide)]; exact h
  | some e =>
    simp only [OptionEAt, EAt, Layouts.OptionE.tagOffset, Layouts.OptionE.Some.tag, Layouts.OptionE.Some.f0,
      Layouts.E.c0, Layouts.E.c1] at h ⊢
    have h1 := h.2.1; have h2 := h.2.2
    simp only [add_ofNat_lit] at h1 h2 ⊢
    exact ⟨by rw [hk 0 (by decide)]; exact h.1, by rw [hk _ (by decide)]; exact h1, by rw [hk _ (by decide)]; exact h2⟩

/-! ## `Sponge::new`'s lanes -/

section Lanes

open Rv64mc.Model

theorem sm_length_foldl_of {α β : Type} (step : List α → β → List α)
    (h : ∀ s k, (step s k).length = s.length) (L : List β) (s : List α) :
    (L.foldl step s).length = s.length := by
  induction L generalizing s with
  | nil => rfl
  | cons a L ih => rw [List.foldl_cons, ih, h]

theorem sm_getD_foldl_set_range (o n : ℕ) (f : ℕ → BitVec 64) (s : List (BitVec 64)) (j : ℕ) :
    ((List.range n).foldl (fun s i ↦ s.set (o + i) (f i)) s).getD j 0 =
      if o ≤ j ∧ j < o + n ∧ j < s.length then f (j - o) else s.getD j 0 := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_set, ih,
      sm_length_foldl_of _ (fun _ _ ↦ List.length_set ..)]
    by_cases h1 : o + n = j
    · subst h1
      by_cases h2 : o + n < s.length <;> simp [h2]
    · by_cases h3 : o ≤ j ∧ j < o + n ∧ j < s.length
      · simp [h1, h3, show j < o + (n + 1) by omega]
      · have h4 : ¬ (o ≤ j ∧ j < o + (n + 1) ∧ j < s.length) := by omega
        simp [h1, h3, h4]

theorem newLanes_length (iv pi : List (BitVec 8)) : (newLanes iv pi).length = 25 := by
  rw [newLanes, sm_length_foldl_of _ (fun _ _ ↦ List.length_set ..),
    sm_length_foldl_of _ (fun _ _ ↦ List.length_set ..), List.length_replicate]

/-- **Lane `j` of `Sponge::new`'s input**: the IV's words, the public input's, then zeros. -/
theorem newLanes_getD (iv pi : List (BitVec 8)) {j : Nat} (hj : j < 25) :
    (newLanes iv pi).getD j 0 =
      if j < 4 then (digestWordsRust iv).getD j 0 else if j < 8 then (digestWordsRust pi).getD (j - 4) 0
      else 0 := by
  have h1 := sm_getD_foldl_set_range 0 4 (fun i ↦ (digestWordsRust iv).getD i 0) (List.replicate 25 0#64)
  simp only [Nat.zero_add] at h1
  rw [newLanes, sm_getD_foldl_set_range, h1, sm_length_foldl_of _ (fun _ _ ↦ List.length_set ..),
    List.length_replicate]
  by_cases ha : j < 4
  · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega, by omega⟩]; simp [ha]
  · by_cases hb : j < 8
    · rw [ite_eq_left ⟨by omega, by omega, by omega⟩]; simp [ha, hb]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hj]
      simp [ha, hb]

end Lanes

/-- A digest read through stores that keep its doublewords. -/
theorem digest_keep {m P : MachineState} {x : Word} {d : List (BitVec 8)} (hd : DigestAt m x d)
    (h : ∀ y : Word, (alignToDword x).toNat ≤ y.toNat → y.toNat < x.toNat + 32 → P.getMem y = m.getMem y) :
    DigestAt P x d := by
  obtain ⟨hl, hb⟩ := hd
  refine ⟨hl, hb.keep fun k hk => getByte_congr (h _ ?_ ?_)⟩
  · rw [toNat_alignToDword, toNat_alignToDword, toNat_add_ofNat (by have := hb.1; omega)]; omega
  · rw [toNat_alignToDword, toNat_add_ofNat (by have := hb.1; omega)]
    simp only [Layouts.Digest.byteSize] at hl; omega

end Rv64mc.Proof.Transcript
