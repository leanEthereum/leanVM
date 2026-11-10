/-
  LeanVM.Guest.B1.KeccakGkr.VkCB

  `verify_keccak`'s first claim record, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCA
public import LeanVM.Guest.B1.KeccakGkr.VkFirst
public import LeanVM.Guest.B1.KeccakGkr.EqTreeC
public import LeanVM.Guest.B1.KeccakGkr.StoreFacts

/-!
# The first claim's record, completely

`loads_complete`: a block of atoms whose only residual atoms are loads, not stores, through
pointers whose words the memory holds, holds on an evaluated valuation.

`vkFirst_complete`: on `verify_keccak`'s evaluated valuation, the instance coordinates at `z_vals`,
the lane coordinates at `92`, the segment coordinate at `66`, the output lanes at `8` and the three
equality trees' levels in memory, the record's words are computed (the instance weights, the lanes'
pointer, the claim's value) and the section holds once its stores do.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- A load through one of the pointers `ps`, at an offset in its range. -/
def ldR (ps : List (V × ℕ × ℕ)) : Atom → Bool
  | .load _ p off => ps.any fun q ↦ q.1 == p && decide (q.2.1 ≤ off) && decide (off < q.2.2)
  | _ => false

/-- **A block whose residual atoms are loads, not stores**, through pointers whose words the
memory holds. -/
theorem loads_complete {B : List Stmt} (hall : B.all isAtom = true) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hk : canonChk [] (atomsL ([] ++ B)) = true) (hg : ∀ s ∈ B, GoodS rd S w σ s)
    {ps : List (V × ℕ × ℕ)} (hl : (resid (atomsL B)).all (ldR ps) = true)
    (hS : noneIn (resid (atomsL B)) S = true)
    (hW : ∀ q ∈ ps, ∀ off, q.2.1 ≤ off → off < q.2.2 → ∃ v, LoadHolds rd (σ q.1) off v) :
    ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ B next kret := by
  refine fun hn ↦ block_holdsP (P := []) hall hσ hk (by simpa using hg) (A := []) (by simp)
    (fun a ha ↦ Or.inr ?_) hn
  have hl' := List.all_eq_true.mp hl a ha
  have hS' := not_mem_of_noneIn hS a ha
  cases a with
  | load d p off =>
    simp only [ldR, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl'
    obtain ⟨q, hq, ⟨rfl, h1⟩, h2⟩ := hl'
    obtain ⟨v, hv⟩ := hW q hq off h1 h2
    exact side_load hS' hv
  | _ => simp [ldR] at hl'

/-- The pairs' dot product of the first record: the lane weights and the output lanes. -/
abbrev vkFirstPD : List Stmt := pairsDotT (.n 276) (.n 8) (consecOffs 30 0 25) 388

theorem vkFirst_kernel :
    noneIn (eqtreeReads (.n 9) (.n 205) 0 206 4) vkSt = true ∧
    noneIn (eqtreeReads (.n 92) (.n 276) 0 277 5) vkSt = true ∧
    noneIn (eqtreeReads (.n 66) (.n 384) 0 385 1) vkSt = true ∧
    noneIn ((List.range 16).map fun i ↦ .load (.n (260 + i)) (.n 205) (14 + i)) vkSt = true ∧
    vkFirstPD.all isAtom = true ∧ canonChk [] (atomsL ([] ++ vkFirstPD)) = true ∧
    (resid (atomsL vkFirstPD)).all (ldR [(.n 276, 30, 55), (.n 8, 0, 25)]) = true ∧
    noneIn (resid (atomsL vkFirstPD)) vkSt = true ∧
    noneIn [.load (.n 487) (.n 384) 1] vkSt = true := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **The first claim's record, completely.** -/
theorem vkFirst_complete (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ s ∈ vkFirstT, GoodS rd vkSt w σ s)
    {chis outs rl : List E} {r0 : E} (h4 : 4 ≤ chis.length)
    (hzv : ∀ i < 4, LoadHolds rd (σ (.n 9)) i (chis.getD i 0))
    (hrlL : rl.length = 5) (hrl : ∀ i < 5, LoadHolds rd (σ (.n 92)) i (rl.getD i 0))
    (hseg : LoadHolds rd (σ (.n 66)) 0 r0) (houts : outs.length = 25)
    (hol : ReadsAt rd (σ (.n 8)) outs)
    (hT203 : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t,
      LoadHolds rd (σ (.n 205)) (2 ^ t - 2 + i) ((eqKernel ((chis.take 4).take t)).getD i 0))
    (hT274 : ∀ t, 1 ≤ t → t ≤ 5 → ∀ i < 2 ^ t,
      LoadHolds rd (σ (.n 276)) (2 ^ t - 2 + i) ((eqKernel (rl.take t)).getD i 0))
    (hT382 : ∀ i < 2, LoadHolds rd (σ (.n 384)) i ((eqKernel [r0]).getD i 0)) :
    σ (.n 204) = 1 ∧ σ (.n 383) = σ (.n 276) * gen ^ 30 ∧
    (∀ i < 16, σ (.n (260 + i)) = (eqKernel (chis.take 4)).getD i 0) ∧
    σ (.n 489) = σ (.n 193) + (eqKernel [r0]).getD 1 0 *
      ∑ k ∈ range 25, (eqKernel rl).getD k 0 * outs.getD k 0 ∧
    ∀ {next : Prop} {kret : List E → Prop},
      LoadHolds rd (σ (.n 203)) 1 (σ (.n 204)) → LoadHolds rd (σ (.n 203)) 2 (σ (.n 60)) →
      (∀ i < 16, LoadHolds rd (σ (.n 203)) (6 + i) (σ (.n (260 + i)))) →
      LoadHolds rd (σ (.n 203)) 3 (σ (.n 383)) → LoadHolds rd (σ (.n 203)) 0 (σ (.n 489)) →
      next → Stmt.HoldsList C rd σ vkFirstT next kret := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := vkFirst_kernel
  have gA : ∀ a, Stmt.atom a ∈ vkFirstT → Good rd vkSt w σ a := fun a h ↦ hg _ h
  have mE1 : ∀ s ∈ eqtreeT (.n 9) (.n 205) 0 206 4, s ∈ vkFirstT := fun s hs ↦ by
    rw [vkFirstT]; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))))))))
  have mCW : ∀ s ∈ copyWordsT (.n 205) (.n 203) 14 6 260 16, s ∈ vkFirstT := fun s hs ↦ by
    rw [vkFirstT]; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))))))
  have mE2 : ∀ s ∈ eqtreeT (.n 92) (.n 276) 0 277 5, s ∈ vkFirstT := fun s hs ↦ by
    rw [vkFirstT]; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))))
  have mE3 : ∀ s ∈ eqtreeT (.n 66) (.n 384) 0 385 1, s ∈ vkFirstT := fun s hs ↦ by
    rw [vkFirstT]; exact (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs)))
  have mPD : ∀ s ∈ vkFirstPD, s ∈ vkFirstT := fun s hs ↦ by
    rw [vkFirstT]; exact (List.mem_append_left _ (List.mem_append_right _ hs))
  -- the atoms
  have c202 : σ (.n 204) = word 1 0 0 := gA ((.const (.n 204) (word 1 0))) (by simp [vkFirstT])
  have c380 : σ (.n 382) = word 1073741824 0 0 :=
    gA ((.const (.n 382) (word 1073741824 0))) (by simp [vkFirstT])
  have m381 := mulG (by norm_num) (by norm_num)
    (gA ((.mul (.n 383) (.n 276) (.n 382))) (by simp [vkFirstT]))
  have g485 : Good rd vkSt w σ (.load (.n 487) (.n 384) 1) :=
    gA ((.load (.n 487) (.n 384) 1)) (by simp [vkFirstT])
  have m486 := mulG (by norm_num) (by norm_num)
    (gA ((.mul (.n 488) (.n 487) (.n 486))) (by simp [vkFirstT]))
  have a487 : σ (.n 489) = σ (.n 193) + σ (.n 488) :=
    gA ((.add (.n 489) (.n 193) (.n 488))) (by simp [vkFirstT])
  have e202 : σ (.n 204) = 1 := by rw [c202, word_one]
  have e381 : σ (.n 383) = σ (.n 276) * gen ^ 30 := by rw [m381, c380, word_2p30]
  -- the trees
  have E1 : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (eqtreeT (.n 9) (.n 205) 0 206 4) next kret :=
    fun hn ↦ eqtree_complete (by norm_num)
      (fun s hs ↦ hg s (mE1 s hs)) (not_mem_of_noneIn k1)
      (rs := chis.take 4) (by simp; omega)
      (fun t ht ↦ by
        have : (chis.take 4).getD t 0 = chis.getD t 0 := by
          simp [List.getD_eq_getElem?_getD, show t < 4 from ht]
        rw [this, zero_add]; exact hzv t ht)
      hT203 hn
  have E2 : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (eqtreeT (.n 92) (.n 276) 0 277 5) next kret :=
    fun hn ↦ eqtree_complete (by norm_num)
      (fun s hs ↦ hg s (mE2 s hs)) (not_mem_of_noneIn k2)
      (rs := rl) hrlL (fun t ht ↦ by rw [zero_add]; exact hrl t ht) hT274 hn
  have E3 : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (eqtreeT (.n 66) (.n 384) 0 385 1) next kret :=
    fun hn ↦ eqtree_complete (by norm_num)
      (fun s hs ↦ hg s (mE3 s hs)) (not_mem_of_noneIn k3)
      (rs := [r0]) rfl (fun t ht ↦ by obtain rfl : t = 0 := by omega
                                      simpa using hseg)
      (fun t h1 h2 i hi ↦ by
        obtain rfl : t = 1 := by omega
        simpa using hT382 i hi) hn
  -- the instance weights copied
  have e258 : ∀ i < 16, σ (.n (260 + i)) = (eqKernel (chis.take 4)).getD i 0 := by
    intro i hi
    have g : Good rd vkSt w σ (.load (.n (260 + i)) (.n 205) (14 + i)) :=
      gA _ (mCW _ (by
        simp only [copyWordsT, List.mem_flatten, List.mem_map, List.mem_range]
        exact ⟨_, ⟨i, hi, rfl⟩, by simp⟩))
    refine load_val g (not_mem_of_noneIn k4 _ (by simp only [List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)) ?_
    have := hT203 4 (by norm_num) le_rfl i (by norm_num; omega)
    rw [List.take_take, min_self] at this
    simpa using this
  -- the output lanes' dot
  have PD : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ vkFirstPD next kret :=
    fun hn ↦ loads_complete k5 hσ k6 (fun s hs ↦ hg s (mPD s hs))
      k7 k8 (fun q hq off h1 h2 ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · have := hT274 5 (by norm_num) le_rfl (off - 30) (by simp only at h1 h2 ⊢; norm_num; omega)
          simp only at h1 h2 ⊢
          rw [show 2 ^ 5 - 2 + (off - 30) = off by norm_num; omega] at this
          exact ⟨_, this⟩
        · exact ⟨_, hol off (by simp only at h2; omega)⟩) hn
  obtain ⟨hdot, -⟩ := pairsDotT_holds (C := C) (P := fun k ↦ (eqKernel rl).getD k 0)
    (Q := fun k ↦ outs.getD k 0) (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      have := hT274 5 (by norm_num) le_rfl k (by norm_num; omega)
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some] at hv
      rw [show rl.take 5 = rl by rw [← hrlL]; exact List.take_length] at this
      exact loadHolds_unique hv (by simpa using this))
    (fun k hk v hv ↦ by
      simp only [consecOffs, List.length_map, List.length_range] at hk
      simp only [consecOffs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some, zero_add] at hv
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact loadHolds_unique hv (hol k (by omega)))
    (by simp [consecOffs]) (PD (next := True) (kret := fun _ ↦ True) trivial)
  simp only [consecOffs, List.length_map, List.length_range, pairsDotV] at hdot
  have l485 : LoadHolds rd (σ (.n 384)) 1 ((eqKernel [r0]).getD 1 0) := hT382 1 (by norm_num)
  have e485 := load_val g485 (not_mem_of_noneIn k9 _ (by simp)) l485
  have e487 : σ (.n 489) = σ (.n 193) + (eqKernel [r0]).getD 1 0 *
      ∑ k ∈ range 25, (eqKernel rl).getD k 0 * outs.getD k 0 := by
    rw [a487, m486, e485, hdot]
  refine ⟨e202, e381, e258, e487, fun {next kret} s1 s2 s6 s3 s0 hn ↦ ?_⟩
  rw [vkFirstT]
  simp only [holdsList_append]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨trivial, c202, s1, s2, trivial, E1 ?_⟩
  rw [copyWordsT, holdsList_range_flatten _ _ (fun _ ↦ rfl)]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨?_, s6 i hi⟩
    rw [e258 i hi]
    have := hT203 4 (by norm_num) le_rfl i (by norm_num; omega)
    rw [List.take_take, min_self] at this
    simpa using this
  refine ⟨trivial, E2 ?_⟩
  refine ⟨c380, m381, s3, trivial, E3 (PD ?_)⟩
  exact ⟨by rw [e485]; exact l485, m486, a487, s0, hn⟩

end
end LeanVM.Guest.B1.VerifySub
