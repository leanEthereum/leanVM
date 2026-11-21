/-
  LeanVM.Guest.B1.Sig.SpWotsSound

  `sp_wots` is sound: whenever its body holds (under any call relation: it calls nothing), it
  returns one word, the WOTS+C leaf of the chain values its frame holds at the key whose
  address is its second and third arguments and the digits the encoding digest, its fourth, holds
  (`base_2b`), of digit sum `T = 128`; over cells.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsGroups
public import LeanVM.Guest.B1.Sig.SpWotsData
public import LeanVM.Guest.B1.Sig.XmssCore

/-!
# `sp_wots`, sound

Over the template (`sp_wots_soundT`): the body holding, `at` is the arguments (the copies), the
powers are `g^s`, the padding run holds; each dispatch takes the arm of its digit word
(`spMatches_sound`), whose walks reach their tips from the starts (`spArmK_sound`); the product is
`g` to the digits' sum, asserted to be `g^128`, and the encoding the `XOR` of the digits' fields
(`spX`), asserted to be the fourth argument, whose `base_2b` digits they therefore are
(`spX_digit`); the leaf is the `keccak_cells` of `pp`, `a0`, `a1 + SP_WOTS_PK` and the tips
(`kMsg_sound`, over the padding run): `spLeafCell`.

The guest numbers the template's values with the unused ones removed (`spBody = renameList spRen
spBodyT`), so a valuation `σ` of the guest's body is `σ ∘ spRen` of the template's
(`Stmt.holdsList_rename`), which agrees with `σ` on the arguments (`sp_wots_sound`). There
`spDigitR σ i` is chain `i`'s digit and `spStartR σ i` the value its start is hinted into.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Core.Value.Keccak LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## Cells -/

/-- **The one-time leaf over cells**: chain `i` walked from digit `d i` from `starts i` with the
step `spStepCell pp a0 a1`, the ends hashed after `pp`, `a0` and `a1 + SP_WOTS_PK` (`T_v`). -/
def spLeafCell (pp a0 a1 : E) (d : Nat → Nat) (starts : Nat → E) : E :=
  (hcell (pp :: a0 :: (a1 + spPkC) :: (List.range 64).map fun i =>
    chainT (spStepCell pp a0 a1) i (3 - d i) (d i) (starts i))).1

/-! ## The template's parts -/

theorem spBodyT_parts : spBodyT = spPre ++ (spGs.1 ++ (spChecks ++
    (spLeafK.1 ++ [copyS (.n spLeafK.2.1) (.n spLeafK.2.2), .ret [.n spLeafK.2.1]]))) := by
  rw [spBodyT, spChecks, spPre, spCopies, spPowers]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem spPre_atoms : atomsOnly spPre = true := by decide +kernel

theorem spLeafK_atoms : atomsOnly spLeafK.1 = true := kMsg_atoms ..

/-- The last group's outputs: the dispatches' product and encoding. -/
theorem spGs_out : spGs.2.2.2 = (.n (spProd false 1 (spState 21).2.2), .n (spEnc false 1 (spState 21).2.2)) := by
  rw [spGs_eq]
  rfl

/-- **The tips, the product and the encoding** of the codeword, its dispatches' atoms holding. -/
theorem spCodeword_sound (hpow : ∀ s < 10, σ (.n (6 + s)) = gen ^ s) (hpad : PadOK σ spPad)
    (hg : ∀ p < 22, SpGroupOK rd σ p) :
    (∀ i < 64, σ (spTip i) = chainT (spStepCell (σ (.n 0)) (σ (.n 4)) (σ (.n 5))) i
      (3 - spDigit σ i) (spDigit σ i) (σ (spStart σ i))) ∧
    σ (.n (spProd false 1 (spState 21).2.2)) = gen ^ (∑ i ∈ Finset.range 64, spDigit σ i) ∧
    σ (.n (spEnc false 1 (spState 21).2.2)) = eOfNat128 (spX (spDigit σ) 64) := by
  have harm : ∀ p < 22, spArmAt σ p < 64 ∧
      SpArmOK σ (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (spArmAt σ p)
        (spStartOf (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1 (spArmAt σ p)
          (spArmB (3 * p) (spN p) (p == 0) (spState p).2.2 (spState p).1 (spState p).2.1
            (spArmAt σ p))) := by
    intro p hp
    obtain ⟨k, hk, hx, ha⟩ := hg p hp
    rw [spArmAt_eq hk hx]
    exact ⟨hk, spArmK_sound hpad ha⟩
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hp : i / 3 < 22 := by omega
    have hr : i % 3 < spN (i / 3) := by
      unfold spN; split
      · omega
      · omega
    have := (harm (i / 3) hp).2.tip (i % 3) hr
    rw [show 3 * (i / 3) + i % 3 = i by omega] at this
    rw [spDigit_eq σ hr]
    exact this
  · have hcw := spCodeword_prod (G := 21) (σ := σ) (by norm_num) le_rfl (spDigitWord σ)
      (fun p _ => spDigitWord_lt σ p) hpow
      (fun p => σ (.n (spProd (p == 0) (spN p) (spState p).2.2)))
      (by
        have := (harm 0 (by norm_num)).2.prod
        show σ (.n (spProd (0 == 0) (spN 0) (spState 0).2.2)) =
          σ (.n (6 + digitSum (spArmAt σ 0 % 4 ^ spN 0) (spN 0)))
        rw [digitSum_mod_pow, this]
        simp)
      (fun p _ => by
        have := (harm (p + 1) (by omega)).2.prod
        show σ (.n (spProd (p + 1 == 0) (spN (p + 1)) (spState (p + 1)).2.2)) =
          σ (.n (spProd (p == 0) (spN p) (spState p).2.2)) *
            σ (.n (6 + digitSum (spArmAt σ (p + 1) % 4 ^ spN (p + 1)) (spN (p + 1))))
        rw [digitSum_mod_pow, this]
        have hb : (p + 1 == 0) = false := by simp
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rw [spState_succ])
    simpa [spN, spDigit] using hcw
  · have hcw := spCodeword_enc (spDigitWord σ)
      (fun p => σ (.n (spEnc (p == 0) (spN p) (spState p).2.2)))
      (by
        have := (harm 0 (by norm_num)).2.enc
        show σ (.n (spEnc (0 == 0) (spN 0) (spState 0).2.2)) =
          lit (spDigitsC 0 3 (spArmAt σ 0 % 4 ^ spN 0))
        rw [this]
        simp [spN])
      (fun p _ => by
        have := (harm (p + 1) (by omega)).2.enc
        show σ (.n (spEnc (p + 1 == 0) (spN (p + 1)) (spState (p + 1)).2.2)) =
          σ (.n (spEnc (p == 0) (spN p) (spState p).2.2)) +
            lit (spDigitsC (3 * (p + 1)) (spN (p + 1)) (spArmAt σ (p + 1) % 4 ^ spN (p + 1)))
        rw [this]
        have hb : (p + 1 == 0) = false := by simp
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        rw [spState_succ])
    exact hcw

/-- **`sp_wots`'s template is sound**: whenever it holds of `σ`, it returns one word
`leaf`: the digits `spDigit σ` sum to `128`, the fourth argument is their encoding (`spX`), and
`leaf` is the one-time leaf of the chain values at `spStart σ` (`spLeafCell`). -/
theorem sp_wots_soundT {rets : List E}
    (h : Stmt.HoldsList C rd σ spBodyT False (fun rs => rs = rets)) :
    ∃ leaf, rets = [leaf] ∧ (∀ i, spDigit σ i < 4) ∧
      ∑ i ∈ Finset.range 64, spDigit σ i = 128 ∧ σ (.n 3) = eOfNat128 (spX (spDigit σ) 64) ∧
      leaf = spLeafCell (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) (spDigit σ) fun i => σ (spStart σ i) := by
  rw [spBodyT_parts] at h
  -- what the body sets first: the copies, the powers and the padding run
  have s0 := holdsList_split_atoms spPre_atoms h
  have hpre := atomsHold_of_holdsList spPre_atoms s0.1
  have h4 : σ (.n 4) = σ (.n 1) := hpre.atom (a := .copy (.n 4) (.n 1)) (by simp [spPre, spCopies, copyS])
  have h5 : σ (.n 5) = σ (.n 2) := hpre.atom (a := .copy (.n 5) (.n 2)) (by simp [spPre, spCopies, copyS])
  have hpow : ∀ s < 10, σ (.n (6 + s)) = gen ^ s := by
    intro s hs
    have e : σ (.n (6 + s)) = word (2 ^ s) 0 := hpre.atom (a := .const (.n (6 + s)) _) (by
      simp only [spPre, List.mem_append]
      left; left; left; left; right
      simp only [spPowers, cst, List.mem_map, List.mem_range]
      exact ⟨s, hs, rfl⟩)
    rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
  have hpad : PadOK σ spPad := padRun_ok (hpre.sub fun x hx => by
    simp only [spPre, List.mem_append]
    left; right; exact hx)
  -- the dispatches
  have s1 := s0.2
  rw [spGs_fst] at s1
  obtain ⟨s3, hg⟩ := spMatches_sound (C := C) (rd := rd) (σ := σ) 22 0 (by simpa only [Nat.zero_add] using s1)
  have hgrp : ∀ p < 22, SpGroupOK rd σ p := fun p hp => by simpa using hg p hp
  obtain ⟨htip, hprod, henc⟩ := spCodeword_sound hpow hpad hgrp
  -- the checks and the leaf
  have hca : atomsOnly (spChecks ++ spLeafK.1) = true := by
    rw [atomsOnly_append, spLeafK_atoms]; rfl
  rw [← List.append_assoc] at s3
  have s4 := holdsList_split_atoms hca s3
  have hc := atomsHold_of_holdsList hca s4.1
  have e2 : σ (.n (spEnc false 1 (spState 21).2.2)) + σ (.n 3) = 0 :=
    hc.atom (a := .assertEq (.n (spEnc false 1 (spState 21).2.2)) (.n 3)) (by simp [spChecks, spGs_out])
  have eC : σ (.n spC) = spTarget := hc.atom (a := .const (.n spC) _) (by simp [spChecks, cst])
  have eP : σ (.n (spProd false 1 (spState 21).2.2)) + σ (.n spC) = 0 :=
    hc.atom (a := .assertEq (.n (spProd false 1 (spState 21).2.2)) (.n spC)) (by simp [spChecks, spGs_out])
  have eL1 : σ (.n (spC + 1)) = spPkC :=
    hc.atom (a := .const (.n (spC + 1)) _) (by simp [spChecks, cst])
  have eL2 : σ (.n (spC + 2)) = σ (.n 2) + σ (.n (spC + 1)) :=
    hc.atom (a := .add (.n (spC + 2)) (.n 2) (.n (spC + 1))) (by simp [spChecks, addS])
  have henc3 : σ (.n 3) = eOfNat128 (spX (spDigit σ) 64) :=
    ((Value.e_add_eq_zero_iff).mp e2).symm.trans henc
  have hdlt : ∀ j, spDigit σ j < 4 := fun j => Nat.mod_lt _ (by norm_num)
  have hsum : ∑ i ∈ Finset.range 64, spDigit σ i = 128 := by
    have hle : ∑ i ∈ Finset.range 64, spDigit σ i ≤ ∑ _i ∈ Finset.range 64, 3 := by
      apply Finset.sum_le_sum
      intro j _
      have := hdlt j
      omega
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
    refine Value.gen_pow_inj (by omega) (by norm_num) ?_
    rw [← hprod, (Value.e_add_eq_zero_iff).mp eP, eC, spTarget_eq]
  -- the leaf's message
  have hl := hc.right
  have hlenC : spLeafCells.length = 67 := by decide +kernel
  have hk := kMsg_sound hpad (cells := spLeafCells.map KC.cell)
    (len := 1072) (tailRun := false) (out := none) (b := spC + 3) (fun h => absurd h (by simp))
    hl (by simp [hlenC]) (fun j hj => by
      rw [List.getD_eq_default _ _ (by rw [length_cellsBytes]; simp [hlenC]; omega)])
  have hcv : (spLeafCells.map KC.cell).map (KC.val σ) = spLeafCells.map σ := by
    rw [List.map_map]
    rfl
  have htake : (cellsBytes (spLeafCells.map σ)).take 1072 = cellsBytes (spLeafCells.map σ) := by
    rw [List.take_of_length_le (by rw [length_cellsBytes]; simp [hlenC])]
  rw [hcv, htake] at hk
  have hleaf : σ (.n spLeafK.2.2) = (hcell (spLeafCells.map σ)).1 := hk
  -- the return
  have s5 := s4.2
  simp only [Stmt.HoldsList, Stmt.Holds, copyS, Atom.Holds, List.map_cons, List.map_nil] at s5
  obtain ⟨hcp', hret⟩ := s5
  refine ⟨σ (.n spLeafK.2.1), hret.symm, hdlt, hsum, henc3, ?_⟩
  rw [hcp', hleaf, spLeafCells_eq, spLeafCell]
  simp only [List.map_cons, List.map_map]
  rw [eL2, eL1]
  have hm : List.map (σ ∘ spTip) (List.range 64) = List.map (fun i => chainT (spStepCell (σ (.n 0))
      (σ (.n 1)) (σ (.n 2))) i (3 - spDigit σ i) (spDigit σ i) (σ (spStart σ i))) (List.range 64) :=
    List.map_congr_left (fun i hi => by
      rw [Function.comp_apply, htip i (List.mem_range.mp hi), h4, h5])
  rw [hm]

/-! ## The guest's numbering -/

theorem spR_small {i : Nat} (hi : i ≤ 28) : spR i = i := by
  unfold spR spZero
  rw [show List.countP (fun x => decide (x < i)) [133, 245, 334, 411, 472, 561, 638, 703, 752, 829,
    894, 947, 984, 1045, 1094, 1131] = 0 by
      rw [List.countP_eq_zero]
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [decide_eq_true_eq, not_lt]
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> omega]
  simp

theorem spRen_small {i : Nat} (hi : i ≤ 28) : spRen (.n i) = .n i := by
  simp [spRen, spR_small hi, V.n]

/-- **Chain `i`'s digit** in the guest's valuation `σ`. -/
noncomputable def spDigitR (σ : Val) (i : Nat) : Nat := spDigit (σ ∘ spRen) i

/-- **Where chain `i`'s start is hinted** in the guest's valuation `σ`: the guest's value of the
template's. -/
noncomputable def spStartR (σ : Val) (i : Nat) : V := spRen (spStart (σ ∘ spRen) i)

/-- **`sp_wots` is sound**: whenever its body holds of `σ`, it returns one word `leaf`:
the digits `spDigitR σ` sum to `128`, the fourth argument is their encoding (`spX`: digit `i` at
`spDigitPos i`, `spX_digit`), and `leaf` is the one-time leaf of the chain values at `spStartR σ`
(`spLeafCell`) at the address `(σ n1, σ n2)`. -/
theorem sp_wots_sound_cells {rets : List E}
    (h : Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False (fun rs => rs = rets)) :
    ∃ leaf, rets = [leaf] ∧ (∀ i, spDigitR σ i < 4) ∧
      ∑ i ∈ Finset.range 64, spDigitR σ i = 128 ∧ σ (.n 3) = eOfNat128 (spX (spDigitR σ) 64) ∧
      leaf = spLeafCell (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) (spDigitR σ) fun i => σ (spStartR σ i) := by
  rw [spBody_eq, spBody, Stmt.holdsList_rename] at h
  obtain ⟨leaf, h1, h3, h4, h5, h6⟩ := sp_wots_soundT h
  have e : ∀ i ≤ 28, (σ ∘ spRen) (.n i) = σ (.n i) := fun i hi => by
    rw [Function.comp_apply, spRen_small hi]
  rw [e 3 (by norm_num)] at h5
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)] at h6
  exact ⟨leaf, h1, h3, h4, h5, h6⟩

end
end LeanVM.Guest.B1.Sig
