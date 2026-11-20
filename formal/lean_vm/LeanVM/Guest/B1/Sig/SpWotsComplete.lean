/-
  LeanVM.Guest.B1.Sig.SpWotsComplete

  `sp_wots`'s template is complete (`sp_wots_completeT`): for digits of sum `128` and any chain
  values, its body holds of a valuation whose arguments are `pp`, the address `(a0, a1)` and the
  digits' encoding, returning the one-time leaf of the values over cells (`spLeafCell`).
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsGroupComplete
public import LeanVM.Guest.B1.Sig.SpWotsSound
public import LeanVM.Guest.B1.Sig.CompleteKit

/-!
# `sp_wots`'s template, complete

The valuation: the arguments; the copies and the powers; the digit words at the digits' groups
(`spK`), hinted; their range checks; the padding run and the hoisted constant; the dispatches, each
by the arm of its digits with the chain values loaded at its starts (`spMatches_complete`); the
checks, which hold since the digits are the encoding's (`spCheck_complete`); the leaf's message
over the padding run (`spLeaf_complete`); the copy. The returned leaf is then read off by
soundness (`sp_wots_soundT`): its digits and chain values are the loaded ones.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## The digits -/

/-- The digits' base-4 number, digit `0` lowest. -/
def spDn (d : Nat → Nat) : Nat := ∑ i ∈ Finset.range 64, d i * 4 ^ i

/-- Group `p`'s digit word: its `spN p` base-4 digits from digit `3p`. -/
def spK (d : Nat → Nat) (p : Nat) : Nat := spDn d / 4 ^ (3 * p) % 4 ^ spN p

theorem spK_lt (d : Nat → Nat) (p : Nat) : spK d p < 4 ^ spN p := Nat.mod_lt _ (by positivity)

theorem spK_lt64 (d : Nat → Nat) (p : Nat) : spK d p < 64 :=
  lt_of_lt_of_le (spK_lt d p) (four_pow_spN_le p)

theorem spK_digit (d : Nat → Nat) {p t : Nat} (ht : t < spN p) :
    spK d p / 4 ^ t % 4 = spDn d / 4 ^ (3 * p + t) % 4 := by
  unfold spK
  obtain ⟨m, hm⟩ : ∃ m, spN p = t + (m + 1) := ⟨spN p - t - 1, by omega⟩
  rw [hm, pow_add, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add, pow_succ,
    Nat.mod_mul_left_mod]

theorem spDn_digit {d : Nat → Nat} (hd : ∀ i, d i < 4) {i : Nat} (hi : i < 64) :
    spDn d / 4 ^ i % 4 = d i :=
  base4_digit hd 64 i hi

theorem spLeafCell_congr {pp a0 a1 : E} {d d' : Nat → Nat} {s s' : Nat → E}
    (hd : ∀ i < 64, d i = d' i) (hs : ∀ i < 64, s i = s' i) :
    spLeafCell pp a0 a1 d s = spLeafCell pp a0 a1 d' s' := by
  have e : (List.range 64).map (fun i => chainT (spStepCell pp a0 a1) i (3 - d i) (d i) (s i)) =
      (List.range 64).map (fun i => chainT (spStepCell pp a0 a1) i (3 - d' i) (d' i) (s' i)) :=
    List.map_congr_left fun i hi => by
      simp only [hd i (List.mem_range.mp hi), hs i (List.mem_range.mp hi)]
  unfold spLeafCell
  rw [e]

theorem spX_congr {d d' : Nat → Nat} (hd : ∀ i < 64, d i = d' i) : spX d 64 = spX d' 64 := by
  have e : (List.range 64).map (spField d) = (List.range 64).map (spField d') :=
    List.map_congr_left fun i hi => by unfold spField; rw [hd i (List.mem_range.mp hi)]
  unfold spX
  rw [e]

theorem spN_mod (i : Nat) (hi : i < 64) : i % 3 < spN (i / 3) := by
  unfold spN; split <;> omega

/-! ## What the body sets before its dispatches -/

/-- The powers `g^s` in place. -/
def SpPw (σ : Val) : Prop := ∀ s < 10, σ (.n (6 + s)) = gen ^ s

/-- The digit words of the digits `d` in place. -/
def SpDw (d : Nat → Nat) (σ : Val) : Prop := ∀ q < 22, σ (.n (spDg + q)) = ofK (addressOfIndex (spK d q))

theorem SpPw.keep {lo hi : Nat} {σ σ' : Val} (he : Ext lo hi σ σ') (hlo : 16 ≤ lo) (h : SpPw σ) :
    SpPw σ' := fun s hs => by rw [he.apply (Or.inl (by omega))]; exact h s hs

theorem SpDw.keep {d : Nat → Nat} {lo hi : Nat} {σ σ' : Val} (he : Ext lo hi σ σ')
    (hlo : spDg + 22 ≤ lo) (h : SpDw d σ) : SpDw d σ' := fun q hq => by
  rw [he.apply (Or.inl (by omega))]; exact h q hq

theorem spInit_seq : SeqOK 4 (spCopies ++ spPowers) 16 := seqB_ok (by decide +kernel)

theorem spPadBlock_seq : SeqOK spPad (padRun spPad ++ [cst (spPad + 5) closeLane]) (spPad + 6) :=
  seqB_ok (by decide +kernel)

theorem spHints_complete (σ : Val) : Completes C rd spDg (spDg + 22) spHints σ (fun σ' => σ' = σ) :=
  completes_atoms (by decide +kernel) (Ext.refl _ _ _) rfl (fun a ha => by
    simp only [spHints, hintW, List.mem_map, List.mem_range, Stmt.atom.injEq] at ha
    obtain ⟨p, -, hp⟩ := ha
    subst hp
    trivial)

theorem spHints_nb : NumBelow (spDg + 22) (Stmt.valsList spHints) := numBelow_of_all (by decide +kernel)

theorem spRangesP_nb : ∀ m, NumBelow (spDg + 22 + 4 * m)
    (Stmt.valsList ((List.range m).flatMap fun p => rangeS (.n (spDg + p)) (spBound p) (spDg + 22 + 4 * p)))
  | 0 => NumBelow.nil _
  | m + 1 => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, valsList_append]
      refine ((spRangesP_nb m).mono (by omega)).append ?_
      intro v hv
      revert hv
      simp only [rangeS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by simp only [spDg]; omega, rfl⟩

theorem spRangesP_complete {d : Nat → Nat} (hm : MemOK rd 64) :
    ∀ m, m ≤ 22 → ∀ σ : Val, SpDw d σ →
    Completes C rd (spDg + 22) (spDg + 22 + 4 * m) ((List.range m).flatMap fun p =>
      rangeS (.n (spDg + p)) (spBound p) (spDg + 22 + 4 * p)) σ (fun _ => True)
  | 0, _, σ, _ => ⟨σ, Ext.refl _ _ _, trivial, fun _ _ hn => hn⟩
  | m + 1, hm22, σ, hx => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine Completes.append (m := spDg + 22 + 4 * m) (by omega) (by omega) (spRangesP_nb m)
        (spRangesP_complete hm m (by omega) σ hx) (fun σ1 he1 _ => ?_)
      have hx1 : σ1 (.n (spDg + m)) = ofK (addressOfIndex (spK d m)) := by
        rw [he1.apply (Or.inl (by omega))]; exact hx m (by omega)
      rw [show spDg + 22 + 4 * (m + 1) = spDg + 22 + 4 * m + 4 by omega]
      have hb : spBound m = ofK (addressOfIndex (4 ^ spN m - 1)) := by
        unfold spBound
        exact word_two_pow_eq (by have := four_pow_spN_le m; omega)
      rw [hb]
      exact rangeS_complete (K := 4 ^ spN m) hm (four_pow_spN_le m) (spK_lt d m) σ1 (.n (spDg + m))
        ⟨spDg + m, by omega, rfl⟩ hx1

theorem spRanges_eq : spRanges = (List.range 22).flatMap fun p =>
    rangeS (.n (spDg + p)) (spBound p) (spDg + 22 + 4 * p) := rfl

theorem spC_ge : spPad + 6 ≤ spC := by
  rw [spC_eq]; have := spState_ge 22; omega

theorem spHeadT_eq : spHeadT = (spCopies ++ spPowers) ++ (spHints ++ (spRanges ++
    ((padRun spPad ++ [cst (spPad + 5) closeLane]) ++ (List.range 22).map spMatch))) := by
  rw [spHeadT, spPre, spGs_fst]
  simp only [List.append_assoc]

/-- **The head completes**: the copies, the powers, the digit words of the digits `d` hinted, their
range checks, the padding run, the dispatches with the values `vals` loaded at their starts. -/
theorem spHead_complete (d : Nat → Nat) (vals : Nat → E) (hm : MemOK rd 64) (σ : Val) :
    Completes C rd 4 spC spHeadT σ
      (fun σ' => SpPw σ' ∧ SpDw d σ' ∧ SpMPost (spK d) vals 0 22 σ') ∧
    NumBelow spC (Stmt.valsList spHeadT) := by
  have hC := spC_ge
  have hnbR : NumBelow (spPad + 6) (Stmt.valsList (spHints ++ (spRanges ++
      (padRun spPad ++ [cst (spPad + 5) closeLane])))) := numBelow_of_all (by decide +kernel)
  have hnbM : NumBelow spC (Stmt.valsList ((List.range 22).map spMatch)) := by
    have := spMatches_numBelow 22 0
    rw [Nat.zero_add, ← spC_eq] at this
    simpa only [Nat.zero_add] using this
  rw [spHeadT_eq]
  refine ⟨Completes.append (m := 16) (by norm_num) (by simp only [spPad] at hC; omega)
    spInit_seq.numBelow (seq_completes spInit_seq σ) (fun σ1 _ hp1 => ?_), ?_⟩
  · have hpow1 : SpPw σ1 := by
      intro s hs
      have e : σ1 (.n (6 + s)) = word (2 ^ s) 0 := hp1.atom (a := .const (.n (6 + s)) _) (by
        simp only [spCopies, spPowers, cst, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨s, hs, rfl⟩)
      rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
    set σr := updRun σ1 spDg 22 (fun q => ofK (addressOfIndex (spK d q))) with hσr
    have her : Ext spDg (spDg + 22) σ1 σr := updRun_ext σ1 spDg 22 _
    have hxr : SpDw d σr := fun q hq => updRun_at σ1 spDg 22 _ hq
    have hpowr : SpPw σr := hpow1.keep her (by simp [spDg])
    refine Completes.reload (her.mono (by simp [spDg]) (by simp only [spDg, spPad] at hC ⊢; omega)) ?_
    -- the hints
    refine Completes.append (m := spDg + 22) (by simp [spDg]) (by simp only [spDg, spPad] at hC ⊢; omega)
      spHints_nb (spHints_complete σr) (fun σ2 _ e2 => ?_)
    subst e2
    -- the range checks
    refine Completes.append (m := spPad) (by simp [spDg, spPad]) (by omega)
      (spRangesP_nb 22) (spRangesP_complete (d := d) (C := C) hm 22 le_rfl σr hxr) (fun σ3 he3 _ => ?_)
    have hx3 : SpDw d σ3 := hxr.keep he3 le_rfl
    have hpow3 : SpPw σ3 := hpowr.keep he3 (by simp [spDg])
    -- the padding run and the hoisted constant
    refine Completes.append (m := spPad + 6) (by omega) hC spPadBlock_seq.numBelow
      (seq_completes spPadBlock_seq σ3) (fun σ4 he4 hp4 => ?_)
    have hx4 : SpDw d σ4 := hx3.keep he4 (by simp [spDg, spPad])
    have hpow4 : SpPw σ4 := hpow3.keep he4 (by simp [spPad])
    have hpad4 : SpGood spPad σ4 :=
      padRun_ok (hp4.sub fun x hx => List.mem_append_left _ hx)
    -- the dispatches
    have hM := spMatches_complete (C := C) (rd := rd) (spK d) (fun p _ => spK_lt d p) vals 22 0 le_rfl σ4
      hpad4 hx4
    rw [spState_zero, Nat.zero_add, ← spC_eq] at hM
    simp only [Nat.zero_add] at hM
    refine (hM.keep (Q := fun σ => SpPw σ ∧ SpDw d σ) (Q' := fun σ => SpPw σ ∧ SpDw d σ) ⟨hpow4, hx4⟩
      (fun σ' he' hq => ⟨hq.1.keep he' (by simp [spPad]), hq.2.keep he' (by simp [spDg, spPad])⟩)).mono
      le_rfl le_rfl (fun σ' ⟨hp, hq⟩ => ⟨hq.1, hq.2, hp⟩)
  · have e : spHints ++ (spRanges ++ ((padRun spPad ++ [cst (spPad + 5) closeLane]) ++
        (List.range 22).map spMatch)) = (spHints ++ (spRanges ++ (padRun spPad ++
          [cst (spPad + 5) closeLane]))) ++ (List.range 22).map spMatch := by
      simp only [List.append_assoc]
    rw [valsList_append (spCopies ++ spPowers), e, valsList_append (spHints ++ _)]
    exact (spInit_seq.numBelow.mono (by simp only [spPad] at hC; omega)).append ((hnbR.mono hC).append hnbM)

/-! ## The codeword's values -/

theorem spDigit_of {d : Nat → Nat} (hd : ∀ i, d i < 4) {σ : Val} (hx : SpDw d σ) {i : Nat} (hi : i < 64) :
    spDigit σ i = d i := by
  unfold spDigit spDigitWord
  rw [spArmAt_eq (spK_lt64 d _) (hx _ (by omega)), Nat.mod_eq_of_lt (spK_lt d _),
    spK_digit d (spN_mod i hi), show 3 * (i / 3) + i % 3 = i by omega, spDn_digit hd hi]

/-- **The codeword's product and encoding**, the dispatches' digits `d`'s. -/
theorem spVals {d : Nat → Nat} (hd : ∀ i, d i < 4) (hsum : ∑ i ∈ Finset.range 64, d i = 128)
    {σ : Val} {rest : List Stmt} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (spGs.1 ++ rest) next kret) (hpow : SpPw σ) (hpad : PadOK σ spPad)
    (hx : SpDw d σ) :
    σ (.n (spEnc false 1 (spState 21).2.2)) = eOfNat128 (spX d 64) ∧
      σ (.n (spProd false 1 (spState 21).2.2)) = spTarget := by
  rw [spGs_fst] at h
  obtain ⟨-, hg⟩ := spMatches_sound (C := C) (rd := rd) (σ := σ) 22 0 (by simpa only [Nat.zero_add] using h)
  have hgrp : ∀ p < 22, SpGroupOK rd σ p := fun p hp => by simpa using hg p hp
  obtain ⟨-, hprod, henc⟩ := spCodeword_sound hpow hpad hgrp
  have hdig : ∀ i < 64, spDigit σ i = d i := fun i hi => spDigit_of hd hx hi
  refine ⟨by rw [henc, spX_congr hdig], ?_⟩
  rw [hprod, Finset.sum_congr rfl fun i hi => hdig i (Finset.mem_range.mp hi), hsum, spTarget_eq]

/-! ## The checks and the leaf -/

theorem upds3 (σ : Val) (e0 e1 e2 : E) (k : Nat) :
    upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n k) = e0 ∧
      upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n (k + 1)) = e1 ∧
      upds σ [(k, e0), (k + 1, e1), (k + 2, e2)] (.n (k + 2)) = e2 := by
  refine ⟨upds_cons_self _ _ _ _, ?_, ?_⟩
  · rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
  · rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]

/-- The codeword's product and encoding lie below the checks. -/
theorem spEP_lt : spEnc false 1 (spState 21).2.2 < spC ∧ spProd false 1 (spState 21).2.2 < spC := by
  have h := spState_step 21
  rw [← spC_eq] at h
  have h1 : spN 21 = 1 := rfl
  rw [h1] at h
  unfold spEnc spProd
  rw [groupStart_eq]
  exact ⟨by omega, by omega⟩

theorem spChecks_eq : spChecks =
    [.atom (.assertEq (.n (spEnc false 1 (spState 21).2.2)) (.n 3)), cst spC spTarget,
      .atom (.assertEq (.n (spProd false 1 (spState 21).2.2)) (.n spC)), cst (spC + 1) spPkC,
      addS (.n (spC + 2)) (.n 2) (.n (spC + 1))] := by
  rw [spChecks, spGs_out]

/-- **The checks complete**, the encoding the argument's and the product the target. -/
theorem spCheck_complete (σ : Val)
    (henc : σ (.n (spEnc false 1 (spState 21).2.2)) = σ (.n 3))
    (hprod : σ (.n (spProd false 1 (spState 21).2.2)) = spTarget) :
    Completes C rd spC (spC + 3) spChecks σ
      (fun σ' => σ' (.n (spC + 2)) = σ (.n 2) + spPkC) := by
  obtain ⟨hE, hP⟩ := spEP_lt
  have hC := spC_ge
  obtain ⟨e0, e1, e2⟩ := upds3 σ spTarget spPkC (σ (.n 2) + spPkC) spC
  have hext : Ext spC (spC + 3) σ
      (upds σ [(spC, spTarget), (spC + 1, spPkC), (spC + 2, σ (.n 2) + spPkC)]) :=
    upds_ext σ _ (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp)
  set σ3 := upds σ [(spC, spTarget), (spC + 1, spPkC), (spC + 2, σ (.n 2) + spPkC)]
    with hσ3
  have below : ∀ j < spC, σ3 (.n j) = σ (.n j) := fun j hj => hext.apply (Or.inl hj)
  rw [spChecks_eq]
  refine completes_atoms rfl hext (by rw [e2]) (fun a ha => ?_)
  simp only [cst, addS, List.mem_cons, Stmt.atom.injEq, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · show σ3 _ + σ3 _ = 0
    rw [below _ hE, below 3 (by simp only [spPad] at hC; omega), henc, e_add_self]
  · exact e0
  · show σ3 _ + σ3 _ = 0
    rw [below _ hP, e0, hprod, e_add_self]
  · exact e1
  · show σ3 _ = σ3 _ + σ3 _
    rw [e2, below 2 (by simp only [spPad] at hC; omega), e1]

theorem spChecks_nb : NumBelow (spC + 3) (Stmt.valsList spChecks) := by
  obtain ⟨hE, hP⟩ := spEP_lt
  have hC := spC_ge
  intro v hv
  rw [spChecks_eq] at hv
  simp only [cst, addS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | rfl) | rfl | (rfl | rfl) | rfl | (rfl | rfl | rfl)
  all_goals exact ⟨_, by simp only [spPad] at hC; omega, rfl⟩

/-- Group `q`'s starts and tips lie below the checks. -/
theorem spState_le_C {q : Nat} (hq : q < 22) : (spState (q + 1)).2.2 + 6 ≤ spC := by
  have := spState_mono (q + 1) (21 - q)
  rw [show q + 1 + (21 - q) = 22 by omega, ← Nat.add_le_add_iff_right (n := 6), ← spC_eq] at this
  exact this

theorem SpMPost.keep {d : Nat → Nat} {vals : Nat → E} {σ σ' : Val} (h : SpMPost (spK d) vals 0 22 σ)
    {lo hi : Nat} (he : Ext lo hi σ σ') (hlo : spC ≤ lo) : SpMPost (spK d) vals 0 22 σ' := by
  have hC := spC_ge
  refine ⟨spGood_congr (B := lo) (by omega) he.agree h.1, fun q h1 h2 t ht => ?_⟩
  obtain ⟨j, ej, -, hj⟩ := spPos_lt (K := spK d) (q := q) (spK_lt d q) ht
  have := spState_le_C (q := q) (by omega)
  rw [ej, he.apply (Or.inl (by omega)), ← ej]
  exact h.2 q h1 h2 t ht

theorem spLeafCells_lt : ∀ v ∈ spLeafCells, ∃ j, v = .n j ∧ j < spC + 3 := by
  have hC := spC_ge
  intro v hv
  rw [spLeafCells_eq] at hv
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hv
  rcases hv with rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · exact ⟨0, rfl, by omega⟩
  · exact ⟨1, rfl, by omega⟩
  · exact ⟨_, rfl, by omega⟩
  · have h := (spTip_lt (q := i / 3) (spN_mod i hi)).2
    have := spState_le_C (q := i / 3) (by omega)
    exact ⟨_, rfl, by omega⟩

theorem spLeafCells_KCb : ∀ c ∈ spLeafCells.map KC.cell, KCb (spC + 3) c := by
  intro c hcm
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hcm
  obtain ⟨j, ej, hj⟩ := spLeafCells_lt v hv
  exact ⟨j, hj, ej⟩

/-- **The leaf's message completes** over the padding run. -/
theorem spLeaf_complete (σ : Val) (hp : PadOK σ spPad) :
    Completes C rd (spC + 3) spLeafK.2.1 spLeafK.1 σ (fun _ => True) := by
  have hC := spC_ge
  exact (kMsg_complete (C := C) (rd := rd) (pad := spPad)
    (cells := spLeafCells.map KC.cell) (len := 1072) (tailRun := false) (b := spC + 3) σ hp
    (by omega) spLeafCells_KCb (fun h => by simp at h)).1

theorem spLeafK_le : spC + 3 ≤ spLeafK.2.1 :=
  kMsg_le (by have := spC_ge; omega) spLeafCells_KCb

theorem spLeafK_out : spLeafK.2.2 < spLeafK.2.1 := by
  have := kMsg_out spPad (spLeafCells.map KC.cell) 1072 false (spC + 3)
  show (kMsg spPad (spLeafCells.map KC.cell) 1072 false none (spC + 3)).2.2 <
    (kMsg spPad (spLeafCells.map KC.cell) 1072 false none (spC + 3)).2.1
  omega

theorem spLeaf_nb : NumBelow spLeafK.2.1 (Stmt.valsList spLeafK.1) :=
  kMsg_numBelow (by have := spC_ge; omega) spLeafCells_KCb

/-! ## `sp_wots`'s template, complete -/

/-- **The chain starts read off the frame are the loaded ones.** -/
theorem spStart_eq {d : Nat → Nat} {vals : Nat → E} {σ : Val} (hx : SpDw d σ)
    (hpost : SpMPost (spK d) vals 0 22 σ) {i : Nat} (hi : i < 64) : σ (spStart σ i) = vals i := by
  have hp : i / 3 < 22 := by omega
  have hs : spStart σ i = spPos (spK d) (i / 3) (i % 3) := by
    unfold spStart spStartAt spPos grpPos
    dsimp only
    rw [spArmAt_eq (spK_lt64 d _) (hx _ hp), spArmB_eq _ _ _ _ _ _ (le_of_lt (spK_lt d _))]
    rfl
  rw [hs, hpost.2 (i / 3) (Nat.zero_le _) (by omega) (i % 3) (spN_mod i hi),
    show 3 * (i / 3) + i % 3 = i by omega]

/-- **`sp_wots`'s template is complete**: for any `pp`, `a0`, `a1`, digits below `4` of sum `128` and
chain values, on a memory of at least `64` words, its body holds of some
valuation whose arguments are `pp`, `a0`, `a1` and the digits' encoding (`spX`), returning the
one-time leaf of the values (`spLeafCell`). -/
theorem sp_wots_completeT {pp a0 a1 : E} {d : Nat → Nat} (hd : ∀ i, d i < 4)
    (hsum : ∑ i ∈ Finset.range 64, d i = 128) {vals : Nat → E} (hm : MemOK rd 64) :
    ∃ σ : Val, σ (.n 0) = pp ∧ σ (.n 1) = a0 ∧ σ (.n 2) = a1 ∧ σ (.n 3) = eOfNat128 (spX d 64) ∧
      Stmt.HoldsList C rd σ spBodyT False (fun rs => rs = [spLeafCell pp a0 a1 d vals]) := by
  set σI : Val := Function.update (Function.update (Function.update (Function.update (fun _ => 0)
    (.n 0) pp) (.n 1) a0) (.n 2) a1) (.n 3) (eOfNat128 (spX d 64)) with hσI
  have i0 : σI (.n 0) = pp := by simp [hσI]
  have i1 : σI (.n 1) = a0 := by simp [hσI]
  have i2 : σI (.n 2) = a1 := by simp [hσI]
  have i3 : σI (.n 3) = eOfNat128 (spX d 64) := by simp [hσI]
  have hC := spC_ge
  obtain ⟨hA, hnbA⟩ := spHead_complete (C := C) (rd := rd) d vals hm σI
  -- the checks
  have hB : Completes C rd 4 (spC + 3) (spHeadT ++ spChecks) σI
      (fun σ' => (SpDw d σ' ∧ SpMPost (spK d) vals 0 22 σ') ∧
        σ' (.n (spC + 2)) = σI (.n 2) + spPkC) := by
    refine Completes.append (m := spC) (by simp only [spPad] at hC; omega) (by omega) hnbA hA.withHolds
      (fun σ2 he2 ⟨⟨hpow, hx, hpost⟩, hh2⟩ => ?_)
    have hag2 : AgreeBelow 4 σI σ2 := he2.agree
    have h23 : σ2 (.n 3) = eOfNat128 (spX d 64) := by rw [← hag2 3 (by norm_num)]; exact i3
    have h22 : σ2 (.n 2) = σI (.n 2) := (hag2 2 (by norm_num)).symm
    have hs := (holdsList_split_atoms (xs := spPre) spPre_atoms (by rw [← spHeadT]; exact hh2)).2
    rw [show spGs.1 = spGs.1 ++ [] by simp] at hs
    obtain ⟨henc, hprod⟩ := spVals hd hsum hs hpow hpost.1 hx
    refine ((spCheck_complete (C := C) (rd := rd) σ2 (by rw [henc, h23]) hprod).keep
      (Q := fun σ => SpDw d σ ∧ SpMPost (spK d) vals 0 22 σ)
      (Q' := fun σ => SpDw d σ ∧ SpMPost (spK d) vals 0 22 σ) ⟨hx, hpost⟩
      (fun σ' he' hq => ⟨hq.1.keep he' (by simp only [spDg, spPad] at hC ⊢; omega),
        hq.2.keep he' le_rfl⟩)).mono le_rfl le_rfl
      (fun σ' ⟨h1, h2⟩ => ⟨h2, by rw [h1, h22]⟩)
  -- the leaf
  have hLe : spC + 3 ≤ spLeafK.2.1 := spLeafK_le
  have hnbB : NumBelow (spC + 3) (Stmt.valsList (spHeadT ++ spChecks)) := by
    rw [valsList_append]; exact (hnbA.mono (by omega)).append spChecks_nb
  have hL : Completes C rd 4 spLeafK.2.1 ((spHeadT ++ spChecks) ++ spLeafK.1) σI
      (fun σ' => SpDw d σ' ∧ SpMPost (spK d) vals 0 22 σ') := by
    refine Completes.append (m := spC + 3) (by omega) hLe hnbB hB (fun σ3 _ ⟨⟨hx3, hpost3⟩, _⟩ => ?_)
    refine ((spLeaf_complete (C := C) (rd := rd) σ3 hpost3.1).keep
      (Q := fun σ => SpDw d σ ∧ SpMPost (spK d) vals 0 22 σ)
      (Q' := fun σ => SpDw d σ ∧ SpMPost (spK d) vals 0 22 σ) ⟨hx3, hpost3⟩
      (fun σ' he' hq => ⟨hq.1.keep he' (by simp only [spDg, spPad] at hC ⊢; omega),
        hq.2.keep he' (by omega)⟩)).mono le_rfl le_rfl (fun σ' h => h.2)
  -- the copy
  have hlt : spLeafK.2.2 < spLeafK.2.1 := spLeafK_out
  have hnbL : NumBelow spLeafK.2.1 (Stmt.valsList ((spHeadT ++ spChecks) ++ spLeafK.1)) := by
    rw [valsList_append]; exact (hnbB.mono hLe).append spLeaf_nb
  have hD : Completes C rd 4 (spLeafK.2.1 + 1)
      (((spHeadT ++ spChecks) ++ spLeafK.1) ++ [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)])
      σI (fun σ' => SpDw d σ' ∧ SpMPost (spK d) vals 0 22 σ') := by
    refine Completes.append (m := spLeafK.2.1) (by omega) (by omega) hnbL hL (fun σ4 he4 hp4 => ?_)
    have hext : Ext spLeafK.2.1 (spLeafK.2.1 + 1) σ4 (upds σ4 [(spLeafK.2.1, σ4 (.n spLeafK.2.2))]) :=
      upds_ext σ4 _ (by simp)
    refine completes_atoms rfl hext ⟨hp4.1.keep hext (by simp only [spDg, spPad] at hC ⊢; omega),
      hp4.2.keep hext (by omega)⟩ (fun a ha => ?_)
    simp only [copyS, List.mem_singleton, Stmt.atom.injEq] at ha
    subst ha
    show upds σ4 _ _ = upds σ4 _ _
    rw [upds_cons_self, hext.apply (Or.inl hlt)]
  obtain ⟨σf, hef, ⟨hxf, hpostf⟩, hhf⟩ := hD
  have f0 : σf (.n 0) = pp := by rw [hef.apply (Or.inl (by norm_num))]; exact i0
  have f1 : σf (.n 1) = a0 := by rw [hef.apply (Or.inl (by norm_num))]; exact i1
  have f2 : σf (.n 2) = a1 := by rw [hef.apply (Or.inl (by norm_num))]; exact i2
  have f3 : σf (.n 3) = eOfNat128 (spX d 64) := by rw [hef.apply (Or.inl (by norm_num))]; exact i3
  have hbody : spBodyT = (((spHeadT ++ spChecks) ++ spLeafK.1) ++
      [copyS (.n spLeafK.2.1) (.n spLeafK.2.2)]) ++ [.ret [.n spLeafK.2.1]] := by
    rw [spBodyT_split, spTailOf]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hH : Stmt.HoldsList C rd σf spBodyT False (fun rs => rs = [σf (.n spLeafK.2.1)]) := by
    rw [hbody, holdsList_append]
    exact hhf _ _ rfl
  obtain ⟨lf, hrets, -, -, -, hval⟩ := sp_wots_soundT hH
  have e : σf (.n spLeafK.2.1) = spLeafCell pp a0 a1 d vals := by
    rw [List.singleton_inj.mp hrets, hval, f0, f1, f2]
    exact spLeafCell_congr (fun i hi => spDigit_of hd hxf hi) (fun i hi => spStart_eq hxf hpostf hi)
  refine ⟨σf, f0, f1, f2, f3, ?_⟩
  rw [← e]
  exact hH

end
end LeanVM.Guest.B1.Sig
