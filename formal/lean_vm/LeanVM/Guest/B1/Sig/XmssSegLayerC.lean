/-
  LeanVM.Guest.B1.Sig.XmssSegLayerC

  A layer of leanXMSS's check inline in `__loop2`, after its message digest, up to its one-time
  leaf, completes: the step addresses, the codeword at the digest's digits and the leaf's
  `KECCAK`.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegCodeC
public import LeanVM.Guest.B1.Sig.XmssSegSound
public import LeanVM.Guest.B1.Sig.XmssCore

/-!
# A layer up to its leaf, complete

* `sCodewordT_numBelow`: the codeword's values are numbered below its end;
* `sCw_eq`: the layer's codeword with the clamped step;
* `sLeaf_complete`: the step addresses, the codeword (its digits the base-4 digits of the
  digest, the chains' starts loaded), the leaf's address and its `KECCAK` complete.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

variable {C : CallRel} {rd : Reader}

attribute [local irreducible] kMsg sCodewordT lxWindowT

theorem sCodewordT_numBelow {W : WotsT} {B : Nat} (hW : StepShape W B) {target : E} {d0 : V} {dg : Nat}
    (hB : B ≤ dg) (hpw : ∀ j, NBv B (W.power j)) (hd0 : NBv dg d0) :
    NumBelow (sCodewordT W target d0 dg).2.1 (Stmt.valsList (sCodewordT W target d0 dg).1) := by
  rw [sCodewordT_fst, sCodewordT_snd, ← sgState_eq_sSt]
  have h15 : dg + 70 ≤ (sgState W (dg + 70) 15).2.2 := sgState_mono W (dg + 70) 0 15 (by omega)
  obtain ⟨hpi, hei⟩ := sgState_in W (dg + 70) 15 le_rfl
  have hg : NumBelow ((sgState W (dg + 70) 15).2.2 + 6)
      (Stmt.valsList ((List.range 15).map fun q => sgMatch W dg (dg + 70) q)) :=
    sGroups_numBelow hW (dg := dg) (v0 := dg + 70) (by omega) (by omega) hpw 15 0 (by omega)
  simp only [valsList_append]
  refine NumBelow.append ?_ (NumBelow.append ((digitChecks_numBelow (dg := dg) 15).mono (by omega))
    (NumBelow.append ?_ (NumBelow.append (hg.mono (by omega)) ?_)))
  · rw [valsList_hint]
    intro v hv
    obtain ⟨j, hj, rfl⟩ := mem_runV.mp hv
    exact ⟨_, by omega, rfl⟩
  · intro v hv
    simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.mem_singleton] at hv
    exact ⟨_, by omega, hv⟩
  · obtain ⟨j, hj, rfl⟩ := hd0
    obtain ⟨j1, hj1, e1⟩ := hpi
    obtain ⟨j2, hj2, e2⟩ := hei
    rw [e1, e2]
    intro v hv
    simp only [copyS, cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by omega, rfl⟩

theorem sCw_eq (layer b : Nat) :
    sCw layer b = sCodewordT (sWc layer b) xTarget (sD0 layer b) (sA layer b + 6) :=
  sCodewordT_c layer b _ _ _

/-- Group `p`'s digits of `N`: its `lxN p` base-4 digits from `4p`. -/
def lxK (N p : Nat) : Nat := N / 4 ^ (4 * p) % 4 ^ lxN p

theorem lxK_lt (N p : Nat) : lxK N p < 4 ^ lxN p := Nat.mod_lt _ (by positivity)

theorem lxDigit_lxK (N : Nat) {i : Nat} (hi : i < 58) : lxDigit (lxK N) i = N / 4 ^ i % 4 := by
  have ht : i % 4 < lxN (i / 4) := by unfold lxN; split <;> omega
  unfold lxDigit lxK
  rw [mod_pow_div_mod _ _ _ ht, Nat.div_div_eq_div_mul, ← pow_add, show 4 * (i / 4) + i % 4 = i by omega]

theorem sTip_nb (layer b : Nat) {i : Nat} (hi : i < 58) :
    NBv ((sCw layer b).2.1 - 1) (sTip (sW layer b) (sA layer b + 6 + 70) i) := by
  rw [sTip_c layer b _ hi, sCw_eq, sCodewordT_snd]
  unfold sTip
  simp only [← sgState_eq_sSt]
  have hq : i / 4 ≤ 14 := by omega
  have ht : i % 4 < lxN (i / 4) := by unfold lxN; split <;> omega
  have h1 := (sgTip_lt (sWc layer b) (sA layer b + 6 + 70) hq ht).2
  have h2 := sgState_mono (sWc layer b) (sA layer b + 6 + 70) (i / 4 + 1) (15 - (i / 4 + 1)) (by omega)
  rw [show i / 4 + 1 + (15 - (i / 4 + 1)) = 15 by omega] at h2
  exact ⟨_, by omega, rfl⟩

theorem sCw_snd_ge (layer b : Nat) : sA layer b + 6 + 77 ≤ (sCw layer b).2.1 := by
  rw [sCw_eq, sCodewordT_snd, ← sgState_eq_sSt]
  have := sgState_mono (sWc layer b) (sA layer b + 6 + 70) 0 15 (by omega)
  exact le_trans (by simp only [sgState]; omega) (Nat.add_le_add_right (Nat.add_le_add_right this 6) 1)

theorem sgPos_nb (layer b N : Nat) {i : Nat} (hi : i < 58) :
    NBv (sCw layer b).2.1 (sgPos (sWc layer b) (sA layer b + 6 + 70) (lxK N) (i / 4) (i % 4)) := by
  have hq : i / 4 ≤ 14 := by omega
  have ht : i % 4 < lxN (i / 4) := by unfold lxN; split <;> omega
  obtain ⟨j, e, -, hj⟩ := sgPos_lt (W := sWc layer b) (v0 := sA layer b + 6 + 70) (K := lxK N) hq (lxK_lt N _) ht
  have h2 := sgState_mono (sWc layer b) (sA layer b + 6 + 70) (i / 4 + 1) (15 - (i / 4 + 1)) (by omega)
  rw [show i / 4 + 1 + (15 - (i / 4 + 1)) = 15 by omega] at h2
  rw [sCw_eq, sCodewordT_snd, ← sgState_eq_sSt]
  exact ⟨j, by omega, e⟩

/-- **A layer after its digest, up to its leaf, completes**: the step addresses, the codeword at
the base-4 digits `N` of the digest (which sum to `106`), the chains' starts `vals` loaded, and the
leaf's `KECCAK`. Afterwards (on any valuation agreeing below the leaf's end) the digit words are the
groups' digits and the starts read off are `vals`. -/
theorem sLeaf_complete {layer b : Nat} (hA : 103 ≤ sA layer b) (hm : MemOK rd 256) (σ : Val)
    (hpad : PadOK σ sLxPad) (hpow : ∀ s < 13, σ (sPower s) = gen ^ s)
    (hidx : NBv (sA layer b) (sLxIdx layer b))
    (hd0 : NBv (sA layer b) (sD0 layer b)) {N : Nat}
    (hN : σ (sD0 layer b) = lit (∑ i ∈ Finset.range 58, N / 4 ^ i % 4 * 4 ^ i))
    (hs : ∑ i ∈ Finset.range 58, N / 4 ^ i % 4 = 106) (vals : Nat → E) :
    Completes C rd (sA layer b) (sLeafK layer b).2.1
      (xStepAddrs (sLxIdx layer b) (sA layer b) ++ ((sCw layer b).1 ++
        ([cst (sCw layer b).2.1 (word (tw 2) 0), addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b)
          (.n (sCw layer b).2.1)] ++ (sLeafK layer b).1))) σ
      (fun σ' => ∀ σ'', AgreeBelow (sLeafK layer b).2.1 σ' σ'' →
        (∀ q < 15, σ'' (.n (sA layer b + 6 + q)) = ofK (addressOfIndex (lxK N q))) ∧
        ∀ i < 58, σ'' (sStart (sW layer b) σ'' (sA layer b + 6) (sA layer b + 6 + 70) i) = vals i) := by
  set dg := sA layer b + 6 with hdg
  have b1 := sCw_snd_ge layer b
  have htips : (sCw layer b).2.2 = (List.range 58).map (sTip (sW layer b) (dg + 70)) :=
    sCodewordT_tips _ _ _ _
  have hcells : ∀ c ∈ (sLeafCells layer b).map KC.cell, ∃ v, c = KC.cell v ∧
      (v = sLxPP ∨ v = .n ((sCw layer b).2.1 + 1) ∨ ∃ i < 58, v = sTip (sW layer b) (dg + 70) i) := by
    intro c hc
    simp only [sLeafCells, List.map_cons, List.mem_cons, htips, List.map_map, List.mem_map,
      List.mem_range, Function.comp_apply] at hc
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, rfl, Or.inr (Or.inr ⟨i, hi, rfl⟩)⟩
  have hcellNB : ∀ c ∈ (sLeafCells layer b).map KC.cell, KCb ((sCw layer b).2.1 + 2) c := by
    intro c hc
    obtain ⟨v, rfl, hv'⟩ := hcells c hc
    rcases hv' with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨66, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
    · exact (sTip_nb layer b hi).mono' (by omega)
  have b2 : (sCw layer b).2.1 + 2 ≤ (sLeafK layer b).2.1 :=
    kMsg_le (show sLxPad + 5 ≤ (sCw layer b).2.1 + 2 by simp [sLxPad]; omega) hcellNB
  -- the step addresses
  refine Completes.seq (xStepAddrs_seq hidx) (by omega) (fun σ1 he1 hh1 => ?_)
  have hag1 : AgreeBelow (sA layer b) σ σ1 := he1.agree
  have hg1 : SGood layer b σ1 := by
    refine ⟨hpad.congr (by simp [sLxPad]; omega) hag1, fun s hs => ?_⟩
    rw [show sPower s = V.n (75 + s) from rfl, hag1.apply ⟨75 + s, by omega, rfl⟩]; exact hpow s hs
  -- the codeword
  have hsum : gen ^ (∑ i ∈ Finset.range 58, lxDigit (lxK N) i) = xTarget := by
    rw [Finset.sum_congr rfl fun i hi => lxDigit_lxK N (Finset.mem_range.mp hi), hs, xTarget_eq]
  have hd0v : σ1 (sD0 layer b) = lit (∑ i ∈ Finset.range 58, lxDigit (lxK N) i * 4 ^ i) := by
    rw [Finset.sum_congr rfl fun i hi => by rw [lxDigit_lxK N (Finset.mem_range.mp hi)], hag1.apply hd0, hN]
  have hcw := sCodewordT_complete (C := C) (rd := rd) (sWc_shape hA) (sGood_stable hA) (sWc_atoms layer b)
    (fun σ hg => sWc_sound hg) (fun σ hg => sWc_pow hg) (target := xTarget) (d0 := sD0 layer b) (dg := dg)
    le_rfl (sWc_pw layer b hA) hm (lxK N) (fun p _ => lxK_lt N p) vals (hd0.mono' (by omega)) σ1 hg1
    hsum hd0v
  rw [← sCw_eq] at hcw
  have hcwNB : NumBelow (sCw layer b).2.1 (Stmt.valsList (sCw layer b).1) := by
    rw [sCw_eq]
    exact sCodewordT_numBelow (sWc_shape hA) le_rfl (sWc_pw layer b hA) (hd0.mono' (by omega))
  refine Completes.append (m := (sCw layer b).2.1) (by omega) (by omega) hcwNB hcw (fun σ2 he2 hp2 => ?_)
  obtain ⟨hg2, hdg2, hkp2⟩ := hp2
  -- the leaf's address
  have hseq : SeqOK (sCw layer b).2.1 [cst (sCw layer b).2.1 (word (tw 2) 0),
      addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b) (.n (sCw layer b).2.1)] ((sCw layer b).2.1 + 2) :=
    ⟨rfl, ⟨rfl, hidx.mono' (by omega), ⟨_, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq hseq (by omega) (fun σ3 he3 _ => ?_)
  have hag3 : AgreeBelow (sCw layer b).2.1 σ2 σ3 := he3.agree
  have hpad3 : PadOK σ3 sLxPad := hg2.1.congr (b := (sCw layer b).2.1) (by simp [sLxPad]; omega) hag3
  obtain ⟨hk1, hk2, -⟩ := kMsg_complete (C := C) (rd := rd) (tailRun := false) (len := 960) σ3 hpad3
    (by simp [sLxPad]; omega) hcellNB (fun h => by simp at h)
  have hQ3 : (∀ q < 15, σ3 (.n (dg + q)) = ofK (addressOfIndex (lxK N q))) ∧
      ∀ i < 58, σ3 (sgPos (sWc layer b) (dg + 70) (lxK N) (i / 4) (i % 4)) = vals i := by
    refine ⟨fun q hq => by rw [hag3.apply ⟨dg + q, by omega, rfl⟩]; exact hdg2 q hq, fun i hi => ?_⟩
    rw [hag3.apply ((sgPos_nb layer b N hi).mono' le_rfl), ← sStart_eq_sgPos (sWc layer b) σ2
      (fun p _ => lxK_lt N p) hdg2 hi]
    exact hkp2 i hi
  refine (hk1.keep (Q := fun σ => PadOK σ sLxPad ∧ (∀ q < 15, σ (.n (dg + q)) = ofK (addressOfIndex (lxK N q))) ∧
      ∀ i < 58, σ (sgPos (sWc layer b) (dg + 70) (lxK N) (i / 4) (i % 4)) = vals i)
    (Q' := fun σ => PadOK σ sLxPad ∧ (∀ q < 15, σ (.n (dg + q)) = ofK (addressOfIndex (lxK N q))) ∧
      ∀ i < 58, σ (sgPos (sWc layer b) (dg + 70) (lxK N) (i / 4) (i % 4)) = vals i) ⟨hpad3, hQ3⟩
    (fun σ' he' ⟨hp, hq⟩ => ⟨hp.congr (b := (sCw layer b).2.1 + 2) (by simp [sLxPad]; omega) he'.agree, fun q hq' => by rw [he'.apply (Or.inl (by omega))]; exact hq.1 q hq',
      fun i hi => by
        obtain ⟨j, hj, e⟩ := sgPos_nb layer b N hi
        rw [e, he'.apply (Or.inl (by omega)), ← e]; exact hq.2 i hi⟩)).mono le_rfl le_rfl
    (fun σ4 ⟨_, _, hq4⟩ σ'' hag => ⟨fun q hq => ?_, fun i hi => ?_⟩)
  · rw [hag.apply ⟨dg + q, by omega, rfl⟩]; exact hq4.1 q hq
  · have hx'' : ∀ q < 15, σ'' (.n (dg + q)) = ofK (addressOfIndex (lxK N q)) := fun q hq => by
      rw [hag.apply ⟨dg + q, by omega, rfl⟩]; exact hq4.1 q hq
    rw [sStart_c layer b σ'' _ _ hi, sStart_eq_sgPos (sWc layer b) σ'' (fun p _ => lxK_lt N p) hx'' hi]
    obtain ⟨j, hj, e⟩ := sgPos_nb layer b N hi
    rw [e, hag.apply ⟨j, by omega, rfl⟩, ← e]
    exact hq4.2 i hi

end
end LeanVM.Guest.B1.Sig
