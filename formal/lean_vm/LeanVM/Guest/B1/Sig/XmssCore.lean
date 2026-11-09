/-
  LeanVM.Guest.B1.Sig.XmssCore

  A layer of `verify_lean_xmss` after its message digest completes: its step addresses, its
  codeword on the digest's digits, its one-time leaf and its path, the chains' starts and the
  path's siblings loaded and kept.
-/

module

public import LeanVM.Guest.B1.Sig.CompleteKit
public import LeanVM.Guest.B1.Sig.XmssStep

/-!
# A layer of `verify_lean_xmss`, complete

* `nDigits G N q`: the digits of group `q` of the base-4 number `N`; `digK_nDigits`;
* `xCore_complete`: the statements of a layer after its digest complete from a valuation holding
  the prologue's facts and a digest `lit N` whose `58` digits sum to `106`, the chains' starts
  `vals` and the path's siblings `sibs` loaded: its root canonical, and, under any agreement below
  its end, the digits, starts and siblings kept.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-- The digits of group `q` of a codeword of `G` groups, from the base-4 number `N`. -/
def nDigits (G N q : Nat) : Nat := N / 4 ^ (3 * q) % 4 ^ cwN G q

theorem nDigits_lt (G N q : Nat) : nDigits G N q < 4 ^ cwN G q := Nat.mod_lt _ (by positivity)

theorem mod_pow_div_mod (x n t : Nat) (ht : t < n) : x % 4 ^ n / 4 ^ t % 4 = x / 4 ^ t % 4 := by
  rw [show 4 ^ n = 4 ^ t * 4 ^ (n - t) by rw [← pow_add]; congr 1; omega, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self 4 (by omega))]

theorem digK_nDigits (G N : Nat) {i : Nat} (hi : i < 3 * G + 1) : digK (nDigits G N) i = N / 4 ^ i % 4 := by
  unfold digK nDigits
  have ht : i % 3 < cwN G (i / 3) := by unfold cwN; split <;> omega
  rw [mod_pow_div_mod _ _ _ ht, Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  omega

theorem canon_eOfNat (n : Nat) : IsCanonical128 (eOfNat n) := by
  rw [← word_eq_eOfNat]; exact canon_word n 0

theorem canon_hcell (cs : List E) : IsCanonical128 (hcell cs).1 := by
  simp [IsCanonical128, hcell, digestHalves]

theorem xStepAddrs_seq {idx : V} {a : Nat} (h : NBv a idx) : SeqOK a (xStepAddrs idx a) (a + 6) :=
  ⟨rfl, ⟨rfl, h.mono' (by omega), ⟨a, by omega, rfl⟩⟩, rfl, ⟨rfl, h.mono' (by omega), ⟨a + 2, by omega, rfl⟩⟩,
    rfl, ⟨rfl, h.mono' (by omega), ⟨a + 4, by omega, rfl⟩⟩, rfl⟩

attribute [local irreducible] kMsg codewordT merkleT

variable {C : CallRel} {rd : Reader}

theorem xCw_eq (layer b : Nat) : xCw layer b = codewordT (xWc layer b) 19 xTarget (xD0 layer b) (xA layer b + 6) :=
  codewordT_weq (xW_weq layer b) _ _ _ (by norm_num)

/-- **A layer after its message digest completes.** -/
theorem xCore_complete {layer b : Nat} (hA : 211 ≤ xA layer b) (hm : MemOK rd 64) (σ : Val)
    (hpre : XPre σ) (hpad : PadOK σ xPad) (hPc : IsCanonical128 (σ (.n 1)))
    (hidx : NBv (xA layer b) (xIdx layer b)) (hidxc : IsCanonical128 (σ (xIdx layer b)))
    (hd0 : NBv (xA layer b) (xD0 layer b)) {N : Nat}
    (hN : σ (xD0 layer b) = lit (∑ i ∈ Finset.range 58, N / 4 ^ i % 4 * 4 ^ i))
    (hs : ∑ i ∈ Finset.range 58, N / 4 ^ i % 4 = 106)
    (vals : Nat → E) (hv : ∀ i, IsCanonical128 (vals i))
    {bits : Nat → Bool} (hbits : ∀ l < 16, NBv (xA layer b) (xBitOf layer l) ∧
      σ (xBitOf layer l) = if bits l then 1 else 0)
    (hnodes : ∀ l nd, xNodeOf layer l = some nd → NBv (xA layer b) nd ∧ IsCanonical128 (σ nd))
    {sibs : Nat → E} (hsc : ∀ l < 16, IsCanonical128 (sibs l)) :
    Completes C rd (xA layer b) (xMk layer b).2.1
      (xStepAddrs (xIdx layer b) (xA layer b) ++ ((xCw layer b).1 ++
        ([cst (xCw layer b).2.1 (word (tw 2) 0 0), addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b)
          (.n (xCw layer b).2.1)] ++ ((xLeafK layer b).1 ++ (xMk layer b).1)))) σ
      (fun σ' => IsCanonical128 (σ' (xMk layer b).2.2) ∧ ∀ σ'', AgreeBelow (xMk layer b).2.1 σ' σ'' →
        (∀ q ≤ 19, σ'' (.n (cwState (xW layer b) (xA layer b + 6) q).2.2) = ofK (addressOfIndex (nDigits 19 N q))) ∧
        (∀ i < 58, σ'' (cwPos (xW layer b) 19 (xA layer b + 6) (nDigits 19 N) i) = vals i) ∧
        ∀ l < 16, mSib σ'' (xBitOf layer) l (mBase (xNodeOf layer) 0 l (xLeafK layer b).2.1) = sibs l) := by
  -- the bounds
  have b1 : xA layer b + 6 < (xCw layer b).2.1 := by
    rw [xCw_eq]
    exact cwBase_lt (xWc layer b) (q := 0) (G := 19) _ _ _ (by norm_num)
  have htips : (xCw layer b).2.2 = (List.range 58).map (cwTip (xW layer b) (xA layer b + 6)) :=
    codewordT_tips (xW layer b) (G := 19) (by norm_num) _ _ _
  have htipNB : ∀ i < 58, NBv (xCw layer b).2.1 (cwTip (xW layer b) (xA layer b + 6) i) := by
    intro i hi
    obtain ⟨j, ej, hj⟩ := cwTip_lt (xW layer b) (G := 19) xTarget (xD0 layer b) (xA layer b + 6)
      (by norm_num) (show i < 3 * 19 + 1 by omega)
    exact ⟨j, hj, ej⟩
  have hcells : ∀ c ∈ (xLeafCells layer b).map KC.cell, ∃ v, c = KC.cell v ∧
      (v = .n 1 ∨ v = .n ((xCw layer b).2.1 + 1) ∨ ∃ i < 58, v = cwTip (xW layer b) (xA layer b + 6) i) := by
    intro c hc
    simp only [xLeafCells, List.map_cons, List.mem_cons, htips, List.map_map, List.mem_map,
      List.mem_range, Function.comp_apply] at hc
    rcases hc with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨_, rfl, Or.inr (Or.inr ⟨i, hi, rfl⟩)⟩
  have hcellNB : ∀ c ∈ (xLeafCells layer b).map KC.cell, KCb ((xCw layer b).2.1 + 2) c := by
    intro c hc
    obtain ⟨v, rfl, hv'⟩ := hcells c hc
    rcases hv' with rfl | rfl | ⟨i, hi, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · exact ⟨_, by omega, rfl⟩
    · exact (htipNB i hi).mono' (by omega)
  have b2 : (xCw layer b).2.1 + 2 ≤ (xLeafK layer b).2.1 :=
    kMsg_le (show xPad + 5 ≤ (xCw layer b).2.1 + 2 by simp [xPad]; omega) hcellNB
  have b3 : (xLeafK layer b).2.1 ≤ (xMk layer b).2.1 := merkleT_snd_ge ..
  have hout : (xLeafK layer b).2.2 + 1 ≤ (xLeafK layer b).2.1 :=
    kMsg_out xPad ((xLeafCells layer b).map KC.cell) 960 false ((xCw layer b).2.1 + 2)
  -- the step addresses
  refine Completes.seq (xStepAddrs_seq hidx) (by omega) (fun σ1 he1 hh1 => ?_)
  have hag1 : AgreeBelow (xA layer b) σ σ1 := he1.agree
  have hsteps := xStepAddrs_sound hh1
  have hidx1 : σ1 (xIdx layer b) = σ (xIdx layer b) := hag1.apply hidx
  have hg1 : XGood layer b σ1 := by
    refine ⟨by rw [hag1.apply ⟨1, by omega, rfl⟩]; exact hPc, fun s hs => ?_, fun i hi => ?_,
      hpad.congr (by simp [xPad]; omega) hag1, fun s hs => ?_⟩
    · rw [hsteps s hs, hidx1]
      exact canon_add hidxc (canon_word _ _)
    · rw [hag1.apply ⟨138 + i, by omega, rfl⟩, show V.n (138 + i) = xTag i from rfl, hpre.tags i hi]
      exact canon_eOfNat i
    · rw [hag1.apply ⟨128 + s, by omega, rfl⟩, show V.n (128 + s) = xPower s from rfl, hpre.powers s hs]
  -- the codeword
  have hdig : ∀ i ∈ Finset.range (3 * 19 + 1), digK (nDigits 19 N) i = N / 4 ^ i % 4 :=
    fun i hi => digK_nDigits 19 N (Finset.mem_range.mp hi)
  have hs' : ∑ i ∈ Finset.range (3 * 19 + 1), N / 4 ^ i % 4 = 106 := hs
  have hsum2 : ∑ i ∈ Finset.range (3 * 19 + 1), digK (nDigits 19 N) i * 4 ^ i =
      ∑ i ∈ Finset.range 58, N / 4 ^ i % 4 * 4 ^ i :=
    Finset.sum_congr rfl fun i hi => by rw [hdig i hi]
  have hcw := codewordT_complete (C := C) (rd := rd) (xWc_shape hA) (xWc_canon hA) (xWc_atoms layer b)
    (fun σ hg => xWc_sound hg) (fun σ hg => xWc_pow hg) (G := 19) (target := xTarget) (d0 := xD0 layer b)
    (b := xA layer b + 6) (by norm_num) (by norm_num) (by omega) le_rfl hm (xWc_pw layer b hA)
    (hd0.mono' (by omega)) (nDigits 19 N) (fun q _ => nDigits_lt 19 N q) vals hv σ1 hg1
    (by rw [Finset.sum_congr rfl hdig, hs', xTarget_eq])
    (by rw [hsum2, hag1.apply hd0, hN])
  rw [← xCw_eq] at hcw
  have hcwNB : NumBelow (xCw layer b).2.1 (Stmt.valsList (xCw layer b).1) := by
    rw [xCw_eq]
    exact codewordT_numBelow (xWc_shape hA) (by omega) le_rfl (xWc_pw layer b hA) (hd0.mono' (by omega))
  refine Completes.append (m := (xCw layer b).2.1) (le_of_lt b1) (by omega) hcwNB hcw
    (fun σ2 he2 hp2 => ?_)
  obtain ⟨hg2, htip2, hdg2, hkp2⟩ := hp2
  have hag2 : AgreeBelow (xA layer b + 6) σ1 σ2 := he2.agree
  -- the leaf's address
  have hseq : SeqOK (xCw layer b).2.1 [cst (xCw layer b).2.1 (word (tw 2) 0 0),
      addS (.n ((xCw layer b).2.1 + 1)) (xIdx layer b) (.n (xCw layer b).2.1)] ((xCw layer b).2.1 + 2) :=
    ⟨rfl, ⟨rfl, hidx.mono' (by omega), ⟨_, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seq hseq (by omega) (fun σ3 he3 hh3 => ?_)
  have hag3 : AgreeBelow (xCw layer b).2.1 σ2 σ3 := he3.agree
  have e1 : σ3 (.n (xCw layer b).2.1) = word (tw 2) 0 0 := hh3.atom (List.mem_cons_self ..)
  have e2 : σ3 (.n ((xCw layer b).2.1 + 1)) = σ3 (xIdx layer b) + σ3 (.n (xCw layer b).2.1) :=
    hh3.atom (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have hidx3 : σ3 (xIdx layer b) = σ (xIdx layer b) := by
    rw [hag3.apply (hidx.mono' (by omega)), hag2.apply (hidx.mono' (by omega)), hidx1]
  have hP3 : σ3 (.n 1) = σ (.n 1) := by
    rw [hag3.apply ⟨1, by omega, rfl⟩, hag2.apply ⟨1, by omega, rfl⟩, hag1.apply ⟨1, by omega, rfl⟩]
  have hpad3 : PadOK σ3 xPad := hg2.2.2.2.1.congr (b := (xCw layer b).2.1) (by simp [xPad]; omega) hag3
  -- the leaf
  have hck : ∀ c ∈ (xLeafCells layer b).map KC.cell, KCb ((xCw layer b).2.1 + 2) c ∧ KCc σ3 c := by
    intro c hc
    refine ⟨hcellNB c hc, ?_⟩
    obtain ⟨v, rfl, hv'⟩ := hcells c hc
    show IsCanonical128 (σ3 v)
    rcases hv' with rfl | rfl | ⟨i, hi, rfl⟩
    · rw [hP3]; exact hPc
    · rw [e2, e1, hidx3]; exact canon_add hidxc (canon_word _ _)
    · rw [hag3.apply (htipNB i hi), cwTip_weq (xW_weq layer b) _ i (by omega)]
      exact htip2 i (by omega)
  obtain ⟨hk1, hk2, -⟩ := kMsg_complete (C := C) (rd := rd) (tailRun := false) (len := 960) σ3 hpad3
    (by simp [xPad]; omega) hck (fun h => by simp at h)
  refine Completes.append (m := (xLeafK layer b).2.1) b2 b3 hk2 hk1.withHolds (fun σ4 he4 hp4 => ?_)
  have hag4 : AgreeBelow ((xCw layer b).2.1 + 2) σ3 σ4 := he4.agree
  have hlk : AtomsHold rd σ4 (kMsg xPad ((xLeafCells layer b).map KC.cell) 960 false none
      ((xCw layer b).2.1 + 2)).1 := atomsHold_of_holdsList (kMsg_atoms ..) hp4.2
  have hpad4 : PadOK σ4 xPad := hpad3.congr (by simp [xPad]; omega) hag4
  have hlen : ((xLeafCells layer b).map KC.cell).length = 60 := by
    rw [List.length_map, xLeafCells, List.length_cons, List.length_cons, htips]; simp
  have hleaf := kMsg_sound (out := none) hpad4 (by simp) hlk (by rw [hlen]) (fun j hj =>
    cellsBytes_getD_past (by rw [List.length_map, hlen]; omega))
  have hleafc : IsCanonical128 (σ4 (.n (xLeafK layer b).2.2)) := by
    have := hleaf
    show IsCanonical128 (σ4 (.n (kMsg xPad ((xLeafCells layer b).map KC.cell) 960 false none
      ((xCw layer b).2.1 + 2)).2.2))
    rw [this]
    simp [IsCanonical128, digestHalves]
  -- the path
  have hag14 : AgreeBelow (xA layer b) σ σ4 := fun j hj =>
    (hag1 j hj).trans ((hag2 j (by omega)).trans ((hag3 j (by omega)).trans (hag4 j (by omega))))
  have hmk := merkleT_complete (C := C) (rd := rd) (pad := xPad) (pp := .n 1) (bitOf := xBitOf layer)
    (nodeOf := xNodeOf layer) (addrOf := xAddrOf layer) (bits := bits) (sibs := sibs) 16 0
    (.n (xLeafK layer b).2.2) (xLeafK layer b).2.1 σ4 hpad4 (by simp [xPad]; omega) ⟨1, by omega, rfl⟩
    ⟨_, by omega, rfl⟩
    (fun j hj => by
      obtain ⟨n1, n2⟩ := hbits j hj
      rw [Nat.zero_add]
      exact ⟨n1.mono' (by omega), by rw [hag14.apply n1]; exact n2⟩)
    (fun l nd h => by
      obtain ⟨n1, n2⟩ := hnodes l nd h
      exact ⟨n1.mono' (by omega), by rw [hag14.apply n1]; exact n2⟩)
    (by rw [hag14.apply ⟨1, by omega, rfl⟩]; exact hPc) hleafc
    (fun j hj => by rw [Nat.zero_add]; exact hsc j hj)
  obtain ⟨σ5, he5, ⟨-, hc5, hsib5⟩, hh5⟩ := hmk
  have hlkm : (xLeafK layer b).2.1 ≤ (merkleT xPad (.n 1) (xBitOf layer) (xNodeOf layer) (xAddrOf layer) 16 0
      (.n (xLeafK layer b).2.2) (xLeafK layer b).2.1).2.1 := merkleT_snd_ge ..
  refine ⟨σ5, he5, ⟨hc5, fun σ'' hag'' => ?_⟩, hh5⟩
  have tr : ∀ k < (xCw layer b).2.1, σ'' (.n k) = σ2 (.n k) := fun k hk => by
    rw [hag''.apply ⟨k, by omega, rfl⟩, he5.apply (Or.inl (by omega)), hag4.apply ⟨k, by omega, rfl⟩,
      hag3.apply ⟨k, hk, rfl⟩]
  refine ⟨fun q hq => ?_, fun i hi => ?_, fun l hl => ?_⟩
  · -- the digits
    have hlt := cwBase_lt (xWc layer b) (G := 19) xTarget (xD0 layer b) (xA layer b + 6) hq
    rw [← xCw_eq] at hlt
    rw [cwState_weq (xW_weq layer b) _ q (by omega), tr _ hlt]
    exact hdg2 q hq
  · -- the starts
    obtain ⟨j, ej, hj⟩ := cwPos_lt (xWc layer b) xTarget (xD0 layer b) (xA layer b + 6) (G := 19)
      (by norm_num) (fun q _ => nDigits_lt 19 N q) (show i < 3 * 19 + 1 by omega)
    rw [← xCw_eq] at hj
    rw [cwPos_weq (xW_weq layer b) 19 _ _ i (by omega) (by norm_num), ej, tr j hj, ← ej]
    exact hkp2 i (by omega)
  · -- the siblings
    have hs5 := hsib5 l hl
    rw [Nat.zero_add] at hs5
    have hlt : mBase (xNodeOf layer) 0 l (xLeafK layer b).2.1 + 2 ≤ (xMk layer b).2.1 :=
      mBase_lt xPad (.n 1) (xBitOf layer) (xNodeOf layer) (xAddrOf layer) 16 0
        (.n (xLeafK layer b).2.2) (xLeafK layer b).2.1 l hl
    obtain ⟨n1, -⟩ := hbits l hl
    unfold mSib at hs5 ⊢
    rw [hag''.apply (n1.mono' (by omega)),
      hag''.apply ⟨mBase (xNodeOf layer) 0 l (xLeafK layer b).2.1, by omega, rfl⟩,
      hag''.apply ⟨mBase (xNodeOf layer) 0 l (xLeafK layer b).2.1 + 1, by omega, rfl⟩]
    exact hs5

end
end LeanVM.Guest.B1.Sig
