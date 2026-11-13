/-
  LeanVM.Guest.B1.Sig.SphincsCompleteConv

  FORS's roots and key in the forms `SphincsSoundFors` computes them (`fRootE` at `key + FORS_TREE`)
  are the statement-shaped cells of `SphincsBridgeCells` (`forsRootCell`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBridgeCells
public import LeanVM.Guest.B1.Sig.SphincsSoundFors
public import LeanVM.Guest.B1.Sig.SphincsForsComplete
public import LeanVM.Guest.B1.Sig.SphincsLayersComplete
public import LeanVM.Guest.B1.Sig.SphincsCompleteBlocks

/-!
# FORS's cells, two ways

The FORS block's soundness and completeness compute a tree's nodes at `fAdrE A1 c z s`, `A1` the
key pair's cell plus `FORS_TREE` (`3·2^24`); the statement's bridge reads them at
`forsAdrCell kp c z s`, `adrsCell1 3 kp z (c·2^(10-z) + s >>> z)`. At `A1 = adrsCell1 3 kp 0 0`
they agree (`fAdrE_eqC`), so do the roots (`fRootE_eq`) and the FORS key's hash (`forsKey_eq`, its
roots listed over `List.range 24` or `List.ofFn`). So spfors's `sForsBlock_complete` gives the
assembly's `ForsBlockCompletes` (`forsBlockCompletes`); the encoding's cell two ways
(`encDigestCell_eq_encOf`), so spfors's `sHtLayer_complete` gives `HtLayerCompletes`
(`htLayerCompletes`); `sphincsBlocksComplete`: both.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-- **A FORS node's address**, two ways. -/
theorem fAdrE_eqC {kp c z s : Nat} (hc : c < 24) (hz : z ≤ 10) (hs : s < 2 ^ 10) :
    fAdrE (adrsCell1 3 kp 0 0) c z s = forsAdrCell kp c z s := by
  have hi := fIdx_lt hc hz hs
  have hh := a1Hi_lt (h := z) (by omega) hi
  rw [fAdrE, forsAdrCell, show c * 2 ^ (10 - z) + s >>> z = fIdx c z s by unfold fIdx; ring,
    ← adrsCell1_add_words23 3 kp z (fIdx c z s)]
  congr 1
  rw [lit, beWordAt_two_of_lt (by omega), beWordAt_three_of_lt_pow16 hi]
  unfold a1Hi at hh ⊢
  congr 1 <;> omega

/-- **A FORS tree's root**, two ways. -/
theorem fRootE_eq (pp a0 : E) {kp c s : Nat} (hc : c < 24) (hs : s < 2 ^ 10) (secret : E)
    (sib : Nat → E) :
    fRootE pp a0 (adrsCell1 3 kp 0 0) c s secret sib = forsRootCell pp a0 kp c s secret sib := by
  unfold fRootE forsRootCell
  rw [show fLeafE pp a0 (adrsCell1 3 kp 0 0) c s secret = forsLeafCell pp a0 kp c s secret by
    rw [fLeafE, forsLeafCell, fAdrE_eqC hc (by norm_num) hs]]
  refine pFold_congr_lt _ _ 10 _ fun z hz => funext fun v => ?_
  rw [fNodeE, forsNodeCell, fAdrE_eqC hc (by omega) hs]

/-- **The FORS key's hash**, two ways: at the key pair's cell `adrsCell1 0 kp 0 0`, `FORS_TREE` and
`FORS_ROOTS` added. -/
theorem forsKey_eq (pp a0 : E) (kp : Nat) (s : Nat → Nat) (hs : ∀ c < 24, s c < 2 ^ 10)
    (secret : Nat → E) (sib : Nat → Nat → E) :
    (hcell ([pp, a0, adrsCell1 0 kp 0 0 + lit (4 * 2 ^ 24)] ++ (List.range 24).map fun c =>
      fRootE pp a0 (adrsCell1 0 kp 0 0 + lit (3 * 2 ^ 24)) c (s c) (secret c) (sib c))).1 =
    (hcell ([pp, a0, adrsCell1 4 kp 0 0] ++ List.ofFn fun c : Sphincs.ForsTreeIndex =>
      forsRootCell pp a0 kp c.val (s c.val) (secret c.val) (sib c.val))).1 := by
  have e4 : adrsCell1 0 kp 0 0 + lit (4 * 2 ^ 24) = adrsCell1 4 kp 0 0 := by
    rw [lit_of_lt (by norm_num)]; exact adrsCell1_add_type (by norm_num)
  have e3 : adrsCell1 0 kp 0 0 + lit (3 * 2 ^ 24) = adrsCell1 3 kp 0 0 := by
    rw [lit_of_lt (by norm_num)]; exact adrsCell1_add_type (by norm_num)
  have hl : ((List.range 24).map fun c =>
      fRootE pp a0 (adrsCell1 3 kp 0 0) c (s c) (secret c) (sib c)) =
      List.ofFn fun c : Sphincs.ForsTreeIndex =>
        forsRootCell pp a0 kp c.val (s c.val) (secret c.val) (sib c.val) := by
    show ((List.range Sphincs.forsTreeCount).map fun c =>
      fRootE pp a0 (adrsCell1 3 kp 0 0) c (s c) (secret c) (sib c)) = _
    rw [← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
    refine List.map_congr_left fun c _ => ?_
    exact fRootE_eq pp a0 c.isLt (hs c c.isLt) _ _
  rw [e4, e3, hl]

theorem sForsBit_nb : ∀ k < 240, nbB 1382 (sForsBit k) = true := by decide +kernel
theorem sVals_nb : ∀ k < 240, nbB 1382 (sVals k) = true := by decide +kernel
/-- **FORS completes** (`ForsBlockCompletes`), from `sForsBlock_complete`. -/
theorem forsBlockCompletes : ForsBlockCompletes := by
  intro C rd σ tree kp s secret sib hp ha0 hkey hs hbit hval
  have h := sForsBlock_complete (C := C) (rd := rd) (pad := sPad) (pp := sPP) (a0 := sA0B)
    (key := sKeyB) (bit := sForsBit) (val := sVals) (b0 := 1382) (secret := secret) (sib := sib) hs σ hp
    (by unfold sPad; omega) ⟨2, by omega, rfl⟩ ⟨1379, by omega, rfl⟩ ⟨1381, by omega, rfl⟩
    (fun k hk => nbB_ok (sForsBit_nb k hk)) (fun k hk => nbB_ok (sVals_nb k hk)) hbit hval
  obtain ⟨t1, t2⟩ := sForsTrees_shape sPad sPP sA0B (.n (1382 + 1)) sForsBit sVals 1382 24 0
  have e0 : forsTreeBase 1382 0 = 1382 + 2 := by simp [forsTreeBase]
  have e24 : forsTreeBase 1382 (0 + 24) = 1382 + 3802 := forsTreeBase_24 1382
  rw [e0, e24] at t1
  rw [e0] at t2
  show Completes C rd 1382 5249 (sForsBlock sPad sPP sA0B sKeyB sForsBit sVals 1382).1 σ _
  rw [sForsBlock_eq]
  generalize sForsTrees sPad sPP sA0B (.n (1382 + 1)) sForsBit sVals 24 0 (1382 + 2) = tr at h t1 t2 ⊢
  rw [t1, t2] at h ⊢
  obtain ⟨σ', he, ⟨-, hk⟩, hh⟩ := h
  rw [hkey, ha0, forsKey_eq _ _ kp s hs secret sib] at hk
  have key : ∀ (n : Nat) (R : E), n = 5248 → σ' (.n n) = R → σ' sForsPk = R := by
    rintro n R rfl hn; exact hn
  refine ⟨σ', he.mono le_rfl (by decide +kernel), key _ _ ?_ hk, hh⟩
  decide +kernel

/-- **The encoding's digest cell**, two ways: the counter's cell `eOfNat N`, `N < 2^32`, cut at its
four bytes. -/
theorem encDigestCell_eq_encOf (pp a0 key signed : E) {N : Nat} (hN : N < 2 ^ 32) :
    encDigestCell pp a0 (key + lit (7 * 2 ^ 24)) signed (eOfNat N) = encOf pp a0 key signed N := by
  unfold encDigestCell encOf
  rw [show [pp, a0, key + lit (7 * 2 ^ 24), signed, eOfNat N] =
      [pp, a0, key + lit (7 * 2 ^ 24), signed] ++ [eOfNat N] from rfl,
    show (68 : Nat) = 16 * [pp, a0, key + lit (7 * 2 ^ 24), signed].length + 4 from rfl,
    take_cellsBytes_append _ _ 4 (by norm_num), cellBytes_eOfNat (by omega),
    ← leBytes_append _ 4 12, List.take_left' (by simp [leBytes])]
  rfl

/-- **A layer completes after its counter** (`HtLayerCompletes`), from `sHtLayer_complete`. -/
theorem htLayerCompletes : HtLayerCompletes := by
  intro C rd σ l a0 a1 signed ctr b lv e sib hl hb ha0 ha1 hsg hct hp hctr hcall he hbit hval
  obtain ⟨N, hN, hc⟩ := hctr
  have hN' : beWordAt 0 N < 2 ^ 32 := beWordAt_zero_lt N
  have h := sHtLayer_complete (C := C) (rd := rd) (pad := sPad) (pp := sPP) (a0 := a0) (key := a1)
    (signed := signed) (ctr := ctr) (bit := sLeafBit) (val := sLVal) (off := sOffOf l)
    (height := sHeightOf l) (b := b) (N := beWordAt 0 N)
    (sib := sib) (by unfold sHeightOf sLeafLen; split <;> omega) he σ (by unfold sPad; omega)
    ⟨2, by omega, rfl⟩ ha0 ha1 hsg hct
    (fun j hj => by
      obtain ⟨k, hk, ek⟩ := sLeafBit_lt (sOff_lt hl hj); exact ⟨k, by omega, ek⟩)
    (fun j _ => by obtain ⟨k, hk, ek⟩ := sLVal_below (sOffOf l + j); exact ⟨k, by omega, ek⟩)
    hp hN' hc hbit hval
    (by rw [← encDigestCell_eq_encOf _ _ _ _ hN', ← hc]; exact hcall)
  exact h.mono le_rfl le_rfl fun _ h => h.2

/-- **`verify_sig_lean_sphincs`'s blocks complete.** -/
theorem sphincsBlocksComplete : SphincsBlocksComplete := ⟨forsBlockCompletes, htLayerCompletes⟩

end
end LeanVM.Guest.B1.Sig
