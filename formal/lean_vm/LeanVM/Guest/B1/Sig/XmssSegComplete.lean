/-
  LeanVM.Guest.B1.Sig.XmssSegComplete

  `verify_lean_xmss`, inline in `__loop2`, is complete: for a claim held at the pointer in its
  canonical cells and a signature that verifies it, the check holds of a valuation changing only
  its own values (`verify_lean_xmss_complete_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegCoreC
public import LeanVM.Guest.B1.Sig.XmssSegPathC
public import LeanVM.Guest.B1.Sig.XmssSegEnds

/-!
# `verify_lean_xmss` in `__loop2`, complete

The valuation: the prologue loads `P`, hints the leaf index's shifts and windows; each layer hints
the signature's randomizer, its digest's digits (which decode, since the signature verifies:
`layerRoot_decode`), its chains' starts and its siblings. Each layer's root is then read off the
valuation by soundness (`sLayerCore_sound`): the valuation holds the signature's layer
(`sPart_eq`), so the roots are the scheme's, the top one the key's, and the final check holds.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

attribute [local irreducible] kMsg sCodewordT lxWindowT

variable {C : CallRel} {rd : Reader}

/-- A layer after its digest. -/
def sCore (layer b : Nat) : List Stmt :=
  xStepAddrs (sLxIdx layer b) (sA layer b) ++ ((sCw layer b).1 ++
    ([cst (sCw layer b).2.1 (word (tw 2) 0), addS (.n ((sCw layer b).2.1 + 1)) (sLxIdx layer b)
      (.n (sCw layer b).2.1)] ++ ((sLeafK layer b).1 ++ ((sWin0 layer b).1 ++ (sWin1 layer b).1))))

theorem xSeg_split : xSeg = sPrologue ++ (sDigest0 88 ++ (sCore 0 88 ++ (sDigest1 62605 (.n 50364) ++
    (sCore 1 62605 ++ [loadS (.n 120763) sSigner 0, .atom (.assertEq (.n 112857) (.n 120763))])))) := by
  have h0 := sLayer0_snd
  have h1 := sLayer1_snd
  simp only [xSeg]
  rw [h0, h1]
  simp only [sLayer, sCore, ↓reduceIte, one_ne_zero, List.append_assoc]

theorem lxTagSlot_lt : ∀ i < 58, lxTagCarried i = true → lxTagSlot i - 1 < 61 := by decide

/-- The carried tags held on a valuation agreeing below `66`. -/
theorem lxTagsHold_congr {σ σ' : Val} (h : LxTagsHold (fun j => σ (sTagParam j))) (hag : AgreeBelow 66 σ σ') :
    LxTagsHold (fun j => σ' (sTagParam j)) := fun i hi hc => by
  have := lxTagSlot_lt i hi hc
  show σ' (.n (5 + (lxTagSlot i - 1))) = _
  rw [hag.apply ⟨_, by omega, rfl⟩]
  exact h i hi hc

/-- **`verify_lean_xmss` is complete**, given the path windows' completeness. -/
theorem verify_lean_xmss_complete_holds_of (hW : LxWindowsC) : verify_lean_xmss_complete_Spec := by
  intro C rd σ pk m sig hm htags hat hv
  obtain ⟨r0, h0, h1⟩ := (xmssVerify_iff pk m sig).mp hv
  obtain ⟨hldR, hldP, hldLo, hldHi⟩ := hat
  set L := sig.leafIndex.val with hLdef
  have hL : L < 2 ^ 32 := sig.leafIndex.isLt
  have hli : sig.leafIndex = ⟨L, hL⟩ := rfl
  have hxpp : xpp (cellOf128 pk.parameter) = pk.parameter := cellVal_cellOf128 _
  set part0 := sig.layers LeanXmss.bottomLayer with hp0
  set part1 := sig.layers LeanXmss.topLayer with hp1
  rw [xSeg_split]
  -- the prologue
  refine Completes.append (m := 88) (by norm_num) (by norm_num) sPrologue_nb
    (sPrologue_complete σ hldP (fun w => eOfNat (L >>> (8 * w))) (fun w => ofK (addressOfIndex (lxWin L w))))
    (fun σ1 he1 ⟨hP1, hhis1, hwin1, hpow1⟩ => ?_)
  have hs1 : σ1 sSigner = σ sSigner := he1.apply (Or.inl (by norm_num))
  have htags1 := lxTagsHold_congr htags he1.agree
  -- the bottom layer's digest
  refine Completes.append (m := 104) (by norm_num) (by norm_num) sDigest0_nb
    (sDigest0_complete (C := C) (rd := rd) σ1 (rho := cellOf128 part0.randomizer)
      (c := cellOf128 (m.extractLsb' 0 128)) (d := cellOf128 (m.extractLsb' 128 128))
      (by rw [hs1]; exact hldLo) (by rw [hs1]; exact hldHi)).withHolds
    (fun σ2 he2 ⟨⟨h88, h91, h92⟩, hh2⟩ => ?_)
  obtain ⟨-, -, hpad2, h90, h103⟩ := sDigest0_sound (atomsHold_of_holdsList (sDigest0_atoms 88) hh2)
  have t2 : ∀ k < 88, σ2 (.n k) = σ1 (.n k) := fun k hk => he2.apply (Or.inl hk)
  have hP2 : σ2 sLxPP = cellOf128 pk.parameter := by rw [show sLxPP = V.n 66 from rfl, t2 66 (by norm_num)]; exact hP1
  have hhis2 : ∀ v < 4, σ2 (sHis v) = eOfNat (L >>> (8 * v)) := fun v hv => by
    rw [show sHis v = V.n (67 + v) from rfl, t2 _ (by omega)]; exact hhis1 v hv
  have hwin2 : ∀ w < 4, σ2 (sWin w) = ofK (addressOfIndex (lxWin L w)) := fun w hw => by
    rw [show sWin w = V.n (71 + w) from rfl, t2 _ (by omega)]; exact hwin1 w hw
  have hpow2 : ∀ s < 13, σ2 (sPower s) = gen ^ s := fun s hs => by
    rw [show sPower s = V.n (75 + s) from rfl, t2 _ (by omega)]; exact hpow1 s hs
  have htags2 := lxTagsHold_congr htags1 (he2.agree.mono (by norm_num))
  have htag2 : ∀ i < 58, σ2 (sTag i) = eOfNat i := fun i hi => by
    rw [sTag_eq σ2 i]
    exact lx_tag hpad2.2.1 (fun s hs => hpow2 s (by omega)) htags2 i hi
  -- the bottom digest decodes
  have hidx0 : σ2 (sHis 0) = eOfNat (xIdxNat 0 L) := by rw [xIdxNat_zero, hhis2 0 (by norm_num)]; rfl
  have hM0 : HashSig.littleEndianBytes 32 m = [σ2 (.n 91), σ2 (.n 92)].flatMap cellBytes := by
    rw [h91, h92]
    calc HashSig.littleEndianBytes 32 m = HashSig.littleEndianBytes 32 (cellPairVal (cellOf128
          (m.extractLsb' 0 128)) (cellOf128 (m.extractLsb' 128 128))) := by rw [cellPairVal_cellOf128]
      _ = _ := by rw [bytesLE_cellPairVal]; simp
  have ha0 : cellBytes (σ2 (.n 90)) = LeanXmss.tweakBytes
      (.message ⟨0, by decide⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨0, by decide⟩)) := by
    rw [h90, hidx0]
    exact xMsgAdr_bytes hL (by norm_num)
  obtain ⟨enc0, hdec0⟩ := layerRoot_decode h0
  have hmd0 := messageDigest_cells xq_keccak (pp := cellOf128 pk.parameter) (rho := cellOf128 part0.randomizer)
    ha0 hM0
  rw [hxpp, show xv (cellOf128 part0.randomizer) = part0.randomizer from cellVal_cellOf128 _] at hmd0
  have hdec0' : LeanXmss.Codeword.decode (xv (hcell (cellOf128 pk.parameter :: σ2 (.n 90) ::
      [σ2 (.n 91), σ2 (.n 92)] ++ [cellOf128 part0.randomizer])).1) = some enc0 := by
    rw [← hmd0]; exact hdec0
  have hD0 : σ2 (.n 103) = (hcell (cellOf128 pk.parameter :: σ2 (.n 90) :: [σ2 (.n 91), σ2 (.n 92)] ++
      [cellOf128 part0.randomizer])).1 := by
    rw [h103, hP2, h88]; rfl
  rw [← hD0] at hdec0'
  obtain ⟨hN0, hs0⟩ := digest_digits hdec0'
  -- the bottom layer
  obtain ⟨hnb0, -, hc0⟩ := sCore_complete (C := C) (rd := rd) hW (layer := 0) (b := 88) (by norm_num)
    (by decide) hm σ2 hpad2 hpow2 hL hhis2 hwin2 ⟨67, by decide, rfl⟩ ⟨103, by decide, rfl⟩ hN0 hs0
    (xVals part0) (xSibs part0)
  have e0 : (sWin1 0 88).2.1 = 62605 := congrArg (·.1) sWin1_0
  have e0' : (sWin1 0 88).2.2 = 50364 := congrArg (·.2) sWin1_0
  rw [show sCore 0 88 = _ from rfl]
  rw [e0] at hnb0 hc0
  refine Completes.append (m := 62605) (by norm_num) (by norm_num) hnb0 hc0.withHolds
    (fun σ3 he3 ⟨hk3, hh3⟩ => ?_)
  have t3 : ∀ k < 104, σ3 (.n k) = σ2 (.n k) := fun k hk => he3.apply (Or.inl hk)
  have hpad3 : PadOK σ3 sLxPad := hpad2.congr (b := 104) (by simp [sLxPad]) he3.agree
  have hP3 : σ3 sLxPP = cellOf128 pk.parameter := by rw [show sLxPP = V.n 66 from rfl, t3 66 (by norm_num)]; exact hP2
  have hhis3 : ∀ v < 4, σ3 (sHis v) = eOfNat (L >>> (8 * v)) := fun v hv => by
    rw [show sHis v = V.n (67 + v) from rfl, t3 _ (by omega)]; exact hhis2 v hv
  have hwin3 : ∀ w < 4, σ3 (sWin w) = ofK (addressOfIndex (lxWin L w)) := fun w hw => by
    rw [show sWin w = V.n (71 + w) from rfl, t3 _ (by omega)]; exact hwin2 w hw
  have hpow3 : ∀ s < 13, σ3 (sPower s) = gen ^ s := fun s hs => by
    rw [show sPower s = V.n (75 + s) from rfl, t3 _ (by omega)]; exact hpow2 s hs
  have htags3 := lxTagsHold_congr htags2 (he3.agree.mono (by norm_num))
  have htag3 : ∀ i < 58, σ3 (sTag i) = eOfNat i := fun i hi => by
    rw [sTag_eq σ3 i]
    exact lx_tag hpad3.2.1 (fun s hs => hpow3 s (by omega)) htags3 i hi
  have hkw3 : ∀ w < 4, sKw σ3 w = lxWin L w := fun w hw =>
    logG_eq (lxWin_lt L w) (by norm_num) (hwin3 w hw)
  -- the bottom root is the scheme's
  have hpart0 : sPart 0 88 σ3 = part0 :=
    sPart_eq (by rw [show sRho 0 88 = V.n 88 from rfl, t3 88 (by norm_num)]; exact h88)
      (hk3 σ3 (fun _ _ => rfl)).1 (hk3 σ3 (fun _ _ => rfl)).2
  have r0' := (sLayerCore_sound (layer := 0) (b := 88) (rest := []) hpad3 hpow3 (by norm_num)
    (by rw [List.append_nil]; exact hh3)).2.2.2 L hL
    (by show σ3 (sHis 0) = _; rw [hhis3 0 (by norm_num), xIdxNat_zero]; simp) hhis3 hkw3 htag3
    (msgCells := [σ3 (.n 91), σ3 (.n 92)]) (M := HashSig.littleEndianBytes 32 m)
    (by rw [hM0, t3 91 (by norm_num), t3 92 (by norm_num)]) (aMsg := σ3 (.n 90))
    (by rw [t3 90 (by norm_num)]; exact ha0)
    (by show σ3 (.n 103) = _; rw [t3 103 (by norm_num), t3 91 (by norm_num), t3 92 (by norm_num),
      t3 90 (by norm_num), h103, show sRho 0 88 = V.n 88 from rfl, t3 88 (by norm_num), hP3, hP2]; rfl)
  rw [hP3, hxpp, hpart0, e0'] at r0'
  have hr0 : xv (σ3 (.n 50364)) = r0 := Option.some.inj (r0'.symm.trans (by rw [← hli]; exact h0))
  -- the top layer's digest
  have hroot3 : NBv 62605 (.n 50364) := ⟨50364, by norm_num, rfl⟩
  refine Completes.append (m := 62605 + 5 + 2) (by norm_num) (by norm_num) (sDigest1_nb (by norm_num) hroot3)
    (sDigest1_complete (C := C) (rd := rd) σ3 (rho := cellOf128 part1.randomizer) (by norm_num) hroot3
      hpad3).withHolds
    (fun σ4 he4 ⟨h4r, hh4⟩ => ?_)
  have t4 : ∀ k < 62605, σ4 (.n k) = σ3 (.n k) := fun k hk => he4.apply (Or.inl hk)
  have hpad4 : PadOK σ4 sLxPad := hpad3.congr (b := 62605) (by simp [sLxPad]) he4.agree
  obtain ⟨e41, e44, e46⟩ := sDigest1_sound hpad4 (atomsHold_of_holdsList (sDigest1_atoms _ _) hh4)
  have hs4 : σ4 sSigner = σ sSigner := by
    rw [show sSigner = V.n 65 from rfl, t4 65 (by norm_num), t3 65 (by norm_num), t2 65 (by norm_num)]
    exact hs1
  have hP4 : σ4 sLxPP = cellOf128 pk.parameter := by rw [show sLxPP = V.n 66 from rfl, t4 66 (by norm_num)]; exact hP3
  have hhis4 : ∀ v < 4, σ4 (sHis v) = eOfNat (L >>> (8 * v)) := fun v hv => by
    rw [show sHis v = V.n (67 + v) from rfl, t4 _ (by omega)]; exact hhis3 v hv
  have hwin4 : ∀ w < 4, σ4 (sWin w) = ofK (addressOfIndex (lxWin L w)) := fun w hw => by
    rw [show sWin w = V.n (71 + w) from rfl, t4 _ (by omega)]; exact hwin3 w hw
  have hpow4 : ∀ s < 13, σ4 (sPower s) = gen ^ s := fun s hs => by
    rw [show sPower s = V.n (75 + s) from rfl, t4 _ (by omega)]; exact hpow3 s hs
  have htags4 := lxTagsHold_congr htags3 (he4.agree.mono (by norm_num))
  have htag4 : ∀ i < 58, σ4 (sTag i) = eOfNat i := fun i hi => by
    rw [sTag_eq σ4 i]
    exact lx_tag hpad4.2.1 (fun s hs => hpow4 s (by omega)) htags4 i hi
  have hR4 : σ4 (.n 50364) = σ3 (.n 50364) := t4 50364 (by norm_num)
  have hidx1 : σ4 (.n (62605 + 1)) = eOfNat (xIdxNat 1 L) := by
    rw [e41, hhis4 2 (by norm_num), xIdxNat_one hL]
  -- the top digest decodes
  have hM1 : HashSig.littleEndianBytes 16 r0 = [σ4 (.n 50364)].flatMap cellBytes := by
    rw [← hr0, ← hR4, bytesLE_xv]; simp
  have ha1 : cellBytes (σ4 (.n (62605 + 4))) = LeanXmss.tweakBytes
      (.message ⟨1, by decide⟩ (LeanXmss.keyIndexOnLayer ⟨L, hL⟩ ⟨1, by decide⟩)) := by
    rw [e44, hidx1]
    exact xMsgAdr_bytes hL (by norm_num)
  obtain ⟨enc1, hdec1⟩ := layerRoot_decode h1
  have hmd1 := messageDigest_cells xq_keccak (pp := cellOf128 pk.parameter) (rho := cellOf128 part1.randomizer)
    ha1 hM1
  rw [hxpp, show xv (cellOf128 part1.randomizer) = part1.randomizer from cellVal_cellOf128 _] at hmd1
  have hdec1' : LeanXmss.Codeword.decode (xv (hcell (cellOf128 pk.parameter :: σ4 (.n (62605 + 4)) ::
      [σ4 (.n 50364)] ++ [cellOf128 part1.randomizer])).1) = some enc1 := by
    rw [← hmd1]; exact hdec1
  have hD1 : σ4 (.n (62605 + 6)) = (hcell (cellOf128 pk.parameter :: σ4 (.n (62605 + 4)) ::
      [σ4 (.n 50364)] ++ [cellOf128 part1.randomizer])).1 := by
    rw [e46, hP4, h4r]; rfl
  rw [← hD1] at hdec1'
  obtain ⟨hN1, hs1'⟩ := digest_digits hdec1'
  -- the top layer
  obtain ⟨hnb1, -, hc1⟩ := sCore_complete (C := C) (rd := rd) hW (layer := 1) (b := 62605) (by norm_num)
    (by decide) hm σ4 hpad4 hpow4 hL hhis4 hwin4 ⟨62606, by decide, rfl⟩ ⟨62611, by decide, rfl⟩
    hN1 hs1' (xVals part1) (xSibs part1)
  have e1 : (sWin1 1 62605).2.1 = 120763 := congrArg (·.1) sWin1_1
  have e1' : (sWin1 1 62605).2.2 = 112857 := congrArg (·.2) sWin1_1
  rw [show sCore 1 62605 = _ from rfl]
  rw [e1] at hnb1 hc1
  refine Completes.append (m := 120763) (by norm_num) (by norm_num) hnb1 hc1.withHolds
    (fun σ5 he5 ⟨hk5, hh5⟩ => ?_)
  have t5 : ∀ k < 62612, σ5 (.n k) = σ4 (.n k) := fun k hk => he5.apply (Or.inl hk)
  have hpad5 : PadOK σ5 sLxPad := hpad4.congr (b := 62612) (by simp [sLxPad]) he5.agree
  have hP5 : σ5 sLxPP = cellOf128 pk.parameter := by rw [show sLxPP = V.n 66 from rfl, t5 66 (by norm_num)]; exact hP4
  have hhis5 : ∀ v < 4, σ5 (sHis v) = eOfNat (L >>> (8 * v)) := fun v hv => by
    rw [show sHis v = V.n (67 + v) from rfl, t5 _ (by omega)]; exact hhis4 v hv
  have hwin5 : ∀ w < 4, σ5 (sWin w) = ofK (addressOfIndex (lxWin L w)) := fun w hw => by
    rw [show sWin w = V.n (71 + w) from rfl, t5 _ (by omega)]; exact hwin4 w hw
  have hpow5 : ∀ s < 13, σ5 (sPower s) = gen ^ s := fun s hs => by
    rw [show sPower s = V.n (75 + s) from rfl, t5 _ (by omega)]; exact hpow4 s hs
  have htags5 := lxTagsHold_congr htags4 (he5.agree.mono (by norm_num))
  have htag5 : ∀ i < 58, σ5 (sTag i) = eOfNat i := fun i hi => by
    rw [sTag_eq σ5 i]
    exact lx_tag hpad5.2.1 (fun s hs => hpow5 s (by omega)) htags5 i hi
  have hkw5 : ∀ w < 4, sKw σ5 w = lxWin L w := fun w hw =>
    logG_eq (lxWin_lt L w) (by norm_num) (hwin5 w hw)
  have hpart1 : sPart 1 62605 σ5 = part1 :=
    sPart_eq (by rw [show sRho 1 62605 = V.n (62605 + 2) from rfl, t5 _ (by norm_num)]; exact h4r)
      (hk5 σ5 (fun _ _ => rfl)).1 (hk5 σ5 (fun _ _ => rfl)).2
  have r1' := (sLayerCore_sound (layer := 1) (b := 62605) (rest := []) hpad5 hpow5 (by norm_num)
    (by rw [List.append_nil]; exact hh5)).2.2.2 L hL
    (by show σ5 (.n (62605 + 1)) = _; rw [t5 _ (by norm_num)]; exact hidx1) hhis5 hkw5 htag5
    (msgCells := [σ5 (.n 50364)]) (M := HashSig.littleEndianBytes 16 r0)
    (by rw [hM1, t5 50364 (by norm_num)]) (aMsg := σ5 (.n (62605 + 4)))
    (by rw [t5 _ (by norm_num)]; exact ha1)
    (by show σ5 (.n (62605 + 6)) = _; rw [t5 _ (by norm_num), t5 50364 (by norm_num),
      t5 (62605 + 4) (by norm_num), hD1, show sRho 1 62605 = V.n (62605 + 2) from rfl,
      t5 (62605 + 2) (by norm_num), hP5, h4r])
  rw [hP5, hxpp, hpart1, e1'] at r1'
  have hr1 : xv (σ5 (.n 112857)) = pk.root := Option.some.inj (r1'.symm.trans (by rw [← hli]; exact h1))
  have hR5 : σ5 (.n 112857) = cellOf128 pk.root :=
    cellVal_inj (by
      show xv (σ5 (.n 112857)) = _
      rw [hr1]; exact (cellVal_cellOf128 _).symm)
  -- the key's root
  refine Completes.load ⟨65, by norm_num, rfl⟩ (w := cellOf128 pk.root)
    (by rw [show sSigner = V.n 65 from rfl, t5 65 (by norm_num)]; rw [show V.n 65 = sSigner from rfl, hs4]
        exact hldR) le_rfl (fun σ6 he6 e6 => ?_)
  refine completes_atoms rfl (Ext.refl _ _ _) trivial (fun a ha => ?_)
  simp only [List.mem_singleton, Stmt.atom.injEq] at ha
  subst ha
  show σ6 (.n 112857) + σ6 (.n 120763) = 0
  rw [he6.apply (Or.inl (by norm_num)), hR5, e6]
  exact e_add_self _

/-- **`verify_lean_xmss` is complete**, inline in `__loop2`. -/
theorem verify_lean_xmss_complete_holds : verify_lean_xmss_complete_Spec :=
  verify_lean_xmss_complete_holds_of lxWindowsC

end
end LeanVM.Guest.B1.Sig
