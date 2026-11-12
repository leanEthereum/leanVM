/-
  LeanVM.Guest.B1.Sig.SphincsSound

  `verify_sig_lean_sphincs` (`lean_ethereum.py:4143-4244`) is sound: under a
  call relation that unfolds at a frame map, on a memory image of at most `2^32` words, whenever
  its body holds it returns no words, and with the byte table at its second argument the signature
  read off its valuation and its three `sp_wots` frames verifies the claim at its first
  (`verify_sig_lean_sphincs_sound_holds`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundHt
public import LeanVM.Guest.B1.Sig.SphincsSoundKey
public import LeanVM.Guest.B1.Sig.SphincsSoundAddrs
public import LeanVM.Guest.B1.Sig.SphincsData

/-!
# `verify_sig_lean_sphincs`, sound

The body (`Data.core20.body = sBody`, `SphincsData`) is four blocks of atoms around the three calls
of `sp_wots` (`sBody_split`, `SphincsSoundBlocks`): the digest block, FORS, the bottom key's
addresses and the bottom layer's counter and encoding (`sBlockA`); the bottom path, the middle
layer's addresses, counter and encoding (`sBlockB`); the middle path and the top layer's
(`sBlockC`); the top path and `root[0] == pk_root` (`sBlockD`).

`verify_sig_lean_sphincs_sound_holds` reads the stages off them (`verifyWithKeccak_iff_stages`):

* the digest block (`sDigestBlock_sound_stmt`, spdig's): the claim at the pointer, and the
  statement's `H_msg` of it and the randomizer `sphincsSigOf` reads is the number `T` the block
  holds the bits and fields of;
* the addresses (`sForsAddrs_sound`, `sMidAddrs_sound`, `sTopAddrs_sound`): each layer's key
  `K_l(idx)`, `idx` the digest's index;
* the FORS key (`forsKey_sound`, over spfors's `sForsBlock_sound`): `fors_pkFromSig` of the
  openings;
* each layer (`layer_sound`, over spwots's `sp_wots_sound_cells`): from the FORS key, then from the
  root below, it reaches the root its path computes;
* the top root is the claim's `PK.root`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)
open HashSig HashSig.OverPermutation
open Sphincs Sphincs.Verification

@[expose] public section

/-- **`verify_sig_lean_sphincs` is sound**, for the signature read off its valuation and the frames
of its `sp_wots` calls. -/
theorem verify_sig_lean_sphincs_sound_holds : verify_sig_lean_sphincs_sound_Spec sphincsSigOf := by
  intro C Vm κ L hκ hV σ rets h
  rw [sBody_eq, sBody_split] at h
  obtain ⟨hA, h⟩ := holdsList_split_atoms sBlockA_atoms h
  have hA := atomsHold_of_holdsList sBlockA_atoms hA
  obtain ⟨c0, h⟩ := h
  obtain ⟨hB, h⟩ := holdsList_split_atoms sBlockB_atoms h
  have hB := atomsHold_of_holdsList sBlockB_atoms hB
  obtain ⟨c1, h⟩ := h
  obtain ⟨hC, h⟩ := holdsList_split_atoms sBlockC_atoms h
  have hC := atomsHold_of_holdsList sBlockC_atoms hC
  obtain ⟨c2, h⟩ := h
  obtain ⟨hD, h⟩ := holdsList_split_atoms sBlockD_atoms h
  have hD := atomsHold_of_holdsList sBlockD_atoms hD
  refine ⟨h.symm, fun hbb => ?_⟩
  have hA' : AtomsHold L.read σ
      (sDigestBlock ++ sForsAddrs ++ sForsB.1 ++ sLayerPre 0 sA0B sKeyB sForsPk) := hA
  have hB' : AtomsHold L.read σ ((sLayerPath 0 sA0B sForsPk).1 ++ sMidAddrs ++
      sLayerPre 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2) := hB
  have hC' : AtomsHold L.read σ ((sLayerPath 1 (sA0Of 1) sLayerB.2.2).1 ++ sTopAddrs ++
      sLayerPre 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2) := hC
  have hD' : AtomsHold L.read σ ((sLayerPath 2 (sA0Of 2) sLayerM.2.2).1 ++
      [.atom (.assertEq sLayerT.2.2 sRoot)]) := hD
  -- the digest, the addresses, the FORS key, the root's check
  obtain ⟨hp, c, d, hclaim, T, hDig, hmd⟩ := sDigestBlock_sound_stmt hκ hbb hA'.left.left.left
  have hT := hDig.1
  obtain ⟨hA0, hK0⟩ := sForsAddrs_sound hDig hA'.left.left.right
  obtain ⟨hA1, hK1⟩ := sMidAddrs_sound hDig hB'.left.right
  obtain ⟨hA2, hK2⟩ := sTopAddrs_sound hDig hC'.left.right
  have hfk := forsKey_sound hp hDig hA0 hK0 hA'.left.right
  have hroot : σ sLayerT.2.2 = σ sRoot :=
    e_add_eq_zero_iff.mp (hD'.right.atom (a := .assertEq sLayerT.2.2 sRoot) (by simp))
  refine ⟨σ sPP, σ sRoot, c, d, hclaim, ?_⟩
  rw [verifyWithKeccak_iff_stages]
  have hdig : sDigestOf (sphincsClaimOf (σ sPP) (σ sRoot) c d).1 (sphincsClaimOf (σ sPP) (σ sRoot) c d).2
      (sphincsSigOf σ Vm) = digestOf T := hmd
  have hfors : sForsKeyOf (sphincsClaimOf (σ sPP) (σ sRoot) c d).1
      (sphincsClaimOf (σ sPP) (σ sRoot) c d).2 (sphincsSigOf σ Vm) = cellVal (σ sForsPk) := by
    unfold sForsKeyOf
    rw [hdig, hfk]
    rfl
  rw [hfors, hdig]
  -- the layers
  have l0 := layer_sound (C := C) hκ hV hbb hp hDig 0 (signed := sForsPk)
    (idx := digestIndex (digestOf T)) hA'.right c0 hB'.left.left
    (by rw [treeOfIndex_digest hT]; exact hA0) (by rw [leafOfIndex_digest hT]; exact hK0)
    (leafOfIndex_digest hT 0)
  have l1 := layer_sound (C := C) hκ hV hbb hp hDig 1 (signed := sLayerB.2.2)
    (idx := digestIndex (digestOf T)) hB'.right c1 hC'.left.left
    (by rw [treeOfIndex_digest hT]; exact hA1) (by rw [leafOfIndex_digest hT]; exact hK1)
    (leafOfIndex_digest hT 1)
  have l2 := layer_sound (C := C) hκ hV hbb hp hDig 2 (signed := sLayerM.2.2)
    (idx := digestIndex (digestOf T)) hC'.right c2 hD'.left
    (by rw [treeOfIndex_digest hT]; exact hA2) (by rw [leafOfIndex_digest hT]; exact hK2)
    (leafOfIndex_digest hT 2)
  refine ⟨_, cellVal (σ sLayerM.2.2), l0, ?_, ?_⟩
  · have e0 : (sLayerPath (0 : Layer).val (sA0Of (0 : Layer).val) sForsPk).2.2 = sLayerB.2.2 :=
      sLayerB_root.symm
    have e1 : (sLayerPath (1 : Layer).val (sA0Of (1 : Layer).val) sLayerB.2.2).2.2 = sLayerM.2.2 :=
      sLayerM_root.symm
    rw [e0]
    rw [e1] at l1
    exact l1
  · have e : (sLayerPath (2 : Layer).val (sA0Of (2 : Layer).val) sLayerM.2.2).2.2 = sLayerT.2.2 :=
      sLayerT_root.symm
    rw [e, hroot] at l2
    exact l2

end
end LeanVM.Guest.B1.Sig
