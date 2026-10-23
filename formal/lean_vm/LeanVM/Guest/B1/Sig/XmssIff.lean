/-
  LeanVM.Guest.B1.Sig.XmssIff

  `verify_lean_xmss` is complete: every claim some signature verifies holds; with its soundness,
  its relation is its meaning.
-/

module

public import LeanVM.Guest.B1.Sig.XmssComplete
public import LeanVM.Guest.B1.Sig.Callees

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1.Sig
open LeanXmss LeanXmss.Concrete

@[expose] public section

namespace Sig

variable {C : CallRel} {rd : Reader}

/-! ## Bounds of the layers -/

theorem xTail_root_lt (layer a : Nat) (idx d0 : V) : NB (xTail layer a idx d0).2.1 (xTail layer a idx d0).2.2 := by
  simp only [xTail]
  exact merkle_snd_lt _ _ _ _ _ 16 0 _ _ (hashValues_snd_lt _ _ _ _ _)

/-- A layer's root is numbered below the next base. -/
theorem xLayer_root_lt (layer b : Nat) (root : V) (hl : layer < 2) :
    NB (xLayer layer b root).2.1 (xLayer layer b root).2.2 := by
  interval_cases layer
  · rw [xLayer_zero]; exact xTail_root_lt _ _ _ _
  · rw [xLayer_one]; exact xTail_root_lt _ _ _ _

theorem xLayer0_below (b : Nat) (hb : 139 ≤ b) (root : V) :
    NumBelow (xLayer 0 b root).2.1 (Stmt.valsList (xLayer 0 b root).1) := by
  have hgt := xLayer_snd_gt 0 b root (by omega)
  rw [xLayer_zero] at hgt ⊢
  dsimp only at hgt ⊢
  rw [valsList_append]
  exact ((xDigest0_below b (by omega)).mono (by omega)).append
    (xTail_below (by omega) (by omega) ⟨128, by omega, rfl⟩ ⟨b + 14, by omega, rfl⟩)

theorem xLayer1_below (b : Nat) (hb : 139 ≤ b) {root : V} (hroot : NB b root) :
    NumBelow (xLayer 1 b root).2.1 (Stmt.valsList (xLayer 1 b root).1) := by
  have hgt := xLayer_snd_gt 1 b root (by omega)
  rw [xLayer_one] at hgt ⊢
  dsimp only at hgt ⊢
  rw [valsList_append]
  exact ((xDigest1_below b (by omega) hroot).mono (by omega)).append
    (xTail_below (by omega) (by omega) ⟨b + 1, by omega, rfl⟩ ⟨b + 8, by omega, rfl⟩)

theorem xBody_split : xBody =
    (xPrologue ++ ((xLayer 0 139 (.n 0)).1 ++ ((xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).1 ++
      [.atom (.load (.n (xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).2.1) (.n 0) 0),
        .atom (.assertEq (xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).2.2
          (.n (xLayer 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2).2.1))]))) ++ [.ret []] := by
  simp only [xBody, List.append_assoc, List.cons_append, List.nil_append]

theorem message_bytes (m : LeanXmss.Message) :
    LeanXmss.bytesLE 32 m = cellBytes (cellOf (m.extractLsb' 0 128)) ++ cellBytes (cellOf (m.extractLsb' 128 128)) :=
  bytesLE_message (cellVal_cellOf _).symm (cellVal_cellOf _).symm

/-- **`verify_lean_xmss` is complete**: for a claim at `p` that some signature verifies, on a
memory holding at least 64 words, the body holds from a valuation with `p` as its argument. -/
theorem verify_lean_xmss_complete (hrd : MemOK rd 64) {p : E} {pk : LeanXmss.PublicKey} {m : LeanXmss.Message}
    {sig : LeanXmss.Signature} (hc : ClaimAt rd p (claimCells pk.root pk.parameter m))
    (hv : Node.xmssVerify pk m sig = true) :
    ∃ σ : Val, σ (.n 0) = p ∧ Stmt.HoldsList C rd σ xBody False (fun rs => rs = []) := by
  have hv' : @LeanXmss.Concrete.verify Id _ ⟨Node.blake2sBits⟩ pk m sig = true := by
    rw [Node.xmssVerify.eq_def, idRun] at hv; exact hv
  generalize hI : (⟨Node.blake2sBits⟩ : HasQuery LeanXmss.HashSpec Id) = inst at hv'
  have hq : XQ inst := hI ▸ xq_blake2s
  obtain ⟨r0, h0, h1⟩ := (verify_iff pk m sig).mp hv'
  have h0' : @layerRoot Id _ inst (xpp (cellOf pk.parameter)) bottomLayer (keyAt sig.leafIndex bottomLayer)
      (cellBytes (cellOf (m.extractLsb' 0 128)) ++ cellBytes (cellOf (m.extractLsb' 128 128)))
      (sig.layers bottomLayer) = some r0 := by
    rw [← message_bytes, show xpp (cellOf pk.parameter) = pk.parameter from cellVal_cellOf _]
    exact h0
  have h1' : @layerRoot Id _ inst (xpp (cellOf pk.parameter)) topLayer (keyAt sig.leafIndex topLayer)
      (cellBytes (cellOf r0)) (sig.layers topLayer) = some pk.root := by
    rw [cellBytes_cellOf r0, show xpp (cellOf pk.parameter) = pk.parameter from cellVal_cellOf _]
    exact h1
  have hL : sig.leafIndex.val < 2 ^ 32 := sig.leafIndex.isLt
  have hgt0 := xLayer_snd_gt 0 139 (.n 0) (by omega)
  have hgt1 := xLayer_snd_gt 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2 (by omega)
  have hroot0 := xLayer_root_lt 0 139 (.n 0) (by omega)
  have hroot1 := xLayer_root_lt 1 (xLayer 0 139 (.n 0)).2.1 (xLayer 0 139 (.n 0)).2.2 (by omega)
  rw [xBody_split]
  set l0 := xLayer 0 139 (.n 0)
  set l1 := xLayer 1 l0.2.1 l0.2.2
  have hcomp : Completes C rd 1 (l1.2.1 + 1) (xPrologue ++ (l0.1 ++ (l1.1 ++
      [.atom (.load (.n l1.2.1) (.n 0) 0), .atom (.assertEq l1.2.2 (.n l1.2.1))]))) (fun _ => p) (fun _ => True) := by
    refine Completes.append (m := 139) (by omega) (by omega) xPrologue_below (xPrologue_complete (hc 1) hL)
      fun σ1 _ ⟨hpre1, hpp1, hag1⟩ => ?_
    have hp1 : σ1 (.n 0) = p := (hag1 0 (by omega)).symm
    have hpar : σ1 (.n 1) = cellOf pk.parameter := hpp1
    refine Completes.append (m := l0.2.1) (by omega) (by omega) (xLayer0_below 139 le_rfl _)
      (xLayer0_complete (inst := inst) hq hrd hpre1
        (key := keyAt sig.leafIndex bottomLayer) (keyAt_bottom_val _) le_rfl (by rw [hp1]; exact hc 2)
        (by rw [hp1]; exact hc 3) (by rw [hpar]; exact isCanonical128_cellOf _) (isCanonical128_cellOf _)
        (isCanonical128_cellOf _) (part := sig.layers bottomLayer) (r := r0)
        (by rw [hpar]; exact h0'))
      fun σ2 _ ⟨hr2, hag2⟩ => ?_
    have hpre2 : XPre σ2 sig.leafIndex.val := hpre1.congr hag2
    have h21 : σ2 (.n 1) = cellOf pk.parameter := (hag2 1 (by omega)).symm.trans hpar
    refine Completes.append (m := l1.2.1) (by omega) (by omega) (xLayer1_below _ (by omega) hroot0)
      (xLayer1_complete (inst := inst) hq hrd hpre2
        (key := keyAt sig.leafIndex topLayer) (keyAt_top_val _) (by omega) hroot0
        (by rw [h21]; exact isCanonical128_cellOf _) (by rw [hr2]; exact isCanonical128_cellOf _)
        (part := sig.layers topLayer) (r := pk.root)
        (by rw [h21, hr2]; exact h1'))
      fun σ3 _ ⟨hr3, hag3⟩ => ?_
    have h30 : σ3 (.n 0) = p := ((hag3 0 (by omega)).symm.trans (hag2 0 (by omega)).symm).trans hp1
    obtain ⟨kr, hkr, hkre⟩ := hroot1
    have hne0 : (V.n 0) ≠ V.n l1.2.1 := fun e => by simp only [V.mk.injEq] at e; omega
    have hner : l1.2.2 ≠ V.n l1.2.1 := fun e => by rw [hkre] at e; simp only [V.mk.injEq] at e; omega
    refine Completes.atom_cons (cellOf pk.root) le_rfl
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨0, by omega, rfl⟩ (.nil _))) ?_ ?_
    · show LoadHolds rd (Function.update σ3 (.n l1.2.1) (cellOf pk.root) (.n 0)) 0
        (Function.update σ3 (.n l1.2.1) (cellOf pk.root) (.n l1.2.1))
      rw [Function.update_self, Function.update_of_ne hne0, h30]
      exact hc 0
    refine Completes.atom_cons0 (.cons ⟨kr, by omega, hkre⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))) ?_
      (Completes.nil _ _ _ trivial)
    show Function.update σ3 (.n l1.2.1) (cellOf pk.root) l1.2.2 +
      Function.update σ3 (.n l1.2.1) (cellOf pk.root) (.n l1.2.1) = 0
    rw [Function.update_self, Function.update_of_ne hner, hr3]
    exact e_add_eq_zero_iff.mpr rfl
  obtain ⟨σ', he, -, hh⟩ := hcomp
  refine ⟨σ', he.apply (Or.inl (by norm_num)), ?_⟩
  have hret : Stmt.HoldsList C rd σ' [.ret []] False (fun rs => rs = []) := by
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil]
  rw [holdsList_append]
  exact hh _ _ hret

end Sig

variable {rd : Reader}

/-- **`verify_lean_xmss` is its meaning**, on a memory holding at least 64 words. -/
theorem verify_lean_xmss_iff (hrd : MemOK rd 64) {args rets : List E} :
    coreProgram.Rel rd "verify_lean_xmss" args rets ↔ Meaning_verify_lean_xmss rd args rets := by
  refine ⟨verify_lean_xmss_meaning, fun ⟨p, ha, hr, pk, m, hc, sig, hv⟩ => ?_⟩
  obtain ⟨σ, hσ, hb⟩ := Sig.verify_lean_xmss_complete (C := coreProgram.Rel rd) hrd hc hv
  refine (rel_iff_sem Sig.find_verify_lean_xmss args rets).mpr ⟨σ, by rw [ha]; simp [hσ], ?_⟩
  rw [hr]
  exact hb

end
end LeanVM.Guest.B1
