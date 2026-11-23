/-
  LeanVM.Guest.B1.Sig.XmssPathPops

  The pops of the leanXMSS path in `main_loop2` (`lx_levels`, `lean_ethereum.py:3804-3828`), completing: a layer's two windows pop the sixteen `"lx_path"` entries, in level order, and on the honest siblings exactly `xmssLayer`'s `"lx_path"` pushes.
-/

module

public import LeanVM.Guest.B1.Sig.XmssWinPops
public import LeanVM.Guest.B1.Sig.XmssSegPathC
public import LeanVM.Guest.B1.Sig.XmssSegCoreC
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.Hints
import LeanVM.Protocol.Verifier.Load

/-!
# The path's pops

* `lxWindows_complete_pops`: `LxWindowsC`'s completion, popping `lxPathPops sibs` on every valuation agreeing below the end;
* `xmssLayer_lxPath`, `lxWindows_complete_honest`: on the layer signature's siblings (`xSibs`), those pops are `xmssLayer`'s `"lx_path"` pushes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory LeanVM.Protocol.Verifier LeanVM.Guest.Value.Keccak

@[expose] public section

variable {rd : Reader}

/-! ## Completeness, popping -/

/-- **A layer's two windows complete popping their siblings** (`LxWindowsC`): on every valuation agreeing below their end, the siblings are `sibs` and the windows pop `lxPathPops 16 sibs`. -/
theorem lxWindows_complete_pops {C : CallRel} (hm : MemOK rd 256) {L : Nat} (hL : L < 2 ^ 32) {layer : Nat}
    (hlay : layer < 2) {cur : V} {b0 : Nat} (hb : 103 ≤ b0) (hcur : NBv b0 cur) (σ : Val) (hpad : PadOK σ sLxPad)
    (hhis : ∀ v < 4, σ (sHis v) = eOfNat (L >>> (8 * v)))
    (hwin : ∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w))) (hpow : ∀ s < 13, σ (sPower s) = gen ^ s)
    (sibs : Nat → E) :
    Completes C rd b0 (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).2.1
      ((lxWindowT (2 * layer) cur b0).1 ++ (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).1) σ
      (fun σ' => ∀ σ'', AgreeBelow (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
            (lxWindowT (2 * layer) cur b0).2.1).2.1 σ' σ'' →
          (∀ r < 8, lxSibOf σ'' (2 * layer) (lxWin L (2 * layer)) b0 r = sibs r) ∧
          (∀ r < 8, lxSibOf σ'' (2 * layer + 1) (lxWin L (2 * layer + 1)) (lxWindowT (2 * layer) cur b0).2.1 r =
            sibs (8 + r)) ∧
          FallPops rd σ'' ((lxWindowT (2 * layer) cur b0).1 ++ (lxWindowT (2 * layer + 1)
            (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).1) (lxPathPops 16 sibs)) := by
  obtain ⟨hend, -, hc⟩ := lxWindowsC C rd layer hlay cur b0 L hm hL hcur hb
  obtain ⟨σ', he, hp, hh⟩ := hc σ hpad hhis hwin hpow sibs
  refine ⟨σ', he, fun σ'' hag => ?_, hh⟩
  obtain ⟨h0, h1⟩ := hp σ'' hag
  have hwin'' : ∀ w < 4, σ'' (sWin w) = ofK (addressOfIndex (lxWin L w)) := fun w hw => by
    rw [show sWin w = V.n (71 + w) from rfl, ← hag _ (by omega), he.apply (Or.inl (by omega))]
    exact hwin w hw
  exact ⟨h0, h1, lxWindows_pops hlay cur b0 hwin'' h0 h1⟩

/-! ## The honest siblings -/

theorem cellOfBytes_cellBytes (x : E) : Hints.cellOfBytes (cellBytes x) = x := by
  have hl : ∀ a : K, (K.toBytes a).length = 8 := fun a => by simp [K.toBytes, LeanVM.Protocol.KeccakHash.wordBytes]
  conv_rhs => rw [eq_ofLimbs x]
  rw [Hints.cellOfBytes, cellBytes, kOfBytes_kBytes_append, List.drop_left' (hl _),
    ← List.append_nil (K.toBytes (x.limb 1)), kOfBytes_kBytes_append]

/-- The hint generator's cell of a 128-bit value is the guest's. -/
theorem cell128_eq (v : BitVec 128) : Hints.cell128 v = cellOf128 v := by
  conv_lhs => rw [← cellVal_cellOf128 v]
  rw [Hints.cell128, bytesLE_cellVal, cellOfBytes_cellBytes]

/-- **A leanXMSS layer's `"lx_path"` pushes** are its siblings' entries, in level order. -/
theorem xmssLayer_lxPath (parameter : HashSig.PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (message : List UInt8) (part : LeanXmss.LayerSignature) :
    (Hints.xmssLayer parameter lay key message part).1.filter (·.1 == "lx_path") = lxPathPops 16 (xSibs part) := by
  have hs : ∀ (l : List (String × Hints.Entry)), (∀ p ∈ l, p.1 ≠ "lx_path") → l.filter (·.1 == "lx_path") = [] :=
    fun l h => List.filter_eq_nil_iff.mpr fun p hp => by simpa using h p hp
  simp only [Hints.xmssLayer, List.filter_append]
  rw [List.filter_eq_self.mpr (fun p hp => by obtain ⟨l, -, rfl⟩ := List.mem_map.mp hp; rfl),
    hs _ (by simp), hs _ (fun p hp => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hp
      exact (by decide : ("chain_starts" : String) ≠ "lx_path")), List.append_nil, List.append_nil]
  refine List.ext_getElem (by simp [lxPathPops, LeanXmss.layerHeight]) fun i h1 h2 => ?_
  have hi : i < 16 := by simpa [lxPathPops] using h2
  simp only [List.getElem_map, List.getElem_finRange, lxPathPops, List.getElem_range, xSibs, hi, dite_true]
  exact congrArg (fun c => (("lx_path" : String), [c])) (cell128_eq _)

/-- **A layer's two windows complete popping `xmssLayer`'s `"lx_path"` pushes**, on the layer signature's siblings. -/
theorem lxWindows_complete_honest {C : CallRel} (hm : MemOK rd 256) {L : Nat} (hL : L < 2 ^ 32) {layer : Nat}
    (hlay : layer < 2) {cur : V} {b0 : Nat} (hb : 103 ≤ b0) (hcur : NBv b0 cur) (σ : Val) (hpad : PadOK σ sLxPad)
    (hhis : ∀ v < 4, σ (sHis v) = eOfNat (L >>> (8 * v)))
    (hwin : ∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w))) (hpow : ∀ s < 13, σ (sPower s) = gen ^ s)
    (parameter : HashSig.PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex) (message : List UInt8)
    (part : LeanXmss.LayerSignature) :
    Completes C rd b0 (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).2.1
      ((lxWindowT (2 * layer) cur b0).1 ++ (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
        (lxWindowT (2 * layer) cur b0).2.1).1) σ
      (fun σ' => ∀ σ'', AgreeBelow (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2)
            (lxWindowT (2 * layer) cur b0).2.1).2.1 σ' σ'' →
          FallPops rd σ'' ((lxWindowT (2 * layer) cur b0).1 ++ (lxWindowT (2 * layer + 1)
            (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).1)
            ((Hints.xmssLayer parameter lay key message part).1.filter (·.1 == "lx_path"))) := by
  rw [xmssLayer_lxPath]
  exact (lxWindows_complete_pops (C := C) hm hL hlay hb hcur σ hpad hhis hwin hpow (xSibs part)).mono le_rfl le_rfl
    fun _ h σ'' hag => (h σ'' hag).2.2

end
end LeanVM.Guest.B1.Sig
