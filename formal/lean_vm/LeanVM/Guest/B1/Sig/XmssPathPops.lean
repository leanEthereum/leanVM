/-
  LeanVM.Guest.B1.Sig.XmssPathPops

  The pops of the leanXMSS path in `main_loop2` (`lx_levels`, `lean_ethereum.py:3804-3828`): a layer's two windows pop the sixteen `"lx_path"` entries, in level order, and on the honest siblings exactly `xmssLayer`'s `"lx_path"` pushes.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegPathC
public import LeanVM.Guest.B1.Sig.XmssSegCoreC
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.Pops
public import LeanVM.Guest.Hints
import LeanVM.Protocol.Verifier.Load

/-!
# The path's pops

* `fallPops_atoms`: a block of atoms pops its hints' entries (`atomsPops`);
* `lxLevelsT_pops`, `lxArmT_pops`, `lxWindowT_pops`: each level of the arm a window's selector takes pops its sibling, from any valuation;
* `lxWindows_pops`: a layer's two windows pop `lxPathPops sibs` when their siblings are `sibs`;
* `lxWindows_complete_pops`: `LxWindowsC`'s completion, popping `lxPathPops sibs` on every valuation agreeing below the end;
* `xmssLayer_lxPath`, `lxWindows_complete_honest`: on the layer signature's siblings (`xSibs`), those pops are `xmssLayer`'s `"lx_path"` pushes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory LeanVM.Protocol.Verifier LeanVM.Guest.Value.Keccak

@[expose] public section

variable {rd : Reader}

/-! ## Blocks of atoms -/

/-- The entries a block's atoms pop. -/
def atomsPops (rd : Reader) (σ : Val) (ss : List Stmt) : List Pop :=
  ss.flatMap fun | .atom a => a.pops rd σ | _ => []

theorem fallPops_atoms (σ : Val) : ∀ {ss : List Stmt}, atomsOnly ss = true → FallPops rd σ ss (atomsPops rd σ ss)
  | [], _ => FallPops.nil
  | .atom a :: ss, h => by
      simp only [atomsOnly] at h
      have := (fallPops_atoms σ h).cons_atom (a := a)
      simpa [atomsPops] using this
  | .ite .. :: _, h | .match_ .. :: _, h | .call .. :: _, h | .callIf .. :: _, h
  | .dispatch .. :: _, h | .ret _ :: _, h => by simp [atomsOnly] at h

/-- The `"lx_path"` entries of the siblings `sibs`, in level order. -/
def lxPathPops (n : Nat) (sibs : Nat → E) : List Pop := (List.range n).map fun l => ("lx_path", [sibs l])

/-! ## A window -/

theorem lxLevelT_pops (σ : Val) (w k r : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    FallPops rd σ (lxLevelT w k r cur outO b).1 [("lx_path", [σ (.n (lxSibCell w r b))])] := by
  have h := fallPops_atoms (rd := rd) σ (lxLevelT_atoms w k r cur outO b)
  convert h using 1
  unfold lxLevelT lxSibCell
  by_cases hw : w + 1 = 4
  · simp [hw, atomsPops, hintW, cst, k64, kecS, Atom.pops, Hint.pops, Dest.words]
  · by_cases hr : r + 1 = 8
    · simp [hw, hr, atomsPops, hintW, cst, addS, k64, kecS, Atom.pops, Hint.pops, Dest.words]
    · simp [hw, hr, atomsPops, hintW, cst, addS, mulS, k64, kecS, Atom.pops, Hint.pops, Dest.words]

theorem lxLevelsT_pops (σ : Val) {w k : Nat} {outO : Option Nat} {b0 : Nat} :
    ∀ m r (cur : V) b, r + m = 8 → b = b0 + lxStride w * r →
      FallPops rd σ (lxLevelsT w k outO m r cur b).1 ((List.range m).map fun j => ("lx_path", [lxSibF σ w b0 (r + j)]))
  | 0, _, _, _, _, _ => FallPops.nil
  | m + 1, r, cur, b, hrm, hb => by
      simp only [lxLevelsT]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, ← List.singleton_append]
      refine FallPops.append ?_ ?_
      · have := lxLevelT_pops (rd := rd) σ w k r cur outO b
        rwa [lxSibF, Nat.add_zero, ← hb]
      · by_cases hm : m = 0
        · subst hm
          exact FallPops.nil
        · have ih := lxLevelsT_pops σ (k := k) (outO := outO) m (r + 1) (lxLevelT w k r cur outO b).2.2 (lxLevelT w k r cur outO b).2.1
            (by omega) (by rw [lxLevelT_next (by omega), hb]; ring)
          convert ih using 2
          funext j
          show (("lx_path", [lxSibF σ w b0 (r + (j + 1))]) : Pop) = ("lx_path", [lxSibF σ w b0 (r + 1 + j)])
          rw [show r + (j + 1) = r + 1 + j by omega]

theorem lxArmT_pops (σ : Val) (w k : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    FallPops rd σ (lxArmT w k cur outO b).1 (lxPathPops 8 (lxSibF σ w b)) := by
  have hl := lxLevelsT_pops (rd := rd) σ (w := w) (k := k) (outO := outO) (b0 := b) 8 0 cur b rfl (by simp)
  simp only [Nat.zero_add] at hl
  rw [lxPathPops, ← List.append_nil ((List.range 8).map _)]
  unfold lxArmT
  split_ifs
  · exact hl.append (FallPops.atom _)
  · exact hl.append (FallPops.atom _)
  · exact hl.append ((FallPops.atom _).append ((FallPops.atom _).append (FallPops.atom _)))

/-- **A window pops the siblings of the arm its selector takes**, in level order. -/
theorem lxWindowT_pops {σ : Val} {w k : Nat} (hk : k < 256) (hx : σ (sWin w) = ofK (addressOfIndex k)) (cur : V)
    (b : Nat) : FallPops rd σ (lxWindowT w cur b).1 (lxPathPops 8 (lxSibF σ w (lxArmB w 0 k (b + 5)))) := by
  dsimp only [lxWindowT]
  rw [← List.nil_append (lxPathPops 8 _)]
  have hr : FallPops rd σ (rangeS (sWin w) bound255 b) [] := by
    have h := fallPops_atoms (rd := rd) σ (ss := rangeS (sWin w) bound255 b) (by simp [rangeS, cst, atomsOnly])
    simpa [atomsPops, rangeS, cst, Atom.pops] using h
  refine FallPops.append hr ?_
  rw [← List.nil_append (lxPathPops 8 _)]
  refine FallPops.cons_atom (a := .const (.n (b + 4)) closeLane) ?_
  have hlen : k < (lxArmsT w cur (lxOut0 w (b + 5)) 256 0 (b + 5)).1.length := by rw [lxArmsT_length]; exact hk
  refine FallPops.match_ hlen (by omega) hx ?_
  rw [lxArmsT_getElem]
  simpa using lxArmT_pops (rd := rd) σ w k cur _ (lxArmB w 0 k (b + 5))

/-- **A layer's two windows pop their siblings**: `sibs` when the arms their selectors take hint them. -/
theorem lxWindows_pops {σ : Val} {L layer : Nat} (hlay : layer < 2) (cur : V) (b0 : Nat)
    (hwin : ∀ w < 4, σ (sWin w) = ofK (addressOfIndex (lxWin L w))) {sibs : Nat → E}
    (h0 : ∀ r < 8, lxSibOf σ (2 * layer) (lxWin L (2 * layer)) b0 r = sibs r)
    (h1 : ∀ r < 8, lxSibOf σ (2 * layer + 1) (lxWin L (2 * layer + 1)) (lxWindowT (2 * layer) cur b0).2.1 r =
      sibs (8 + r)) :
    FallPops rd σ ((lxWindowT (2 * layer) cur b0).1 ++
      (lxWindowT (2 * layer + 1) (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1).1)
      (lxPathPops 16 sibs) := by
  have p0 := lxWindowT_pops (rd := rd) (lxWin_lt L (2 * layer)) (hwin _ (by omega)) cur b0
  have p1 := lxWindowT_pops (rd := rd) (lxWin_lt L (2 * layer + 1)) (hwin _ (by omega))
    (.n (lxWindowT (2 * layer) cur b0).2.2) (lxWindowT (2 * layer) cur b0).2.1
  have e : lxPathPops 16 sibs = lxPathPops 8 sibs ++ lxPathPops 8 fun r => sibs (8 + r) := by
    simp only [lxPathPops, show 16 = 8 + 8 from rfl, List.range_add, List.map_append, List.map_map]
    rfl
  have q0 : lxPathPops 8 (lxSibF σ (2 * layer) (lxArmB (2 * layer) 0 (lxWin L (2 * layer)) (b0 + 5))) =
      lxPathPops 8 sibs := List.map_congr_left fun r hr => by
    rw [show lxSibF σ _ _ r = sibs r from h0 r (List.mem_range.mp hr)]
  have q1 : lxPathPops 8 (lxSibF σ (2 * layer + 1) (lxArmB (2 * layer + 1) 0 (lxWin L (2 * layer + 1))
      ((lxWindowT (2 * layer) cur b0).2.1 + 5))) = lxPathPops 8 fun r => sibs (8 + r) :=
    List.map_congr_left fun r hr => by rw [show lxSibF σ _ _ r = sibs (8 + r) from h1 r (List.mem_range.mp hr)]
  rw [e, ← q0, ← q1]
  exact p0.append p1

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
