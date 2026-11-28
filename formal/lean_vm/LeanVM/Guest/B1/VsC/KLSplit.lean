/-
  LeanVM.Guest.B1.VsC.KLSplit

  `keccak_layer`'s template around its two dispatches: its walk, `HeapBuf`s, callees, loads and
  hints, checked by the kernel.
-/

module

public import LeanVM.Guest.B1.VsC.KLBody
public import LeanVM.Guest.B1.VsC.FwdCalls
public import LeanVM.Guest.B1.VsC.SlowC
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Memory.HintsCheck
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# A layer's template around its dispatches

`layerT_split`: the body is a run of atoms `lP1`, the dispatch on `step_g`, the atoms `packMid`,
the dispatch on `rem_g`, the atoms `lP3`, then its return. On a valuation reading `step_g` as
`g^j1` and `rem_g` as `g^j2`, its walk is the straight body `lPre first j1 j2` with the two
dispatches entered as calls (`layer_walk`). The kernel checks the atoms (`layer_atoms`): their
`HeapBuf`s (the point, the local point, the next claim's lanes and flips), no `frameAddr`, no heap
hint, no witness hint, every hint trivially exact or the inlined `grind_check`'s, every load through
the claim, the cursor, `out`, the cursor after the pack rounds, the claim's lanes and local point,
the layer's buffers or `grind_check`'s table pointers.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The split -/

/-- The pack section before its first dispatch. -/
def packHead (o : ℕ) : List Stmt :=
  [.atom (.load (.n (o + 781)) (.n (valf% «keccak_layer» "claim")) 2),
    .atom (.hint (.allocDyn (.n (o + 782)) (.n (valf% «keccak_layer» "y_g")))),
    .atom (.const (.n (o + 783)) (word 281474976710656 0)),
    .atom (.mul (.n (o + 784)) (.n (valf% «keccak_layer» "cursor@1")) (.n (o + 783)))]

/-- The first dispatch's arguments and returns. -/
def lA1 (o : ℕ) : List V := (cap5 (o + 539)) ++ [.n (o + 784), .n (o + 780), .n (o + 781), .n (o + 782),
  .n (valf% «keccak_layer» "tabs")]
def lR1 (o : ℕ) : List V := (List.range 7).map fun k ↦ .n (o + 785 + k)

/-- The pack section between its dispatches. -/
def packMid (o : ℕ) : List Stmt :=
  [.atom (.mul (.n (o + 792)) (.n (valf% «keccak_layer» "step_g")) (.n (valf% «keccak_layer» "step_g"))),
    .atom (.mul (.n (o + 793)) (.n (o + 792)) (.n (o + 792))),
    .atom (.mul (.n (o + 794)) (.n (o + 793)) (.n (o + 793))),
    .atom (.mul (.n (o + 795)) (.n (o + 794)) (.n (o + 794))),
    .atom (.mul (.n (o + 796)) (.n (o + 781)) (.n (o + 795))),
    .atom (.mul (.n (o + 797)) (.n (o + 782)) (.n (o + 795)))]

/-- The second dispatch's arguments and returns. -/
def lA2 (o : ℕ) : List V := lR1 o ++ [.n (o + 796), .n (o + 797), .n (valf% «keccak_layer» "tabs")]
def lR2 (o : ℕ) : List V := (List.range 7).map fun k ↦ .n (o + 798 + k)

/-- The pack section after its second dispatch. -/
def packTail (o : ℕ) : List Stmt :=
  (List.range 5).map (fun j ↦ .atom (.copy (.n (o + 805 + j)) (.n (o + 798 + j)))) ++
  [.atom (.hint (.alloc (.n (o + 810)) 11))]

theorem packT_split (o : ℕ) : packT o = packHead o ++
    [.dispatch (.n (valf% «keccak_layer» "step_g")) stepNames (lA1 o) (lR1 o)] ++ packMid o ++
    [.dispatch (.n (valf% «keccak_layer» "rem_g")) remNames (lA2 o) (lR2 o)] ++ packTail o := by
  simp only [packT, packHead, packMid, packTail, lA1, lR1, lA2, lR2,
    List.cons_append, List.nil_append]

/-- The atoms before the first dispatch. -/
def lP1 (first : ℕ) : List Stmt :=
  secA1 first ++ secA2 first ++ rmfeBlockT (preOff first) ++ hornerS first ++ packHead (preOff first)

/-- The atoms after the second dispatch, but the return. -/
def lP3 (first : ℕ) : List Stmt :=
  packTail (preOff first) ++ localS (layOff first) ++ tReadsT (layOff first) ++ eqfS (layOff first) ++
    weightT first (layOff first) ++ tailPre (layOff first) (tW first) (tV first)

/-- The returns. -/
def lRet (first : ℕ) : List V :=
  [.n (topV (tW first) + 305), .n (topV (tW first) + 306), .n (topV (tW first) + 307),
    .n (topV (tW first) + 308), .n (topV (tW first) + 309), .n (topV (tW first) + 312)]

theorem layerT_split (first : ℕ) : layerT first = lP1 first ++
    [.dispatch (.n (valf% «keccak_layer» "step_g")) stepNames (lA1 (preOff first)) (lR1 (preOff first))] ++
    packMid (preOff first) ++
    [.dispatch (.n (valf% «keccak_layer» "rem_g")) remNames (lA2 (preOff first)) (lR2 (preOff first))] ++
    lP3 first ++ [.ret (lRet first)] := by
  rw [layerT_sections, packT_split, tailT_split]
  simp only [lP1, lP3, lRet, List.append_assoc, List.cons_append, List.nil_append]

/-- The body with the two dispatches entered as calls, but its return. -/
def lPre (first j1 j2 : ℕ) : List Stmt :=
  lP1 first ++ [.call (stepNames.getD j1 "") (lA1 (preOff first)) (lR1 (preOff first))] ++
    packMid (preOff first) ++
    [.call (remNames.getD j2 "") (lA2 (preOff first)) (lR2 (preOff first))] ++ lP3 first

/-! ## The walk -/

theorem walk_congr_mid (σ : Val) {s s' : Stmt} (h : walk1 σ s = walk1 σ s') :
    ∀ (A B : List Stmt), walk σ (A ++ s :: B) = walk σ (A ++ s' :: B)
  | [], B => by simp only [List.nil_append, walk, h]
  | a :: A, B => by simp only [List.cons_append, walk, walk_congr_mid σ h A B]

theorem walk1_dispatch {σ : Val} {x : V} {gs : List String} {args rets : List V} {j : ℕ}
    (hj : j < gs.length) (hj' : j < 2 ^ 64 - 1) (hx : σ x = ofK (addressOfIndex j)) :
    walk1 σ (.dispatch x gs args rets) = walk1 σ (.call (gs.getD j "") args rets) := by
  have hp := pick_eq σ x args rets gs 0 j (by omega) (by simpa using hj) hj' hx
  rw [walk1, walk1, hp, List.getD_eq_getElem _ _ hj]
  rfl

/-- **A layer's walk**: its dispatches entered as calls. -/
theorem layer_walk {σ : Val} (first : ℕ) {j1 j2 : ℕ} (hj1 : j1 < 2) (hj2 : j2 < 16)
    (hx1 : σ (.n (valf% «keccak_layer» "step_g")) = ofK (addressOfIndex j1))
    (hx2 : σ (.n (valf% «keccak_layer» "rem_g")) = ofK (addressOfIndex j2)) :
    walk σ (layerT first) = walk σ (lPre first j1 j2 ++ [.ret (lRet first)]) := by
  rw [layerT_split]
  have e1 := walk1_dispatch (σ := σ) (gs := stepNames) (args := lA1 (preOff first))
    (rets := lR1 (preOff first)) (by simpa [stepNames] using hj1) (by omega) hx1
  have e2 := walk1_dispatch (σ := σ) (gs := remNames) (args := lA2 (preOff first))
    (rets := lR2 (preOff first)) (by simpa [remNames] using hj2) (by omega) hx2
  have s1 : lP1 first ++
      [.dispatch (.n (valf% «keccak_layer» "step_g")) stepNames (lA1 (preOff first)) (lR1 (preOff first))] ++
      packMid (preOff first) ++
      [.dispatch (.n (valf% «keccak_layer» "rem_g")) remNames (lA2 (preOff first)) (lR2 (preOff first))] ++
      lP3 first ++ [.ret (lRet first)] =
      lP1 first ++ .dispatch (.n (valf% «keccak_layer» "step_g")) stepNames (lA1 (preOff first)) (lR1 (preOff first)) ::
        (packMid (preOff first) ++
          [.dispatch (.n (valf% «keccak_layer» "rem_g")) remNames (lA2 (preOff first)) (lR2 (preOff first))] ++
          lP3 first ++ [.ret (lRet first)]) := by simp
  rw [s1, walk_congr_mid σ e1]
  have s2 : lP1 first ++ .call (stepNames.getD j1 "") (lA1 (preOff first)) (lR1 (preOff first)) ::
        (packMid (preOff first) ++
          [.dispatch (.n (valf% «keccak_layer» "rem_g")) remNames (lA2 (preOff first)) (lR2 (preOff first))] ++
          lP3 first ++ [.ret (lRet first)]) =
      (lP1 first ++ [.call (stepNames.getD j1 "") (lA1 (preOff first)) (lR1 (preOff first))] ++
        packMid (preOff first)) ++
        .dispatch (.n (valf% «keccak_layer» "rem_g")) remNames (lA2 (preOff first)) (lR2 (preOff first)) ::
          (lP3 first ++ [.ret (lRet first)]) := by simp
  rw [s2, walk_congr_mid σ e2]
  congr 1
  simp [lPre]

/-! ## The atoms, checked -/

/-- The atoms of the three runs. -/
def lAtoms (first : ℕ) : List Stmt := lP1 first ++ packMid (preOff first) ++ lP3 first

/-- The pointers the layer loads through, with their bounds. -/
def ldPs (first : ℕ) : List (V × ℕ) :=
  [(.n (valf% «keccak_layer» "claim"), kcSize), (.n (valf% «keccak_layer» "cursor@1"), 48),
    (.n (valf% «keccak_layer» "out"), kcSize), (.n (layOff first + 802), 36),
    (.n (layOff first + 1240), 25), (.n (layOff first + 809), 11),
    (.n (tW first + 25), 25), (.n (topV (tW first) + 3), 7)] ++
    if first = 1 then [] else [(.n (layOff first + 1241), 11)]

/-- A load through one of `ldPs`, or a table read of the inlined `grind_check`. -/
def ldOk (first : ℕ) (a : Atom) : Bool :=
  ldIn (ldPs first) a || match a with
    | .load _ p off => (gcPtrs 3 (preOff first + 544)).contains p && off == 0
    | _ => false

/-- A load. -/
def isLoad : Atom → Bool
  | .load .. => true
  | _ => false

/-- A hint writing no heap word. -/
def noHeapHint : Atom → Bool
  | .hint h => ((hintDest? h).bind destHeap?).isNone
  | _ => true

/-- An atom of the inlined `grind_check`'s. -/
def inGc (first : ℕ) (a : Atom) : Bool := (atomsL (gcInlineT 3 (preOff first + 544)
  (.n (preOff first + 532)) (.n (valf% «keccak_layer» "tabs")))).contains a

/-- **What the kernel checks of a layer's atoms.** -/
def layerAtomsOk (first : ℕ) : Bool :=
  (lAtoms first).all isAtom && (atomsL (lAtoms first)).all (fun a ↦ !isLoad a || ldOk first a) &&
    (atomsL (lAtoms first)).all noHeapHint && (atomsL (lAtoms first)).all VsC.atomQuiet &&
    (atomsL (lAtoms first)).all (fun a ↦ VsC.trivExact a || inGc first a) &&
    decide ((lAtoms first).filterMap Stmt.allocSz = [(.n (preOff first + 782), .inr (.n (valf% «keccak_layer» "y_g"))),
      (.n (preOff first + 810), .inl 11), (.n (tW first + 25), .inl 25), (.n (topV (tW first) + 3), .inl 7)]) &&
    decide ((lAtoms first).filterMap Stmt.addrS = []) && decide ((lAtoms first).filterMap Stmt.callS = [])

set_option maxRecDepth 100000 in
theorem layer_atoms1 {first : ℕ} (hf : first < 2) : (lAtoms first).all isAtom = true := by
  interval_cases first <;> decide +kernel
set_option maxRecDepth 100000 in
theorem layer_atoms2 {first : ℕ} (hf : first < 2) :
    (atomsL (lAtoms first)).all (fun a ↦ !isLoad a || ldOk first a) = true := by
  interval_cases first <;> decide +kernel
set_option maxRecDepth 100000 in
theorem layer_atoms3 {first : ℕ} (hf : first < 2) :
    (atomsL (lAtoms first)).all noHeapHint = true ∧ (atomsL (lAtoms first)).all VsC.atomQuiet = true := by
  interval_cases first <;> exact ⟨by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
theorem layer_atoms4 {first : ℕ} (hf : first < 2) :
    (atomsL (lAtoms first)).all (fun a ↦ VsC.trivExact a || inGc first a) = true := by
  interval_cases first <;> decide +kernel
set_option maxRecDepth 100000 in
theorem layer_atoms5 {first : ℕ} (hf : first < 2) :
    (lAtoms first).filterMap Stmt.allocSz = [(.n (preOff first + 782), .inr (.n (valf% «keccak_layer» "y_g"))),
      (.n (preOff first + 810), .inl 11), (.n (tW first + 25), .inl 25), (.n (topV (tW first) + 3), .inl 7)] ∧
    (lAtoms first).filterMap Stmt.addrS = [] ∧ (lAtoms first).filterMap Stmt.callS = [] := by
  interval_cases first <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem gc_mem {first : ℕ} (hf : first < 2) {s : Stmt} (hs : s ∈ gcInlineT 3 (preOff first + 544)
    (.n (preOff first + 532)) (.n (valf% «keccak_layer» "tabs"))) : s ∈ layerT first := by
  interval_cases first <;> norm_num [preOff] at hs <;> simp [layerT, sqT, hs]

end
end LeanVM.Guest.B1.VerifySub.KL
