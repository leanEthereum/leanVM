/-
  LeanVM.Guest.B1.Sig.XmssSegPath

  The path of the leanXMSS check in `main_loop2` (`lx_window`, `lx_top_window`, `lx_levels`,
  `lean_ethereum.py:3577-3617, 3680-3689`), sound a window at a time: the dispatch takes an arm
  `k < 256`, whose eight levels fold the node with the hinted siblings in the order of `k`'s bits,
  and whose pin ties the hinted shifts.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegT
public import LeanVM.Guest.B1.Sig.Merkle

/-!
# A window of the path, sound

* `lxLevelT_sound`: level `r` of arm `k` hashes `P`, the address `lxAt` and the pair (the node and
  the hinted sibling at `lxSibCell`) in the order of `k`'s bit `r`;
* `lxLevelsT_sound`: the eight levels are `mFold` over the level addresses (`lxAtF`), bits
  (`lxBitF`) and siblings (`lxSibF`), the levels `lxStride` apart, the last writing `out`;
* `lxArmBase`: where arm `k` of a window starts; `lxArmsT_getElem`;
* `lxWindowT_sound`: the window's dispatch takes an arm `k < 256`: its pin (`LxPin`) and its fold.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## Layout -/

/-- The values of a level of window `w` before the last. -/
def lxStride (w : Nat) : Nat := if w + 1 = 4 then 4 else 6

/-- The hinted sibling of level `r` of window `w` at base `b`. -/
def lxSibCell (w r b : Nat) : Nat := if w + 1 = 4 then b else if r + 1 = 8 then b + 2 else b + 3

/-- The base after the last level of window `w`, from its base: `out` numbered there in arm `0`. -/
def lxLastNext (w : Nat) (outO : Option Nat) : Nat :=
  if w + 1 = 4 then (if outO.isSome then 3 else 4) else (if outO.isSome then 4 else 5)

/-- Level `r`'s address in arm `k` of window `w`. -/
def lxAtF (σ : Val) (w k r : Nat) : E := lxAt (σ (sHis (w + 1))) (σ (sPower (7 - r))) w r k

/-- Arm `k`'s bit `r`. -/
def lxBitF (k r : Nat) : Bool := decide (k / 2 ^ r % 2 = 1)

/-- The hinted sibling of level `r` of an arm of window `w` from base `b0`. -/
def lxSibF (σ : Val) (w b0 r : Nat) : E := σ (.n (lxSibCell w r (b0 + lxStride w * r)))

/-! ## A level -/

theorem lxLevelT_atoms (w k r : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    atomsOnly (lxLevelT w k r cur outO b).1 = true := by
  unfold lxLevelT
  split_ifs <;> rfl

theorem ord_hash {k r : Nat} {cur sib : E} :
    [if k / 2 ^ r % 2 = 0 then cur else sib, if k / 2 ^ r % 2 = 0 then sib else cur] =
      [if lxBitF k r then sib else cur, if lxBitF k r then cur else sib] := by
  by_cases hb : k / 2 ^ r % 2 = 0
  · simp [lxBitF, hb]
  · have : k / 2 ^ r % 2 = 1 := by omega
    simp [lxBitF, this]

/-- **A level of a window**: its parent is the hash of `P`, the address and the pair in the order of
the arm's bit. -/
theorem lxLevelT_sound (hpad : PadOK σ sLxPad) {w k r : Nat} {cur : V} {outO : Option Nat} {b : Nat}
    (h : AtomsHold rd σ (lxLevelT w k r cur outO b).1) :
    σ (lxLevelT w k r cur outO b).2.2 = (hcell [σ sLxPP, lxAtF σ w k r,
      if lxBitF k r then σ (.n (lxSibCell w r b)) else σ cur,
      if lxBitF k r then σ cur else σ (.n (lxSibCell w r b))]).1 := by
  rw [← ord_hash]
  unfold lxLevelT at h ⊢
  by_cases hw : w + 1 = 4
  · simp only [hw, ↓reduceIte] at h ⊢
    have hk := k64_sound hpad h.right
    have hc : σ (.n (b + 1)) = word (lxNodeConst w r + k / 2 ^ (r + 1)) 0 :=
      h.left.atom (a := .const (.n (b + 1)) _) (by simp [cst])
    rw [show σ _ = _ from hk, hc]
    simp only [lxAtF, lxAt, hw, ↓reduceIte, lxSibCell]
    by_cases hb : k / 2 ^ r % 2 = 0 <;> simp [hb]
  · by_cases hr : r + 1 = 8
    · obtain rfl : r = 7 := by omega
      simp only [hw, ↓reduceIte, show 7 + 1 = 8 from rfl] at h ⊢
      have hk := k64_sound hpad h.right
      have hc : σ (.n b) = word (lxNodeConst w 7 + k / 2 ^ 8) 0 :=
        h.left.atom (a := .const (.n b) _) (by simp [cst])
      have ha : σ (.n (b + 1)) = σ (sHis (w + 1)) + σ (.n b) :=
        h.left.atom (a := .add (.n (b + 1)) (sHis (w + 1)) (.n b)) (by simp [addS])
      rw [show σ _ = _ from hk, ha, hc]
      simp only [lxAtF, lxAt, hw, ↓reduceIte, lxSibCell, show 7 + 1 = 8 from rfl]
      by_cases hb : k / 128 % 2 = 0 <;> simp [hb]
    · simp only [hw, hr, ↓reduceIte] at h ⊢
      have hk := k64_sound hpad h.right
      have hm : σ (.n b) = σ (sHis (w + 1)) * σ (sPower (7 - r)) :=
        h.left.atom (a := .mul (.n b) (sHis (w + 1)) (sPower (7 - r))) (by simp [mulS])
      have hc : σ (.n (b + 1)) = word (lxNodeConst w r + k / 2 ^ (r + 1)) 0 :=
        h.left.atom (a := .const (.n (b + 1)) _) (by simp [cst])
      have ha : σ (.n (b + 2)) = σ (.n b) + σ (.n (b + 1)) :=
        h.left.atom (a := .add (.n (b + 2)) (.n b) (.n (b + 1))) (by simp [addS])
      rw [show σ _ = _ from hk, ha, hm, hc]
      simp only [lxAtF, lxAt, hw, hr, ↓reduceIte, lxSibCell]
      by_cases hb : k / 2 ^ r % 2 = 0 <;> simp [hb]

theorem lxLevelT_next {w k r : Nat} {cur : V} {outO : Option Nat} {b : Nat} (hr : r + 1 ≠ 8) :
    (lxLevelT w k r cur outO b).2.1 = b + lxStride w := by
  unfold lxLevelT lxStride
  by_cases hw : w + 1 = 4 <;> simp [hw, hr]

theorem lxLevelT_last {w k : Nat} {cur : V} {outO : Option Nat} {b : Nat} :
    (lxLevelT w k 7 cur outO b).2.1 = b + lxLastNext w outO ∧
      (lxLevelT w k 7 cur outO b).2.2 = .n (outO.getD (b + (if w + 1 = 4 then 3 else 4))) := by
  unfold lxLevelT lxLastNext
  by_cases hw : w + 1 = 4 <;> cases outO <;> simp [hw]

/-! ## The levels of an arm -/

theorem lxLevelsT_atoms (w k : Nat) (outO : Option Nat) :
    ∀ m r cur b, atomsOnly (lxLevelsT w k outO m r cur b).1 = true
  | 0, _, _, _ => rfl
  | m + 1, r, cur, b => by
      simp only [lxLevelsT, atomsOnly_append, lxLevelT_atoms, lxLevelsT_atoms w k outO m, Bool.and_self]

/-- The levels of an arm: the last level's base and output. -/
theorem lxLevelsT_shape {w k : Nat} {outO : Option Nat} {b0 : Nat} :
    ∀ m r cur b, r + m = 8 → 0 < m → b = b0 + lxStride w * r →
      (lxLevelsT w k outO m r cur b).2.1 = b0 + lxStride w * 7 + lxLastNext w outO ∧
        (lxLevelsT w k outO m r cur b).2.2 =
          .n (outO.getD (b0 + lxStride w * 7 + (if w + 1 = 4 then 3 else 4)))
  | 0, _, _, _, _, h0, _ => absurd h0 (by omega)
  | m + 1, r, cur, b, hrm, _, hb => by
      simp only [lxLevelsT]
      by_cases hm : m = 0
      · subst hm
        have hr7 : r = 7 := by omega
        subst hr7
        obtain ⟨e1, e2⟩ := lxLevelT_last (w := w) (k := k) (cur := cur) (outO := outO) (b := b)
        simp only [lxLevelsT]
        exact ⟨by rw [e1, hb], by rw [e2, hb]⟩
      · have hr : r + 1 ≠ 8 := by omega
        exact lxLevelsT_shape m (r + 1) _ _ (by omega) (by omega)
          (by rw [lxLevelT_next hr, hb, lxStride]; split <;> ring)

/-- **The levels of an arm** are `mFold` over the levels' addresses, bits and siblings. -/
theorem lxLevelsT_sound (hpad : PadOK σ sLxPad) {w k : Nat} {outO : Option Nat} {b0 : Nat} :
    ∀ m r cur b, r + m = 8 → b = b0 + lxStride w * r →
      AtomsHold rd σ (lxLevelsT w k outO m r cur b).1 →
      σ (lxLevelsT w k outO m r cur b).2.2 = mFold (σ sLxPP) (lxAtF σ w k) (lxBitF k)
          (lxSibF σ w b0) m r (σ cur)
  | 0, _, _, _, _, _, _ => rfl
  | m + 1, r, cur, b, hrm, hb, h => by
      simp only [lxLevelsT] at h ⊢
      have hl := lxLevelT_sound hpad (w := w) (k := k) (r := r) (cur := cur) (outO := outO) (b := b) h.left
      by_cases hm : m = 0
      · subst hm
        simp only [lxLevelsT, mFold]
        rw [hl]
        simp only [lxSibF, hb]
      · have hr : r + 1 ≠ 8 := by omega
        have ih := lxLevelsT_sound hpad m (r + 1) (lxLevelT w k r cur outO b).2.2
          (lxLevelT w k r cur outO b).2.1 (by omega)
          (by rw [lxLevelT_next hr, hb, lxStride]; split <;> ring) h.right
        rw [ih, hl]
        simp only [mFold, lxSibF, hb]

/-! ## An arm and its pin -/

/-- **Arm `k`'s pin**: `his[w] = his[w + 1] · g^8 + k`, `his[3] = k` at the top. -/
def LxPin (σ : Val) (w k : Nat) : Prop :=
  σ (sHis w) = if w + 1 = 4 then eOfNat k else σ (sHis (w + 1)) * σ (sPower 8) + eOfNat k

theorem lxArmT_atoms (w k : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    atomsOnly (lxArmT w k cur outO b).1 = true := by
  unfold lxArmT
  split_ifs <;> simp [atomsOnly_append, lxLevelsT_atoms, atomsOnly, cst, mulS, addS]

theorem lxArmT_pin {w k : Nat} {cur : V} {outO : Option Nat} {b : Nat}
    (h : AtomsHold rd σ (lxArmT w k cur outO b).1) : LxPin σ w k := by
  unfold lxArmT at h
  unfold LxPin
  by_cases hw : w + 1 = 4
  · simp only [hw, ↓reduceIte] at h ⊢
    have e : σ (.n (67 + w)) = word k 0 := h.right.atom (a := .const (.n (67 + w)) _) (by simp [cst])
    rw [sHis, e, word_eq_eOfNat]
  · by_cases hk : k = 0
    · subst hk
      simp only [hw, ↓reduceIte] at h ⊢
      have e : σ (sHis w) = σ (sHis (w + 1)) * σ (sPower 8) :=
        h.right.atom (a := .mul (sHis w) (sHis (w + 1)) (sPower 8)) (by simp [mulS])
      rw [e, eOfNat_zero, add_zero]
    · simp only [hw, hk, ↓reduceIte] at h ⊢
      have e1 := h.right.atom (a := .mul (.n (lxLevelsT w k outO 8 0 cur b).2.1) (sHis (w + 1)) (sPower 8))
        (by simp [mulS])
      have e2 := h.right.atom (a := .const (.n ((lxLevelsT w k outO 8 0 cur b).2.1 + 1)) (word k 0))
        (by simp [cst])
      have e3 := h.right.atom (a := .add (sHis w) (.n (lxLevelsT w k outO 8 0 cur b).2.1)
        (.n ((lxLevelsT w k outO 8 0 cur b).2.1 + 1))) (by simp [addS])
      simp only [Atom.Holds] at e1 e2 e3
      rw [e3, e1, e2, word_eq_eOfNat]

/-- **An arm of a window**: its pin, and its output is the fold of its eight levels. -/
theorem lxArmT_sound (hpad : PadOK σ sLxPad) {w k : Nat} {cur : V} {outO : Option Nat} {b : Nat}
    (h : AtomsHold rd σ (lxArmT w k cur outO b).1) :
    LxPin σ w k ∧
      σ (.n (outO.getD (b + lxStride w * 7 + (if w + 1 = 4 then 3 else 4)))) =
        mFold (σ sLxPP) (lxAtF σ w k) (lxBitF k) (lxSibF σ w b) 8 0 (σ cur) := by
  refine ⟨lxArmT_pin h, ?_⟩
  have hl : AtomsHold rd σ (lxLevelsT w k outO 8 0 cur b).1 := by
    unfold lxArmT at h
    split_ifs at h
    all_goals exact h.left
  rw [← (lxLevelsT_shape (w := w) (k := k) (outO := outO) (b0 := b) 8 0 cur b rfl (by omega)
    (by simp)).2]
  exact lxLevelsT_sound hpad 8 0 cur b rfl (by simp) hl

theorem lxArmT_next (w k : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    (lxArmT w k cur outO b).2 = b + lxStride w * 7 + lxLastNext w outO +
      (if w + 1 = 4 then 0 else if k = 0 then 0 else 2) := by
  have e := (lxLevelsT_shape (w := w) (k := k) (outO := outO) (b0 := b) 8 0 cur b rfl (by omega)
    (by simp)).1
  unfold lxArmT
  by_cases hw : w + 1 = 4
  · simp [hw, e]
  · by_cases hk : k = 0
    · subst hk; simp [hw, e]
    · simp [hw, hk, e]


/-! ## A window -/

/-- The values of arm `k` of window `w`. -/
def lxArmSize (w k : Nat) : Nat :=
  lxStride w * 7 + lxLastNext w (if k = 0 then none else some 0) +
    (if w + 1 = 4 then 0 else if k = 0 then 0 else 2)

/-- The base of arm `k + j` of window `w`, arm `k` at `b`. -/
def lxArmB (w : Nat) : Nat → Nat → Nat → Nat
  | _, 0, b => b
  | k, j + 1, b => lxArmB w (k + 1) j (b + lxArmSize w k)

theorem lxArmT_next' (w k : Nat) (cur : V) (o b : Nat) :
    (lxArmT w k cur (if k = 0 then none else some o) b).2 = b + lxArmSize w k := by
  rw [lxArmT_next, lxArmSize]
  by_cases hk : k = 0 <;> simp [hk, lxLastNext, Nat.add_assoc]

theorem lxArmsT_length (w : Nat) (cur : V) (o : Nat) :
    ∀ m k b, (lxArmsT w cur o m k b).1.length = m
  | 0, _, _ => rfl
  | m + 1, k, b => by simp [lxArmsT, lxArmsT_length w cur o m]

theorem lxArmsT_getElem (w : Nat) (cur : V) (o : Nat) :
    ∀ m k b j (hj : j < (lxArmsT w cur o m k b).1.length),
      (lxArmsT w cur o m k b).1[j] =
        (lxArmT w (k + j) cur (if k + j = 0 then none else some o) (lxArmB w k j b)).1
  | 0, _, _, j, hj => absurd hj (by simp [lxArmsT])
  | m + 1, k, b, 0, _ => by simp [lxArmsT, lxArmB]
  | m + 1, k, b, j + 1, hj => by
      simp only [lxArmsT, List.getElem_cons_succ]
      rw [lxArmsT_getElem w cur o m (k + 1) _ j (by simp [lxArmsT, lxArmsT_length] at hj ⊢; omega),
        lxArmT_next']
      simp only [lxArmB, show k + 1 + j = k + (j + 1) by omega]

/-- **A window of the path, sound**: its dispatch takes an arm `k < 256` (its selector `g^k`), whose
pin holds and whose output is the fold of its eight levels. -/
theorem lxWindowT_sound (hpad : PadOK σ sLxPad) {w : Nat} {cur : V} {b : Nat} {rest : List Stmt}
    {next : Prop} (h : Stmt.HoldsList C rd σ ((lxWindowT w cur b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ ∃ k < 256, σ (sWin w) = ofK (addressOfIndex k) ∧
      LxPin σ w k ∧ σ (.n (lxWindowT w cur b).2.2) =
        mFold (σ sLxPP) (lxAtF σ w k) (lxBitF k) (lxSibF σ w (lxArmB w 0 k (b + 5))) 8 0 (σ cur) := by
  simp only [lxWindowT, rangeS, List.cons_append, List.nil_append, Stmt.HoldsList] at h
  have hm := h.2.2.2
  rw [holds_match_iff] at hm
  obtain ⟨j, hj, hx, ha⟩ := hm
  rw [lxArmsT_length] at hj
  rw [lxArmsT_getElem] at ha
  simp only [Nat.zero_add] at ha
  have ha' := (holdsList_noRet _ (noRetList_of_atomsOnly (lxArmT_atoms _ _ _ _ _)) _ _).mp ha
  obtain ⟨hpin, hout⟩ := lxArmT_sound hpad (atomsHold_of_holdsList (lxArmT_atoms _ _ _ _ _) ha'.1)
  refine ⟨ha'.2, j, hj, hx, hpin, ?_⟩
  rw [show (lxWindowT w cur b).2.2 = lxOut0 w (b + 5) from rfl, ← hout]
  congr 2
  by_cases h0 : j = 0
  · subst h0
    simp only [↓reduceIte, Option.getD_none, lxArmB, lxOut0, lxStride]
    split <;> omega
  · simp [h0]

end
end LeanVM.Guest.B1.Sig
