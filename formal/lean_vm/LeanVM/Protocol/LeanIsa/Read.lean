/-
  LeanVM.Protocol.LeanIsa.Read

  Reading the leanISA stack: a committed column's cells at its block's offset, a `KECCAK` input
  lane's or spare column's cells at its slot of `QKECCAK`, an output lane's as the permutation of
  the input lanes.
-/

module

public import LeanVM.Protocol.LeanIsa

/-!
# Reading the leanISA stack

The leanISA instance reads every column off the one stack `q`. Cell `x` of a committed column `c`
is the stack's cell `x + offset`, at the offset of `c`'s block (`column_committed`). Cell `x` of
input lane `l` of the `KECCAK` table is the stack's cell `x + l · 2^τ` past `QKECCAK`'s offset,
which is word `x` of slot `l` of the Keccak region (`column_inCol`); cell `x` of a column riding
a spare slot is word `x` of its slot `50 … 63` (`column_spare`). Cell `x` of output lane `l`
is lane `l` of Keccak-f[1600] of the state the region's slots `0 … 24` hold at step `x`
(`column_outCol`): the derived column, read through the same slices.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CMlPolynomialEval

@[expose] public section

variable (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- An output lane is a lane. -/
theorem IsOut.isLane {c : Col} (h : IsOut c) : IsLane c := ⟨h.1, by have := h.2.1; omega, h.2.2⟩

/-- An output lane is virtual. -/
theorem IsOut.isVirtual {c : Col} (h : IsOut c) : IsVirtual c := h.isLane.isVirtual

/-- A spare column is not an output lane. -/
theorem IsSpare.not_isOut {c : Col} (h : IsSpare c) : ¬ IsOut c := fun ho ↦ by
  have := ho.2.1; have := h.2; omega

/-- Only the output lanes are derived. -/
theorem derived_eq_none {c : Col} (h : ¬ IsOut c) : derived prog s c = none := by
  simp [derived, h]

/-- A column that is not derived is read off the stack through the layout. -/
theorem column_of_not_isOut {c : Col} (h : ¬ IsOut c) :
    (leanIsaInstance prog s).column q c = (leanIsaInstance prog s).layout.read q c := by
  unfold M3Instance.column
  rw [show (leanIsaInstance prog s).derived c = none from derived_eq_none prog s h]
  rfl

/-- A column that is not derived is read off the stack: its cell is the stack's cell at the
lifted cube point. -/
private theorem column_get (c : Col) (h : ¬ IsOut c) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance prog s).column q c).values.get x =
      q.values.get (boolIndex ((layout prog s).extend c (boolVec x))) := by
  unfold M3Instance.column
  rw [show (leanIsaInstance prog s).derived c = none from derived_eq_none prog s h]
  simp only [Option.elim, Layout.read, Layout.readWith]
  exact Vector.get_ofFn _ _

/-- The pieces of the layout, before the renaming. -/
private abbrev pieces :
    Layout (leanIsaμ prog s) (Fin (blocks prog s).n ⊕ Fin 64)
      (Sum.elim (blocks prog s).size fun _ ↦ s.τ 5) :=
  ((blocks prog s).layout (blocks_fits prog s)).piecewise
    ((blocks prog s).sliceLayout (blocks_fits prog s) (keccakBlock prog s) 6
      (fun l : Fin 64 ↦ (⟨l, by omega⟩ : Fin (2 ^ 6)))
      (κ := fun _ ↦ s.τ 5) fun _ ↦ size_keccakBlock prog s)

/-- Through a route to a block, a cell is the stack's cell at the block's offset. -/
private theorem get_inl (c : Col) (x : Fin (2 ^ kappa prog s c))
    (b : Fin (blocks prog s).n) (hb : (blocks prog s).size b = kappa prog s c) :
    ∀ (r : Fin (blocks prog s).n ⊕ Fin 64)
      (e : Sum.elim (blocks prog s).size (fun _ ↦ s.τ 5) r = kappa prog s c), r = .inl b →
      q.values.get (boolIndex ((pieces prog s).extend r (Vector.cast e.symm (boolVec x)))) =
        q.values[x.val + (blocks prog s).offset b]'(by
          have := (blocks prog s).offset_add_pow_le_total b
          have := blocks_fits prog s
          have h1 := x.isLt
          have h2 : 2 ^ kappa prog s c = 2 ^ (blocks prog s).size b := by rw [hb]
          omega) := by
  rintro r e rfl
  simp only [pieces, Layout.piecewise, boolVec_cast]
  exact (blocks prog s).get_extendPoint (blocks_fits prog s) q b (Fin.cast (by rw [hb]) x)

/-- Through a route to a slot, a cell is the stack's cell at the slot of `QKECCAK`. -/
private theorem get_inr (c : Col) (x : Fin (2 ^ kappa prog s c))
    (k : Fin 64) (hk : s.τ 5 = kappa prog s c) :
    ∀ (r : Fin (blocks prog s).n ⊕ Fin 64)
      (e : Sum.elim (blocks prog s).size (fun _ ↦ s.τ 5) r = kappa prog s c), r = .inr k →
      q.values.get (boolIndex ((pieces prog s).extend r (Vector.cast e.symm (boolVec x)))) =
        q.values[x.val + 2 ^ s.τ 5 * k.val + (blocks prog s).offset (keccakBlock prog s)]'(by
          have := (blocks prog s).offset_add_pow_le_total (keccakBlock prog s)
          have := blocks_fits prog s
          have h1 := (cubeIndex (k := s.τ 5) (m := 6) (Fin.cast (congrArg (2 ^ ·) hk.symm) x)
            ⟨k, by omega⟩).isLt
          have h2 : 2 ^ (s.τ 5 + 6) = 2 ^ (blocks prog s).size (keccakBlock prog s) := by
            rw [size_keccakBlock]
          simp only [cubeIndex, Fin.val_cast] at h1
          omega) := by
  rintro r e rfl
  simp only [pieces, Layout.piecewise, boolVec_cast]
  exact (blocks prog s).get_sliceLayout (blocks_fits prog s) (keccakBlock prog s) 6
    (fun l : Fin 64 ↦ (⟨l, by omega⟩ : Fin (2 ^ 6)))
    (κ := fun _ ↦ s.τ 5) (fun _ ↦ size_keccakBlock prog s) q k (Fin.cast (by rw [hk]) x)

/-- Cell `x` of a committed column is the stack's cell `x` past its block's offset. -/
theorem column_committed (c : Col) (h : ¬ IsVirtual c) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance prog s).column q c).values.get x =
      q.values[x.val + (blocks prog s).offset (blockOf c h)]'(by
        have := (blocks prog s).offset_add_pow_le_total (blockOf c h)
        have := blocks_fits prog s
        have h1 := x.isLt
        have h2 : 2 ^ kappa prog s c = 2 ^ (blocks prog s).size (blockOf c h) := by
          rw [size_blockOf]
        omega) := by
  refine (column_get prog s q c (fun ho ↦ h ho.isVirtual) x).trans ?_
  exact get_inl prog s q c x (blockOf c h) (size_blockOf prog s c h) (route prog s c)
    (route_kappa prog s c) (by simp [route, h])

/-- Input lane `l` of the `KECCAK` table reads the stack at slot `l` of `QKECCAK`: its cell `x`
is the region's cell `x + l · 2 ^ τ`. -/
theorem column_inCol_stack (l : Fin 25) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance prog s).column q (inCol l)).values.get x =
      q.values[x.val + 2 ^ s.τ 5 * l.val + (blocks prog s).offset (keccakBlock prog s)]'(by
        have := (blocks prog s).offset_add_pow_le_total (keccakBlock prog s)
        have := blocks_fits prog s
        have h1 := (cubeIndex (k := s.τ 5) (m := 6) x ⟨l, by omega⟩).isLt
        have h2 : 2 ^ (s.τ 5 + 6) = 2 ^ (blocks prog s).size (keccakBlock prog s) := by
          rw [size_keccakBlock]
        simp only [cubeIndex] at h1
        omega) := by
  have hl : IsVirtual (inCol l) := ⟨rfl, by simp [inCol]; omega⟩
  have ho : ¬ IsOut (inCol l) := fun h ↦ by have := h.2.1; simp [inCol] at this; omega
  refine (column_get prog s q (inCol l) ho x).trans ?_
  refine (get_inr prog s q (inCol l) x ⟨l, by omega⟩ rfl (route prog s (inCol l))
    (route_kappa prog s (inCol l)) ?_).trans rfl
  simp only [route, hl, dite_true, qSlot_inCol]

/-- Word `x` of slot `slot < 64` is a cell of `QKECCAK`. -/
theorem slot_lt {n : ℕ} (x : Fin (2 ^ n)) (slot : ℕ) (hslot : slot < 64) :
    x.val + 2 ^ n * slot < 2 ^ (n + 6) :=
  (cubeIndex (k := n) (m := 6) x ⟨slot, hslot⟩).isLt

/-- Word `x` of slot `slot < 64` of the Keccak region is cell `x + slot · 2 ^ τ` of `QKECCAK`. -/
theorem word_eq_column (slot : ℕ) (hslot : slot < 64) (x : Fin (2 ^ s.τ 5)) :
    (keccakRegion prog s).word
        ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) q) slot x =
      ((leanIsaInstance prog s).column q keccakCol).values.get
        ⟨x.val + 2 ^ s.τ 5 * slot, slot_lt x slot hslot⟩ := by
  have hlt : x.val + 2 ^ s.τ 5 * slot < 2 ^ (s.τ 5 + 6) := slot_lt x slot hslot
  show ((leanIsaInstance prog s).column q keccakCol).values.toArray.getD
    (x.val + 2 ^ s.τ 5 * slot) 0 = _
  rw [Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by rw [Vector.size_toArray]; exact hlt), Option.getD_some]
  rfl

/-- Word `x` of slot `slot < 64` of the Keccak region is the stack's cell `x + slot · 2 ^ τ`
past `QKECCAK`'s offset. -/
theorem word_keccakColumn (slot : ℕ) (hslot : slot < 64) (x : Fin (2 ^ s.τ 5)) :
    (keccakRegion prog s).word
        ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) q) slot x =
      q.values[x.val + 2 ^ s.τ 5 * slot + (blocks prog s).offset (keccakBlock prog s)]'(by
        have := (blocks prog s).offset_add_pow_le_total (keccakBlock prog s)
        have := blocks_fits prog s
        have h1 := (cubeIndex (k := s.τ 5) (m := 6) x ⟨slot, hslot⟩).isLt
        have h2 : 2 ^ (s.τ 5 + 6) = 2 ^ (blocks prog s).size (keccakBlock prog s) := by
          rw [size_keccakBlock]
        simp only [cubeIndex] at h1
        omega) := by
  have hlt : x.val + 2 ^ s.τ 5 * slot < 2 ^ (s.τ 5 + 6) := slot_lt x slot hslot
  exact (word_eq_column prog s q slot hslot x).trans
    (column_committed prog s q keccakCol not_isVirtual_keccakCol ⟨_, hlt⟩)

/-- **The input lanes are the region's input slots**: cell `x` of input lane `l` is word `x`
of slot `l` of the Keccak region. -/
theorem column_inCol (l : Fin 25) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance prog s).column q (inCol l)).values.get x =
      (keccakRegion prog s).word
        ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) q) l x := by
  rw [column_inCol_stack, word_keccakColumn prog s q l (by omega)]

/-- **The spare columns are the region's spare slots**: cell `x` of a column riding a spare slot
of `QKECCAK` (`IsSpare`) is word `x` of its slot `qSlot c`, one of `50 … 63`. -/
theorem column_spare (c : Col) (h : IsSpare c) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance prog s).column q c).values.get
        (Fin.cast (congrArg (2 ^ ·) (kappa_of_isVirtual prog s h.isVirtual).symm) x) =
      (keccakRegion prog s).word
        ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) q) (qSlot c) x := by
  have hk := (kappa_of_isVirtual prog s h.isVirtual).symm
  refine (column_get prog s q c h.not_isOut _).trans ?_
  refine (get_inr prog s q c _ (qSlot c) hk (route prog s c) (route_kappa prog s c)
    (by simp [route, h.isVirtual])).trans ?_
  rw [word_keccakColumn prog s q (qSlot c) (qSlot c).isLt x]
  rfl

/-- The region's column is `QKECCAK` read off the stack. -/
theorem keccakColumn_eq :
    (leanIsaInstance prog s).keccakColumn (keccakRegion prog s) q =
      ((layout prog s).read q keccakCol : Column (s.τ 5 + 6)) := by
  unfold M3Instance.keccakColumn
  rw [column_of_not_isOut prog s q (c := (keccakRegion prog s).col)
    (fun h ↦ not_isVirtual_keccakCol h.isVirtual)]
  rfl

/-- **The output lanes are the second segment of the committed middle state**: cell `x` of
output lane `l` is lane `l` of the last twelve rounds of Keccak-f[1600] of the state the region's
slots `25 … 49` hold at step `x`. -/
theorem column_outCol (l : Fin 25) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance prog s).column q (outCol l)).values.get x =
      stateLanes (keccakSegment 1 ((keccakRegion prog s).state
        ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) q) 25 x)) l := by
  have ho : IsOut (outCol l) := ⟨rfl, by simp [outCol], by simp [outCol]; omega⟩
  have hd : (leanIsaInstance prog s).derived (outCol l) =
      some fun q ↦ outColumn prog s q (outCol l) ho := by
    show derived prog s (outCol l) = _
    unfold derived
    rw [dite_eq_left ho]
  unfold M3Instance.column
  rw [hd]
  show (outColumn prog s q (outCol l) ho).values.get x = _
  simp only [outColumn]
  refine (Vector.get_ofFn _ _).trans ?_
  have hl : (⟨(outCol l).2.val - 40, by have := ho.2.2; omega⟩ : Fin 25) = l := by
    ext
    simp [outCol]
  rw [hl, keccakColumn_eq]
  rfl

/-- **With the Keccak predicate, the output lanes are the permutation of the input slots**: cell
`x` of output lane `l` is lane `l` of Keccak-f[1600] of the state the region's slots `0 … 24`
hold at step `x`. -/
theorem column_outCol_of_aux (h : (leanIsaInstance prog s).aux q) (l : Fin 25)
    (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance prog s).column q (outCol l)).values.get x =
      stateLanes (keccakF1600 ((keccakRegion prog s).state
        ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) q) 0 x)) l := by
  rw [column_outCol, h (keccakRegion prog s) rfl x, keccakF_eq_segments]

end

end LeanVM.Protocol.LeanIsa
