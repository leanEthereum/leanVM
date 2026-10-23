/-
  LeanVM.Protocol.LeanIsa.Read

  Reading the leanISA stack: a committed column's cells at its block's offset, a `BLAKE2S` limb's
  cells at its strided slot of the Flock region, and the Flock region's blocks.
-/

module

public import LeanVM.Protocol.LeanIsa

/-!
# Reading the leanISA stack

The leanISA instance reads every column off the one stack `q` through its layout. Cell `x` of a
committed column `c` is the stack's cell `x + offset`, at the offset of `c`'s block
(`column_committed`); cell `x` of limb `k` of the `BLAKE2S` table is the stack's cell
`slot k + 256 · x` past the Flock region's offset (`column_limb`), which is cell `slot k` of block
`x` of the Flock region (`slotLimbs_flockColumn`): the limbs of row `x` are the limbs the region's
block `x` carries at the specification's slots.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CMlPolynomialEval

@[expose] public section

variable (F : FlockSpec) (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- A column's cell is the stack's cell at the lifted cube point. -/
private theorem column_get (c : Col) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance F prog s).column q c).values.get x =
      q.values.get (boolIndex ((layout prog s F.slot).extend c (boolVec x))) := by
  simp only [M3Instance.column, Layout.read, Layout.readWith]
  exact Vector.get_ofFn _ _

/-- Through a route to a block, a cell is the stack's cell at the block's offset. -/
private theorem get_inl (slot : Fin 18 → Fin 256) (c : Col) (x : Fin (2 ^ kappa prog s c))
    (b : Fin (blocks prog s).n) (hb : (blocks prog s).size b = kappa prog s c) :
    ∀ (r : Fin (blocks prog s).n ⊕ Fin 18)
      (e : Sum.elim (blocks prog s).size (fun _ ↦ s.τ 5) r = kappa prog s c), r = .inl b →
      q.values.get (boolIndex ((((blocks prog s).layout (blocks_fits prog s)).piecewise
        ((blocks prog s).stridedLayout (blocks_fits prog s) (flockBlock prog s) 8 slot
          (κ := fun _ ↦ s.τ 5) fun _ ↦ size_flockBlock prog s)).extend r
            (Vector.cast e.symm (boolVec x)))) =
        q.values[x.val + (blocks prog s).offset b]'(by
          have := (blocks prog s).offset_add_pow_le_total b
          have := blocks_fits prog s
          have h1 := x.isLt
          have h2 : 2 ^ kappa prog s c = 2 ^ (blocks prog s).size b := by rw [hb]
          omega) := by
  rintro r e rfl
  simp only [Layout.piecewise, boolVec_cast]
  exact (blocks prog s).get_extendPoint (blocks_fits prog s) q b (Fin.cast (by rw [hb]) x)

/-- Through a route to a slot, a cell is the stack's cell at the slot of the Flock region. -/
private theorem get_inr (slot : Fin 18 → Fin 256) (c : Col) (x : Fin (2 ^ kappa prog s c))
    (k : Fin 18) (hk : s.τ 5 = kappa prog s c) :
    ∀ (r : Fin (blocks prog s).n ⊕ Fin 18)
      (e : Sum.elim (blocks prog s).size (fun _ ↦ s.τ 5) r = kappa prog s c), r = .inr k →
      q.values.get (boolIndex ((((blocks prog s).layout (blocks_fits prog s)).piecewise
        ((blocks prog s).stridedLayout (blocks_fits prog s) (flockBlock prog s) 8 slot
          (κ := fun _ ↦ s.τ 5) fun _ ↦ size_flockBlock prog s)).extend r
            (Vector.cast e.symm (boolVec x)))) =
        q.values[(cubeIndex (k := 8) (slot k) (Fin.cast (congrArg (2 ^ ·) hk.symm) x)).val +
          (blocks prog s).offset (flockBlock prog s)]'(by
          have := (blocks prog s).offset_add_pow_le_total (flockBlock prog s)
          have := blocks_fits prog s
          have h1 := (cubeIndex (k := 8) (slot k) (Fin.cast (congrArg (2 ^ ·) hk.symm) x)).isLt
          have h2 : 2 ^ (8 + s.τ 5) = 2 ^ (blocks prog s).size (flockBlock prog s) := by
            rw [size_flockBlock]
          omega) := by
  rintro r e rfl
  simp only [Layout.piecewise, boolVec_cast]
  exact (blocks prog s).get_stridedLayout (blocks_fits prog s) (flockBlock prog s) 8 slot
    (κ := fun _ ↦ s.τ 5) (fun _ ↦ size_flockBlock prog s) q k (Fin.cast (by rw [hk]) x)

/-- Cell `x` of a committed column is the stack's cell `x` past its block's offset. -/
theorem column_committed (c : Col) (h : ¬ IsLimb c) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance F prog s).column q c).values.get x =
      q.values[x.val + (blocks prog s).offset (blockOf c h)]'(by
        have := (blocks prog s).offset_add_pow_le_total (blockOf c h)
        have := blocks_fits prog s
        have h1 := x.isLt
        have h2 : 2 ^ kappa prog s c = 2 ^ (blocks prog s).size (blockOf c h) := by
          rw [size_blockOf]
        omega) := by
  refine (column_get F prog s q c x).trans ?_
  exact get_inl prog s q F.slot c x (blockOf c h) (size_blockOf prog s c h) (route prog s c)
    (route_kappa prog s c) (by simp [route, h])

/-- Limb `k` of the `BLAKE2S` table reads the stack at the strided slot `F.slot k` of the Flock
region: its cell `x` is the region's cell `slot k + 256 · x`. -/
theorem column_limb (k : Fin 18) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance F prog s).column q (limbCol k)).values.get x =
      q.values[(cubeIndex (k := 8) (F.slot k) x).val + (blocks prog s).offset (flockBlock prog
          s)]'(by
        have := (blocks prog s).offset_add_pow_le_total (flockBlock prog s)
        have := blocks_fits prog s
        have h1 := (cubeIndex (k := 8) (F.slot k) x).isLt
        have h2 : 2 ^ (8 + s.τ 5) = 2 ^ (blocks prog s).size (flockBlock prog s) := by
          rw [size_flockBlock]
        omega) := by
  refine (column_get F prog s q (limbCol k) x).trans ?_
  have hl : IsLimb (limbCol k) := ⟨rfl, by simp [limbCol], by simp [limbCol]; omega⟩
  refine (get_inr prog s q F.slot (limbCol k) x k rfl (route prog s (limbCol k))
    (route_kappa prog s (limbCol k)) ?_).trans rfl
  simp only [route, hl, dite_true, Sum.inr.injEq]
  ext
  simp [limbCol]

/-- The limbs of row `x` of the `BLAKE2S` table are the limbs block `x` of the Flock region
carries at the specification's slots. -/
theorem slotLimbs_flockColumn (x : Fin (2 ^ s.τ 5)) :
    slotLimbs F.slot ((leanIsaInstance F prog s).flockColumn (flockRegion prog s F) q) x =
      fun k ↦ ((leanIsaInstance F prog s).column q (limbCol k)).values.get x := by
  funext k
  refine Eq.trans ?_ (column_limb F prog s q k x).symm
  have h := column_committed F prog s q flockCol not_isLimb_flockCol (cubeIndex (F.slot k) x)
  exact h

end

end LeanVM.Protocol.LeanIsa
