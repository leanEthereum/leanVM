/-
  LeanVM.Guest.B1.Place.OsSpec

  What `open_stacked` returns placed, and the bound of its callees.
-/

module

public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Whir.CompleteIface
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.Memory.SizeTotal

/-!
# `open_stacked`, placed: its returns and its callees' bound

`OsOut μ w`: the returns and returned buffers, the run's claim, the point zero-padded, one plus
each coordinate one-padded, the glued weight and the residual's value.

**The callees' bound** (`OsLeafBounds fs Bnd`): every callee of every arm (`osCalleeNames`) has
its trees within `Bnd` of its name on the arguments the arm passes it (`osArgsOk`: `level_positions`' squeezes and
`level_residual`'s batches, the exponents they read). `osBosAt fs Bnd μ`: the arm of `μ`'s bound (`osBos`), the largest over the rates (`osBos_le_osBosAt`).
`scripts/count/vsos.py` mirrors it.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL)

@[expose] public section

/-- What `open_stacked` returns: the claim, the two point buffers' pointers, the glued weight and
the residual's value; the buffers the point zero-padded and one plus it one-padded. -/
def OsOut (μ : ℕ) (w : WhirEnd) : List E → Layout → Prop := fun rets Lout ↦
  ∃ b b1 : ℕ, rets = [w.target, ofK (addressOfIndex b), ofK (addressOfIndex b1), w.inner,
      w.residual] ∧
    Lout = [(b, w.point ++ List.replicate (pointCap - μ) 0),
      (b1, w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)]

/-! ## The callees' bound -/

/-- The number of opening arms. -/
abbrev osArms : ℕ := openArms

/-- **The callees' words bounds**: every callee `f` of every arm has its trees within `Bnd f`
words, on the arguments the arm passes it (`osArgsOk`). -/
def OsLeafBounds (fs : String → ℕ) (Bnd : String → ℕ) : Prop :=
  ∀ m < osArms, ∀ f ∈ osCalleeNames (osCfg m), TotalLeOn coreProgram fs f (osArgsOk m f) (fun _ ↦ Bnd f)

/-- `open_stacked`'s frame-size bound at the arm of the stack log `μ`: the largest over the rates (the positions'
buffers are the rate's, `osPosTotal`). -/
def osBosAt (fs Bnd : String → ℕ) (μ : ℕ) : ℕ :=
  ((List.range ligNRates).map fun ri ↦ osBos fs Bnd (openName μ) (osCfgR (μ - minOpenLog) ri)).foldl max 0

/-- **Each rate's bound is within `osBosAt`.** -/
theorem osBos_le_osBosAt (fs Bnd : String → ℕ) (μ : ℕ) {ri : ℕ} (hri : ri < ligNRates) :
    osBos fs Bnd (openName μ) (osCfgR (μ - minOpenLog) ri) ≤ osBosAt fs Bnd μ := by
  unfold osBosAt
  exact le_foldl_max_map (fun ri ↦ osBos fs Bnd (openName μ) (osCfgR (μ - minOpenLog) ri)) (List.mem_range.mpr hri)

/-! ## The statements -/

end
end LeanVM.Guest.B1
