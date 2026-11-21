module

public import NativeVm.Code.Phase3.Common

/-!
# `accumulateSide` by its parts

A side's fold (`accumulateSide`) is `sideFold` over the table blocks' selectors and padding
weights, then the side's total from the framework selectors (`accumulateSide_split`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model LeanVM.Parameters

theorem zip_map_zip {α β γ : Type} (xs : Array α) (ys : Array β) (f : β → γ) :
    (xs.zip (ys.map f)).zip ys = (xs.zip ys).map fun p ↦ ((p.1, f p.2), p.2) := by
  apply Array.ext'
  simp only [Array.toList_zip, Array.toList_map]
  generalize xs.toList = l
  generalize ys.toList = m
  induction l generalizing m with
  | nil => simp
  | cons a l ih => cases m with
    | nil => simp
    | cons b m => simp [ih]

/-- **A side's fold by its parts.** -/
theorem accumulateSide_split (forms : Array (Array FormW)) (side : Nat) (blocks : Array BusBlockW)
    (L : BusLayoutW) (ffp ws : Array EW) (β : EW) (point : Array EW) (tv : EW) :
    accumulateSide forms side blocks L ffp ws β point tv =
      ((sideFold forms side blocks (L.tables.map (eqAbove · point)) (padWeights blocks point) ws β).1,
        tv + dot (L.framework.map (eqAbove · point)) (ffp.map (β + ·)) +
          (sumE (L.framework.map (eqAbove · point) ++ L.tables.map (eqAbove · point)) + 1) +
          (sideFold forms side blocks (L.tables.map (eqAbove · point))
            (padWeights blocks point) ws β).2) := by
  unfold accumulateSide sideFold padWeights
  rw [zip_map_zip, Array.foldl_map]

end NativeVm.Code.P3
