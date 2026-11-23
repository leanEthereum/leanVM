module

public import NativeVm.Math.Tables.Model

/-!
# The tables' weights
-/

@[expose] public section

namespace NativeVm.Math.Tables

open NativeVm.Model LeanVM.Parameters

/-- Coordinate `c`'s factor of a table of log-height `h`, the point's entry `ch`. -/
def wtFac (eqp : Array EW) (h : Nat) (ch : EW) (c : Nat) : EW :=
  if c < h then 1 + eqp.getD c 0 + ch else ch

/-- A table's weight over the point's first `k` coordinates. -/
def wtPre (eqp point : Array EW) (h k : Nat) : EW :=
  ((point.toList.zipIdx).take k).foldl (fun acc p ↦ acc * wtFac eqp h p.1 p.2) 1

theorem wtPre_succ (eqp point : Array EW) (h : Nat) {k : Nat} (hk : k < point.size) :
    wtPre eqp point h (k + 1) = wtPre eqp point h k * wtFac eqp h point[k] k := by
  unfold wtPre
  rw [List.take_add_one, List.foldl_append]
  have : (point.toList.zipIdx)[k]? = some (point[k], k) := by
    rw [List.getElem?_zipIdx]; simp [hk]
  rw [this]
  rfl

theorem wtPre_zero (eqp point : Array EW) (h : Nat) : wtPre eqp point h 0 = 1 := rfl

theorem wt_foldl_weights (heights : Array Nat) (eqp : Array EW) (L : List (EW × Nat)) :
    ∀ (ws : Array EW), ws.size = heights.size →
      (L.foldl (fun weights (p : EW × Nat) ↦ Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights) ws).size
        = heights.size ∧
      ∀ i (h1 : i < (L.foldl (fun weights (p : EW × Nat) ↦ Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights) ws).size)
        (h2 : i < ws.size) (h3 : i < heights.size),
        (L.foldl (fun weights (p : EW × Nat) ↦ Array.zipWith (fun weight height ↦
          weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights) ws)[i]
          = L.foldl (fun acc p ↦ acc * wtFac eqp heights[i] p.1 p.2) ws[i] := by
  induction L with
  | nil => intro ws hs; exact ⟨hs, fun i _ _ _ ↦ rfl⟩
  | cons p L ih =>
    intro ws hs
    have hz : (Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) ws heights).size =
        heights.size := by simp [hs]
    obtain ⟨ih1, ih2⟩ := ih _ hz
    refine ⟨ih1, fun i h1 h2 h3 ↦ ?_⟩
    simp only [List.foldl_cons]
    refine (ih2 i h1 (by simp; omega) h3).trans ?_
    rw [Array.getElem_zipWith]
    rfl

theorem tableWeights_get (heights : Array Nat) (eqp point : Array EW) :
    (tableWeights heights eqp point).size = heights.size ∧
      ∀ i (h1 : i < (tableWeights heights eqp point).size) (h3 : i < heights.size),
        (tableWeights heights eqp point)[i] = wtPre eqp point heights[i] point.size := by
  have H := wt_foldl_weights heights eqp point.toList.zipIdx (heights.map fun _ ↦ 1) (by simp)
  have e : tableWeights heights eqp point = point.toList.zipIdx.foldl (fun weights (p : EW × Nat) ↦
      Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights)
      (heights.map fun _ ↦ 1) := by
    unfold tableWeights
    rw [← Array.foldl_toList, Array.toList_zipIdx]
  rw [e]
  refine ⟨H.1, fun i h1 h3 ↦ ?_⟩
  rw [H.2 i h1 (by simp; omega) h3]
  unfold wtPre
  rw [List.take_of_length_le (by simp)]
  simp

theorem tableWeights_size (heights : Array Nat) (eqp point : Array EW) :
    (tableWeights heights eqp point).size = heights.size :=
  (tableWeights_get heights eqp point).1

end NativeVm.Math.Tables
