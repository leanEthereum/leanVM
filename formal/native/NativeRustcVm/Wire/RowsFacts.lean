module

public import NativeRustcVm.Wire.Rep

/-!
# `rdRows` row by row

The rows read one more at a time (`rdRows_succ`), a row that cannot be read failing every longer
read (`rdRows_none`); a padded leaf's words (`map_lane_paddedLeaf`).
-/

namespace NativeRustcVm.Wire

open NativeVm NativeVm.Wire LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

theorem rdRows_add (B : List UInt8) (w : Nat) : ∀ (a b c : Nat),
    rdRows B w (a + b) c = (rdRows B w a c).bind fun p ↦
      (rdRows B w b p.2).bind fun q ↦ some (p.1 ++ q.1, q.2)
  | 0, b, c => by simp [rdRows]
  | a + 1, b, c => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [rdRows, Option.bind_eq_bind]
    cases rdWords B w c with
    | none => rfl
    | some p =>
      simp only [Option.bind_some, rdRows_add B w a b p.2]
      cases rdRows B w a p.2 with
      | none => rfl
      | some q =>
        simp only [Option.bind_some]
        cases rdRows B w b q.2 <;> simp

/-- **One more row.** -/
theorem rdRows_succ {B : List UInt8} {w i c c1 : Nat} {rs : List (List K)}
    (h : rdRows B w i c = some (rs, c1)) :
    rdRows B w (i + 1) c = (rdWords B w c1).map fun p ↦ (rs ++ [p.1], p.2) := by
  rw [rdRows_add, h]
  simp only [Option.bind_some, rdRows, Option.bind_eq_bind]
  cases rdWords B w c1 <;> simp

/-- **A row that cannot be read** fails every read past it. -/
theorem rdRows_none {B : List UInt8} {w i n c c1 : Nat} {rs : List (List K)}
    (h : rdRows B w i c = some (rs, c1)) (hw : rdWords B w c1 = none) (hi : i < n) :
    rdRows B w n c = none := by
  rw [show n = (i + 1) + (n - i - 1) by omega, rdRows_add, rdRows_succ h, hw]
  rfl

theorem rdWords_length {B : List UInt8} {n c c' : Nat} {ws : List K}
    (h : rdWords B n c = some (ws, c')) : ws.length = n := by
  unfold rdWords at h
  split at h
  · cases h; simp
  · cases h

theorem lane_zero : (0 : K).lane = 0 := rfl

/-- A padded leaf's words: zeros, then the row's. -/
theorem map_lane_paddedLeaf (row : List K) (lw : Nat) :
    (paddedLeaf row lw).map K.lane = List.replicate (lw - row.length) 0 ++ row.map K.lane := by
  simp [paddedLeaf, List.map_replicate, lane_zero]

end

end NativeRustcVm.Wire
