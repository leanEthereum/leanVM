/-
  LeanVM.Guest.B1.Da.DvBound

  `da_verify`'s words bound on `r` blobs padded to `2^L` (G:4323-4392): its frame, its buffers and
  its callees' bounds, in call order, for the budget.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Main.IterK

/-!
# `da_verify`'s words bound

`dvSizes r L`: `da_verify`'s `HeapBuf`s, the blobs' regions (`641` words a blob: its tree's `512`
and its running sum's `129`), their bases (`r`) and the roots (`4·2^L`). `colB fs SB SK r`: a
column's words, its frame, its weights' expansion (`da_expand__L7_L8`) and its row loop's `r`
iterations (`__loop25`). A static loop helper's run is charged `iterK fs SK g` per iteration and
its phantom frame `fs g` once. `clB fs f Bc t`: a column loop's `t` iterations, each its frame and its
column's `Bc`, and the last's untaken tail call's frame. `dvKBs`, `dvKB`: `da_verify`'s callees'
bounds in call order, their total (`__loop24`'s frame alone when it does not run). `dvB`: `da_verify`'s
frame, its buffers and `dvKB`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.B1.Main (iterK)

@[expose] public section

/-- `da_verify`'s `HeapBuf`s on `r` blobs padded to `2^L`: the regions, their bases, the roots. -/
def dvSizes (r L : ℕ) : List ℕ := [641 * r, r, 4 * 2 ^ L]

/-- **A column's words bound** on `r` blobs: its frame, its weights' expansion and its row
loop's `r` iterations and phantom frame. -/
def colB (fs : String → ℕ) (SB SK : String → ℕ) (r : ℕ) : ℕ :=
  fs "da_verify_column" + SB "da_expand__L7_L8" + (r * iterK fs SK "__loop25" + fs "__loop25")

/-- **A column loop's words bound** for `t` iterations: each its frame and its column's `Bc`,
and the last's untaken tail call's frame. -/
def clB (fs : String → ℕ) (f : String) (Bc t : ℕ) : ℕ := t * (fs f + Bc) + fs f

/-- `da_verify`'s callees' bounds, in call order. -/
def dvKBs (fs : String → ℕ) (SB SK : String → ℕ) (r L : ℕ) : List ℕ :=
  [fs "da_row_shape", SB "da_vector", r * iterK fs SK "__loop21" + fs "__loop21",
    clB fs "__loop22" (colB fs SB SK r) 128, r * iterK fs SK "__loop23" + fs "__loop23",
    (2 ^ L - r) * iterK fs SK "__loop24" + fs "__loop24", SB dlNames[L]!]

/-- **`da_verify`'s callees' words bound**: their total as `kidsBoundL` counts it (`__loop24`'s
frame when it does not run). -/
def dvKB (fs : String → ℕ) (SB SK : String → ℕ) (r L : ℕ) : ℕ :=
  fs "da_row_shape" + (SB "da_vector" + ((r * iterK fs SK "__loop21" + fs "__loop21") +
    (clB fs "__loop22" (colB fs SB SK r) 128 + ((r * iterK fs SK "__loop23" + fs "__loop23") +
    ((if 2 ^ L - r ≠ 0 then (2 ^ L - r) * iterK fs SK "__loop24" + fs "__loop24" else fs "__loop24") +
      SB dlNames[L]!)))))

/-- **`da_verify`'s words bound** on `r` blobs padded to `2^L`. -/
def dvB (fs : String → ℕ) (SB SK : String → ℕ) (r L : ℕ) : ℕ :=
  fs "da_verify" + (dvSizes r L).sum + dvKB fs SB SK r L

end
end LeanVM.Guest.B1.Da
