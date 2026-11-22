/-
  LeanVM.Guest.B1.Da.DvBound

  `da_verify`'s words bound on `r` blobs padded to `2^L`: its frame, its buffers and its callees'
  bounds, in call order, for the budget.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Main.IterK
public import LeanVM.Guest.Data.NameStrings

/-!
# `da_verify`'s words bound

`dvSizes r L`: `da_verify`'s `HeapBuf`, the roots (`4·2^L`). A static loop helper's run is charged
`iterK fs SK g` per iteration and its phantom frame `fs g` once. `padB`: `da_pad`'s
frame and its loop's (its frame alone when it does not run). `dvKBs`, `dvKB`: `da_verify`'s callees' bounds in call order, their
total. `dvB`: `da_verify`'s frame, its buffers and `dvKB`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.B1.Main (iterK)

@[expose] public section

/-- `da_verify`'s `HeapBuf` on `r` blobs padded to `2^L`: the roots. -/
def dvSizes (_r L : ℕ) : List ℕ := [4 * 2 ^ L]

/-- **`da_pad`'s words bound** at the gap `g`: its frame, its loop's `g` iterations and phantom
frame (its frame alone when it does not run). -/
def padB (fs SK : String → ℕ) (g : ℕ) : ℕ :=
  fs "da_pad" + (if g ≠ 0 then g * iterK fs SK name% «da_pad_loop0» + fs name% «da_pad_loop0» else
    fs name% «da_pad_loop0»)

/-- `da_verify`'s callees' bounds, in call order. -/
def dvKBs (fs SB SK : String → ℕ) (r L : ℕ) : List ℕ :=
  [fs "da_padding", SB "da_vector", SB "da_weights",
    r * iterK fs SK name% «da_verify_loop0» + fs name% «da_verify_loop0», padB fs SK (2 ^ L - r),
    SB (daLevelsName L)]

/-- **`da_verify`'s callees' words bound**: their total as `kidsBoundL` counts it. -/
def dvKB (fs SB SK : String → ℕ) (r L : ℕ) : ℕ :=
  fs "da_padding" + (SB "da_vector" + (SB "da_weights" +
    ((r * iterK fs SK name% «da_verify_loop0» + fs name% «da_verify_loop0») +
      (padB fs SK (2 ^ L - r) + SB (daLevelsName L)))))

/-- **`da_verify`'s words bound** on `r` blobs padded to `2^L`. -/
def dvB (fs SB SK : String → ℕ) (r L : ℕ) : ℕ :=
  fs "da_verify" + (dvSizes r L).sum + dvKB fs SB SK r L

end
end LeanVM.Guest.B1.Da
