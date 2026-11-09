/-
  LeanVM.Guest.B1.VerifySub.C.Own

  `verify_sub`'s own buffers: its sixteen allocations, their sizes, and the words of those the
  honest run fixes by itself.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Flat
public import LeanVM.Guest.Hints
public import LeanVM.Guest.AcceptableChild

/-!
# The own buffers

`vs_allocs` (by the kernel): `verify_sub`'s thirteen allocations, in order, are `claim_pool`
(`6`, 167 words), `stream` (`25`, 8192), `table_rows` (`26`, 6), `dims_g` (`127`, 7),
`kappa_base` (`139`, 8), `zeta` (`310`, `g^μ` words: the one dynamic allocation, by the bus depth
`309`), `bus_alpha` (`346`, 4), `fp_w` (`427`, 16), `chi` (`635`, 34), `z_vals` (`647`, 78),
`slices` (`648`, 64), the ring map's challenges (`664`, 6) and `c_table` (`665`, 64). `vsSizes μ`:
their sizes, the bus depth `μ`.

Words fixed by the run alone (`vsStreamW`, `vsDimsW`, `vsKbW`): the stream padded to
`childStreamCap` (`Hints.childHints`' `"stream"`), the row counts, `dims_g` (`g^logMem`, then the
tables' heights as `count`, `Hints.childHints`' `"table_logs"`), `kappa_base`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The allocations' values, in order. -/
def vsAllocVars : List ℕ := [6, 25, 26, 127, 139, 310, 346, 427, 635, 647, 648, 664, 665]

/-- **The allocations, by the kernel**: their values and sizes (the dynamic one by `522`). -/
theorem vs_allocs : vsCPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz =
    (vsAllocVars.zip [.inl 167, .inl 8192, .inl 6, .inl 7, .inl 8, .inr (.n 309),
      .inl 4, .inl 16, .inl 34, .inl 78, .inl 64, .inl 6, .inl 64]).map
      (fun x ↦ (V.n x.1, x.2)) := by decide +kernel

/-- The own buffers' sizes, the bus depth `μ`. -/
def vsSizes (μ : ℕ) : List ℕ :=
  [167, 8192, 6, 7, 8, μ, 4, 16, 34, 78, 64, 6, 64]

/-- The stream buffer's words: the stream, padded to `childStreamCap` (`Hints.childHints`' `"stream"`). -/
def vsStreamW (stream : List E) : List E :=
  stream ++ List.replicate (Coverage.childStreamCap - stream.length) 0

/-- `dims_g`'s words: `g^logMem`, then the tables' heights as `count` (`"table_logs"`). -/
noncomputable def vsDimsW (logMem : ℕ) (heights : List ℕ) : List E :=
  gen ^ logMem :: heights.map Hints.count

/-- `kappa_base`'s words: `1`, `g^logMem`, the heights' powers. -/
noncomputable def vsKbW (logMem : ℕ) (heights : List ℕ) : List E :=
  1 :: gen ^ logMem :: heights.map Hints.count

end
end LeanVM.Guest.B1.VerifySub
