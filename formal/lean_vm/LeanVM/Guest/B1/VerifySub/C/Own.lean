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

`vs_allocs` (by the kernel): `verify_sub`'s fifteen allocations, in order, are `claim_pool`
(`6`, 159 words), `stream` (`25`, 8192), `table_rows` (`26`, 6), `dims_g` (`71`, 7), `kappa_base`
(`83`, 8), `zeta` (`254`, `g^d` words: the one dynamic allocation, by the bus depth `253`), `ood_z`
(`304`, 28), `ood_value` (`310`, 1), `fp_w` (`335`, 16), `chi` (`569`, 34), `bc_point` (`570`, 4),
`z_vals` (`584`, 78), `slices` (`585`, 64), the ring map's challenges (`847`, 16) and `c_table`
(`848`, 64). `vsSizes d`: their sizes, the bus depth `d`.

Words fixed by the run alone (`vsStreamW`, `vsDimsW`, `vsKbW`): the stream padded to
`childStreamCap` (`Hints.childHints`' `"stream"`), the row counts, `dims_g` (`g^logMem`, then the
tables' heights as `count`, `Hints.childHints`' `"table_logs"`), `kappa_base`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The allocations' values, in order. -/
def vsAllocVars : List ℕ := [6, 25, 26, 71, 83, 254, 304, 310, 335, 569, 570, 584, 585, 847, 848]

/-- **The allocations, by the kernel**: their values and sizes (the dynamic one by `253`). -/
theorem vs_allocs : vsCPre.filterMap LeanVM.Guest.Memory.Stmt.allocSz =
    (vsAllocVars.zip [.inl 159, .inl 8192, .inl 6, .inl 7, .inl 8, .inr (.n 253), .inl 28, .inl 1,
      .inl 16, .inl 34, .inl 4, .inl 78, .inl 64, .inl 16, .inl 64]).map
      (fun x ↦ (V.n x.1, x.2)) := by decide +kernel

/-- The own buffers' sizes, the bus depth `d`. -/
def vsSizes (d : ℕ) : List ℕ :=
  [159, 8192, 6, 7, 8, d, 28, 1, 16, 34, 4, 78, 64, 16, 64]

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
