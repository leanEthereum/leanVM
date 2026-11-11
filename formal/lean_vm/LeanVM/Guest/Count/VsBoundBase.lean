/-
  LeanVM.Guest.Count.VsBoundBase

  `open_stacked`'s bound per arm with its name spelled by `natStr` (`osC`), so that the kernel
  evaluates it (`openNames` spells the names by `toString`, whose body the kernel cannot see), and
  by the search tree's lookups (`osCF`); `osC m = osCF m` (`osC_eq_fast`), and `osBosAt` at the
  deployed frame sizes is `osC` (`osBosAt_eq`).
-/

module

public import LeanVM.Guest.Count.VsOsDefs
public import LeanVM.Guest.B1.Whir.Names

namespace LeanVM.Guest.Count

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

/-- `open_stacked`'s words at the arm `m`, its name spelled by `natStr`. -/
noncomputable def osC (m : ℕ) : ℕ :=
  B1.osBos B2C.fs wSB ("open_stacked__L" ++ natStr m) (osCfg m)

theorem osC_eq_fast (m : ℕ) : osC m = osCF m := by
  unfold osC osCF
  rw [fsFast_eq, wSBFast_eq]

/-- `osBosAt` at an arm is `osC`. -/
theorem osBosAt_eq {μ : ℕ} (h1 : minOpenLog ≤ μ) (h2 : μ ≤ 30) :
    B1.osBosAt B2C.fs wSB μ = osC (μ - minOpenLog) := by
  have h : μ - minOpenLog < 11 := by simp only [minOpenLog] at h1 h2 ⊢; omega
  unfold B1.osBosAt osC openName openNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
    Option.getD_some, natStr_eq]

end
end LeanVM.Guest.Count
