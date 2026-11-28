/-
  LeanVM.Guest.EndExecAMain

  `main`'s frame in b2c's layout: `MainA` for every layout with b2c's frame sizes.
-/

module

public import LeanVM.Guest.EndExecA
public import LeanVM.Guest.B2C.Table
public import LeanVM.Guest.B2C.Frame
import all Statement.Data.AdviceHints

/-!
# `main`'s frame in the layout

`mainA_of : L.fs = B2C.fs → MainA L`: `main` is no loop helper (`B2C.main_not_loop`) and its frame
is the advice's `mainFrame`, `B2C.fs "main" = B2C.mainFrame` (`B2C.fs_main`), `433` cells and the
jump table's `15429` slots.
-/

namespace LeanVM.Guest.EndExec

public section

theorem mainFrame_eq : B2C.mainFrame = Data.adviceMainFrame := by
  unfold B2C.mainFrame
  decide +kernel

/-- **`main`'s frame in every layout with b2c's frame sizes.** -/
theorem mainA_of {L : Lay} (h : L.fs = B2C.fs) : MainA L :=
  ⟨B2C.main_not_loop, by rw [h, B2C.fs_main, mainFrame_eq]⟩

end

end LeanVM.Guest.EndExec
