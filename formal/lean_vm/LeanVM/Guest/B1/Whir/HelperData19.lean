/-
  LeanVM.Guest.B1.Whir.HelperData19

  Specializations of `open_stacked`'s helpers are their templates, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Whir.DataSpec

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

set_option maxRecDepth 100000 in
/-- `residual_batch__L24`. -/
theorem rb_1785 : FnIs "residual_batch__L24" (osParams 4) (rbBody 24) :=
  ⟨Data.core1785, Program.find?_of_indexOf? (j := 1785) (by decide +kernel) rfl, by decide +kernel,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
/-- `residual_batch__L25`. -/
theorem rb_1792 : FnIs "residual_batch__L25" (osParams 4) (rbBody 25) :=
  ⟨Data.core1792, Program.find?_of_indexOf? (j := 1792) (by decide +kernel) rfl, by decide +kernel,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
/-- `residual_batch__L26`. -/
theorem rb_1797 : FnIs "residual_batch__L26" (osParams 4) (rbBody 26) :=
  ⟨Data.core1797, Program.find?_of_indexOf? (j := 1797) (by decide +kernel) rfl, by decide +kernel,
    stmtsEqb_sound (by decide +kernel)⟩

end
end LeanVM.Guest.B1.Whir
