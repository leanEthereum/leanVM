/-
  LeanVM.Guest.B1.Whir.CHonAlloc1

  The arms' buffer sizes at every rate, by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc

namespace LeanVM.Guest.B1.Whir

@[expose] public section

set_option maxRecDepth 100000 in
theorem bodySizes_all : ∀ m < 11, ∀ ri < 4, BodySizes (osCfgR m ri) := by decide +kernel

end
end LeanVM.Guest.B1.Whir
