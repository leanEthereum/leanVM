/-
  LeanVM.Guest.B1.Sig.SphincsDigestData

  `verify_sig_lean_sphincs` in the guest's core IR starts with the template `sDigestBlock`.
-/

module

public import LeanVM.Guest.Data.Core04
public import LeanVM.Guest.B1.Sig.SphincsDigestT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem sDigestBlock_length : sDigestBlock.length = 1358 := by decide +kernel

open scoped Dec in
theorem sDigestBlock_slice_0 : (Data.core20.body.drop 0).take 500 = (sDigestBlock.drop 0).take 500 := by
  decide +kernel

open scoped Dec in
theorem sDigestBlock_slice_500 :
    (Data.core20.body.drop 500).take 500 = (sDigestBlock.drop 500).take 500 := by
  decide +kernel

open scoped Dec in
theorem sDigestBlock_slice_1000 :
    (Data.core20.body.drop 1000).take 358 = (sDigestBlock.drop 1000).take 358 := by
  decide +kernel

/-- **`verify_sig_lean_sphincs`'s body starts with the digest block**, checked by the kernel in
slices of 500 statements. -/
theorem sDigestBlock_prefix : Data.core20.body.take 1358 = sDigestBlock := by
  have hs : ∀ l : List Stmt, l.take 1358 = (l.drop 0).take 500 ++ ((l.drop 500).take 500 ++
      (l.drop 1000).take 358) := by
    intro l
    rw [show 1358 = 500 + (500 + 358) from rfl, List.take_add, List.take_add]
    simp only [List.drop_drop, List.drop_zero]
  rw [hs, sDigestBlock_slice_0, sDigestBlock_slice_500, sDigestBlock_slice_1000,
    ← hs, List.take_of_length_le (le_of_eq sDigestBlock_length)]

end
end LeanVM.Guest.B1.Sig
