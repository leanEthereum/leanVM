/-
  LeanVM.Guest.B1.Sig.SphincsDigestData

  `verify_sig_lean_sphincs` in the guest's core IR starts with the template `sDigestBlock`.
-/

module

public import LeanVM.Guest.Pack.verify_sig_lean_sphincs.Core
public import LeanVM.Guest.B1.Sig.SphincsDigestT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sig_lean_sphincs»

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem sDigestBlock_length : sDigestBlock.length = 1358 := by decide +kernel

set_option maxRecDepth 100000 in
theorem sDigestBlock_slice_0 : ((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s0#0")).take (pos% «verify_sig_lean_sphincs» "s18.u6.s0.i0:sp_fors_field.s1.u9.s0#2") =
    (sDigestBlock.drop 0).take 500 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sDigestBlock_slice_500 :
    ((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s18.u6.s0.i0:sp_fors_field.s1.u9.s0#2")).take (span% «verify_sig_lean_sphincs» "s18.u6.s0.i0:sp_fors_field.s1.u9.s0#2" "s20.i0:sp_leaf_shifts.s1.u2.s0#2") = (sDigestBlock.drop 500).take 500
        :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sDigestBlock_slice_1000 :
    ((Fn.«verify_sig_lean_sphincs».core).body.drop (pos% «verify_sig_lean_sphincs» "s20.i0:sp_leaf_shifts.s1.u2.s0#2")).take (span% «verify_sig_lean_sphincs» "s20.i0:sp_leaf_shifts.s1.u2.s0#2" "a0_b~0") = (sDigestBlock.drop 1000).take
        358
        :=
  stmtsEqb_sound (by decide +kernel)

/-- **`verify_sig_lean_sphincs`'s body starts with the digest block**, checked by the kernel in
slices of 500 statements. -/
theorem sDigestBlock_prefix : (Fn.«verify_sig_lean_sphincs».core).body.take (pos% «verify_sig_lean_sphincs» "s40#0") = sDigestBlock :=
  by
  have hs : ∀ l : List Stmt, l.take 1358 = (l.drop 0).take 500 ++ ((l.drop 500).take 500 ++
      (l.drop 1000).take 358) := by
    intro l
    rw [show 1358 = 500 + (500 + 358) from rfl, List.take_add, List.take_add]
    simp only [List.drop_drop, List.drop_zero]
  rw [hs, sDigestBlock_slice_0, sDigestBlock_slice_500, sDigestBlock_slice_1000,
    ← hs, List.take_of_length_le (le_of_eq sDigestBlock_length)]

end
end LeanVM.Guest.B1.Sig
