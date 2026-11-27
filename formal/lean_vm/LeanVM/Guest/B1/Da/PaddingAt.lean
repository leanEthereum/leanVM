/-
  LeanVM.Guest.B1.Da.PaddingAt

  `da_padding` in the uniform placed form: it reads no memory, its range check the memory below
  `2^16`.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.PaddingComplete
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_padding»
import LeanVM.Guest.StmtsAppend

/-!
# `da_padding`, placed

`da_padding` is atoms and a return, with no load; its range check reads the memory below `2^16`
(`LowDef 16`), which is no load.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (LowDef CompleteAtD Returns disj_nil)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- `da_padding`'s atoms. -/
def padAs : List Atom := [
    .const (.n (val% «da_padding» "s0#0")) (word 1 0), .add (.n (val% «da_padding» "s0#1")) (.n (val% «da_padding» "n_blob_g")) (.n (val% «da_padding» "s0#0")), .hint (.inverse (.n (val% «da_padding» "s0#1")) (.n (val% «da_padding» "s0#2"))),
    .assertNe (.n (val% «da_padding» "s0#1")) (.n (val% «da_padding» "s0#2")) (.n (val% «da_padding» "s0#3")), .const (.n (val% «da_padding» "s1#0")) (word (2 ^ guest_const% DA_MAX_ROWS) 0),
    .rangeCheck (.n (val% «da_padding» "n_blob_g")) (.n (val% «da_padding» "s1#1")) (.n (val% «da_padding» "s1#2")) (.n (val% «da_padding» "s1#3")) (.n (val% «da_padding» "s1#0")), .const (.n (val% «da_padding» "s2#1")) (word (2 ^ guest_const% DA_MAX_ROWS) 0),
    .mul (.n (val% «da_padding» "s2#1")) (.n (val% «da_padding» "s2#2")) (.n (val% «da_padding» "n_blob_g")), .copy (.n (val% «da_padding» "s2#0")) (.n (val% «da_padding» "s2#2"))]

theorem pad_split : Fn.body fn% «da_padding» = padAs.map Stmt.atom ⧺ [.ret [.n (val% «da_padding» "s2#0")]] := by
  rw [da_padding_body]; rfl

theorem pad_loop : coreProgram.loop "da_padding" = false := by
  rw [Program.loop_of_find? find_da_padding]; decide +kernel

end
end LeanVM.Guest.B1.Da
