/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStB

  The proof stream's reads, sound at the honest frames: `keccak_layer`'s and its two
  loops' reads past their cursors lie inside the stream.
-/

module

public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStP
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L_loop0»
import LeanVM.Guest.Data.ValNames.«keccak_layer__L_loop1»

/-!
# The stream loops' cursors

`loopCur`: a stream loop's cursor value. `loop_atoms_top`: a stream loop's top-level atoms hold its
cursor's product.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-- A loop's cursor value (`cur_i`), and its cell. -/
def loopCur (rem : Bool) : V :=
  if rem then .n (valf% «keccak_layer» «_loop1» "cur_i") else .n (valf% «keccak_layer» «_loop0» "cur_i")

end

public section

theorem loop_atoms_top {first : ℕ} (hf : first < 2) (rem : Bool) {fn : Fn}
    (hfn : coreProgram.find? (stLoop first rem) = some fn) :
    (topAtoms fn.body).contains (.mul (.n 6) (.n 2) (.n 0)) = true ∧
      (topAtoms fn.body).contains (.load (loopCur rem) (.n 6) 55) = true := by
  interval_cases first <;> cases rem
  · rw [Option.some.inj (hfn.symm.trans find_pack8_458)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_packRem_459)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_pack8_456)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_packRem_457)]; decide +kernel

end

end LeanVM.Guest.EndExec
