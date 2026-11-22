/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStB

  The proof stream's reads (`Res.stB`), sound at the honest frames: `keccak_layer`'s and its two
  loops' reads past their cursors lie inside the stream.
-/

module

public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStP
public import LeanVM.Guest.CoreMode.Fam.SubDefs
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

/-- **The proof stream's readers**: function, its cursor's cell, the stream's base (the layer's
parameter, the loops' through their header), the words read past the cursor. -/
def stSites : List (String × ℕ × Mode.Base × ℕ) :=
  [(name% «keccak_layer__L0», 747, .fr 17, 36), (name% «keccak_layer__L1», 773, .fr 17, 36),
    (name% «keccak_layer__L0_loop0», 20, .hp 1 17, 16), (name% «keccak_layer__L1_loop0», 20, .hp 1 17, 16),
    (name% «keccak_layer__L0_loop1», 17, .hp 1 17, 2), (name% «keccak_layer__L1_loop1», 17, .hp 1 17, 2)]

/-- **A read of the proof stream** at function `j`: a site's, below its words. -/
noncomputable def stB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => stSites.any fun s ↦ (coreOf j).name == s.1 && decide (a.q.k < s.2.2.2) &&
      decide (Mode.Res.sub a bs = stRes s.2.1 s.2.2.1 a.q.k)
  | _ => false

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.VerifySub
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (stB stRes stSites topAtoms)
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
      (topAtoms fn.body).contains (.load (loopCur rem) (.n 6) 80) = true := by
  interval_cases first <;> cases rem
  · rw [Option.some.inj (hfn.symm.trans find_pack8_458)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_packRem_459)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_pack8_456)]; decide +kernel
  · rw [Option.some.inj (hfn.symm.trans find_packRem_457)]; decide +kernel

end

end LeanVM.Guest.EndExec
