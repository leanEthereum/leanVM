/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.Fam

  `keccak_layer`'s own residual families (`CoreMode/FnReg.lean`): its reads past its last record's cursor and its pack rounds' words.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»
import LeanVM.Guest.Data.ValNames.«keccak_layer__L0»
import LeanVM.Guest.Data.ValNames.«keccak_layer__L1»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `keccak_layer__L{first}`'s last record's cursor value, `cursor@2` (`EndExec.layer_cur`). -/
def layCur (fn : Fn) : Option ℕ :=
  bif fn.name == name% «keccak_layer__L0» then some (val% «keccak_layer__L0» "cursor@2")
  else bif fn.name == name% «keccak_layer__L1» then some (val% «keccak_layer__L1» "cursor@2") else none

/-- **`keccak_layer`'s family** (`EndExec.LayQ`): a read `c < 36` words past its last record's cursor, one of its
stream's, parameter `stream`'s `[0, 8192)`; its pack rounds' words `e(step_g), e(rem_g) < n`, `32 ≤ n`; either under branch
conditions (`EndExec.layQC_inst`). -/
def layQC (fn : Fn) : CRes → Bool
  | .sub c q => (layCur fn).any (fun v ↦ decide (c.bases = [(v, 1)])) && decide (c.off < 36) &&
      decide (q = ⟨⟨[(valf% «keccak_layer» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩)
  | .lt (.val x) (.num n) => (layCur fn).isSome &&
      (Nat.beq x (valf% «keccak_layer» "step_g") || Nat.beq x (valf% «keccak_layer» "rem_g")) && decide (32 ≤ n) &&
      decide (n < capE)
  | .under _ r => layQC fn r
  | _ => false

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.keccak_layer

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family** (`layQC`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «keccak_layer__L0», layQC), (name% «keccak_layer__L1», layQC)]

end

end LeanVM.Guest.CoreMode.Own.keccak_layer
