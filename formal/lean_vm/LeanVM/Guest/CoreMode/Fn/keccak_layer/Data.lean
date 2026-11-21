/-
  LeanVM.Guest.CoreMode.Fn.keccak_layer.Data

  `keccak_layer`'s own routing data (`CoreMode/FnReg.lean`): its loops' reads of the proof stream, its callers.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.keccak_layer

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its loops read the proof stream past their cursors** (`CoreMode.stLoops`): the stream their caller's cell `17`,
the eight-round loop's cursor its value `20`, `16` words an iteration, the remainder loop's `14`, `2`. -/
def stLoops : List (String × ℕ × ℕ × ℕ) :=
  [(name% «keccak_layer__L0_loop0», 17, 20, 16), (name% «keccak_layer__L1_loop0», 17, 20, 16),
    (name% «keccak_layer__L0_loop1», 17, 14, 2), (name% «keccak_layer__L1_loop1», 17, 14, 2)]

/-- **Its callers and its loops'** (`Res.callersG`): `verify_keccak`, and itself. -/
def stCallers : List (String × String) :=
  [(name% «keccak_layer__L0», name% «verify_keccak»), (name% «keccak_layer__L1», name% «verify_keccak»),
    (name% «keccak_layer__L0_loop0», name% «keccak_layer__L0»),
    (name% «keccak_layer__L0_loop1», name% «keccak_layer__L0»),
    (name% «keccak_layer__L1_loop0», name% «keccak_layer__L1»),
    (name% «keccak_layer__L1_loop1», name% «keccak_layer__L1»)]

end

end LeanVM.Guest.CoreMode.Own.keccak_layer
