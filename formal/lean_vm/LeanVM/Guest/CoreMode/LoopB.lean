/-
  LeanVM.Guest.CoreMode.LoopB

  A leaf loop helper's body: atoms, its tail call, `ret []`.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsDefs
public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.Bridge.Prefix

/-!
# A leaf loop helper's body

`loopB fn`: the body of atoms, the tail call `callIf c fn.name args` with one word per parameter, and
`ret []`.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (stmtsOf stmtsSub walk_ret_cons walk_callIf_cons walk_atoms)

@[expose] public section

/-- An atom statement. -/
def isAtomS : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- **A leaf loop helper's body**: atoms, its tail call to itself with one word per parameter,
`ret []`. -/
def loopB (fn : Fn) : Bool :=
  match fn.body.reverse with
  | .ret [] :: .callIf _ g args :: pre => (g == fn.name) && Nat.beq args.length fn.params.length && pre.all isAtomS
  | _ => false

end

end LeanVM.Guest.CoreMode
