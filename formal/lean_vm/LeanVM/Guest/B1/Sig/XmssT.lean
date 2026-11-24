/-
  LeanVM.Guest.B1.Sig.XmssT

  Pieces of `verify_lean_xmss` as templates (`lean_ethereum.py`): the target sum, a layer's step
  addresses and its node addresses' constants.
-/

module

public import LeanVM.Guest.B1.Sig.WotsT

/-!
# `verify_lean_xmss`'s pieces as templates

* `xTarget`: `g^106`, the target sum in the exponent;
* `xStepAddrs idx b`: the three step addresses from base `b`;
* `xAddrOf layer l`: the constant of level `l`'s node address.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- `g^106`, the leanXMSS target sum in the exponent. -/
def xTarget : E := word 118747255799808 0

/-- The three step addresses from base `b`, at `n(b + 2s + 1)`. -/
def xStepAddrs (idx : V) (b : Nat) : List Stmt :=
  (List.range 3).flatMap fun s =>
    [cst (b + 2 * s) (word (tw 1 + s * stepMul) 0), addS (.n (b + 2 * s + 1)) idx (.n (b + 2 * s))]

/-! ## A layer -/

/-- The constant of layer `layer`'s level-`l` node address. -/
def xAddrOf (layer l : Nat) : Nat := tw 3 + (l + 1) * hiMul + layer * lxTop
end
end LeanVM.Guest.B1.Sig
