/-
  LeanVM.Guest.Memory.HeapPops

  The advised `HeapBuf` sizes a call tree pops, in pre-order: at each entered instance, the sizes
  of the buffers its advice names, then its callees'.
-/

module

public import LeanVM.Guest.Memory.Eval

/-!
# The advised sizes of a tree

`Tree.heapPops slots t`: the `heap_sizes` entries an execution of `t` pops, in order: at a node of
`f`, for each buffer index `k` of `slots f` (the buffers its `allocAdvice` hints stand for), the
entry `[g^n]` of its `k`-th buffer of `n` words, empty when its path allocates none
(`advEntry`); then its callees', in call order. A phantom is not entered and pops none.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

/-- The `heap_sizes` entry of the buffer of index `k`: `[g^n]` for `n` words, empty if none. -/
def advEntry (bufs : List ℕ) (k : ℕ) : List E := (bufs[k]?.map fun n ↦ ofK (addressOfIndex n)).toList

mutual
/-- **The advised sizes a tree pops**, in pre-order. -/
def Tree.heapPops (slots : String → List ℕ) : Tree → List (List E)
  | .node f _ bufs kids => (slots f).map (advEntry bufs) ++ Tree.heapPopsKids slots kids
  | .phantom .. => []

/-- The advised sizes callees pop, in call order. -/
def Tree.heapPopsKids (slots : String → List ℕ) : List Tree → List (List E)
  | [] => []
  | k :: ks => k.heapPops slots ++ Tree.heapPopsKids slots ks
end

end

end LeanVM.Guest.Memory
