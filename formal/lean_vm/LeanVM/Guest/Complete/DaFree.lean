module

public import LeanVM.Guest.Complete.AggFree
import LeanVM.Guest.CoreRef

/-!
# `da_verify`'s callees, free, and its subtree exact

`da_vector`, `da_weights` and `da_pad` have no witness hint in their subtrees and every computed
hint pinned (kernel evaluation), so each completes where its relation holds (`callCompletes_free`).
`da_verify`'s whole subtree pins its computed hints, so every valid tree of it is exact
(`da_verify_exactFree`), and so are its blob check's and cell check's (`da_verify_blob_exactFree`,
`da_verify_cell_exactFree`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem da_vector_free : NoWitG "da_vector" ∧ ExactFreeG "da_vector" :=
  free_of (by decide +kernel : freeAt "da_vector" idx% «da_vector» = true)

set_option maxRecDepth 100000 in
theorem da_weights_free : NoWitG "da_weights" ∧ ExactFreeG "da_weights" :=
  free_of (by decide +kernel : freeAt "da_weights" idx% «da_weights» = true)

set_option maxRecDepth 100000 in
theorem da_verify_exactFree : ExactFreeG "da_verify" :=
  exactFreeG_of (by decide +kernel : exactFree "da_verify" idx% «da_verify» = true)

set_option maxRecDepth 100000 in
theorem da_verify_blob_exactFree : ExactFreeG "da_verify_blob" :=
  exactFreeG_of (by decide +kernel : exactFree "da_verify_blob" idx% «da_verify_blob» = true)

set_option maxRecDepth 100000 in
theorem da_verify_cell_exactFree : ExactFreeG "da_verify_cell" :=
  exactFreeG_of (by decide +kernel : exactFree "da_verify_cell" idx% «da_verify_cell» = true)

end
end LeanVM.Guest.Complete
