/-
  LeanVM.Protocol.EndToEnd.Front.KeccakLayout

  `q_keccak` on a stack of the verifier's layout: its words, where the verifier's layout places it.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance

/-!
# `q_keccak` on the verifier's layout

The Keccak reduction (`verifyKeccak`) and ring switching speak of the Keccak reduction's committed
column `q_keccak` (global column `QKECCAK`) as a function of its word index (`LeanVM.Protocol.Keccak`:
step bits low, the six slot bits high). On a stack `q` of a verifier layout, `qkOf layout q n` is
word `n` of the block the layout places `QKECCAK` at (`layout.placement qkeccak`).

`placement_qkeccak`: at the verifier's layout, `QKECCAK` is placed on `τ_KECCAK + 6` variables at
its block's offset.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa

@[expose] public section

/-- Word `n` of `q_keccak` on a stack of the layout: the stack's cell `n` past `QKECCAK`'s
offset. -/
def qkOf (layout : Verifier.Layout) (q : Column layout.stackLog) (n : ℕ) : K :=
  q.values.toArray.getD ((layout.placement qkeccak).index + n) 0

/-- **`QKECCAK`'s placement at the verifier's layout**: `τ_KECCAK + 6` variables at its block's
offset. -/
theorem placement_qkeccak (prog : LeanIsaProgram) (s : Sizes) :
    (verifierLayout prog s).placement qkeccak =
      { variableCount := s.τ 5 + 6, index := (blocks prog s).offset (keccakBlock prog s) } := by
  rw [← refCol_keccakCol, placement_committed prog s keccakCol not_isVirtual_keccakCol]
  rfl

end
end LeanVM.Protocol.EndToEnd.Front
