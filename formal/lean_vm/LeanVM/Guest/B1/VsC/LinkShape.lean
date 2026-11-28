/-
  LeanVM.Guest.B1.VsC.LinkShape

  The link's sizes on an accepted child, against the guest's dispatches and buffers: the chunk
  count, the packed challenges' permutations, the width's cases.
-/

module

public import LeanVM.Guest.B1.VsC.Shape
public import LeanVM.Guest.GuestConst
public import LeanVM.Guest.Data.Consts

/-!
# The link's shape on an accepted child

`verify_sub` dispatches the link on the pointer width `w - BYTECODE_LOG < LINK_W_ARMS` and its
chunk count `d - LINK_D_MIN < LINK_D_ARMS`, draws the packed challenges in `p` permutations with
`8(p - 1) < LINK_FIXED + n + w + d ≤ 8p` into `chal` (`LINK_CHAL_CAP` cells, `θ_0` first), and
checks the width against the cycles' bit length or the memory's and program's logs. For the
honest `p = ⌈packedChallenges / 8⌉` (`link_shape`, `childHints`):

* `chunkD_range`: every width `19 ..= 24` chunks into `6 ..= 9`, `LINK_D_MIN + LINK_D_ARMS - 1`;
* `packedChallenges_eq`: `packedChallenges tables n w = LINK_FIXED + n + w + d`;
* `packed_vanish`: `8p - (LINK_FIXED + n + w + d) < 8`, the root of `vanish`;
* `chal_fits`: `8p + 1 ≤ LINK_CHAL_CAP` at `n, w ≤ 24`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The chunk count of a width, `0` for a width `Chunks.new` refuses. -/
def chunkCount (w : ℕ) : ℕ := ((Chunks.new w).map Chunks.d).getD 0

/-- **Every deployed width chunks into `LINK_D_MIN ..= LINK_D_MIN + LINK_D_ARMS - 1`**, and
`Chunks.new` accepts it. -/
theorem chunkD_range : ∀ w, 19 ≤ w → w ≤ 24 →
    (Chunks.new w).isSome ∧ guest_const% LINK_D_MIN ≤ chunkCount w ∧
      chunkCount w - guest_const% LINK_D_MIN < guest_const% LINK_D_ARMS := by
  intro w h1 h2
  interval_cases w <;> decide +kernel

/-- The link's fixed challenges after `θ_0`: `θ`'s rest, `γ`, `μ`, `α`, `η`, `ε`, the guest's
`LINK_FIXED`. -/
theorem linkFixed_eq : (nTables - 1) + 5 + (tables.map (·.links.memory.length)).sum +
    bytecodeSlotBits + 2 + (tables.map (·.links.pointers.length)).sum = guest_const% LINK_FIXED := by
  decide +kernel

/-- **The packed challenges' count is `LINK_FIXED + n + w + d`.** -/
theorem packedChallenges_eq (n w : ℕ) :
    packedChallenges tables n w = guest_const% LINK_FIXED + n + w + chunkCount w := by
  unfold packedChallenges chunkCount
  rw [← linkFixed_eq]

/-- **The honest permutation count is a root of `vanish`**: `8p` exceeds the count by less than
`8`, at `p = ⌈count / 8⌉`. -/
theorem packed_vanish (count : ℕ) : count ≤ 8 * ((count + 7) / 8) ∧ 8 * ((count + 7) / 8) - count < 8 := by
  omega

/-- **The packed challenges fit `chal`** at heights and widths at most `24`. -/
theorem chal_fits {n w : ℕ} (hn : n ≤ 24) (hw1 : 19 ≤ w) (hw : w ≤ 24) :
    8 * ((packedChallenges tables n w + 7) / 8) + 1 ≤ guest_const% LINK_CHAL_CAP := by
  rw [packedChallenges_eq]
  have := (chunkD_range w hw1 hw).2.2
  have h88 : guest_const% LINK_FIXED = 88 := rfl
  have hd : guest_const% LINK_D_MIN = 6 := rfl
  have ha : guest_const% LINK_D_ARMS = 4 := rfl
  have hc : guest_const% LINK_CHAL_CAP = 153 := rfl
  rw [h88, hc]
  rw [hd, ha] at this
  omega

end
end LeanVM.Guest.B1.VsC
