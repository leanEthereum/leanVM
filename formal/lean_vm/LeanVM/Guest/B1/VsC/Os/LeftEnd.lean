/-
  LeanVM.Guest.B1.VsC.Os.LeftEnd

  `open_stacked`'s end bounded: `OpenStackedEndA` at every arm when every frame is at most `2^16`.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftPost
public import LeanVM.Guest.B1.VsC.OpenStackedEndA
import LeanVM.Guest.Complete.FsSmall

/-!
# `open_stacked`'s end, bounded

Each callee's end is bounded by its sizes and frames (`LpAE`, `OqAE`, `LqAGE`, `LrAE`, `LsumAE`,
`LrsAE`), each level's by `osChainB`, the tail's by `kidsAtF_tailB`, and the arms' sizes by one
kernel check (`osBnd`), so `OsKidsAt` carries `e ≤ c + 2^36` when every frame is at most `2^16`
(`osKidsAt_of_post`). `osCallAtA_of_kids` adds the point buffers below the end.
`openStackedEndA_all`: `OpenStackedEndA` at every arm from `∀ f, B2C.fs f ≤ 2^16`, which
`osFs_le16` gives from `fs_lt16`: `openStackedEndA_17`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`open_stacked`'s end bounded at every arm** from what is left of it, every frame at most `2^16`. -/
theorem openStackedEndA_of_kids {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    (hk : 11 ≤ k) (h : OsKidsHyp fs al cert k) (hfs : ∀ f, fs f ≤ 2 ^ 16) :
    ∀ m, m ≤ 14 → OpenStackedEndA fs al cert k m := by
  intro m hm r root fsv target ic it xs os w s' roots' qs R hr1 hr4 hfl hcar hrun hq hRx hRt fp c hfc
  obtain ⟨H, hK⟩ := h m hm r root fsv target ic it xs os w s' roots' qs R hr1 hr4 hfl hcar hrun hq hRx hRt fp c hfc
  obtain ⟨e, he, hb0, hb1, heB⟩ := osCallAtA_of_kids hk hm hr1 hr4 (by simp [hfl]) H hRx hRt hfc hK
  have h1 := heB hfs (osBnd (by omega : m < 15) (by omega : r - 1 < 4)).2.2.1
  exact ⟨_, _, e, he, hb0, hb1, h1⟩

/-- **`open_stacked`'s end bounded at every arm**, every compiled frame at most `2^16`. -/
theorem openStackedEndA_all (al : String → Bool) {k : ℕ} (hk : 11 ≤ k) (hfs : ∀ f, B2C.fs f ≤ 2 ^ 16) :
    ∀ m, m ≤ 14 → OpenStackedEndA B2C.fs al B2C.cert k m :=
  openStackedEndA_of_kids hk (osKidsHyp_of_post hk (osPostHyp k)) hfs

/-- **Every compiled frame at most `2^16`** (`fs_lt16`). -/
theorem osFs_le16 (f : String) : B2C.fs f ≤ 2 ^ 16 := le_of_lt (fs_lt16 f)

/-- **`GuestLeft.openStacked`, its end bounded**: at the deployed choices. -/
theorem openStackedEndA_17 : ∀ m, m ≤ 14 → OpenStackedEndA B2C.fs alW B2C.cert 17 m :=
  openStackedEndA_all alW (by norm_num) osFs_le16

end
end LeanVM.Guest.B1.VsC
