/-
  LeanVM.Guest.B1.Whir.Stacked

  `open_stacked` is sound at every candidate: group 6's `SoundOpen`.
-/

module

public import LeanVM.Guest.B1.Whir.StackedInst0
public import LeanVM.Guest.B1.Whir.StackedInst1
public import LeanVM.Guest.B1.Whir.StackedInst2
public import LeanVM.Guest.B1.Whir.StackedInst3

/-!
# `open_stacked` (TRIAGE #36): `SoundOpen`

At every candidate `22 ≤ μ ≤ 28`, `1 ≤ r ≤ 4`, the specialization `openName μ r` is
`open_stacked__L{(μ - 22) + 7·(r - 1)}`, sound by `open_stacked_L…_sound`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **`open_stacked` is sound** at every candidate (`VerifySub.SoundOpen`). -/
theorem soundOpen (rd : Reader) : SoundOpen rd := by
  intro μ r h1 h2 h3 h4 root fs0 fs1 target root0 root1 cur rets hroot h
  interval_cases μ <;> interval_cases r
  · exact open_stacked_L0_sound hroot h
  · exact open_stacked_L7_sound hroot h
  · exact open_stacked_L14_sound hroot h
  · exact open_stacked_L21_sound hroot h
  · exact open_stacked_L1_sound hroot h
  · exact open_stacked_L8_sound hroot h
  · exact open_stacked_L15_sound hroot h
  · exact open_stacked_L22_sound hroot h
  · exact open_stacked_L2_sound hroot h
  · exact open_stacked_L9_sound hroot h
  · exact open_stacked_L16_sound hroot h
  · exact open_stacked_L23_sound hroot h
  · exact open_stacked_L3_sound hroot h
  · exact open_stacked_L10_sound hroot h
  · exact open_stacked_L17_sound hroot h
  · exact open_stacked_L24_sound hroot h
  · exact open_stacked_L4_sound hroot h
  · exact open_stacked_L11_sound hroot h
  · exact open_stacked_L18_sound hroot h
  · exact open_stacked_L25_sound hroot h
  · exact open_stacked_L5_sound hroot h
  · exact open_stacked_L12_sound hroot h
  · exact open_stacked_L19_sound hroot h
  · exact open_stacked_L26_sound hroot h
  · exact open_stacked_L6_sound hroot h
  · exact open_stacked_L13_sound hroot h
  · exact open_stacked_L20_sound hroot h
  · exact open_stacked_L27_sound hroot h

end
end LeanVM.Guest.B1
