/-
  LeanVM.Guest.B1.Sig.XmssSegEnds

  The ends and roots of the two layers of leanXMSS's check in `main_loop2`, evaluated.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop2»

/-!
# The layers' ends

`sLayer0_snd`, `sLayer1_snd`: the bottom layer ends at `xTop` with its root at `xRoot0`, the top
layer at `xEnd` with its root at `xRoot1` (by kernel evaluation). The four are named once, in
`XmssSegT.lean`, so a renumbering of `main_loop2` changes their values there and nothing that
cites them.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem sLayer0_snd : (sLayer 0 88 (.n 0)).2 = (xTop, .n xRoot0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem sLayer1_snd : (sLayer 1 xTop (.n xRoot0)).2 = (xEnd, .n xRoot1) := by decide +kernel

theorem sWin1_0 : (sWin1 0 88).2 = (xTop, xRoot0) := by
  have h := sLayer0_snd
  simp only [sLayer] at h
  simp only [Prod.mk.injEq, V.mk.injEq, true_and] at h
  exact Prod.ext h.1 h.2

theorem sWin1_1 : (sWin1 1 xTop).2 = (xEnd, xRoot1) := by
  have h := sLayer1_snd
  simp only [sLayer] at h
  simp only [Prod.mk.injEq, V.mk.injEq, true_and] at h
  exact Prod.ext h.1 h.2

end
end LeanVM.Guest.B1.Sig
