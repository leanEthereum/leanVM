/-
  LeanVM.Guest.Memory.GuestWf

  The guest's core IR is well formed (`Program.Wf`): every `callIf` names a loop helper taking
  its arguments, and every `match` and fused dispatch has at most `2^64 - 1` arms; so every
  derivation of its `Program.Rel` is an honest evaluation.
-/

module

public import LeanVM.Guest.Memory.GuestWf.Part00
public import LeanVM.Guest.Memory.GuestWf.Part01
public import LeanVM.Guest.Memory.GuestWf.Part02
public import LeanVM.Guest.Memory.GuestWf.Part03
public import LeanVM.Guest.Memory.GuestWf.Part04
public import LeanVM.Guest.Memory.GuestWf.Part05
public import LeanVM.Guest.Memory.GuestWf.Part06
public import LeanVM.Guest.Memory.GuestWf.Part07
public import LeanVM.Guest.Memory.GuestWf.Part08
public import LeanVM.Guest.Memory.GuestWf.Part09
public import LeanVM.Guest.Memory.GuestWf.Part10

/-!
# The guest is well formed

`Stmt.wfList` is evaluated by the kernel on ranges of `coreProgram`'s functions (`WfRange`, one
declaration each), the ranges cut by the number of `callIf`s, whose callee lookups the kernel's
cost is in, and spread over modules (`GuestWf/Part*.lean`) so that each runs in a process of its
own. The ranges concatenate to the whole program (`wfRange_all`).
-/

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- The ranges, concatenated. -/
theorem wfRange_all : WfRange 0 1043 := by
  have h0 : WfRange 0 11 := wfRange_0
  have h1 : WfRange 0 12 := h0.append' wfRange_11 (by norm_num) (by norm_num)
  have h2 : WfRange 0 38 := h1.append' wfRange_12 (by norm_num) (by norm_num)
  have h3 : WfRange 0 91 := h2.append' wfRange_38 (by norm_num) (by norm_num)
  have h4 : WfRange 0 116 := h3.append' wfRange_91 (by norm_num) (by norm_num)
  have h5 : WfRange 0 141 := h4.append' wfRange_116 (by norm_num) (by norm_num)
  have h6 : WfRange 0 179 := h5.append' wfRange_141 (by norm_num) (by norm_num)
  have h7 : WfRange 0 181 := h6.append' wfRange_179 (by norm_num) (by norm_num)
  have h8 : WfRange 0 183 := h7.append' wfRange_181 (by norm_num) (by norm_num)
  have h9 : WfRange 0 185 := h8.append' wfRange_183 (by norm_num) (by norm_num)
  have h10 : WfRange 0 187 := h9.append' wfRange_185 (by norm_num) (by norm_num)
  have h11 : WfRange 0 189 := h10.append' wfRange_187 (by norm_num) (by norm_num)
  have h12 : WfRange 0 191 := h11.append' wfRange_189 (by norm_num) (by norm_num)
  have h13 : WfRange 0 193 := h12.append' wfRange_191 (by norm_num) (by norm_num)
  have h14 : WfRange 0 195 := h13.append' wfRange_193 (by norm_num) (by norm_num)
  have h15 : WfRange 0 197 := h14.append' wfRange_195 (by norm_num) (by norm_num)
  have h16 : WfRange 0 199 := h15.append' wfRange_197 (by norm_num) (by norm_num)
  have h17 : WfRange 0 201 := h16.append' wfRange_199 (by norm_num) (by norm_num)
  have h18 : WfRange 0 203 := h17.append' wfRange_201 (by norm_num) (by norm_num)
  have h19 : WfRange 0 353 := h18.append' wfRange_203 (by norm_num) (by norm_num)
  have h20 : WfRange 0 503 := h19.append' wfRange_353 (by norm_num) (by norm_num)
  have h21 : WfRange 0 542 := h20.append' wfRange_503 (by norm_num) (by norm_num)
  have h22 : WfRange 0 545 := h21.append' wfRange_542 (by norm_num) (by norm_num)
  have h23 : WfRange 0 574 := h22.append' wfRange_545 (by norm_num) (by norm_num)
  have h24 : WfRange 0 607 := h23.append' wfRange_574 (by norm_num) (by norm_num)
  have h25 : WfRange 0 636 := h24.append' wfRange_607 (by norm_num) (by norm_num)
  have h26 : WfRange 0 661 := h25.append' wfRange_636 (by norm_num) (by norm_num)
  have h27 : WfRange 0 686 := h26.append' wfRange_661 (by norm_num) (by norm_num)
  have h28 : WfRange 0 711 := h27.append' wfRange_686 (by norm_num) (by norm_num)
  have h29 : WfRange 0 736 := h28.append' wfRange_711 (by norm_num) (by norm_num)
  have h30 : WfRange 0 761 := h29.append' wfRange_736 (by norm_num) (by norm_num)
  have h31 : WfRange 0 786 := h30.append' wfRange_761 (by norm_num) (by norm_num)
  have h32 : WfRange 0 811 := h31.append' wfRange_786 (by norm_num) (by norm_num)
  have h33 : WfRange 0 836 := h32.append' wfRange_811 (by norm_num) (by norm_num)
  have h34 : WfRange 0 861 := h33.append' wfRange_836 (by norm_num) (by norm_num)
  have h35 : WfRange 0 886 := h34.append' wfRange_861 (by norm_num) (by norm_num)
  have h36 : WfRange 0 911 := h35.append' wfRange_886 (by norm_num) (by norm_num)
  have h37 : WfRange 0 934 := h36.append' wfRange_911 (by norm_num) (by norm_num)
  have h38 : WfRange 0 959 := h37.append' wfRange_934 (by norm_num) (by norm_num)
  have h39 : WfRange 0 991 := h38.append' wfRange_959 (by norm_num) (by norm_num)
  have h40 : WfRange 0 1020 := h39.append' wfRange_991 (by norm_num) (by norm_num)
  have h41 : WfRange 0 1043 := h40.append' wfRange_1020 (by norm_num) (by norm_num)
  exact h41

/-- **The guest's core IR is well formed.** -/
theorem coreProgram_wf : coreProgram.Wf := by
  have h := wfRange_all
  unfold WfRange at h
  rw [List.drop_zero, List.take_of_length_le (by rw [coreProgram_length]), List.all_eq_true] at h
  exact fun fn hfn => h fn hfn

end
end LeanVM.Guest
