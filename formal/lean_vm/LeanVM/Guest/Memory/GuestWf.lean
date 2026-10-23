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
public import LeanVM.Guest.Memory.GuestWf.Part11
public import LeanVM.Guest.Memory.GuestWf.Part12
public import LeanVM.Guest.Memory.GuestWf.Part13
public import LeanVM.Guest.Memory.GuestWf.Part14
public import LeanVM.Guest.Memory.GuestWf.Part15
public import LeanVM.Guest.Memory.GuestWf.Part16
public import LeanVM.Guest.Memory.GuestWf.Part17
public import LeanVM.Guest.Memory.GuestWf.Part18
public import LeanVM.Guest.Memory.GuestWf.Part19
public import LeanVM.Guest.Memory.GuestWf.Part20
public import LeanVM.Guest.Memory.GuestWf.Part21
public import LeanVM.Guest.Memory.GuestWf.Part22
public import LeanVM.Guest.Memory.GuestWf.Part23
public import LeanVM.Guest.Memory.GuestWf.Part24
public import LeanVM.Guest.Memory.GuestWf.Part25
public import LeanVM.Guest.Memory.GuestWf.Part26
public import LeanVM.Guest.Memory.GuestWf.Part27
public import LeanVM.Guest.Memory.GuestWf.Part28
public import LeanVM.Guest.Memory.GuestWf.Part29
public import LeanVM.Guest.Memory.GuestWf.Part30
public import LeanVM.Guest.Memory.GuestWf.Part31
public import LeanVM.Guest.Memory.GuestWf.Part32
public import LeanVM.Guest.Memory.GuestWf.Part33
public import LeanVM.Guest.Memory.GuestWf.Part34
public import LeanVM.Guest.Memory.GuestWf.Part35
public import LeanVM.Guest.Memory.GuestWf.Part36
public import LeanVM.Guest.Memory.GuestWf.Part37
public import LeanVM.Guest.Memory.GuestWf.Part38
public import LeanVM.Guest.Memory.GuestWf.Part39
public import LeanVM.Guest.Memory.GuestWf.Part40
public import LeanVM.Guest.Memory.GuestWf.Part41
public import LeanVM.Guest.Memory.GuestWf.Part42
public import LeanVM.Guest.Memory.GuestWf.Part43
public import LeanVM.Guest.Memory.GuestWf.Part44
public import LeanVM.Guest.Memory.GuestWf.Part45
public import LeanVM.Guest.Memory.GuestWf.Part46
public import LeanVM.Guest.Memory.GuestWf.Part47
public import LeanVM.Guest.Memory.GuestWf.Part48
public import LeanVM.Guest.Memory.GuestWf.Part49
public import LeanVM.Guest.Memory.GuestWf.Part50
public import LeanVM.Guest.Memory.GuestWf.Part51
public import LeanVM.Guest.Memory.GuestWf.Part52
public import LeanVM.Guest.Memory.GuestWf.Part53
public import LeanVM.Guest.Memory.GuestWf.Part54
public import LeanVM.Guest.Memory.GuestWf.Part55
public import LeanVM.Guest.Memory.GuestWf.Part56
public import LeanVM.Guest.Memory.GuestWf.Part57
public import LeanVM.Guest.Memory.GuestWf.Part58
public import LeanVM.Guest.Memory.GuestWf.Part59
public import LeanVM.Guest.Memory.GuestWf.Part60
public import LeanVM.Guest.Memory.GuestWf.Part61
public import LeanVM.Guest.Memory.GuestWf.Part62
public import LeanVM.Guest.Memory.GuestWf.Part63
public import LeanVM.Guest.Memory.GuestWf.Part64
public import LeanVM.Guest.Memory.GuestWf.Part65
public import LeanVM.Guest.Memory.GuestWf.Part66
public import LeanVM.Guest.Memory.GuestWf.Part67
public import LeanVM.Guest.Memory.GuestWf.Part68
public import LeanVM.Guest.Memory.GuestWf.Part69
public import LeanVM.Guest.Memory.GuestWf.Part70
public import LeanVM.Guest.Memory.GuestWf.Part71
public import LeanVM.Guest.Memory.GuestWf.Part72
public import LeanVM.Guest.Memory.GuestWf.Part73
public import LeanVM.Guest.Memory.GuestWf.Part74
public import LeanVM.Guest.Memory.GuestWf.Part75
public import LeanVM.Guest.Memory.GuestWf.Part76
public import LeanVM.Guest.Memory.GuestWf.Part77
public import LeanVM.Guest.Memory.GuestWf.Part78
public import LeanVM.Guest.Memory.GuestWf.Part79
public import LeanVM.Guest.Memory.GuestWf.Part80
public import LeanVM.Guest.Memory.GuestWf.Part81
public import LeanVM.Guest.Memory.GuestWf.Part82
public import LeanVM.Guest.Memory.GuestWf.Part83

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
  have h2 : WfRange 0 17 := h1.append' wfRange_12 (by norm_num) (by norm_num)
  have h3 : WfRange 0 23 := h2.append' wfRange_17 (by norm_num) (by norm_num)
  have h4 : WfRange 0 25 := h3.append' wfRange_23 (by norm_num) (by norm_num)
  have h5 : WfRange 0 38 := h4.append' wfRange_25 (by norm_num) (by norm_num)
  have h6 : WfRange 0 91 := h5.append' wfRange_38 (by norm_num) (by norm_num)
  have h7 : WfRange 0 116 := h6.append' wfRange_91 (by norm_num) (by norm_num)
  have h8 : WfRange 0 141 := h7.append' wfRange_116 (by norm_num) (by norm_num)
  have h9 : WfRange 0 179 := h8.append' wfRange_141 (by norm_num) (by norm_num)
  have h10 : WfRange 0 181 := h9.append' wfRange_179 (by norm_num) (by norm_num)
  have h11 : WfRange 0 183 := h10.append' wfRange_181 (by norm_num) (by norm_num)
  have h12 : WfRange 0 185 := h11.append' wfRange_183 (by norm_num) (by norm_num)
  have h13 : WfRange 0 187 := h12.append' wfRange_185 (by norm_num) (by norm_num)
  have h14 : WfRange 0 189 := h13.append' wfRange_187 (by norm_num) (by norm_num)
  have h15 : WfRange 0 190 := h14.append' wfRange_189 (by norm_num) (by norm_num)
  have h16 : WfRange 0 191 := h15.append' wfRange_190 (by norm_num) (by norm_num)
  have h17 : WfRange 0 193 := h16.append' wfRange_191 (by norm_num) (by norm_num)
  have h18 : WfRange 0 194 := h17.append' wfRange_193 (by norm_num) (by norm_num)
  have h19 : WfRange 0 195 := h18.append' wfRange_194 (by norm_num) (by norm_num)
  have h20 : WfRange 0 196 := h19.append' wfRange_195 (by norm_num) (by norm_num)
  have h21 : WfRange 0 197 := h20.append' wfRange_196 (by norm_num) (by norm_num)
  have h22 : WfRange 0 198 := h21.append' wfRange_197 (by norm_num) (by norm_num)
  have h23 : WfRange 0 199 := h22.append' wfRange_198 (by norm_num) (by norm_num)
  have h24 : WfRange 0 200 := h23.append' wfRange_199 (by norm_num) (by norm_num)
  have h25 : WfRange 0 201 := h24.append' wfRange_200 (by norm_num) (by norm_num)
  have h26 : WfRange 0 202 := h25.append' wfRange_201 (by norm_num) (by norm_num)
  have h27 : WfRange 0 203 := h26.append' wfRange_202 (by norm_num) (by norm_num)
  have h28 : WfRange 0 204 := h27.append' wfRange_203 (by norm_num) (by norm_num)
  have h29 : WfRange 0 211 := h28.append' wfRange_204 (by norm_num) (by norm_num)
  have h30 : WfRange 0 228 := h29.append' wfRange_211 (by norm_num) (by norm_num)
  have h31 : WfRange 0 253 := h30.append' wfRange_228 (by norm_num) (by norm_num)
  have h32 : WfRange 0 303 := h31.append' wfRange_253 (by norm_num) (by norm_num)
  have h33 : WfRange 0 353 := h32.append' wfRange_303 (by norm_num) (by norm_num)
  have h34 : WfRange 0 503 := h33.append' wfRange_353 (by norm_num) (by norm_num)
  have h35 : WfRange 0 523 := h34.append' wfRange_503 (by norm_num) (by norm_num)
  have h36 : WfRange 0 534 := h35.append' wfRange_523 (by norm_num) (by norm_num)
  have h37 : WfRange 0 538 := h36.append' wfRange_534 (by norm_num) (by norm_num)
  have h38 : WfRange 0 540 := h37.append' wfRange_538 (by norm_num) (by norm_num)
  have h39 : WfRange 0 542 := h38.append' wfRange_540 (by norm_num) (by norm_num)
  have h40 : WfRange 0 544 := h39.append' wfRange_542 (by norm_num) (by norm_num)
  have h41 : WfRange 0 545 := h40.append' wfRange_544 (by norm_num) (by norm_num)
  have h42 : WfRange 0 546 := h41.append' wfRange_545 (by norm_num) (by norm_num)
  have h43 : WfRange 0 548 := h42.append' wfRange_546 (by norm_num) (by norm_num)
  have h44 : WfRange 0 560 := h43.append' wfRange_548 (by norm_num) (by norm_num)
  have h45 : WfRange 0 574 := h44.append' wfRange_560 (by norm_num) (by norm_num)
  have h46 : WfRange 0 591 := h45.append' wfRange_574 (by norm_num) (by norm_num)
  have h47 : WfRange 0 607 := h46.append' wfRange_591 (by norm_num) (by norm_num)
  have h48 : WfRange 0 622 := h47.append' wfRange_607 (by norm_num) (by norm_num)
  have h49 : WfRange 0 636 := h48.append' wfRange_622 (by norm_num) (by norm_num)
  have h50 : WfRange 0 649 := h49.append' wfRange_636 (by norm_num) (by norm_num)
  have h51 : WfRange 0 661 := h50.append' wfRange_649 (by norm_num) (by norm_num)
  have h52 : WfRange 0 674 := h51.append' wfRange_661 (by norm_num) (by norm_num)
  have h53 : WfRange 0 686 := h52.append' wfRange_674 (by norm_num) (by norm_num)
  have h54 : WfRange 0 699 := h53.append' wfRange_686 (by norm_num) (by norm_num)
  have h55 : WfRange 0 711 := h54.append' wfRange_699 (by norm_num) (by norm_num)
  have h56 : WfRange 0 724 := h55.append' wfRange_711 (by norm_num) (by norm_num)
  have h57 : WfRange 0 736 := h56.append' wfRange_724 (by norm_num) (by norm_num)
  have h58 : WfRange 0 749 := h57.append' wfRange_736 (by norm_num) (by norm_num)
  have h59 : WfRange 0 761 := h58.append' wfRange_749 (by norm_num) (by norm_num)
  have h60 : WfRange 0 774 := h59.append' wfRange_761 (by norm_num) (by norm_num)
  have h61 : WfRange 0 786 := h60.append' wfRange_774 (by norm_num) (by norm_num)
  have h62 : WfRange 0 799 := h61.append' wfRange_786 (by norm_num) (by norm_num)
  have h63 : WfRange 0 811 := h62.append' wfRange_799 (by norm_num) (by norm_num)
  have h64 : WfRange 0 824 := h63.append' wfRange_811 (by norm_num) (by norm_num)
  have h65 : WfRange 0 836 := h64.append' wfRange_824 (by norm_num) (by norm_num)
  have h66 : WfRange 0 849 := h65.append' wfRange_836 (by norm_num) (by norm_num)
  have h67 : WfRange 0 861 := h66.append' wfRange_849 (by norm_num) (by norm_num)
  have h68 : WfRange 0 874 := h67.append' wfRange_861 (by norm_num) (by norm_num)
  have h69 : WfRange 0 886 := h68.append' wfRange_874 (by norm_num) (by norm_num)
  have h70 : WfRange 0 899 := h69.append' wfRange_886 (by norm_num) (by norm_num)
  have h71 : WfRange 0 911 := h70.append' wfRange_899 (by norm_num) (by norm_num)
  have h72 : WfRange 0 923 := h71.append' wfRange_911 (by norm_num) (by norm_num)
  have h73 : WfRange 0 934 := h72.append' wfRange_923 (by norm_num) (by norm_num)
  have h74 : WfRange 0 947 := h73.append' wfRange_934 (by norm_num) (by norm_num)
  have h75 : WfRange 0 959 := h74.append' wfRange_947 (by norm_num) (by norm_num)
  have h76 : WfRange 0 970 := h75.append' wfRange_959 (by norm_num) (by norm_num)
  have h77 : WfRange 0 981 := h76.append' wfRange_970 (by norm_num) (by norm_num)
  have h78 : WfRange 0 991 := h77.append' wfRange_981 (by norm_num) (by norm_num)
  have h79 : WfRange 0 1001 := h78.append' wfRange_991 (by norm_num) (by norm_num)
  have h80 : WfRange 0 1011 := h79.append' wfRange_1001 (by norm_num) (by norm_num)
  have h81 : WfRange 0 1020 := h80.append' wfRange_1011 (by norm_num) (by norm_num)
  have h82 : WfRange 0 1032 := h81.append' wfRange_1020 (by norm_num) (by norm_num)
  have h83 : WfRange 0 1043 := h82.append' wfRange_1032 (by norm_num) (by norm_num)
  exact h83

/-- **The guest's core IR is well formed.** -/
theorem coreProgram_wf : coreProgram.Wf := by
  have h := wfRange_all
  unfold WfRange at h
  rw [List.drop_zero, List.take_of_length_le (by rw [coreProgram_length]), List.all_eq_true] at h
  exact fun fn hfn => h fn hfn

end
end LeanVM.Guest
