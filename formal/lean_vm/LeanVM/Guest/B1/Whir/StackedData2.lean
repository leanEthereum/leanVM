/-
  LeanVM.Guest.B1.Whir.StackedData2

  The bodies of `open_stacked__L14` to `open_stacked__L20` and of their loop helpers, equal to
  their templates.
-/

module

public import LeanVM.Guest.B1.Whir.StackedCfg

/-!
# `open_stacked__L14` to `open_stacked__L20`, by kernel evaluation

Each body equal to its template (`stmtsEqb_sound`), with the function's and its loops' lookups.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section


set_option maxRecDepth 100000 in
theorem os_find_14 : coreProgram.find? "open_stacked__L14" = some Data.core191 :=
  Program.find?_of_indexOf? (j := 191) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_14 : Fn.body Data.core191 = osBody osCfg14 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_14_0 : coreProgram.find? "__loop238" = some Data.core764 :=
  Program.find?_of_indexOf? (j := 764) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_14_0 : Fn.body Data.core764 = sqLoopOf (osCfg14.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_14_0 : coreProgram.find? "__loop242" = some Data.core768 :=
  Program.find?_of_indexOf? (j := 768) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_14_0 : Fn.body Data.core768 = resLoopOf osCfg14 0 (osCfg14.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_14_1 : coreProgram.find? "__loop239" = some Data.core765 :=
  Program.find?_of_indexOf? (j := 765) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_14_1 : Fn.body Data.core765 = sqLoopOf (osCfg14.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_14_1 : coreProgram.find? "__loop243" = some Data.core769 :=
  Program.find?_of_indexOf? (j := 769) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_14_1 : Fn.body Data.core769 = resLoopOf osCfg14 1 (osCfg14.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_14_2 : coreProgram.find? "__loop240" = some Data.core766 :=
  Program.find?_of_indexOf? (j := 766) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_14_2 : Fn.body Data.core766 = sqLoopOf (osCfg14.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_14_2 : coreProgram.find? "__loop244" = some Data.core770 :=
  Program.find?_of_indexOf? (j := 770) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_14_2 : Fn.body Data.core770 = resLoopOf osCfg14 2 (osCfg14.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_14_3 : coreProgram.find? "__loop241" = some Data.core767 :=
  Program.find?_of_indexOf? (j := 767) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_14_3 : Fn.body Data.core767 = sqLoopOf (osCfg14.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_14_3 : coreProgram.find? "__loop245" = some Data.core771 :=
  Program.find?_of_indexOf? (j := 771) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_14_3 : Fn.body Data.core771 = resLoopOf osCfg14 3 (osCfg14.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_15 : coreProgram.find? "open_stacked__L15" = some Data.core192 :=
  Program.find?_of_indexOf? (j := 192) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_15 : Fn.body Data.core192 = osBody osCfg15 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_15_0 : coreProgram.find? "__loop246" = some Data.core772 :=
  Program.find?_of_indexOf? (j := 772) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_15_0 : Fn.body Data.core772 = sqLoopOf (osCfg15.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_15_0 : coreProgram.find? "__loop250" = some Data.core776 :=
  Program.find?_of_indexOf? (j := 776) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_15_0 : Fn.body Data.core776 = resLoopOf osCfg15 0 (osCfg15.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_15_1 : coreProgram.find? "__loop247" = some Data.core773 :=
  Program.find?_of_indexOf? (j := 773) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_15_1 : Fn.body Data.core773 = sqLoopOf (osCfg15.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_15_1 : coreProgram.find? "__loop251" = some Data.core777 :=
  Program.find?_of_indexOf? (j := 777) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_15_1 : Fn.body Data.core777 = resLoopOf osCfg15 1 (osCfg15.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_15_2 : coreProgram.find? "__loop248" = some Data.core774 :=
  Program.find?_of_indexOf? (j := 774) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_15_2 : Fn.body Data.core774 = sqLoopOf (osCfg15.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_15_2 : coreProgram.find? "__loop252" = some Data.core778 :=
  Program.find?_of_indexOf? (j := 778) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_15_2 : Fn.body Data.core778 = resLoopOf osCfg15 2 (osCfg15.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_15_3 : coreProgram.find? "__loop249" = some Data.core775 :=
  Program.find?_of_indexOf? (j := 775) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_15_3 : Fn.body Data.core775 = sqLoopOf (osCfg15.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_15_3 : coreProgram.find? "__loop253" = some Data.core779 :=
  Program.find?_of_indexOf? (j := 779) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_15_3 : Fn.body Data.core779 = resLoopOf osCfg15 3 (osCfg15.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_16 : coreProgram.find? "open_stacked__L16" = some Data.core193 :=
  Program.find?_of_indexOf? (j := 193) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_16 : Fn.body Data.core193 = osBody osCfg16 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_16_0 : coreProgram.find? "__loop254" = some Data.core780 :=
  Program.find?_of_indexOf? (j := 780) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_16_0 : Fn.body Data.core780 = sqLoopOf (osCfg16.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_16_0 : coreProgram.find? "__loop259" = some Data.core785 :=
  Program.find?_of_indexOf? (j := 785) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_16_0 : Fn.body Data.core785 = resLoopOf osCfg16 0 (osCfg16.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_16_1 : coreProgram.find? "__loop255" = some Data.core781 :=
  Program.find?_of_indexOf? (j := 781) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_16_1 : Fn.body Data.core781 = sqLoopOf (osCfg16.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_16_1 : coreProgram.find? "__loop260" = some Data.core786 :=
  Program.find?_of_indexOf? (j := 786) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_16_1 : Fn.body Data.core786 = resLoopOf osCfg16 1 (osCfg16.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_16_2 : coreProgram.find? "__loop256" = some Data.core782 :=
  Program.find?_of_indexOf? (j := 782) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_16_2 : Fn.body Data.core782 = sqLoopOf (osCfg16.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_16_2 : coreProgram.find? "__loop261" = some Data.core787 :=
  Program.find?_of_indexOf? (j := 787) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_16_2 : Fn.body Data.core787 = resLoopOf osCfg16 2 (osCfg16.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_16_3 : coreProgram.find? "__loop257" = some Data.core783 :=
  Program.find?_of_indexOf? (j := 783) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_16_3 : Fn.body Data.core783 = sqLoopOf (osCfg16.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_16_3 : coreProgram.find? "__loop262" = some Data.core788 :=
  Program.find?_of_indexOf? (j := 788) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_16_3 : Fn.body Data.core788 = resLoopOf osCfg16 3 (osCfg16.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_16_4 : coreProgram.find? "__loop258" = some Data.core784 :=
  Program.find?_of_indexOf? (j := 784) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_16_4 : Fn.body Data.core784 = sqLoopOf (osCfg16.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_16_4 : coreProgram.find? "__loop263" = some Data.core789 :=
  Program.find?_of_indexOf? (j := 789) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_16_4 : Fn.body Data.core789 = resLoopOf osCfg16 4 (osCfg16.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_17 : coreProgram.find? "open_stacked__L17" = some Data.core194 :=
  Program.find?_of_indexOf? (j := 194) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_17 : Fn.body Data.core194 = osBody osCfg17 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_17_0 : coreProgram.find? "__loop264" = some Data.core790 :=
  Program.find?_of_indexOf? (j := 790) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_17_0 : Fn.body Data.core790 = sqLoopOf (osCfg17.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_17_0 : coreProgram.find? "__loop269" = some Data.core795 :=
  Program.find?_of_indexOf? (j := 795) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_17_0 : Fn.body Data.core795 = resLoopOf osCfg17 0 (osCfg17.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_17_1 : coreProgram.find? "__loop265" = some Data.core791 :=
  Program.find?_of_indexOf? (j := 791) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_17_1 : Fn.body Data.core791 = sqLoopOf (osCfg17.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_17_1 : coreProgram.find? "__loop270" = some Data.core796 :=
  Program.find?_of_indexOf? (j := 796) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_17_1 : Fn.body Data.core796 = resLoopOf osCfg17 1 (osCfg17.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_17_2 : coreProgram.find? "__loop266" = some Data.core792 :=
  Program.find?_of_indexOf? (j := 792) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_17_2 : Fn.body Data.core792 = sqLoopOf (osCfg17.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_17_2 : coreProgram.find? "__loop271" = some Data.core797 :=
  Program.find?_of_indexOf? (j := 797) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_17_2 : Fn.body Data.core797 = resLoopOf osCfg17 2 (osCfg17.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_17_3 : coreProgram.find? "__loop267" = some Data.core793 :=
  Program.find?_of_indexOf? (j := 793) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_17_3 : Fn.body Data.core793 = sqLoopOf (osCfg17.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_17_3 : coreProgram.find? "__loop272" = some Data.core798 :=
  Program.find?_of_indexOf? (j := 798) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_17_3 : Fn.body Data.core798 = resLoopOf osCfg17 3 (osCfg17.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_17_4 : coreProgram.find? "__loop268" = some Data.core794 :=
  Program.find?_of_indexOf? (j := 794) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_17_4 : Fn.body Data.core794 = sqLoopOf (osCfg17.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_17_4 : coreProgram.find? "__loop273" = some Data.core799 :=
  Program.find?_of_indexOf? (j := 799) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_17_4 : Fn.body Data.core799 = resLoopOf osCfg17 4 (osCfg17.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_18 : coreProgram.find? "open_stacked__L18" = some Data.core195 :=
  Program.find?_of_indexOf? (j := 195) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_18 : Fn.body Data.core195 = osBody osCfg18 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_18_0 : coreProgram.find? "__loop274" = some Data.core800 :=
  Program.find?_of_indexOf? (j := 800) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_18_0 : Fn.body Data.core800 = sqLoopOf (osCfg18.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_18_0 : coreProgram.find? "__loop279" = some Data.core805 :=
  Program.find?_of_indexOf? (j := 805) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_18_0 : Fn.body Data.core805 = resLoopOf osCfg18 0 (osCfg18.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_18_1 : coreProgram.find? "__loop275" = some Data.core801 :=
  Program.find?_of_indexOf? (j := 801) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_18_1 : Fn.body Data.core801 = sqLoopOf (osCfg18.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_18_1 : coreProgram.find? "__loop280" = some Data.core806 :=
  Program.find?_of_indexOf? (j := 806) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_18_1 : Fn.body Data.core806 = resLoopOf osCfg18 1 (osCfg18.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_18_2 : coreProgram.find? "__loop276" = some Data.core802 :=
  Program.find?_of_indexOf? (j := 802) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_18_2 : Fn.body Data.core802 = sqLoopOf (osCfg18.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_18_2 : coreProgram.find? "__loop281" = some Data.core807 :=
  Program.find?_of_indexOf? (j := 807) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_18_2 : Fn.body Data.core807 = resLoopOf osCfg18 2 (osCfg18.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_18_3 : coreProgram.find? "__loop277" = some Data.core803 :=
  Program.find?_of_indexOf? (j := 803) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_18_3 : Fn.body Data.core803 = sqLoopOf (osCfg18.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_18_3 : coreProgram.find? "__loop282" = some Data.core808 :=
  Program.find?_of_indexOf? (j := 808) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_18_3 : Fn.body Data.core808 = resLoopOf osCfg18 3 (osCfg18.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_18_4 : coreProgram.find? "__loop278" = some Data.core804 :=
  Program.find?_of_indexOf? (j := 804) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_18_4 : Fn.body Data.core804 = sqLoopOf (osCfg18.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_18_4 : coreProgram.find? "__loop283" = some Data.core809 :=
  Program.find?_of_indexOf? (j := 809) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_18_4 : Fn.body Data.core809 = resLoopOf osCfg18 4 (osCfg18.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_19 : coreProgram.find? "open_stacked__L19" = some Data.core196 :=
  Program.find?_of_indexOf? (j := 196) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_19 : Fn.body Data.core196 = osBody osCfg19 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_19_0 : coreProgram.find? "__loop284" = some Data.core810 :=
  Program.find?_of_indexOf? (j := 810) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_19_0 : Fn.body Data.core810 = sqLoopOf (osCfg19.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_19_0 : coreProgram.find? "__loop289" = some Data.core815 :=
  Program.find?_of_indexOf? (j := 815) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_19_0 : Fn.body Data.core815 = resLoopOf osCfg19 0 (osCfg19.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_19_1 : coreProgram.find? "__loop285" = some Data.core811 :=
  Program.find?_of_indexOf? (j := 811) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_19_1 : Fn.body Data.core811 = sqLoopOf (osCfg19.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_19_1 : coreProgram.find? "__loop290" = some Data.core816 :=
  Program.find?_of_indexOf? (j := 816) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_19_1 : Fn.body Data.core816 = resLoopOf osCfg19 1 (osCfg19.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_19_2 : coreProgram.find? "__loop286" = some Data.core812 :=
  Program.find?_of_indexOf? (j := 812) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_19_2 : Fn.body Data.core812 = sqLoopOf (osCfg19.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_19_2 : coreProgram.find? "__loop291" = some Data.core817 :=
  Program.find?_of_indexOf? (j := 817) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_19_2 : Fn.body Data.core817 = resLoopOf osCfg19 2 (osCfg19.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_19_3 : coreProgram.find? "__loop287" = some Data.core813 :=
  Program.find?_of_indexOf? (j := 813) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_19_3 : Fn.body Data.core813 = sqLoopOf (osCfg19.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_19_3 : coreProgram.find? "__loop292" = some Data.core818 :=
  Program.find?_of_indexOf? (j := 818) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_19_3 : Fn.body Data.core818 = resLoopOf osCfg19 3 (osCfg19.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_19_4 : coreProgram.find? "__loop288" = some Data.core814 :=
  Program.find?_of_indexOf? (j := 814) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_19_4 : Fn.body Data.core814 = sqLoopOf (osCfg19.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_19_4 : coreProgram.find? "__loop293" = some Data.core819 :=
  Program.find?_of_indexOf? (j := 819) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_19_4 : Fn.body Data.core819 = resLoopOf osCfg19 4 (osCfg19.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_20 : coreProgram.find? "open_stacked__L20" = some Data.core197 :=
  Program.find?_of_indexOf? (j := 197) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_20 : Fn.body Data.core197 = osBody osCfg20 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_20_0 : coreProgram.find? "__loop294" = some Data.core820 :=
  Program.find?_of_indexOf? (j := 820) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_20_0 : Fn.body Data.core820 = sqLoopOf (osCfg20.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_20_0 : coreProgram.find? "__loop300" = some Data.core830 :=
  Program.find?_of_indexOf? (j := 830) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_20_0 : Fn.body Data.core830 = resLoopOf osCfg20 0 (osCfg20.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_20_1 : coreProgram.find? "__loop295" = some Data.core822 :=
  Program.find?_of_indexOf? (j := 822) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_20_1 : Fn.body Data.core822 = sqLoopOf (osCfg20.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_20_1 : coreProgram.find? "__loop301" = some Data.core831 :=
  Program.find?_of_indexOf? (j := 831) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_20_1 : Fn.body Data.core831 = resLoopOf osCfg20 1 (osCfg20.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_20_2 : coreProgram.find? "__loop296" = some Data.core824 :=
  Program.find?_of_indexOf? (j := 824) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_20_2 : Fn.body Data.core824 = sqLoopOf (osCfg20.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_20_2 : coreProgram.find? "__loop302" = some Data.core832 :=
  Program.find?_of_indexOf? (j := 832) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_20_2 : Fn.body Data.core832 = resLoopOf osCfg20 2 (osCfg20.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_20_3 : coreProgram.find? "__loop297" = some Data.core826 :=
  Program.find?_of_indexOf? (j := 826) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_20_3 : Fn.body Data.core826 = sqLoopOf (osCfg20.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_20_3 : coreProgram.find? "__loop303" = some Data.core833 :=
  Program.find?_of_indexOf? (j := 833) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_20_3 : Fn.body Data.core833 = resLoopOf osCfg20 3 (osCfg20.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_20_4 : coreProgram.find? "__loop298" = some Data.core827 :=
  Program.find?_of_indexOf? (j := 827) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_20_4 : Fn.body Data.core827 = sqLoopOf (osCfg20.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_20_4 : coreProgram.find? "__loop304" = some Data.core834 :=
  Program.find?_of_indexOf? (j := 834) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_20_4 : Fn.body Data.core834 = resLoopOf osCfg20 4 (osCfg20.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_20_5 : coreProgram.find? "__loop299" = some Data.core829 :=
  Program.find?_of_indexOf? (j := 829) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_20_5 : Fn.body Data.core829 = sqLoopOf (osCfg20.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_20_5 : coreProgram.find? "__loop305" = some Data.core835 :=
  Program.find?_of_indexOf? (j := 835) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_20_5 : Fn.body Data.core835 = resLoopOf osCfg20 5 (osCfg20.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
