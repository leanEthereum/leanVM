/-
  LeanVM.Guest.B1.Whir.StackedData0

  The bodies of `open_stacked__L0` to `open_stacked__L6` and of their loop helpers, equal to
  their templates.
-/

module

public import LeanVM.Guest.B1.Whir.StackedCfg

/-!
# `open_stacked__L0` to `open_stacked__L6`, by kernel evaluation

Each body equal to its template (`stmtsEqb_sound`), with the function's and its loops' lookups.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section


set_option maxRecDepth 100000 in
theorem os_find_0 : coreProgram.find? "open_stacked__L0" = some Data.core177 :=
  Program.find?_of_indexOf? (j := 177) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_0 : Fn.body Data.core177 = osBody osCfg0 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_0_0 : coreProgram.find? "__loop102" = some Data.core577 :=
  Program.find?_of_indexOf? (j := 577) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_0_0 : Fn.body Data.core577 = sqLoopOf (osCfg0.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_0_0 : coreProgram.find? "__loop106" = some Data.core592 :=
  Program.find?_of_indexOf? (j := 592) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_0_0 : Fn.body Data.core592 = resLoopOf osCfg0 0 (osCfg0.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_0_1 : coreProgram.find? "__loop103" = some Data.core581 :=
  Program.find?_of_indexOf? (j := 581) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_0_1 : Fn.body Data.core581 = sqLoopOf (osCfg0.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_0_1 : coreProgram.find? "__loop107" = some Data.core593 :=
  Program.find?_of_indexOf? (j := 593) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_0_1 : Fn.body Data.core593 = resLoopOf osCfg0 1 (osCfg0.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_0_2 : coreProgram.find? "__loop104" = some Data.core585 :=
  Program.find?_of_indexOf? (j := 585) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_0_2 : Fn.body Data.core585 = sqLoopOf (osCfg0.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_0_2 : coreProgram.find? "__loop108" = some Data.core594 :=
  Program.find?_of_indexOf? (j := 594) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_0_2 : Fn.body Data.core594 = resLoopOf osCfg0 2 (osCfg0.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_0_3 : coreProgram.find? "__loop105" = some Data.core589 :=
  Program.find?_of_indexOf? (j := 589) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_0_3 : Fn.body Data.core589 = sqLoopOf (osCfg0.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_0_3 : coreProgram.find? "__loop109" = some Data.core595 :=
  Program.find?_of_indexOf? (j := 595) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_0_3 : Fn.body Data.core595 = resLoopOf osCfg0 3 (osCfg0.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_1 : coreProgram.find? "open_stacked__L1" = some Data.core178 :=
  Program.find?_of_indexOf? (j := 178) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_1 : Fn.body Data.core178 = osBody osCfg1 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_1_0 : coreProgram.find? "__loop110" = some Data.core596 :=
  Program.find?_of_indexOf? (j := 596) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_1_0 : Fn.body Data.core596 = sqLoopOf (osCfg1.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_1_0 : coreProgram.find? "__loop114" = some Data.core605 :=
  Program.find?_of_indexOf? (j := 605) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_1_0 : Fn.body Data.core605 = resLoopOf osCfg1 0 (osCfg1.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_1_1 : coreProgram.find? "__loop111" = some Data.core598 :=
  Program.find?_of_indexOf? (j := 598) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_1_1 : Fn.body Data.core598 = sqLoopOf (osCfg1.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_1_1 : coreProgram.find? "__loop115" = some Data.core606 :=
  Program.find?_of_indexOf? (j := 606) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_1_1 : Fn.body Data.core606 = resLoopOf osCfg1 1 (osCfg1.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_1_2 : coreProgram.find? "__loop112" = some Data.core600 :=
  Program.find?_of_indexOf? (j := 600) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_1_2 : Fn.body Data.core600 = sqLoopOf (osCfg1.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_1_2 : coreProgram.find? "__loop116" = some Data.core607 :=
  Program.find?_of_indexOf? (j := 607) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_1_2 : Fn.body Data.core607 = resLoopOf osCfg1 2 (osCfg1.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_1_3 : coreProgram.find? "__loop113" = some Data.core603 :=
  Program.find?_of_indexOf? (j := 603) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_1_3 : Fn.body Data.core603 = sqLoopOf (osCfg1.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_1_3 : coreProgram.find? "__loop117" = some Data.core608 :=
  Program.find?_of_indexOf? (j := 608) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_1_3 : Fn.body Data.core608 = resLoopOf osCfg1 3 (osCfg1.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_2 : coreProgram.find? "open_stacked__L2" = some Data.core179 :=
  Program.find?_of_indexOf? (j := 179) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_2 : Fn.body Data.core179 = osBody osCfg2 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_2_0 : coreProgram.find? "__loop118" = some Data.core609 :=
  Program.find?_of_indexOf? (j := 609) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_2_0 : Fn.body Data.core609 = sqLoopOf (osCfg2.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_2_0 : coreProgram.find? "__loop123" = some Data.core619 :=
  Program.find?_of_indexOf? (j := 619) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_2_0 : Fn.body Data.core619 = resLoopOf osCfg2 0 (osCfg2.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_2_1 : coreProgram.find? "__loop119" = some Data.core611 :=
  Program.find?_of_indexOf? (j := 611) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_2_1 : Fn.body Data.core611 = sqLoopOf (osCfg2.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_2_1 : coreProgram.find? "__loop124" = some Data.core620 :=
  Program.find?_of_indexOf? (j := 620) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_2_1 : Fn.body Data.core620 = resLoopOf osCfg2 1 (osCfg2.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_2_2 : coreProgram.find? "__loop120" = some Data.core613 :=
  Program.find?_of_indexOf? (j := 613) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_2_2 : Fn.body Data.core613 = sqLoopOf (osCfg2.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_2_2 : coreProgram.find? "__loop125" = some Data.core621 :=
  Program.find?_of_indexOf? (j := 621) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_2_2 : Fn.body Data.core621 = resLoopOf osCfg2 2 (osCfg2.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_2_3 : coreProgram.find? "__loop121" = some Data.core615 :=
  Program.find?_of_indexOf? (j := 615) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_2_3 : Fn.body Data.core615 = sqLoopOf (osCfg2.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_2_3 : coreProgram.find? "__loop126" = some Data.core622 :=
  Program.find?_of_indexOf? (j := 622) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_2_3 : Fn.body Data.core622 = resLoopOf osCfg2 3 (osCfg2.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_2_4 : coreProgram.find? "__loop122" = some Data.core617 :=
  Program.find?_of_indexOf? (j := 617) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_2_4 : Fn.body Data.core617 = sqLoopOf (osCfg2.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_2_4 : coreProgram.find? "__loop127" = some Data.core623 :=
  Program.find?_of_indexOf? (j := 623) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_2_4 : Fn.body Data.core623 = resLoopOf osCfg2 4 (osCfg2.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_3 : coreProgram.find? "open_stacked__L3" = some Data.core180 :=
  Program.find?_of_indexOf? (j := 180) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_3 : Fn.body Data.core180 = osBody osCfg3 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_3_0 : coreProgram.find? "__loop128" = some Data.core624 :=
  Program.find?_of_indexOf? (j := 624) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_3_0 : Fn.body Data.core624 = sqLoopOf (osCfg3.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_3_0 : coreProgram.find? "__loop133" = some Data.core634 :=
  Program.find?_of_indexOf? (j := 634) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_3_0 : Fn.body Data.core634 = resLoopOf osCfg3 0 (osCfg3.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_3_1 : coreProgram.find? "__loop129" = some Data.core626 :=
  Program.find?_of_indexOf? (j := 626) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_3_1 : Fn.body Data.core626 = sqLoopOf (osCfg3.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_3_1 : coreProgram.find? "__loop134" = some Data.core635 :=
  Program.find?_of_indexOf? (j := 635) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_3_1 : Fn.body Data.core635 = resLoopOf osCfg3 1 (osCfg3.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_3_2 : coreProgram.find? "__loop130" = some Data.core628 :=
  Program.find?_of_indexOf? (j := 628) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_3_2 : Fn.body Data.core628 = sqLoopOf (osCfg3.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_3_2 : coreProgram.find? "__loop135" = some Data.core636 :=
  Program.find?_of_indexOf? (j := 636) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_3_2 : Fn.body Data.core636 = resLoopOf osCfg3 2 (osCfg3.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_3_3 : coreProgram.find? "__loop131" = some Data.core630 :=
  Program.find?_of_indexOf? (j := 630) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_3_3 : Fn.body Data.core630 = sqLoopOf (osCfg3.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_3_3 : coreProgram.find? "__loop136" = some Data.core637 :=
  Program.find?_of_indexOf? (j := 637) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_3_3 : Fn.body Data.core637 = resLoopOf osCfg3 3 (osCfg3.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_3_4 : coreProgram.find? "__loop132" = some Data.core632 :=
  Program.find?_of_indexOf? (j := 632) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_3_4 : Fn.body Data.core632 = sqLoopOf (osCfg3.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_3_4 : coreProgram.find? "__loop137" = some Data.core638 :=
  Program.find?_of_indexOf? (j := 638) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_3_4 : Fn.body Data.core638 = resLoopOf osCfg3 4 (osCfg3.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_4 : coreProgram.find? "open_stacked__L4" = some Data.core181 :=
  Program.find?_of_indexOf? (j := 181) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_4 : Fn.body Data.core181 = osBody osCfg4 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_4_0 : coreProgram.find? "__loop138" = some Data.core639 :=
  Program.find?_of_indexOf? (j := 639) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_4_0 : Fn.body Data.core639 = sqLoopOf (osCfg4.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_4_0 : coreProgram.find? "__loop143" = some Data.core647 :=
  Program.find?_of_indexOf? (j := 647) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_4_0 : Fn.body Data.core647 = resLoopOf osCfg4 0 (osCfg4.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_4_1 : coreProgram.find? "__loop139" = some Data.core641 :=
  Program.find?_of_indexOf? (j := 641) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_4_1 : Fn.body Data.core641 = sqLoopOf (osCfg4.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_4_1 : coreProgram.find? "__loop144" = some Data.core648 :=
  Program.find?_of_indexOf? (j := 648) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_4_1 : Fn.body Data.core648 = resLoopOf osCfg4 1 (osCfg4.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_4_2 : coreProgram.find? "__loop140" = some Data.core643 :=
  Program.find?_of_indexOf? (j := 643) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_4_2 : Fn.body Data.core643 = sqLoopOf (osCfg4.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_4_2 : coreProgram.find? "__loop145" = some Data.core649 :=
  Program.find?_of_indexOf? (j := 649) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_4_2 : Fn.body Data.core649 = resLoopOf osCfg4 2 (osCfg4.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_4_3 : coreProgram.find? "__loop141" = some Data.core645 :=
  Program.find?_of_indexOf? (j := 645) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_4_3 : Fn.body Data.core645 = sqLoopOf (osCfg4.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_4_3 : coreProgram.find? "__loop146" = some Data.core650 :=
  Program.find?_of_indexOf? (j := 650) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_4_3 : Fn.body Data.core650 = resLoopOf osCfg4 3 (osCfg4.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_4_4 : coreProgram.find? "__loop142" = some Data.core646 :=
  Program.find?_of_indexOf? (j := 646) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_4_4 : Fn.body Data.core646 = sqLoopOf (osCfg4.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_4_4 : coreProgram.find? "__loop147" = some Data.core651 :=
  Program.find?_of_indexOf? (j := 651) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_4_4 : Fn.body Data.core651 = resLoopOf osCfg4 4 (osCfg4.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_5 : coreProgram.find? "open_stacked__L5" = some Data.core182 :=
  Program.find?_of_indexOf? (j := 182) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_5 : Fn.body Data.core182 = osBody osCfg5 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_5_0 : coreProgram.find? "__loop148" = some Data.core652 :=
  Program.find?_of_indexOf? (j := 652) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_5_0 : Fn.body Data.core652 = sqLoopOf (osCfg5.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_5_0 : coreProgram.find? "__loop153" = some Data.core660 :=
  Program.find?_of_indexOf? (j := 660) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_5_0 : Fn.body Data.core660 = resLoopOf osCfg5 0 (osCfg5.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_5_1 : coreProgram.find? "__loop149" = some Data.core654 :=
  Program.find?_of_indexOf? (j := 654) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_5_1 : Fn.body Data.core654 = sqLoopOf (osCfg5.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_5_1 : coreProgram.find? "__loop154" = some Data.core661 :=
  Program.find?_of_indexOf? (j := 661) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_5_1 : Fn.body Data.core661 = resLoopOf osCfg5 1 (osCfg5.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_5_2 : coreProgram.find? "__loop150" = some Data.core656 :=
  Program.find?_of_indexOf? (j := 656) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_5_2 : Fn.body Data.core656 = sqLoopOf (osCfg5.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_5_2 : coreProgram.find? "__loop155" = some Data.core662 :=
  Program.find?_of_indexOf? (j := 662) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_5_2 : Fn.body Data.core662 = resLoopOf osCfg5 2 (osCfg5.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_5_3 : coreProgram.find? "__loop151" = some Data.core658 :=
  Program.find?_of_indexOf? (j := 658) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_5_3 : Fn.body Data.core658 = sqLoopOf (osCfg5.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_5_3 : coreProgram.find? "__loop156" = some Data.core663 :=
  Program.find?_of_indexOf? (j := 663) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_5_3 : Fn.body Data.core663 = resLoopOf osCfg5 3 (osCfg5.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_5_4 : coreProgram.find? "__loop152" = some Data.core659 :=
  Program.find?_of_indexOf? (j := 659) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_5_4 : Fn.body Data.core659 = sqLoopOf (osCfg5.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_5_4 : coreProgram.find? "__loop157" = some Data.core664 :=
  Program.find?_of_indexOf? (j := 664) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_5_4 : Fn.body Data.core664 = resLoopOf osCfg5 4 (osCfg5.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_6 : coreProgram.find? "open_stacked__L6" = some Data.core183 :=
  Program.find?_of_indexOf? (j := 183) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_6 : Fn.body Data.core183 = osBody osCfg6 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_6_0 : coreProgram.find? "__loop158" = some Data.core665 :=
  Program.find?_of_indexOf? (j := 665) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_6_0 : Fn.body Data.core665 = sqLoopOf (osCfg6.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_6_0 : coreProgram.find? "__loop164" = some Data.core676 :=
  Program.find?_of_indexOf? (j := 676) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_6_0 : Fn.body Data.core676 = resLoopOf osCfg6 0 (osCfg6.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_6_1 : coreProgram.find? "__loop159" = some Data.core667 :=
  Program.find?_of_indexOf? (j := 667) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_6_1 : Fn.body Data.core667 = sqLoopOf (osCfg6.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_6_1 : coreProgram.find? "__loop165" = some Data.core677 :=
  Program.find?_of_indexOf? (j := 677) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_6_1 : Fn.body Data.core677 = resLoopOf osCfg6 1 (osCfg6.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_6_2 : coreProgram.find? "__loop160" = some Data.core669 :=
  Program.find?_of_indexOf? (j := 669) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_6_2 : Fn.body Data.core669 = sqLoopOf (osCfg6.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_6_2 : coreProgram.find? "__loop166" = some Data.core678 :=
  Program.find?_of_indexOf? (j := 678) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_6_2 : Fn.body Data.core678 = resLoopOf osCfg6 2 (osCfg6.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_6_3 : coreProgram.find? "__loop161" = some Data.core671 :=
  Program.find?_of_indexOf? (j := 671) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_6_3 : Fn.body Data.core671 = sqLoopOf (osCfg6.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_6_3 : coreProgram.find? "__loop167" = some Data.core679 :=
  Program.find?_of_indexOf? (j := 679) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_6_3 : Fn.body Data.core679 = resLoopOf osCfg6 3 (osCfg6.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_6_4 : coreProgram.find? "__loop162" = some Data.core672 :=
  Program.find?_of_indexOf? (j := 672) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_6_4 : Fn.body Data.core672 = sqLoopOf (osCfg6.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_6_4 : coreProgram.find? "__loop168" = some Data.core680 :=
  Program.find?_of_indexOf? (j := 680) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_6_4 : Fn.body Data.core680 = resLoopOf osCfg6 4 (osCfg6.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_6_5 : coreProgram.find? "__loop163" = some Data.core673 :=
  Program.find?_of_indexOf? (j := 673) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_6_5 : Fn.body Data.core673 = sqLoopOf (osCfg6.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_6_5 : coreProgram.find? "__loop169" = some Data.core681 :=
  Program.find?_of_indexOf? (j := 681) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_6_5 : Fn.body Data.core681 = resLoopOf osCfg6 5 (osCfg6.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
