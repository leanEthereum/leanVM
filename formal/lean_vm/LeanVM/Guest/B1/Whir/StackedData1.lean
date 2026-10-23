/-
  LeanVM.Guest.B1.Whir.StackedData1

  The bodies of `open_stacked__L7` to `open_stacked__L13` and of their loop helpers, equal to
  their templates.
-/

module

public import LeanVM.Guest.B1.Whir.StackedCfg

/-!
# `open_stacked__L7` to `open_stacked__L13`, by kernel evaluation

Each body equal to its template (`stmtsEqb_sound`), with the function's and its loops' lookups.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section


set_option maxRecDepth 100000 in
theorem os_find_7 : coreProgram.find? "open_stacked__L7" = some Data.core184 :=
  Program.find?_of_indexOf? (j := 184) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_7 : Fn.body Data.core184 = osBody osCfg7 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_7_0 : coreProgram.find? "__loop170" = some Data.core682 :=
  Program.find?_of_indexOf? (j := 682) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_7_0 : Fn.body Data.core682 = sqLoopOf (osCfg7.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_7_0 : coreProgram.find? "__loop174" = some Data.core688 :=
  Program.find?_of_indexOf? (j := 688) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_7_0 : Fn.body Data.core688 = resLoopOf osCfg7 0 (osCfg7.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_7_1 : coreProgram.find? "__loop171" = some Data.core685 :=
  Program.find?_of_indexOf? (j := 685) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_7_1 : Fn.body Data.core685 = sqLoopOf (osCfg7.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_7_1 : coreProgram.find? "__loop175" = some Data.core689 :=
  Program.find?_of_indexOf? (j := 689) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_7_1 : Fn.body Data.core689 = resLoopOf osCfg7 1 (osCfg7.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_7_2 : coreProgram.find? "__loop172" = some Data.core686 :=
  Program.find?_of_indexOf? (j := 686) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_7_2 : Fn.body Data.core686 = sqLoopOf (osCfg7.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_7_2 : coreProgram.find? "__loop176" = some Data.core690 :=
  Program.find?_of_indexOf? (j := 690) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_7_2 : Fn.body Data.core690 = resLoopOf osCfg7 2 (osCfg7.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_7_3 : coreProgram.find? "__loop173" = some Data.core687 :=
  Program.find?_of_indexOf? (j := 687) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_7_3 : Fn.body Data.core687 = sqLoopOf (osCfg7.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_7_3 : coreProgram.find? "__loop177" = some Data.core691 :=
  Program.find?_of_indexOf? (j := 691) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_7_3 : Fn.body Data.core691 = resLoopOf osCfg7 3 (osCfg7.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_8 : coreProgram.find? "open_stacked__L8" = some Data.core185 :=
  Program.find?_of_indexOf? (j := 185) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_8 : Fn.body Data.core185 = osBody osCfg8 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_8_0 : coreProgram.find? "__loop178" = some Data.core692 :=
  Program.find?_of_indexOf? (j := 692) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_8_0 : Fn.body Data.core692 = sqLoopOf (osCfg8.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_8_0 : coreProgram.find? "__loop182" = some Data.core697 :=
  Program.find?_of_indexOf? (j := 697) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_8_0 : Fn.body Data.core697 = resLoopOf osCfg8 0 (osCfg8.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_8_1 : coreProgram.find? "__loop179" = some Data.core694 :=
  Program.find?_of_indexOf? (j := 694) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_8_1 : Fn.body Data.core694 = sqLoopOf (osCfg8.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_8_1 : coreProgram.find? "__loop183" = some Data.core698 :=
  Program.find?_of_indexOf? (j := 698) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_8_1 : Fn.body Data.core698 = resLoopOf osCfg8 1 (osCfg8.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_8_2 : coreProgram.find? "__loop180" = some Data.core695 :=
  Program.find?_of_indexOf? (j := 695) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_8_2 : Fn.body Data.core695 = sqLoopOf (osCfg8.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_8_2 : coreProgram.find? "__loop184" = some Data.core699 :=
  Program.find?_of_indexOf? (j := 699) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_8_2 : Fn.body Data.core699 = resLoopOf osCfg8 2 (osCfg8.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_8_3 : coreProgram.find? "__loop181" = some Data.core696 :=
  Program.find?_of_indexOf? (j := 696) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_8_3 : Fn.body Data.core696 = sqLoopOf (osCfg8.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_8_3 : coreProgram.find? "__loop185" = some Data.core700 :=
  Program.find?_of_indexOf? (j := 700) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_8_3 : Fn.body Data.core700 = resLoopOf osCfg8 3 (osCfg8.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_9 : coreProgram.find? "open_stacked__L9" = some Data.core186 :=
  Program.find?_of_indexOf? (j := 186) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_9 : Fn.body Data.core186 = osBody osCfg9 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_9_0 : coreProgram.find? "__loop186" = some Data.core701 :=
  Program.find?_of_indexOf? (j := 701) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_9_0 : Fn.body Data.core701 = sqLoopOf (osCfg9.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_9_0 : coreProgram.find? "__loop191" = some Data.core708 :=
  Program.find?_of_indexOf? (j := 708) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_9_0 : Fn.body Data.core708 = resLoopOf osCfg9 0 (osCfg9.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_9_1 : coreProgram.find? "__loop187" = some Data.core703 :=
  Program.find?_of_indexOf? (j := 703) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_9_1 : Fn.body Data.core703 = sqLoopOf (osCfg9.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_9_1 : coreProgram.find? "__loop192" = some Data.core709 :=
  Program.find?_of_indexOf? (j := 709) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_9_1 : Fn.body Data.core709 = resLoopOf osCfg9 1 (osCfg9.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_9_2 : coreProgram.find? "__loop188" = some Data.core704 :=
  Program.find?_of_indexOf? (j := 704) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_9_2 : Fn.body Data.core704 = sqLoopOf (osCfg9.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_9_2 : coreProgram.find? "__loop193" = some Data.core710 :=
  Program.find?_of_indexOf? (j := 710) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_9_2 : Fn.body Data.core710 = resLoopOf osCfg9 2 (osCfg9.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_9_3 : coreProgram.find? "__loop189" = some Data.core705 :=
  Program.find?_of_indexOf? (j := 705) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_9_3 : Fn.body Data.core705 = sqLoopOf (osCfg9.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_9_3 : coreProgram.find? "__loop194" = some Data.core711 :=
  Program.find?_of_indexOf? (j := 711) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_9_3 : Fn.body Data.core711 = resLoopOf osCfg9 3 (osCfg9.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_9_4 : coreProgram.find? "__loop190" = some Data.core706 :=
  Program.find?_of_indexOf? (j := 706) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_9_4 : Fn.body Data.core706 = sqLoopOf (osCfg9.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_9_4 : coreProgram.find? "__loop195" = some Data.core712 :=
  Program.find?_of_indexOf? (j := 712) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_9_4 : Fn.body Data.core712 = resLoopOf osCfg9 4 (osCfg9.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_10 : coreProgram.find? "open_stacked__L10" = some Data.core187 :=
  Program.find?_of_indexOf? (j := 187) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_10 : Fn.body Data.core187 = osBody osCfg10 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_10_0 : coreProgram.find? "__loop196" = some Data.core713 :=
  Program.find?_of_indexOf? (j := 713) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_10_0 : Fn.body Data.core713 = sqLoopOf (osCfg10.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_10_0 : coreProgram.find? "__loop201" = some Data.core720 :=
  Program.find?_of_indexOf? (j := 720) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_10_0 : Fn.body Data.core720 = resLoopOf osCfg10 0 (osCfg10.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_10_1 : coreProgram.find? "__loop197" = some Data.core715 :=
  Program.find?_of_indexOf? (j := 715) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_10_1 : Fn.body Data.core715 = sqLoopOf (osCfg10.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_10_1 : coreProgram.find? "__loop202" = some Data.core721 :=
  Program.find?_of_indexOf? (j := 721) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_10_1 : Fn.body Data.core721 = resLoopOf osCfg10 1 (osCfg10.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_10_2 : coreProgram.find? "__loop198" = some Data.core716 :=
  Program.find?_of_indexOf? (j := 716) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_10_2 : Fn.body Data.core716 = sqLoopOf (osCfg10.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_10_2 : coreProgram.find? "__loop203" = some Data.core722 :=
  Program.find?_of_indexOf? (j := 722) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_10_2 : Fn.body Data.core722 = resLoopOf osCfg10 2 (osCfg10.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_10_3 : coreProgram.find? "__loop199" = some Data.core717 :=
  Program.find?_of_indexOf? (j := 717) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_10_3 : Fn.body Data.core717 = sqLoopOf (osCfg10.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_10_3 : coreProgram.find? "__loop204" = some Data.core723 :=
  Program.find?_of_indexOf? (j := 723) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_10_3 : Fn.body Data.core723 = resLoopOf osCfg10 3 (osCfg10.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_10_4 : coreProgram.find? "__loop200" = some Data.core718 :=
  Program.find?_of_indexOf? (j := 718) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_10_4 : Fn.body Data.core718 = sqLoopOf (osCfg10.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_10_4 : coreProgram.find? "__loop205" = some Data.core724 :=
  Program.find?_of_indexOf? (j := 724) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_10_4 : Fn.body Data.core724 = resLoopOf osCfg10 4 (osCfg10.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_11 : coreProgram.find? "open_stacked__L11" = some Data.core188 :=
  Program.find?_of_indexOf? (j := 188) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_11 : Fn.body Data.core188 = osBody osCfg11 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_11_0 : coreProgram.find? "__loop206" = some Data.core725 :=
  Program.find?_of_indexOf? (j := 725) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_11_0 : Fn.body Data.core725 = sqLoopOf (osCfg11.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_11_0 : coreProgram.find? "__loop211" = some Data.core731 :=
  Program.find?_of_indexOf? (j := 731) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_11_0 : Fn.body Data.core731 = resLoopOf osCfg11 0 (osCfg11.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_11_1 : coreProgram.find? "__loop207" = some Data.core727 :=
  Program.find?_of_indexOf? (j := 727) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_11_1 : Fn.body Data.core727 = sqLoopOf (osCfg11.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_11_1 : coreProgram.find? "__loop212" = some Data.core732 :=
  Program.find?_of_indexOf? (j := 732) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_11_1 : Fn.body Data.core732 = resLoopOf osCfg11 1 (osCfg11.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_11_2 : coreProgram.find? "__loop208" = some Data.core728 :=
  Program.find?_of_indexOf? (j := 728) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_11_2 : Fn.body Data.core728 = sqLoopOf (osCfg11.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_11_2 : coreProgram.find? "__loop213" = some Data.core733 :=
  Program.find?_of_indexOf? (j := 733) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_11_2 : Fn.body Data.core733 = resLoopOf osCfg11 2 (osCfg11.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_11_3 : coreProgram.find? "__loop209" = some Data.core729 :=
  Program.find?_of_indexOf? (j := 729) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_11_3 : Fn.body Data.core729 = sqLoopOf (osCfg11.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_11_3 : coreProgram.find? "__loop214" = some Data.core734 :=
  Program.find?_of_indexOf? (j := 734) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_11_3 : Fn.body Data.core734 = resLoopOf osCfg11 3 (osCfg11.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_11_4 : coreProgram.find? "__loop210" = some Data.core730 :=
  Program.find?_of_indexOf? (j := 730) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_11_4 : Fn.body Data.core730 = sqLoopOf (osCfg11.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_11_4 : coreProgram.find? "__loop215" = some Data.core735 :=
  Program.find?_of_indexOf? (j := 735) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_11_4 : Fn.body Data.core735 = resLoopOf osCfg11 4 (osCfg11.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_12 : coreProgram.find? "open_stacked__L12" = some Data.core189 :=
  Program.find?_of_indexOf? (j := 189) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_12 : Fn.body Data.core189 = osBody osCfg12 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_12_0 : coreProgram.find? "__loop216" = some Data.core736 :=
  Program.find?_of_indexOf? (j := 736) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_12_0 : Fn.body Data.core736 = sqLoopOf (osCfg12.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_12_0 : coreProgram.find? "__loop221" = some Data.core743 :=
  Program.find?_of_indexOf? (j := 743) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_12_0 : Fn.body Data.core743 = resLoopOf osCfg12 0 (osCfg12.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_12_1 : coreProgram.find? "__loop217" = some Data.core738 :=
  Program.find?_of_indexOf? (j := 738) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_12_1 : Fn.body Data.core738 = sqLoopOf (osCfg12.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_12_1 : coreProgram.find? "__loop222" = some Data.core744 :=
  Program.find?_of_indexOf? (j := 744) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_12_1 : Fn.body Data.core744 = resLoopOf osCfg12 1 (osCfg12.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_12_2 : coreProgram.find? "__loop218" = some Data.core739 :=
  Program.find?_of_indexOf? (j := 739) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_12_2 : Fn.body Data.core739 = sqLoopOf (osCfg12.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_12_2 : coreProgram.find? "__loop223" = some Data.core745 :=
  Program.find?_of_indexOf? (j := 745) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_12_2 : Fn.body Data.core745 = resLoopOf osCfg12 2 (osCfg12.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_12_3 : coreProgram.find? "__loop219" = some Data.core740 :=
  Program.find?_of_indexOf? (j := 740) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_12_3 : Fn.body Data.core740 = sqLoopOf (osCfg12.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_12_3 : coreProgram.find? "__loop224" = some Data.core746 :=
  Program.find?_of_indexOf? (j := 746) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_12_3 : Fn.body Data.core746 = resLoopOf osCfg12 3 (osCfg12.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_12_4 : coreProgram.find? "__loop220" = some Data.core741 :=
  Program.find?_of_indexOf? (j := 741) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_12_4 : Fn.body Data.core741 = sqLoopOf (osCfg12.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_12_4 : coreProgram.find? "__loop225" = some Data.core747 :=
  Program.find?_of_indexOf? (j := 747) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_12_4 : Fn.body Data.core747 = resLoopOf osCfg12 4 (osCfg12.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_13 : coreProgram.find? "open_stacked__L13" = some Data.core190 :=
  Program.find?_of_indexOf? (j := 190) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_13 : Fn.body Data.core190 = osBody osCfg13 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_13_0 : coreProgram.find? "__loop226" = some Data.core748 :=
  Program.find?_of_indexOf? (j := 748) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_13_0 : Fn.body Data.core748 = sqLoopOf (osCfg13.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_13_0 : coreProgram.find? "__loop232" = some Data.core758 :=
  Program.find?_of_indexOf? (j := 758) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_13_0 : Fn.body Data.core758 = resLoopOf osCfg13 0 (osCfg13.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_13_1 : coreProgram.find? "__loop227" = some Data.core750 :=
  Program.find?_of_indexOf? (j := 750) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_13_1 : Fn.body Data.core750 = sqLoopOf (osCfg13.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_13_1 : coreProgram.find? "__loop233" = some Data.core759 :=
  Program.find?_of_indexOf? (j := 759) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_13_1 : Fn.body Data.core759 = resLoopOf osCfg13 1 (osCfg13.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_13_2 : coreProgram.find? "__loop228" = some Data.core752 :=
  Program.find?_of_indexOf? (j := 752) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_13_2 : Fn.body Data.core752 = sqLoopOf (osCfg13.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_13_2 : coreProgram.find? "__loop234" = some Data.core760 :=
  Program.find?_of_indexOf? (j := 760) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_13_2 : Fn.body Data.core760 = resLoopOf osCfg13 2 (osCfg13.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_13_3 : coreProgram.find? "__loop229" = some Data.core754 :=
  Program.find?_of_indexOf? (j := 754) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_13_3 : Fn.body Data.core754 = sqLoopOf (osCfg13.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_13_3 : coreProgram.find? "__loop235" = some Data.core761 :=
  Program.find?_of_indexOf? (j := 761) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_13_3 : Fn.body Data.core761 = resLoopOf osCfg13 3 (osCfg13.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_13_4 : coreProgram.find? "__loop230" = some Data.core755 :=
  Program.find?_of_indexOf? (j := 755) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_13_4 : Fn.body Data.core755 = sqLoopOf (osCfg13.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_13_4 : coreProgram.find? "__loop236" = some Data.core762 :=
  Program.find?_of_indexOf? (j := 762) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_13_4 : Fn.body Data.core762 = resLoopOf osCfg13 4 (osCfg13.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_13_5 : coreProgram.find? "__loop231" = some Data.core757 :=
  Program.find?_of_indexOf? (j := 757) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_13_5 : Fn.body Data.core757 = sqLoopOf (osCfg13.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_13_5 : coreProgram.find? "__loop237" = some Data.core763 :=
  Program.find?_of_indexOf? (j := 763) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_13_5 : Fn.body Data.core763 = resLoopOf osCfg13 5 (osCfg13.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
