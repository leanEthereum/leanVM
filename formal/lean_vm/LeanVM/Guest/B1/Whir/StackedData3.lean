/-
  LeanVM.Guest.B1.Whir.StackedData3

  The bodies of `open_stacked__L21` to `open_stacked__L27` and of their loop helpers, equal to
  their templates.
-/

module

public import LeanVM.Guest.B1.Whir.StackedCfg

/-!
# `open_stacked__L21` to `open_stacked__L27`, by kernel evaluation

Each body equal to its template (`stmtsEqb_sound`), with the function's and its loops' lookups.
-/

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section


set_option maxRecDepth 100000 in
theorem os_find_21 : coreProgram.find? "open_stacked__L21" = some Data.core198 :=
  Program.find?_of_indexOf? (j := 198) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_21 : Fn.body Data.core198 = osBody osCfg21 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_21_0 : coreProgram.find? "__loop306" = some Data.core836 :=
  Program.find?_of_indexOf? (j := 836) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_21_0 : Fn.body Data.core836 = sqLoopOf (osCfg21.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_21_0 : coreProgram.find? "__loop310" = some Data.core841 :=
  Program.find?_of_indexOf? (j := 841) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_21_0 : Fn.body Data.core841 = resLoopOf osCfg21 0 (osCfg21.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_21_1 : coreProgram.find? "__loop307" = some Data.core838 :=
  Program.find?_of_indexOf? (j := 838) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_21_1 : Fn.body Data.core838 = sqLoopOf (osCfg21.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_21_1 : coreProgram.find? "__loop311" = some Data.core842 :=
  Program.find?_of_indexOf? (j := 842) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_21_1 : Fn.body Data.core842 = resLoopOf osCfg21 1 (osCfg21.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_21_2 : coreProgram.find? "__loop308" = some Data.core839 :=
  Program.find?_of_indexOf? (j := 839) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_21_2 : Fn.body Data.core839 = sqLoopOf (osCfg21.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_21_2 : coreProgram.find? "__loop312" = some Data.core843 :=
  Program.find?_of_indexOf? (j := 843) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_21_2 : Fn.body Data.core843 = resLoopOf osCfg21 2 (osCfg21.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_21_3 : coreProgram.find? "__loop309" = some Data.core840 :=
  Program.find?_of_indexOf? (j := 840) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_21_3 : Fn.body Data.core840 = sqLoopOf (osCfg21.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_21_3 : coreProgram.find? "__loop313" = some Data.core844 :=
  Program.find?_of_indexOf? (j := 844) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_21_3 : Fn.body Data.core844 = resLoopOf osCfg21 3 (osCfg21.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_22 : coreProgram.find? "open_stacked__L22" = some Data.core199 :=
  Program.find?_of_indexOf? (j := 199) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_22 : Fn.body Data.core199 = osBody osCfg22 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_22_0 : coreProgram.find? "__loop314" = some Data.core845 :=
  Program.find?_of_indexOf? (j := 845) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_22_0 : Fn.body Data.core845 = sqLoopOf (osCfg22.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_22_0 : coreProgram.find? "__loop318" = some Data.core850 :=
  Program.find?_of_indexOf? (j := 850) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_22_0 : Fn.body Data.core850 = resLoopOf osCfg22 0 (osCfg22.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_22_1 : coreProgram.find? "__loop315" = some Data.core847 :=
  Program.find?_of_indexOf? (j := 847) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_22_1 : Fn.body Data.core847 = sqLoopOf (osCfg22.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_22_1 : coreProgram.find? "__loop319" = some Data.core851 :=
  Program.find?_of_indexOf? (j := 851) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_22_1 : Fn.body Data.core851 = resLoopOf osCfg22 1 (osCfg22.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_22_2 : coreProgram.find? "__loop316" = some Data.core848 :=
  Program.find?_of_indexOf? (j := 848) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_22_2 : Fn.body Data.core848 = sqLoopOf (osCfg22.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_22_2 : coreProgram.find? "__loop320" = some Data.core852 :=
  Program.find?_of_indexOf? (j := 852) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_22_2 : Fn.body Data.core852 = resLoopOf osCfg22 2 (osCfg22.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_22_3 : coreProgram.find? "__loop317" = some Data.core849 :=
  Program.find?_of_indexOf? (j := 849) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_22_3 : Fn.body Data.core849 = sqLoopOf (osCfg22.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_22_3 : coreProgram.find? "__loop321" = some Data.core853 :=
  Program.find?_of_indexOf? (j := 853) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_22_3 : Fn.body Data.core853 = resLoopOf osCfg22 3 (osCfg22.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_23 : coreProgram.find? "open_stacked__L23" = some Data.core200 :=
  Program.find?_of_indexOf? (j := 200) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_23 : Fn.body Data.core200 = osBody osCfg23 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_23_0 : coreProgram.find? "__loop322" = some Data.core854 :=
  Program.find?_of_indexOf? (j := 854) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_23_0 : Fn.body Data.core854 = sqLoopOf (osCfg23.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_23_0 : coreProgram.find? "__loop327" = some Data.core860 :=
  Program.find?_of_indexOf? (j := 860) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_23_0 : Fn.body Data.core860 = resLoopOf osCfg23 0 (osCfg23.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_23_1 : coreProgram.find? "__loop323" = some Data.core856 :=
  Program.find?_of_indexOf? (j := 856) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_23_1 : Fn.body Data.core856 = sqLoopOf (osCfg23.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_23_1 : coreProgram.find? "__loop328" = some Data.core861 :=
  Program.find?_of_indexOf? (j := 861) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_23_1 : Fn.body Data.core861 = resLoopOf osCfg23 1 (osCfg23.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_23_2 : coreProgram.find? "__loop324" = some Data.core857 :=
  Program.find?_of_indexOf? (j := 857) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_23_2 : Fn.body Data.core857 = sqLoopOf (osCfg23.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_23_2 : coreProgram.find? "__loop329" = some Data.core862 :=
  Program.find?_of_indexOf? (j := 862) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_23_2 : Fn.body Data.core862 = resLoopOf osCfg23 2 (osCfg23.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_23_3 : coreProgram.find? "__loop325" = some Data.core858 :=
  Program.find?_of_indexOf? (j := 858) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_23_3 : Fn.body Data.core858 = sqLoopOf (osCfg23.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_23_3 : coreProgram.find? "__loop330" = some Data.core863 :=
  Program.find?_of_indexOf? (j := 863) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_23_3 : Fn.body Data.core863 = resLoopOf osCfg23 3 (osCfg23.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_23_4 : coreProgram.find? "__loop326" = some Data.core859 :=
  Program.find?_of_indexOf? (j := 859) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_23_4 : Fn.body Data.core859 = sqLoopOf (osCfg23.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_23_4 : coreProgram.find? "__loop331" = some Data.core864 :=
  Program.find?_of_indexOf? (j := 864) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_23_4 : Fn.body Data.core864 = resLoopOf osCfg23 4 (osCfg23.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_24 : coreProgram.find? "open_stacked__L24" = some Data.core201 :=
  Program.find?_of_indexOf? (j := 201) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_24 : Fn.body Data.core201 = osBody osCfg24 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_24_0 : coreProgram.find? "__loop332" = some Data.core865 :=
  Program.find?_of_indexOf? (j := 865) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_24_0 : Fn.body Data.core865 = sqLoopOf (osCfg24.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_24_0 : coreProgram.find? "__loop337" = some Data.core871 :=
  Program.find?_of_indexOf? (j := 871) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_24_0 : Fn.body Data.core871 = resLoopOf osCfg24 0 (osCfg24.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_24_1 : coreProgram.find? "__loop333" = some Data.core867 :=
  Program.find?_of_indexOf? (j := 867) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_24_1 : Fn.body Data.core867 = sqLoopOf (osCfg24.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_24_1 : coreProgram.find? "__loop338" = some Data.core872 :=
  Program.find?_of_indexOf? (j := 872) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_24_1 : Fn.body Data.core872 = resLoopOf osCfg24 1 (osCfg24.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_24_2 : coreProgram.find? "__loop334" = some Data.core868 :=
  Program.find?_of_indexOf? (j := 868) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_24_2 : Fn.body Data.core868 = sqLoopOf (osCfg24.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_24_2 : coreProgram.find? "__loop339" = some Data.core873 :=
  Program.find?_of_indexOf? (j := 873) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_24_2 : Fn.body Data.core873 = resLoopOf osCfg24 2 (osCfg24.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_24_3 : coreProgram.find? "__loop335" = some Data.core869 :=
  Program.find?_of_indexOf? (j := 869) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_24_3 : Fn.body Data.core869 = sqLoopOf (osCfg24.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_24_3 : coreProgram.find? "__loop340" = some Data.core874 :=
  Program.find?_of_indexOf? (j := 874) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_24_3 : Fn.body Data.core874 = resLoopOf osCfg24 3 (osCfg24.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_24_4 : coreProgram.find? "__loop336" = some Data.core870 :=
  Program.find?_of_indexOf? (j := 870) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_24_4 : Fn.body Data.core870 = sqLoopOf (osCfg24.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_24_4 : coreProgram.find? "__loop341" = some Data.core875 :=
  Program.find?_of_indexOf? (j := 875) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_24_4 : Fn.body Data.core875 = resLoopOf osCfg24 4 (osCfg24.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_25 : coreProgram.find? "open_stacked__L25" = some Data.core202 :=
  Program.find?_of_indexOf? (j := 202) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_25 : Fn.body Data.core202 = osBody osCfg25 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_25_0 : coreProgram.find? "__loop342" = some Data.core876 :=
  Program.find?_of_indexOf? (j := 876) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_25_0 : Fn.body Data.core876 = sqLoopOf (osCfg25.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_25_0 : coreProgram.find? "__loop347" = some Data.core882 :=
  Program.find?_of_indexOf? (j := 882) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_25_0 : Fn.body Data.core882 = resLoopOf osCfg25 0 (osCfg25.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_25_1 : coreProgram.find? "__loop343" = some Data.core878 :=
  Program.find?_of_indexOf? (j := 878) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_25_1 : Fn.body Data.core878 = sqLoopOf (osCfg25.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_25_1 : coreProgram.find? "__loop348" = some Data.core883 :=
  Program.find?_of_indexOf? (j := 883) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_25_1 : Fn.body Data.core883 = resLoopOf osCfg25 1 (osCfg25.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_25_2 : coreProgram.find? "__loop344" = some Data.core879 :=
  Program.find?_of_indexOf? (j := 879) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_25_2 : Fn.body Data.core879 = sqLoopOf (osCfg25.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_25_2 : coreProgram.find? "__loop349" = some Data.core884 :=
  Program.find?_of_indexOf? (j := 884) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_25_2 : Fn.body Data.core884 = resLoopOf osCfg25 2 (osCfg25.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_25_3 : coreProgram.find? "__loop345" = some Data.core880 :=
  Program.find?_of_indexOf? (j := 880) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_25_3 : Fn.body Data.core880 = sqLoopOf (osCfg25.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_25_3 : coreProgram.find? "__loop350" = some Data.core885 :=
  Program.find?_of_indexOf? (j := 885) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_25_3 : Fn.body Data.core885 = resLoopOf osCfg25 3 (osCfg25.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_25_4 : coreProgram.find? "__loop346" = some Data.core881 :=
  Program.find?_of_indexOf? (j := 881) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_25_4 : Fn.body Data.core881 = sqLoopOf (osCfg25.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_25_4 : coreProgram.find? "__loop351" = some Data.core886 :=
  Program.find?_of_indexOf? (j := 886) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_25_4 : Fn.body Data.core886 = resLoopOf osCfg25 4 (osCfg25.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_26 : coreProgram.find? "open_stacked__L26" = some Data.core203 :=
  Program.find?_of_indexOf? (j := 203) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_26 : Fn.body Data.core203 = osBody osCfg26 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_26_0 : coreProgram.find? "__loop352" = some Data.core887 :=
  Program.find?_of_indexOf? (j := 887) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_26_0 : Fn.body Data.core887 = sqLoopOf (osCfg26.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_26_0 : coreProgram.find? "__loop357" = some Data.core894 :=
  Program.find?_of_indexOf? (j := 894) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_26_0 : Fn.body Data.core894 = resLoopOf osCfg26 0 (osCfg26.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_26_1 : coreProgram.find? "__loop353" = some Data.core889 :=
  Program.find?_of_indexOf? (j := 889) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_26_1 : Fn.body Data.core889 = sqLoopOf (osCfg26.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_26_1 : coreProgram.find? "__loop358" = some Data.core895 :=
  Program.find?_of_indexOf? (j := 895) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_26_1 : Fn.body Data.core895 = resLoopOf osCfg26 1 (osCfg26.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_26_2 : coreProgram.find? "__loop354" = some Data.core891 :=
  Program.find?_of_indexOf? (j := 891) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_26_2 : Fn.body Data.core891 = sqLoopOf (osCfg26.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_26_2 : coreProgram.find? "__loop359" = some Data.core896 :=
  Program.find?_of_indexOf? (j := 896) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_26_2 : Fn.body Data.core896 = resLoopOf osCfg26 2 (osCfg26.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_26_3 : coreProgram.find? "__loop355" = some Data.core892 :=
  Program.find?_of_indexOf? (j := 892) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_26_3 : Fn.body Data.core892 = sqLoopOf (osCfg26.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_26_3 : coreProgram.find? "__loop360" = some Data.core897 :=
  Program.find?_of_indexOf? (j := 897) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_26_3 : Fn.body Data.core897 = resLoopOf osCfg26 3 (osCfg26.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_26_4 : coreProgram.find? "__loop356" = some Data.core893 :=
  Program.find?_of_indexOf? (j := 893) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_26_4 : Fn.body Data.core893 = sqLoopOf (osCfg26.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_26_4 : coreProgram.find? "__loop361" = some Data.core898 :=
  Program.find?_of_indexOf? (j := 898) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_26_4 : Fn.body Data.core898 = resLoopOf osCfg26 4 (osCfg26.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_find_27 : coreProgram.find? "open_stacked__L27" = some Data.core204 :=
  Program.find?_of_indexOf? (j := 204) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_body_27 : Fn.body Data.core204 = osBody osCfg27 := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_27_0 : coreProgram.find? "__loop362" = some Data.core899 :=
  Program.find?_of_indexOf? (j := 899) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_27_0 : Fn.body Data.core899 = sqLoopOf (osCfg27.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_27_0 : coreProgram.find? "__loop368" = some Data.core908 :=
  Program.find?_of_indexOf? (j := 908) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_27_0 : Fn.body Data.core908 = resLoopOf osCfg27 0 (osCfg27.levels.getD 0 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_27_1 : coreProgram.find? "__loop363" = some Data.core901 :=
  Program.find?_of_indexOf? (j := 901) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_27_1 : Fn.body Data.core901 = sqLoopOf (osCfg27.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_27_1 : coreProgram.find? "__loop369" = some Data.core909 :=
  Program.find?_of_indexOf? (j := 909) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_27_1 : Fn.body Data.core909 = resLoopOf osCfg27 1 (osCfg27.levels.getD 1 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_27_2 : coreProgram.find? "__loop364" = some Data.core903 :=
  Program.find?_of_indexOf? (j := 903) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_27_2 : Fn.body Data.core903 = sqLoopOf (osCfg27.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_27_2 : coreProgram.find? "__loop370" = some Data.core910 :=
  Program.find?_of_indexOf? (j := 910) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_27_2 : Fn.body Data.core910 = resLoopOf osCfg27 2 (osCfg27.levels.getD 2 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_27_3 : coreProgram.find? "__loop365" = some Data.core904 :=
  Program.find?_of_indexOf? (j := 904) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_27_3 : Fn.body Data.core904 = sqLoopOf (osCfg27.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_27_3 : coreProgram.find? "__loop371" = some Data.core911 :=
  Program.find?_of_indexOf? (j := 911) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_27_3 : Fn.body Data.core911 = resLoopOf osCfg27 3 (osCfg27.levels.getD 3 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_27_4 : coreProgram.find? "__loop366" = some Data.core905 :=
  Program.find?_of_indexOf? (j := 905) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_27_4 : Fn.body Data.core905 = sqLoopOf (osCfg27.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_27_4 : coreProgram.find? "__loop372" = some Data.core912 :=
  Program.find?_of_indexOf? (j := 912) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_27_4 : Fn.body Data.core912 = resLoopOf osCfg27 4 (osCfg27.levels.getD 4 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_sq_find_27_5 : coreProgram.find? "__loop367" = some Data.core907 :=
  Program.find?_of_indexOf? (j := 907) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_sq_body_27_5 : Fn.body Data.core907 = sqLoopOf (osCfg27.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem os_res_find_27_5 : coreProgram.find? "__loop373" = some Data.core913 :=
  Program.find?_of_indexOf? (j := 913) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem os_res_body_27_5 : Fn.body Data.core913 = resLoopOf osCfg27 5 (osCfg27.levels.getD 5 default) :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
