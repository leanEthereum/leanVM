/-
  LeanVM.Guest.Memory.GuestCntJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntJ.Part00
public import LeanVM.Guest.Memory.GuestCntJ.Part01
public import LeanVM.Guest.Memory.GuestCntJ.Part02
public import LeanVM.Guest.Memory.GuestCntJ.Part03
public import LeanVM.Guest.Memory.GuestCntJ.Part04
public import LeanVM.Guest.Memory.GuestCntJ.Part05
public import LeanVM.Guest.Memory.GuestCntJ.Part06
public import LeanVM.Guest.Memory.GuestCntJ.Part07
public import LeanVM.Guest.Memory.GuestCntJ.Part08
public import LeanVM.Guest.Memory.GuestCntJ.Part09
public import LeanVM.Guest.Memory.GuestCntJ.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjchkIdx_19 : kwjchkIdx 19 = true := by
  have hb : blockB (kwjlookJ 19) (kwjomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwjsplit_19_0.1 rfl kwjsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwjsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwjsplit_19_96]
    rfl
  exact kwjchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwjchkIdx_all : ∀ j < 1535, kwjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwjchkIdx_19
  by_cases h0 : j < 11
  · exact kwjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwjstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwjstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwjstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwjstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwjstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwjstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwjstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwjstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwjstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwjstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwjstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwjstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kwjstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 313
  · exact kwjstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kwjstaticRange_313.get (by omega) (by omega)
  by_cases h17 : j < 346
  · exact kwjstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 376
  · exact kwjstaticRange_346.get (by omega) (by omega)
  by_cases h19 : j < 406
  · exact kwjstaticRange_376.get (by omega) (by omega)
  by_cases h20 : j < 436
  · exact kwjstaticRange_406.get (by omega) (by omega)
  by_cases h21 : j < 466
  · exact kwjstaticRange_436.get (by omega) (by omega)
  by_cases h22 : j < 496
  · exact kwjstaticRange_466.get (by omega) (by omega)
  by_cases h23 : j < 526
  · exact kwjstaticRange_496.get (by omega) (by omega)
  by_cases h24 : j < 556
  · exact kwjstaticRange_526.get (by omega) (by omega)
  by_cases h25 : j < 586
  · exact kwjstaticRange_556.get (by omega) (by omega)
  by_cases h26 : j < 616
  · exact kwjstaticRange_586.get (by omega) (by omega)
  by_cases h27 : j < 646
  · exact kwjstaticRange_616.get (by omega) (by omega)
  by_cases h28 : j < 676
  · exact kwjstaticRange_646.get (by omega) (by omega)
  by_cases h29 : j < 706
  · exact kwjstaticRange_676.get (by omega) (by omega)
  by_cases h30 : j < 736
  · exact kwjstaticRange_706.get (by omega) (by omega)
  by_cases h31 : j < 766
  · exact kwjstaticRange_736.get (by omega) (by omega)
  by_cases h32 : j < 796
  · exact kwjstaticRange_766.get (by omega) (by omega)
  by_cases h33 : j < 826
  · exact kwjstaticRange_796.get (by omega) (by omega)
  by_cases h34 : j < 856
  · exact kwjstaticRange_826.get (by omega) (by omega)
  by_cases h35 : j < 886
  · exact kwjstaticRange_856.get (by omega) (by omega)
  by_cases h36 : j < 916
  · exact kwjstaticRange_886.get (by omega) (by omega)
  by_cases h37 : j < 946
  · exact kwjstaticRange_916.get (by omega) (by omega)
  by_cases h38 : j < 976
  · exact kwjstaticRange_946.get (by omega) (by omega)
  by_cases h39 : j < 1006
  · exact kwjstaticRange_976.get (by omega) (by omega)
  by_cases h40 : j < 1036
  · exact kwjstaticRange_1006.get (by omega) (by omega)
  by_cases h41 : j < 1066
  · exact kwjstaticRange_1036.get (by omega) (by omega)
  by_cases h42 : j < 1096
  · exact kwjstaticRange_1066.get (by omega) (by omega)
  by_cases h43 : j < 1126
  · exact kwjstaticRange_1096.get (by omega) (by omega)
  by_cases h44 : j < 1156
  · exact kwjstaticRange_1126.get (by omega) (by omega)
  by_cases h45 : j < 1186
  · exact kwjstaticRange_1156.get (by omega) (by omega)
  by_cases h46 : j < 1216
  · exact kwjstaticRange_1186.get (by omega) (by omega)
  by_cases h47 : j < 1246
  · exact kwjstaticRange_1216.get (by omega) (by omega)
  by_cases h48 : j < 1276
  · exact kwjstaticRange_1246.get (by omega) (by omega)
  by_cases h49 : j < 1306
  · exact kwjstaticRange_1276.get (by omega) (by omega)
  by_cases h50 : j < 1336
  · exact kwjstaticRange_1306.get (by omega) (by omega)
  by_cases h51 : j < 1366
  · exact kwjstaticRange_1336.get (by omega) (by omega)
  by_cases h52 : j < 1396
  · exact kwjstaticRange_1366.get (by omega) (by omega)
  by_cases h53 : j < 1426
  · exact kwjstaticRange_1396.get (by omega) (by omega)
  by_cases h54 : j < 1456
  · exact kwjstaticRange_1426.get (by omega) (by omega)
  by_cases h55 : j < 1486
  · exact kwjstaticRange_1456.get (by omega) (by omega)
  by_cases h56 : j < 1516
  · exact kwjstaticRange_1486.get (by omega) (by omega)
  exact kwjstaticRange_1516.get (by omega) (by omega)

end
end LeanVM.Guest
