/-
  LeanVM.Guest.Memory.GuestCntM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntM.Part00
public import LeanVM.Guest.Memory.GuestCntM.Part01
public import LeanVM.Guest.Memory.GuestCntM.Part02
public import LeanVM.Guest.Memory.GuestCntM.Part03
public import LeanVM.Guest.Memory.GuestCntM.Part04
public import LeanVM.Guest.Memory.GuestCntM.Part05
public import LeanVM.Guest.Memory.GuestCntM.Part06
public import LeanVM.Guest.Memory.GuestCntM.Part07
public import LeanVM.Guest.Memory.GuestCntM.Part08
public import LeanVM.Guest.Memory.GuestCntM.Part09
public import LeanVM.Guest.Memory.GuestCntM.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmchkIdx_19 : kwmchkIdx 19 = true := by
  have hb : blockB (kwmlookJ 19) (kwmomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwmsplit_19_0.1 rfl kwmsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwmsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwmsplit_19_96]
    rfl
  exact kwmchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwmchkIdx_all : ∀ j < 1535, kwmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwmchkIdx_19
  by_cases h0 : j < 11
  · exact kwmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwmstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwmstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwmstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwmstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwmstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwmstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwmstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwmstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwmstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwmstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwmstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwmstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwmstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kwmstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 313
  · exact kwmstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kwmstaticRange_313.get (by omega) (by omega)
  by_cases h17 : j < 346
  · exact kwmstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 376
  · exact kwmstaticRange_346.get (by omega) (by omega)
  by_cases h19 : j < 406
  · exact kwmstaticRange_376.get (by omega) (by omega)
  by_cases h20 : j < 436
  · exact kwmstaticRange_406.get (by omega) (by omega)
  by_cases h21 : j < 466
  · exact kwmstaticRange_436.get (by omega) (by omega)
  by_cases h22 : j < 496
  · exact kwmstaticRange_466.get (by omega) (by omega)
  by_cases h23 : j < 526
  · exact kwmstaticRange_496.get (by omega) (by omega)
  by_cases h24 : j < 556
  · exact kwmstaticRange_526.get (by omega) (by omega)
  by_cases h25 : j < 586
  · exact kwmstaticRange_556.get (by omega) (by omega)
  by_cases h26 : j < 616
  · exact kwmstaticRange_586.get (by omega) (by omega)
  by_cases h27 : j < 646
  · exact kwmstaticRange_616.get (by omega) (by omega)
  by_cases h28 : j < 676
  · exact kwmstaticRange_646.get (by omega) (by omega)
  by_cases h29 : j < 706
  · exact kwmstaticRange_676.get (by omega) (by omega)
  by_cases h30 : j < 736
  · exact kwmstaticRange_706.get (by omega) (by omega)
  by_cases h31 : j < 766
  · exact kwmstaticRange_736.get (by omega) (by omega)
  by_cases h32 : j < 796
  · exact kwmstaticRange_766.get (by omega) (by omega)
  by_cases h33 : j < 826
  · exact kwmstaticRange_796.get (by omega) (by omega)
  by_cases h34 : j < 856
  · exact kwmstaticRange_826.get (by omega) (by omega)
  by_cases h35 : j < 886
  · exact kwmstaticRange_856.get (by omega) (by omega)
  by_cases h36 : j < 916
  · exact kwmstaticRange_886.get (by omega) (by omega)
  by_cases h37 : j < 946
  · exact kwmstaticRange_916.get (by omega) (by omega)
  by_cases h38 : j < 976
  · exact kwmstaticRange_946.get (by omega) (by omega)
  by_cases h39 : j < 1006
  · exact kwmstaticRange_976.get (by omega) (by omega)
  by_cases h40 : j < 1036
  · exact kwmstaticRange_1006.get (by omega) (by omega)
  by_cases h41 : j < 1066
  · exact kwmstaticRange_1036.get (by omega) (by omega)
  by_cases h42 : j < 1096
  · exact kwmstaticRange_1066.get (by omega) (by omega)
  by_cases h43 : j < 1126
  · exact kwmstaticRange_1096.get (by omega) (by omega)
  by_cases h44 : j < 1156
  · exact kwmstaticRange_1126.get (by omega) (by omega)
  by_cases h45 : j < 1186
  · exact kwmstaticRange_1156.get (by omega) (by omega)
  by_cases h46 : j < 1216
  · exact kwmstaticRange_1186.get (by omega) (by omega)
  by_cases h47 : j < 1246
  · exact kwmstaticRange_1216.get (by omega) (by omega)
  by_cases h48 : j < 1276
  · exact kwmstaticRange_1246.get (by omega) (by omega)
  by_cases h49 : j < 1306
  · exact kwmstaticRange_1276.get (by omega) (by omega)
  by_cases h50 : j < 1336
  · exact kwmstaticRange_1306.get (by omega) (by omega)
  by_cases h51 : j < 1366
  · exact kwmstaticRange_1336.get (by omega) (by omega)
  by_cases h52 : j < 1396
  · exact kwmstaticRange_1366.get (by omega) (by omega)
  by_cases h53 : j < 1426
  · exact kwmstaticRange_1396.get (by omega) (by omega)
  by_cases h54 : j < 1456
  · exact kwmstaticRange_1426.get (by omega) (by omega)
  by_cases h55 : j < 1486
  · exact kwmstaticRange_1456.get (by omega) (by omega)
  by_cases h56 : j < 1516
  · exact kwmstaticRange_1486.get (by omega) (by omega)
  exact kwmstaticRange_1516.get (by omega) (by omega)

end
end LeanVM.Guest
