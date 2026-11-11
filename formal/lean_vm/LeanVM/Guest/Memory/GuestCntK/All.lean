/-
  LeanVM.Guest.Memory.GuestCntK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntK.Part00
public import LeanVM.Guest.Memory.GuestCntK.Part01
public import LeanVM.Guest.Memory.GuestCntK.Part02
public import LeanVM.Guest.Memory.GuestCntK.Part03
public import LeanVM.Guest.Memory.GuestCntK.Part04
public import LeanVM.Guest.Memory.GuestCntK.Part05
public import LeanVM.Guest.Memory.GuestCntK.Part06
public import LeanVM.Guest.Memory.GuestCntK.Part07
public import LeanVM.Guest.Memory.GuestCntK.Part08
public import LeanVM.Guest.Memory.GuestCntK.Part09
public import LeanVM.Guest.Memory.GuestCntK.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkchkIdx_19 : kwkchkIdx 19 = true := by
  have hb : blockB (kwklookJ 19) (kwkomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwksplit_19_0.1 rfl kwksplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwksplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwksplit_19_96]
    rfl
  exact kwkchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwkchkIdx_all : ∀ j < 1535, kwkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwkchkIdx_19
  by_cases h0 : j < 11
  · exact kwkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwkstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwkstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwkstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwkstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwkstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwkstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwkstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwkstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwkstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwkstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwkstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwkstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwkstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kwkstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 313
  · exact kwkstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kwkstaticRange_313.get (by omega) (by omega)
  by_cases h17 : j < 346
  · exact kwkstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 376
  · exact kwkstaticRange_346.get (by omega) (by omega)
  by_cases h19 : j < 406
  · exact kwkstaticRange_376.get (by omega) (by omega)
  by_cases h20 : j < 436
  · exact kwkstaticRange_406.get (by omega) (by omega)
  by_cases h21 : j < 466
  · exact kwkstaticRange_436.get (by omega) (by omega)
  by_cases h22 : j < 496
  · exact kwkstaticRange_466.get (by omega) (by omega)
  by_cases h23 : j < 526
  · exact kwkstaticRange_496.get (by omega) (by omega)
  by_cases h24 : j < 556
  · exact kwkstaticRange_526.get (by omega) (by omega)
  by_cases h25 : j < 586
  · exact kwkstaticRange_556.get (by omega) (by omega)
  by_cases h26 : j < 616
  · exact kwkstaticRange_586.get (by omega) (by omega)
  by_cases h27 : j < 646
  · exact kwkstaticRange_616.get (by omega) (by omega)
  by_cases h28 : j < 676
  · exact kwkstaticRange_646.get (by omega) (by omega)
  by_cases h29 : j < 706
  · exact kwkstaticRange_676.get (by omega) (by omega)
  by_cases h30 : j < 736
  · exact kwkstaticRange_706.get (by omega) (by omega)
  by_cases h31 : j < 766
  · exact kwkstaticRange_736.get (by omega) (by omega)
  by_cases h32 : j < 796
  · exact kwkstaticRange_766.get (by omega) (by omega)
  by_cases h33 : j < 826
  · exact kwkstaticRange_796.get (by omega) (by omega)
  by_cases h34 : j < 856
  · exact kwkstaticRange_826.get (by omega) (by omega)
  by_cases h35 : j < 886
  · exact kwkstaticRange_856.get (by omega) (by omega)
  by_cases h36 : j < 916
  · exact kwkstaticRange_886.get (by omega) (by omega)
  by_cases h37 : j < 946
  · exact kwkstaticRange_916.get (by omega) (by omega)
  by_cases h38 : j < 976
  · exact kwkstaticRange_946.get (by omega) (by omega)
  by_cases h39 : j < 1006
  · exact kwkstaticRange_976.get (by omega) (by omega)
  by_cases h40 : j < 1036
  · exact kwkstaticRange_1006.get (by omega) (by omega)
  by_cases h41 : j < 1066
  · exact kwkstaticRange_1036.get (by omega) (by omega)
  by_cases h42 : j < 1096
  · exact kwkstaticRange_1066.get (by omega) (by omega)
  by_cases h43 : j < 1126
  · exact kwkstaticRange_1096.get (by omega) (by omega)
  by_cases h44 : j < 1156
  · exact kwkstaticRange_1126.get (by omega) (by omega)
  by_cases h45 : j < 1186
  · exact kwkstaticRange_1156.get (by omega) (by omega)
  by_cases h46 : j < 1216
  · exact kwkstaticRange_1186.get (by omega) (by omega)
  by_cases h47 : j < 1246
  · exact kwkstaticRange_1216.get (by omega) (by omega)
  by_cases h48 : j < 1276
  · exact kwkstaticRange_1246.get (by omega) (by omega)
  by_cases h49 : j < 1306
  · exact kwkstaticRange_1276.get (by omega) (by omega)
  by_cases h50 : j < 1336
  · exact kwkstaticRange_1306.get (by omega) (by omega)
  by_cases h51 : j < 1366
  · exact kwkstaticRange_1336.get (by omega) (by omega)
  by_cases h52 : j < 1396
  · exact kwkstaticRange_1366.get (by omega) (by omega)
  by_cases h53 : j < 1426
  · exact kwkstaticRange_1396.get (by omega) (by omega)
  by_cases h54 : j < 1456
  · exact kwkstaticRange_1426.get (by omega) (by omega)
  by_cases h55 : j < 1486
  · exact kwkstaticRange_1456.get (by omega) (by omega)
  by_cases h56 : j < 1516
  · exact kwkstaticRange_1486.get (by omega) (by omega)
  exact kwkstaticRange_1516.get (by omega) (by omega)

end
end LeanVM.Guest
