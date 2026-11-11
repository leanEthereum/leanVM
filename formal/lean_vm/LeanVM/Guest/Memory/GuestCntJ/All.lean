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
public import LeanVM.Guest.Memory.GuestCntJ.Part11

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

theorem kwjchkIdx_all : ∀ j < 1752, kwjchkIdx j = true := by
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
  by_cases h14 : j < 313
  · exact kwjstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 316
  · exact kwjstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 319
  · exact kwjstaticRange_316.get (by omega) (by omega)
  by_cases h17 : j < 321
  · exact kwjstaticRange_319.get (by omega) (by omega)
  by_cases h18 : j < 351
  · exact kwjstaticRange_321.get (by omega) (by omega)
  by_cases h19 : j < 381
  · exact kwjstaticRange_351.get (by omega) (by omega)
  by_cases h20 : j < 411
  · exact kwjstaticRange_381.get (by omega) (by omega)
  by_cases h21 : j < 441
  · exact kwjstaticRange_411.get (by omega) (by omega)
  by_cases h22 : j < 471
  · exact kwjstaticRange_441.get (by omega) (by omega)
  by_cases h23 : j < 501
  · exact kwjstaticRange_471.get (by omega) (by omega)
  by_cases h24 : j < 531
  · exact kwjstaticRange_501.get (by omega) (by omega)
  by_cases h25 : j < 561
  · exact kwjstaticRange_531.get (by omega) (by omega)
  by_cases h26 : j < 591
  · exact kwjstaticRange_561.get (by omega) (by omega)
  by_cases h27 : j < 621
  · exact kwjstaticRange_591.get (by omega) (by omega)
  by_cases h28 : j < 651
  · exact kwjstaticRange_621.get (by omega) (by omega)
  by_cases h29 : j < 681
  · exact kwjstaticRange_651.get (by omega) (by omega)
  by_cases h30 : j < 711
  · exact kwjstaticRange_681.get (by omega) (by omega)
  by_cases h31 : j < 741
  · exact kwjstaticRange_711.get (by omega) (by omega)
  by_cases h32 : j < 771
  · exact kwjstaticRange_741.get (by omega) (by omega)
  by_cases h33 : j < 801
  · exact kwjstaticRange_771.get (by omega) (by omega)
  by_cases h34 : j < 831
  · exact kwjstaticRange_801.get (by omega) (by omega)
  by_cases h35 : j < 861
  · exact kwjstaticRange_831.get (by omega) (by omega)
  by_cases h36 : j < 891
  · exact kwjstaticRange_861.get (by omega) (by omega)
  by_cases h37 : j < 921
  · exact kwjstaticRange_891.get (by omega) (by omega)
  by_cases h38 : j < 951
  · exact kwjstaticRange_921.get (by omega) (by omega)
  by_cases h39 : j < 981
  · exact kwjstaticRange_951.get (by omega) (by omega)
  by_cases h40 : j < 1011
  · exact kwjstaticRange_981.get (by omega) (by omega)
  by_cases h41 : j < 1041
  · exact kwjstaticRange_1011.get (by omega) (by omega)
  by_cases h42 : j < 1071
  · exact kwjstaticRange_1041.get (by omega) (by omega)
  by_cases h43 : j < 1101
  · exact kwjstaticRange_1071.get (by omega) (by omega)
  by_cases h44 : j < 1131
  · exact kwjstaticRange_1101.get (by omega) (by omega)
  by_cases h45 : j < 1161
  · exact kwjstaticRange_1131.get (by omega) (by omega)
  by_cases h46 : j < 1191
  · exact kwjstaticRange_1161.get (by omega) (by omega)
  by_cases h47 : j < 1221
  · exact kwjstaticRange_1191.get (by omega) (by omega)
  by_cases h48 : j < 1251
  · exact kwjstaticRange_1221.get (by omega) (by omega)
  by_cases h49 : j < 1281
  · exact kwjstaticRange_1251.get (by omega) (by omega)
  by_cases h50 : j < 1311
  · exact kwjstaticRange_1281.get (by omega) (by omega)
  by_cases h51 : j < 1341
  · exact kwjstaticRange_1311.get (by omega) (by omega)
  by_cases h52 : j < 1371
  · exact kwjstaticRange_1341.get (by omega) (by omega)
  by_cases h53 : j < 1401
  · exact kwjstaticRange_1371.get (by omega) (by omega)
  by_cases h54 : j < 1431
  · exact kwjstaticRange_1401.get (by omega) (by omega)
  by_cases h55 : j < 1461
  · exact kwjstaticRange_1431.get (by omega) (by omega)
  by_cases h56 : j < 1491
  · exact kwjstaticRange_1461.get (by omega) (by omega)
  by_cases h57 : j < 1521
  · exact kwjstaticRange_1491.get (by omega) (by omega)
  by_cases h58 : j < 1551
  · exact kwjstaticRange_1521.get (by omega) (by omega)
  by_cases h59 : j < 1581
  · exact kwjstaticRange_1551.get (by omega) (by omega)
  by_cases h60 : j < 1611
  · exact kwjstaticRange_1581.get (by omega) (by omega)
  by_cases h61 : j < 1641
  · exact kwjstaticRange_1611.get (by omega) (by omega)
  by_cases h62 : j < 1671
  · exact kwjstaticRange_1641.get (by omega) (by omega)
  by_cases h63 : j < 1701
  · exact kwjstaticRange_1671.get (by omega) (by omega)
  by_cases h64 : j < 1731
  · exact kwjstaticRange_1701.get (by omega) (by omega)
  exact kwjstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
