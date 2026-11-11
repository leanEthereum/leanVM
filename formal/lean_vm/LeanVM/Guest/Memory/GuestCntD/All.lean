/-
  LeanVM.Guest.Memory.GuestCntD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntD.Part00
public import LeanVM.Guest.Memory.GuestCntD.Part01
public import LeanVM.Guest.Memory.GuestCntD.Part02
public import LeanVM.Guest.Memory.GuestCntD.Part03
public import LeanVM.Guest.Memory.GuestCntD.Part04
public import LeanVM.Guest.Memory.GuestCntD.Part05
public import LeanVM.Guest.Memory.GuestCntD.Part06
public import LeanVM.Guest.Memory.GuestCntD.Part07
public import LeanVM.Guest.Memory.GuestCntD.Part08
public import LeanVM.Guest.Memory.GuestCntD.Part09
public import LeanVM.Guest.Memory.GuestCntD.Part10
public import LeanVM.Guest.Memory.GuestCntD.Part11

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdchkIdx_19 : kwdchkIdx 19 = true := by
  have hb : blockB (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwdsplit_19_0.1 rfl kwdsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwdsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwdsplit_19_96]
    rfl
  exact kwdchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwdchkIdx_all : ∀ j < 1752, kwdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwdchkIdx_19
  by_cases h0 : j < 11
  · exact kwdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwdstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwdstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwdstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwdstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwdstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwdstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwdstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwdstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwdstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwdstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwdstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwdstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwdstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 313
  · exact kwdstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 316
  · exact kwdstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 319
  · exact kwdstaticRange_316.get (by omega) (by omega)
  by_cases h17 : j < 321
  · exact kwdstaticRange_319.get (by omega) (by omega)
  by_cases h18 : j < 351
  · exact kwdstaticRange_321.get (by omega) (by omega)
  by_cases h19 : j < 381
  · exact kwdstaticRange_351.get (by omega) (by omega)
  by_cases h20 : j < 411
  · exact kwdstaticRange_381.get (by omega) (by omega)
  by_cases h21 : j < 441
  · exact kwdstaticRange_411.get (by omega) (by omega)
  by_cases h22 : j < 471
  · exact kwdstaticRange_441.get (by omega) (by omega)
  by_cases h23 : j < 501
  · exact kwdstaticRange_471.get (by omega) (by omega)
  by_cases h24 : j < 531
  · exact kwdstaticRange_501.get (by omega) (by omega)
  by_cases h25 : j < 561
  · exact kwdstaticRange_531.get (by omega) (by omega)
  by_cases h26 : j < 591
  · exact kwdstaticRange_561.get (by omega) (by omega)
  by_cases h27 : j < 621
  · exact kwdstaticRange_591.get (by omega) (by omega)
  by_cases h28 : j < 651
  · exact kwdstaticRange_621.get (by omega) (by omega)
  by_cases h29 : j < 681
  · exact kwdstaticRange_651.get (by omega) (by omega)
  by_cases h30 : j < 711
  · exact kwdstaticRange_681.get (by omega) (by omega)
  by_cases h31 : j < 741
  · exact kwdstaticRange_711.get (by omega) (by omega)
  by_cases h32 : j < 771
  · exact kwdstaticRange_741.get (by omega) (by omega)
  by_cases h33 : j < 801
  · exact kwdstaticRange_771.get (by omega) (by omega)
  by_cases h34 : j < 831
  · exact kwdstaticRange_801.get (by omega) (by omega)
  by_cases h35 : j < 861
  · exact kwdstaticRange_831.get (by omega) (by omega)
  by_cases h36 : j < 891
  · exact kwdstaticRange_861.get (by omega) (by omega)
  by_cases h37 : j < 921
  · exact kwdstaticRange_891.get (by omega) (by omega)
  by_cases h38 : j < 951
  · exact kwdstaticRange_921.get (by omega) (by omega)
  by_cases h39 : j < 981
  · exact kwdstaticRange_951.get (by omega) (by omega)
  by_cases h40 : j < 1011
  · exact kwdstaticRange_981.get (by omega) (by omega)
  by_cases h41 : j < 1041
  · exact kwdstaticRange_1011.get (by omega) (by omega)
  by_cases h42 : j < 1071
  · exact kwdstaticRange_1041.get (by omega) (by omega)
  by_cases h43 : j < 1101
  · exact kwdstaticRange_1071.get (by omega) (by omega)
  by_cases h44 : j < 1131
  · exact kwdstaticRange_1101.get (by omega) (by omega)
  by_cases h45 : j < 1161
  · exact kwdstaticRange_1131.get (by omega) (by omega)
  by_cases h46 : j < 1191
  · exact kwdstaticRange_1161.get (by omega) (by omega)
  by_cases h47 : j < 1221
  · exact kwdstaticRange_1191.get (by omega) (by omega)
  by_cases h48 : j < 1251
  · exact kwdstaticRange_1221.get (by omega) (by omega)
  by_cases h49 : j < 1281
  · exact kwdstaticRange_1251.get (by omega) (by omega)
  by_cases h50 : j < 1311
  · exact kwdstaticRange_1281.get (by omega) (by omega)
  by_cases h51 : j < 1341
  · exact kwdstaticRange_1311.get (by omega) (by omega)
  by_cases h52 : j < 1371
  · exact kwdstaticRange_1341.get (by omega) (by omega)
  by_cases h53 : j < 1401
  · exact kwdstaticRange_1371.get (by omega) (by omega)
  by_cases h54 : j < 1431
  · exact kwdstaticRange_1401.get (by omega) (by omega)
  by_cases h55 : j < 1461
  · exact kwdstaticRange_1431.get (by omega) (by omega)
  by_cases h56 : j < 1491
  · exact kwdstaticRange_1461.get (by omega) (by omega)
  by_cases h57 : j < 1521
  · exact kwdstaticRange_1491.get (by omega) (by omega)
  by_cases h58 : j < 1551
  · exact kwdstaticRange_1521.get (by omega) (by omega)
  by_cases h59 : j < 1581
  · exact kwdstaticRange_1551.get (by omega) (by omega)
  by_cases h60 : j < 1611
  · exact kwdstaticRange_1581.get (by omega) (by omega)
  by_cases h61 : j < 1641
  · exact kwdstaticRange_1611.get (by omega) (by omega)
  by_cases h62 : j < 1671
  · exact kwdstaticRange_1641.get (by omega) (by omega)
  by_cases h63 : j < 1701
  · exact kwdstaticRange_1671.get (by omega) (by omega)
  by_cases h64 : j < 1731
  · exact kwdstaticRange_1701.get (by omega) (by omega)
  exact kwdstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
