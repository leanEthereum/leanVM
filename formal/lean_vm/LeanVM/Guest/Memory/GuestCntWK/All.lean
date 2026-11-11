/-
  LeanVM.Guest.Memory.GuestCntWK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWK.Part00
public import LeanVM.Guest.Memory.GuestCntWK.Part01
public import LeanVM.Guest.Memory.GuestCntWK.Part02
public import LeanVM.Guest.Memory.GuestCntWK.Part03
public import LeanVM.Guest.Memory.GuestCntWK.Part04
public import LeanVM.Guest.Memory.GuestCntWK.Part05
public import LeanVM.Guest.Memory.GuestCntWK.Part06
public import LeanVM.Guest.Memory.GuestCntWK.Part07
public import LeanVM.Guest.Memory.GuestCntWK.Part08
public import LeanVM.Guest.Memory.GuestCntWK.Part09

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 1752, kukchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kukstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kukstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kukstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kukstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kukstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kukstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kukstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kukstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kukstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kukstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 258
  · exact kukstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kukstaticRange_258.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kukstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kukstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kukstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kukstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 351
  · exact kukstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 381
  · exact kukstaticRange_351.get (by omega) (by omega)
  by_cases h18 : j < 411
  · exact kukstaticRange_381.get (by omega) (by omega)
  by_cases h19 : j < 441
  · exact kukstaticRange_411.get (by omega) (by omega)
  by_cases h20 : j < 471
  · exact kukstaticRange_441.get (by omega) (by omega)
  by_cases h21 : j < 501
  · exact kukstaticRange_471.get (by omega) (by omega)
  by_cases h22 : j < 531
  · exact kukstaticRange_501.get (by omega) (by omega)
  by_cases h23 : j < 561
  · exact kukstaticRange_531.get (by omega) (by omega)
  by_cases h24 : j < 591
  · exact kukstaticRange_561.get (by omega) (by omega)
  by_cases h25 : j < 621
  · exact kukstaticRange_591.get (by omega) (by omega)
  by_cases h26 : j < 651
  · exact kukstaticRange_621.get (by omega) (by omega)
  by_cases h27 : j < 681
  · exact kukstaticRange_651.get (by omega) (by omega)
  by_cases h28 : j < 711
  · exact kukstaticRange_681.get (by omega) (by omega)
  by_cases h29 : j < 741
  · exact kukstaticRange_711.get (by omega) (by omega)
  by_cases h30 : j < 771
  · exact kukstaticRange_741.get (by omega) (by omega)
  by_cases h31 : j < 801
  · exact kukstaticRange_771.get (by omega) (by omega)
  by_cases h32 : j < 831
  · exact kukstaticRange_801.get (by omega) (by omega)
  by_cases h33 : j < 861
  · exact kukstaticRange_831.get (by omega) (by omega)
  by_cases h34 : j < 891
  · exact kukstaticRange_861.get (by omega) (by omega)
  by_cases h35 : j < 921
  · exact kukstaticRange_891.get (by omega) (by omega)
  by_cases h36 : j < 951
  · exact kukstaticRange_921.get (by omega) (by omega)
  by_cases h37 : j < 981
  · exact kukstaticRange_951.get (by omega) (by omega)
  by_cases h38 : j < 1011
  · exact kukstaticRange_981.get (by omega) (by omega)
  by_cases h39 : j < 1041
  · exact kukstaticRange_1011.get (by omega) (by omega)
  by_cases h40 : j < 1071
  · exact kukstaticRange_1041.get (by omega) (by omega)
  by_cases h41 : j < 1101
  · exact kukstaticRange_1071.get (by omega) (by omega)
  by_cases h42 : j < 1131
  · exact kukstaticRange_1101.get (by omega) (by omega)
  by_cases h43 : j < 1161
  · exact kukstaticRange_1131.get (by omega) (by omega)
  by_cases h44 : j < 1191
  · exact kukstaticRange_1161.get (by omega) (by omega)
  by_cases h45 : j < 1221
  · exact kukstaticRange_1191.get (by omega) (by omega)
  by_cases h46 : j < 1251
  · exact kukstaticRange_1221.get (by omega) (by omega)
  by_cases h47 : j < 1281
  · exact kukstaticRange_1251.get (by omega) (by omega)
  by_cases h48 : j < 1311
  · exact kukstaticRange_1281.get (by omega) (by omega)
  by_cases h49 : j < 1341
  · exact kukstaticRange_1311.get (by omega) (by omega)
  by_cases h50 : j < 1371
  · exact kukstaticRange_1341.get (by omega) (by omega)
  by_cases h51 : j < 1401
  · exact kukstaticRange_1371.get (by omega) (by omega)
  by_cases h52 : j < 1431
  · exact kukstaticRange_1401.get (by omega) (by omega)
  by_cases h53 : j < 1461
  · exact kukstaticRange_1431.get (by omega) (by omega)
  by_cases h54 : j < 1491
  · exact kukstaticRange_1461.get (by omega) (by omega)
  by_cases h55 : j < 1521
  · exact kukstaticRange_1491.get (by omega) (by omega)
  by_cases h56 : j < 1551
  · exact kukstaticRange_1521.get (by omega) (by omega)
  by_cases h57 : j < 1581
  · exact kukstaticRange_1551.get (by omega) (by omega)
  by_cases h58 : j < 1611
  · exact kukstaticRange_1581.get (by omega) (by omega)
  by_cases h59 : j < 1641
  · exact kukstaticRange_1611.get (by omega) (by omega)
  by_cases h60 : j < 1671
  · exact kukstaticRange_1641.get (by omega) (by omega)
  by_cases h61 : j < 1701
  · exact kukstaticRange_1671.get (by omega) (by omega)
  by_cases h62 : j < 1731
  · exact kukstaticRange_1701.get (by omega) (by omega)
  exact kukstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
