/-
  LeanVM.Guest.Memory.GuestCntWM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWM.Part00
public import LeanVM.Guest.Memory.GuestCntWM.Part01
public import LeanVM.Guest.Memory.GuestCntWM.Part02
public import LeanVM.Guest.Memory.GuestCntWM.Part03
public import LeanVM.Guest.Memory.GuestCntWM.Part04
public import LeanVM.Guest.Memory.GuestCntWM.Part05
public import LeanVM.Guest.Memory.GuestCntWM.Part06
public import LeanVM.Guest.Memory.GuestCntWM.Part07
public import LeanVM.Guest.Memory.GuestCntWM.Part08
public import LeanVM.Guest.Memory.GuestCntWM.Part09

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 1752, kumchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kumstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kumstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kumstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kumstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kumstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kumstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kumstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kumstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kumstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kumstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 258
  · exact kumstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kumstaticRange_258.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kumstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kumstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kumstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kumstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 351
  · exact kumstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 381
  · exact kumstaticRange_351.get (by omega) (by omega)
  by_cases h18 : j < 411
  · exact kumstaticRange_381.get (by omega) (by omega)
  by_cases h19 : j < 441
  · exact kumstaticRange_411.get (by omega) (by omega)
  by_cases h20 : j < 471
  · exact kumstaticRange_441.get (by omega) (by omega)
  by_cases h21 : j < 501
  · exact kumstaticRange_471.get (by omega) (by omega)
  by_cases h22 : j < 531
  · exact kumstaticRange_501.get (by omega) (by omega)
  by_cases h23 : j < 561
  · exact kumstaticRange_531.get (by omega) (by omega)
  by_cases h24 : j < 591
  · exact kumstaticRange_561.get (by omega) (by omega)
  by_cases h25 : j < 621
  · exact kumstaticRange_591.get (by omega) (by omega)
  by_cases h26 : j < 651
  · exact kumstaticRange_621.get (by omega) (by omega)
  by_cases h27 : j < 681
  · exact kumstaticRange_651.get (by omega) (by omega)
  by_cases h28 : j < 711
  · exact kumstaticRange_681.get (by omega) (by omega)
  by_cases h29 : j < 741
  · exact kumstaticRange_711.get (by omega) (by omega)
  by_cases h30 : j < 771
  · exact kumstaticRange_741.get (by omega) (by omega)
  by_cases h31 : j < 801
  · exact kumstaticRange_771.get (by omega) (by omega)
  by_cases h32 : j < 831
  · exact kumstaticRange_801.get (by omega) (by omega)
  by_cases h33 : j < 861
  · exact kumstaticRange_831.get (by omega) (by omega)
  by_cases h34 : j < 891
  · exact kumstaticRange_861.get (by omega) (by omega)
  by_cases h35 : j < 921
  · exact kumstaticRange_891.get (by omega) (by omega)
  by_cases h36 : j < 951
  · exact kumstaticRange_921.get (by omega) (by omega)
  by_cases h37 : j < 981
  · exact kumstaticRange_951.get (by omega) (by omega)
  by_cases h38 : j < 1011
  · exact kumstaticRange_981.get (by omega) (by omega)
  by_cases h39 : j < 1041
  · exact kumstaticRange_1011.get (by omega) (by omega)
  by_cases h40 : j < 1071
  · exact kumstaticRange_1041.get (by omega) (by omega)
  by_cases h41 : j < 1101
  · exact kumstaticRange_1071.get (by omega) (by omega)
  by_cases h42 : j < 1131
  · exact kumstaticRange_1101.get (by omega) (by omega)
  by_cases h43 : j < 1161
  · exact kumstaticRange_1131.get (by omega) (by omega)
  by_cases h44 : j < 1191
  · exact kumstaticRange_1161.get (by omega) (by omega)
  by_cases h45 : j < 1221
  · exact kumstaticRange_1191.get (by omega) (by omega)
  by_cases h46 : j < 1251
  · exact kumstaticRange_1221.get (by omega) (by omega)
  by_cases h47 : j < 1281
  · exact kumstaticRange_1251.get (by omega) (by omega)
  by_cases h48 : j < 1311
  · exact kumstaticRange_1281.get (by omega) (by omega)
  by_cases h49 : j < 1341
  · exact kumstaticRange_1311.get (by omega) (by omega)
  by_cases h50 : j < 1371
  · exact kumstaticRange_1341.get (by omega) (by omega)
  by_cases h51 : j < 1401
  · exact kumstaticRange_1371.get (by omega) (by omega)
  by_cases h52 : j < 1431
  · exact kumstaticRange_1401.get (by omega) (by omega)
  by_cases h53 : j < 1461
  · exact kumstaticRange_1431.get (by omega) (by omega)
  by_cases h54 : j < 1491
  · exact kumstaticRange_1461.get (by omega) (by omega)
  by_cases h55 : j < 1521
  · exact kumstaticRange_1491.get (by omega) (by omega)
  by_cases h56 : j < 1551
  · exact kumstaticRange_1521.get (by omega) (by omega)
  by_cases h57 : j < 1581
  · exact kumstaticRange_1551.get (by omega) (by omega)
  by_cases h58 : j < 1611
  · exact kumstaticRange_1581.get (by omega) (by omega)
  by_cases h59 : j < 1641
  · exact kumstaticRange_1611.get (by omega) (by omega)
  by_cases h60 : j < 1671
  · exact kumstaticRange_1641.get (by omega) (by omega)
  by_cases h61 : j < 1701
  · exact kumstaticRange_1671.get (by omega) (by omega)
  by_cases h62 : j < 1731
  · exact kumstaticRange_1701.get (by omega) (by omega)
  exact kumstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
