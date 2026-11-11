/-
  LeanVM.Guest.Memory.GuestCntWS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWS.Part00
public import LeanVM.Guest.Memory.GuestCntWS.Part01
public import LeanVM.Guest.Memory.GuestCntWS.Part02
public import LeanVM.Guest.Memory.GuestCntWS.Part03
public import LeanVM.Guest.Memory.GuestCntWS.Part04
public import LeanVM.Guest.Memory.GuestCntWS.Part05
public import LeanVM.Guest.Memory.GuestCntWS.Part06
public import LeanVM.Guest.Memory.GuestCntWS.Part07
public import LeanVM.Guest.Memory.GuestCntWS.Part08
public import LeanVM.Guest.Memory.GuestCntWS.Part09

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 1752, kuschkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kusstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kusstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kusstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kusstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kusstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 128
  · exact kusstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kusstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kusstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kusstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 230
  · exact kusstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 258
  · exact kusstaticRange_230.get (by omega) (by omega)
  by_cases h11 : j < 288
  · exact kusstaticRange_258.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kusstaticRange_288.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kusstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kusstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kusstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 351
  · exact kusstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 381
  · exact kusstaticRange_351.get (by omega) (by omega)
  by_cases h18 : j < 411
  · exact kusstaticRange_381.get (by omega) (by omega)
  by_cases h19 : j < 441
  · exact kusstaticRange_411.get (by omega) (by omega)
  by_cases h20 : j < 471
  · exact kusstaticRange_441.get (by omega) (by omega)
  by_cases h21 : j < 501
  · exact kusstaticRange_471.get (by omega) (by omega)
  by_cases h22 : j < 531
  · exact kusstaticRange_501.get (by omega) (by omega)
  by_cases h23 : j < 561
  · exact kusstaticRange_531.get (by omega) (by omega)
  by_cases h24 : j < 591
  · exact kusstaticRange_561.get (by omega) (by omega)
  by_cases h25 : j < 621
  · exact kusstaticRange_591.get (by omega) (by omega)
  by_cases h26 : j < 651
  · exact kusstaticRange_621.get (by omega) (by omega)
  by_cases h27 : j < 681
  · exact kusstaticRange_651.get (by omega) (by omega)
  by_cases h28 : j < 711
  · exact kusstaticRange_681.get (by omega) (by omega)
  by_cases h29 : j < 741
  · exact kusstaticRange_711.get (by omega) (by omega)
  by_cases h30 : j < 771
  · exact kusstaticRange_741.get (by omega) (by omega)
  by_cases h31 : j < 801
  · exact kusstaticRange_771.get (by omega) (by omega)
  by_cases h32 : j < 831
  · exact kusstaticRange_801.get (by omega) (by omega)
  by_cases h33 : j < 861
  · exact kusstaticRange_831.get (by omega) (by omega)
  by_cases h34 : j < 891
  · exact kusstaticRange_861.get (by omega) (by omega)
  by_cases h35 : j < 921
  · exact kusstaticRange_891.get (by omega) (by omega)
  by_cases h36 : j < 951
  · exact kusstaticRange_921.get (by omega) (by omega)
  by_cases h37 : j < 981
  · exact kusstaticRange_951.get (by omega) (by omega)
  by_cases h38 : j < 1011
  · exact kusstaticRange_981.get (by omega) (by omega)
  by_cases h39 : j < 1041
  · exact kusstaticRange_1011.get (by omega) (by omega)
  by_cases h40 : j < 1071
  · exact kusstaticRange_1041.get (by omega) (by omega)
  by_cases h41 : j < 1101
  · exact kusstaticRange_1071.get (by omega) (by omega)
  by_cases h42 : j < 1131
  · exact kusstaticRange_1101.get (by omega) (by omega)
  by_cases h43 : j < 1161
  · exact kusstaticRange_1131.get (by omega) (by omega)
  by_cases h44 : j < 1191
  · exact kusstaticRange_1161.get (by omega) (by omega)
  by_cases h45 : j < 1221
  · exact kusstaticRange_1191.get (by omega) (by omega)
  by_cases h46 : j < 1251
  · exact kusstaticRange_1221.get (by omega) (by omega)
  by_cases h47 : j < 1281
  · exact kusstaticRange_1251.get (by omega) (by omega)
  by_cases h48 : j < 1311
  · exact kusstaticRange_1281.get (by omega) (by omega)
  by_cases h49 : j < 1341
  · exact kusstaticRange_1311.get (by omega) (by omega)
  by_cases h50 : j < 1371
  · exact kusstaticRange_1341.get (by omega) (by omega)
  by_cases h51 : j < 1401
  · exact kusstaticRange_1371.get (by omega) (by omega)
  by_cases h52 : j < 1431
  · exact kusstaticRange_1401.get (by omega) (by omega)
  by_cases h53 : j < 1461
  · exact kusstaticRange_1431.get (by omega) (by omega)
  by_cases h54 : j < 1491
  · exact kusstaticRange_1461.get (by omega) (by omega)
  by_cases h55 : j < 1521
  · exact kusstaticRange_1491.get (by omega) (by omega)
  by_cases h56 : j < 1551
  · exact kusstaticRange_1521.get (by omega) (by omega)
  by_cases h57 : j < 1581
  · exact kusstaticRange_1551.get (by omega) (by omega)
  by_cases h58 : j < 1611
  · exact kusstaticRange_1581.get (by omega) (by omega)
  by_cases h59 : j < 1641
  · exact kusstaticRange_1611.get (by omega) (by omega)
  by_cases h60 : j < 1671
  · exact kusstaticRange_1641.get (by omega) (by omega)
  by_cases h61 : j < 1701
  · exact kusstaticRange_1671.get (by omega) (by omega)
  by_cases h62 : j < 1731
  · exact kusstaticRange_1701.get (by omega) (by omega)
  exact kusstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
