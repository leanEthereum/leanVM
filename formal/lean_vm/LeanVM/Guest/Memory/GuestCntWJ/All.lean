/-
  LeanVM.Guest.Memory.GuestCntWJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWJ.Part00
public import LeanVM.Guest.Memory.GuestCntWJ.Part01
public import LeanVM.Guest.Memory.GuestCntWJ.Part02
public import LeanVM.Guest.Memory.GuestCntWJ.Part03
public import LeanVM.Guest.Memory.GuestCntWJ.Part04
public import LeanVM.Guest.Memory.GuestCntWJ.Part05
public import LeanVM.Guest.Memory.GuestCntWJ.Part06
public import LeanVM.Guest.Memory.GuestCntWJ.Part07
public import LeanVM.Guest.Memory.GuestCntWJ.Part08
public import LeanVM.Guest.Memory.GuestCntWJ.Part09
public import LeanVM.Guest.Memory.GuestCntWJ.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 1803, kujchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kujstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kujstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kujstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kujstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kujstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 132
  · exact kujstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 159
  · exact kujstaticRange_132.get (by omega) (by omega)
  by_cases h7 : j < 185
  · exact kujstaticRange_159.get (by omega) (by omega)
  by_cases h8 : j < 209
  · exact kujstaticRange_185.get (by omega) (by omega)
  by_cases h9 : j < 235
  · exact kujstaticRange_209.get (by omega) (by omega)
  by_cases h10 : j < 263
  · exact kujstaticRange_235.get (by omega) (by omega)
  by_cases h11 : j < 293
  · exact kujstaticRange_263.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kujstaticRange_293.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kujstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kujstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kujstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 323
  · exact kujstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 353
  · exact kujstaticRange_323.get (by omega) (by omega)
  by_cases h18 : j < 383
  · exact kujstaticRange_353.get (by omega) (by omega)
  by_cases h19 : j < 413
  · exact kujstaticRange_383.get (by omega) (by omega)
  by_cases h20 : j < 443
  · exact kujstaticRange_413.get (by omega) (by omega)
  by_cases h21 : j < 473
  · exact kujstaticRange_443.get (by omega) (by omega)
  by_cases h22 : j < 503
  · exact kujstaticRange_473.get (by omega) (by omega)
  by_cases h23 : j < 533
  · exact kujstaticRange_503.get (by omega) (by omega)
  by_cases h24 : j < 563
  · exact kujstaticRange_533.get (by omega) (by omega)
  by_cases h25 : j < 593
  · exact kujstaticRange_563.get (by omega) (by omega)
  by_cases h26 : j < 623
  · exact kujstaticRange_593.get (by omega) (by omega)
  by_cases h27 : j < 653
  · exact kujstaticRange_623.get (by omega) (by omega)
  by_cases h28 : j < 683
  · exact kujstaticRange_653.get (by omega) (by omega)
  by_cases h29 : j < 713
  · exact kujstaticRange_683.get (by omega) (by omega)
  by_cases h30 : j < 743
  · exact kujstaticRange_713.get (by omega) (by omega)
  by_cases h31 : j < 773
  · exact kujstaticRange_743.get (by omega) (by omega)
  by_cases h32 : j < 803
  · exact kujstaticRange_773.get (by omega) (by omega)
  by_cases h33 : j < 833
  · exact kujstaticRange_803.get (by omega) (by omega)
  by_cases h34 : j < 863
  · exact kujstaticRange_833.get (by omega) (by omega)
  by_cases h35 : j < 893
  · exact kujstaticRange_863.get (by omega) (by omega)
  by_cases h36 : j < 923
  · exact kujstaticRange_893.get (by omega) (by omega)
  by_cases h37 : j < 953
  · exact kujstaticRange_923.get (by omega) (by omega)
  by_cases h38 : j < 983
  · exact kujstaticRange_953.get (by omega) (by omega)
  by_cases h39 : j < 1013
  · exact kujstaticRange_983.get (by omega) (by omega)
  by_cases h40 : j < 1043
  · exact kujstaticRange_1013.get (by omega) (by omega)
  by_cases h41 : j < 1073
  · exact kujstaticRange_1043.get (by omega) (by omega)
  by_cases h42 : j < 1103
  · exact kujstaticRange_1073.get (by omega) (by omega)
  by_cases h43 : j < 1133
  · exact kujstaticRange_1103.get (by omega) (by omega)
  by_cases h44 : j < 1163
  · exact kujstaticRange_1133.get (by omega) (by omega)
  by_cases h45 : j < 1193
  · exact kujstaticRange_1163.get (by omega) (by omega)
  by_cases h46 : j < 1223
  · exact kujstaticRange_1193.get (by omega) (by omega)
  by_cases h47 : j < 1253
  · exact kujstaticRange_1223.get (by omega) (by omega)
  by_cases h48 : j < 1283
  · exact kujstaticRange_1253.get (by omega) (by omega)
  by_cases h49 : j < 1313
  · exact kujstaticRange_1283.get (by omega) (by omega)
  by_cases h50 : j < 1343
  · exact kujstaticRange_1313.get (by omega) (by omega)
  by_cases h51 : j < 1373
  · exact kujstaticRange_1343.get (by omega) (by omega)
  by_cases h52 : j < 1403
  · exact kujstaticRange_1373.get (by omega) (by omega)
  by_cases h53 : j < 1433
  · exact kujstaticRange_1403.get (by omega) (by omega)
  by_cases h54 : j < 1463
  · exact kujstaticRange_1433.get (by omega) (by omega)
  by_cases h55 : j < 1493
  · exact kujstaticRange_1463.get (by omega) (by omega)
  by_cases h56 : j < 1523
  · exact kujstaticRange_1493.get (by omega) (by omega)
  by_cases h57 : j < 1553
  · exact kujstaticRange_1523.get (by omega) (by omega)
  by_cases h58 : j < 1583
  · exact kujstaticRange_1553.get (by omega) (by omega)
  by_cases h59 : j < 1613
  · exact kujstaticRange_1583.get (by omega) (by omega)
  by_cases h60 : j < 1643
  · exact kujstaticRange_1613.get (by omega) (by omega)
  by_cases h61 : j < 1673
  · exact kujstaticRange_1643.get (by omega) (by omega)
  by_cases h62 : j < 1703
  · exact kujstaticRange_1673.get (by omega) (by omega)
  by_cases h63 : j < 1733
  · exact kujstaticRange_1703.get (by omega) (by omega)
  by_cases h64 : j < 1763
  · exact kujstaticRange_1733.get (by omega) (by omega)
  by_cases h65 : j < 1793
  · exact kujstaticRange_1763.get (by omega) (by omega)
  exact kujstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
