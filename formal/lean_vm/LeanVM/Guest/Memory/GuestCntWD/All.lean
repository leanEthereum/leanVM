/-
  LeanVM.Guest.Memory.GuestCntWD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWD.Part00
public import LeanVM.Guest.Memory.GuestCntWD.Part01
public import LeanVM.Guest.Memory.GuestCntWD.Part02
public import LeanVM.Guest.Memory.GuestCntWD.Part03
public import LeanVM.Guest.Memory.GuestCntWD.Part04
public import LeanVM.Guest.Memory.GuestCntWD.Part05
public import LeanVM.Guest.Memory.GuestCntWD.Part06
public import LeanVM.Guest.Memory.GuestCntWD.Part07
public import LeanVM.Guest.Memory.GuestCntWD.Part08
public import LeanVM.Guest.Memory.GuestCntWD.Part09
public import LeanVM.Guest.Memory.GuestCntWD.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 1803, kudchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kudstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kudstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kudstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kudstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kudstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 132
  · exact kudstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 159
  · exact kudstaticRange_132.get (by omega) (by omega)
  by_cases h7 : j < 185
  · exact kudstaticRange_159.get (by omega) (by omega)
  by_cases h8 : j < 209
  · exact kudstaticRange_185.get (by omega) (by omega)
  by_cases h9 : j < 235
  · exact kudstaticRange_209.get (by omega) (by omega)
  by_cases h10 : j < 263
  · exact kudstaticRange_235.get (by omega) (by omega)
  by_cases h11 : j < 293
  · exact kudstaticRange_263.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kudstaticRange_293.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kudstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kudstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kudstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 323
  · exact kudstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 353
  · exact kudstaticRange_323.get (by omega) (by omega)
  by_cases h18 : j < 383
  · exact kudstaticRange_353.get (by omega) (by omega)
  by_cases h19 : j < 413
  · exact kudstaticRange_383.get (by omega) (by omega)
  by_cases h20 : j < 443
  · exact kudstaticRange_413.get (by omega) (by omega)
  by_cases h21 : j < 473
  · exact kudstaticRange_443.get (by omega) (by omega)
  by_cases h22 : j < 503
  · exact kudstaticRange_473.get (by omega) (by omega)
  by_cases h23 : j < 533
  · exact kudstaticRange_503.get (by omega) (by omega)
  by_cases h24 : j < 563
  · exact kudstaticRange_533.get (by omega) (by omega)
  by_cases h25 : j < 593
  · exact kudstaticRange_563.get (by omega) (by omega)
  by_cases h26 : j < 623
  · exact kudstaticRange_593.get (by omega) (by omega)
  by_cases h27 : j < 653
  · exact kudstaticRange_623.get (by omega) (by omega)
  by_cases h28 : j < 683
  · exact kudstaticRange_653.get (by omega) (by omega)
  by_cases h29 : j < 713
  · exact kudstaticRange_683.get (by omega) (by omega)
  by_cases h30 : j < 743
  · exact kudstaticRange_713.get (by omega) (by omega)
  by_cases h31 : j < 773
  · exact kudstaticRange_743.get (by omega) (by omega)
  by_cases h32 : j < 803
  · exact kudstaticRange_773.get (by omega) (by omega)
  by_cases h33 : j < 833
  · exact kudstaticRange_803.get (by omega) (by omega)
  by_cases h34 : j < 863
  · exact kudstaticRange_833.get (by omega) (by omega)
  by_cases h35 : j < 893
  · exact kudstaticRange_863.get (by omega) (by omega)
  by_cases h36 : j < 923
  · exact kudstaticRange_893.get (by omega) (by omega)
  by_cases h37 : j < 953
  · exact kudstaticRange_923.get (by omega) (by omega)
  by_cases h38 : j < 983
  · exact kudstaticRange_953.get (by omega) (by omega)
  by_cases h39 : j < 1013
  · exact kudstaticRange_983.get (by omega) (by omega)
  by_cases h40 : j < 1043
  · exact kudstaticRange_1013.get (by omega) (by omega)
  by_cases h41 : j < 1073
  · exact kudstaticRange_1043.get (by omega) (by omega)
  by_cases h42 : j < 1103
  · exact kudstaticRange_1073.get (by omega) (by omega)
  by_cases h43 : j < 1133
  · exact kudstaticRange_1103.get (by omega) (by omega)
  by_cases h44 : j < 1163
  · exact kudstaticRange_1133.get (by omega) (by omega)
  by_cases h45 : j < 1193
  · exact kudstaticRange_1163.get (by omega) (by omega)
  by_cases h46 : j < 1223
  · exact kudstaticRange_1193.get (by omega) (by omega)
  by_cases h47 : j < 1253
  · exact kudstaticRange_1223.get (by omega) (by omega)
  by_cases h48 : j < 1283
  · exact kudstaticRange_1253.get (by omega) (by omega)
  by_cases h49 : j < 1313
  · exact kudstaticRange_1283.get (by omega) (by omega)
  by_cases h50 : j < 1343
  · exact kudstaticRange_1313.get (by omega) (by omega)
  by_cases h51 : j < 1373
  · exact kudstaticRange_1343.get (by omega) (by omega)
  by_cases h52 : j < 1403
  · exact kudstaticRange_1373.get (by omega) (by omega)
  by_cases h53 : j < 1433
  · exact kudstaticRange_1403.get (by omega) (by omega)
  by_cases h54 : j < 1463
  · exact kudstaticRange_1433.get (by omega) (by omega)
  by_cases h55 : j < 1493
  · exact kudstaticRange_1463.get (by omega) (by omega)
  by_cases h56 : j < 1523
  · exact kudstaticRange_1493.get (by omega) (by omega)
  by_cases h57 : j < 1553
  · exact kudstaticRange_1523.get (by omega) (by omega)
  by_cases h58 : j < 1583
  · exact kudstaticRange_1553.get (by omega) (by omega)
  by_cases h59 : j < 1613
  · exact kudstaticRange_1583.get (by omega) (by omega)
  by_cases h60 : j < 1643
  · exact kudstaticRange_1613.get (by omega) (by omega)
  by_cases h61 : j < 1673
  · exact kudstaticRange_1643.get (by omega) (by omega)
  by_cases h62 : j < 1703
  · exact kudstaticRange_1673.get (by omega) (by omega)
  by_cases h63 : j < 1733
  · exact kudstaticRange_1703.get (by omega) (by omega)
  by_cases h64 : j < 1763
  · exact kudstaticRange_1733.get (by omega) (by omega)
  by_cases h65 : j < 1793
  · exact kudstaticRange_1763.get (by omega) (by omega)
  exact kudstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
