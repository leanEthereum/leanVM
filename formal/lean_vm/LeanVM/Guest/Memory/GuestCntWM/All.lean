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
public import LeanVM.Guest.Memory.GuestCntWM.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 1803, kumchkIdx j = true := by
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
  by_cases h5 : j < 132
  · exact kumstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 159
  · exact kumstaticRange_132.get (by omega) (by omega)
  by_cases h7 : j < 185
  · exact kumstaticRange_159.get (by omega) (by omega)
  by_cases h8 : j < 209
  · exact kumstaticRange_185.get (by omega) (by omega)
  by_cases h9 : j < 235
  · exact kumstaticRange_209.get (by omega) (by omega)
  by_cases h10 : j < 263
  · exact kumstaticRange_235.get (by omega) (by omega)
  by_cases h11 : j < 293
  · exact kumstaticRange_263.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kumstaticRange_293.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kumstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kumstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kumstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 323
  · exact kumstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 353
  · exact kumstaticRange_323.get (by omega) (by omega)
  by_cases h18 : j < 383
  · exact kumstaticRange_353.get (by omega) (by omega)
  by_cases h19 : j < 413
  · exact kumstaticRange_383.get (by omega) (by omega)
  by_cases h20 : j < 443
  · exact kumstaticRange_413.get (by omega) (by omega)
  by_cases h21 : j < 473
  · exact kumstaticRange_443.get (by omega) (by omega)
  by_cases h22 : j < 503
  · exact kumstaticRange_473.get (by omega) (by omega)
  by_cases h23 : j < 533
  · exact kumstaticRange_503.get (by omega) (by omega)
  by_cases h24 : j < 563
  · exact kumstaticRange_533.get (by omega) (by omega)
  by_cases h25 : j < 593
  · exact kumstaticRange_563.get (by omega) (by omega)
  by_cases h26 : j < 623
  · exact kumstaticRange_593.get (by omega) (by omega)
  by_cases h27 : j < 653
  · exact kumstaticRange_623.get (by omega) (by omega)
  by_cases h28 : j < 683
  · exact kumstaticRange_653.get (by omega) (by omega)
  by_cases h29 : j < 713
  · exact kumstaticRange_683.get (by omega) (by omega)
  by_cases h30 : j < 743
  · exact kumstaticRange_713.get (by omega) (by omega)
  by_cases h31 : j < 773
  · exact kumstaticRange_743.get (by omega) (by omega)
  by_cases h32 : j < 803
  · exact kumstaticRange_773.get (by omega) (by omega)
  by_cases h33 : j < 833
  · exact kumstaticRange_803.get (by omega) (by omega)
  by_cases h34 : j < 863
  · exact kumstaticRange_833.get (by omega) (by omega)
  by_cases h35 : j < 893
  · exact kumstaticRange_863.get (by omega) (by omega)
  by_cases h36 : j < 923
  · exact kumstaticRange_893.get (by omega) (by omega)
  by_cases h37 : j < 953
  · exact kumstaticRange_923.get (by omega) (by omega)
  by_cases h38 : j < 983
  · exact kumstaticRange_953.get (by omega) (by omega)
  by_cases h39 : j < 1013
  · exact kumstaticRange_983.get (by omega) (by omega)
  by_cases h40 : j < 1043
  · exact kumstaticRange_1013.get (by omega) (by omega)
  by_cases h41 : j < 1073
  · exact kumstaticRange_1043.get (by omega) (by omega)
  by_cases h42 : j < 1103
  · exact kumstaticRange_1073.get (by omega) (by omega)
  by_cases h43 : j < 1133
  · exact kumstaticRange_1103.get (by omega) (by omega)
  by_cases h44 : j < 1163
  · exact kumstaticRange_1133.get (by omega) (by omega)
  by_cases h45 : j < 1193
  · exact kumstaticRange_1163.get (by omega) (by omega)
  by_cases h46 : j < 1223
  · exact kumstaticRange_1193.get (by omega) (by omega)
  by_cases h47 : j < 1253
  · exact kumstaticRange_1223.get (by omega) (by omega)
  by_cases h48 : j < 1283
  · exact kumstaticRange_1253.get (by omega) (by omega)
  by_cases h49 : j < 1313
  · exact kumstaticRange_1283.get (by omega) (by omega)
  by_cases h50 : j < 1343
  · exact kumstaticRange_1313.get (by omega) (by omega)
  by_cases h51 : j < 1373
  · exact kumstaticRange_1343.get (by omega) (by omega)
  by_cases h52 : j < 1403
  · exact kumstaticRange_1373.get (by omega) (by omega)
  by_cases h53 : j < 1433
  · exact kumstaticRange_1403.get (by omega) (by omega)
  by_cases h54 : j < 1463
  · exact kumstaticRange_1433.get (by omega) (by omega)
  by_cases h55 : j < 1493
  · exact kumstaticRange_1463.get (by omega) (by omega)
  by_cases h56 : j < 1523
  · exact kumstaticRange_1493.get (by omega) (by omega)
  by_cases h57 : j < 1553
  · exact kumstaticRange_1523.get (by omega) (by omega)
  by_cases h58 : j < 1583
  · exact kumstaticRange_1553.get (by omega) (by omega)
  by_cases h59 : j < 1613
  · exact kumstaticRange_1583.get (by omega) (by omega)
  by_cases h60 : j < 1643
  · exact kumstaticRange_1613.get (by omega) (by omega)
  by_cases h61 : j < 1673
  · exact kumstaticRange_1643.get (by omega) (by omega)
  by_cases h62 : j < 1703
  · exact kumstaticRange_1673.get (by omega) (by omega)
  by_cases h63 : j < 1733
  · exact kumstaticRange_1703.get (by omega) (by omega)
  by_cases h64 : j < 1763
  · exact kumstaticRange_1733.get (by omega) (by omega)
  by_cases h65 : j < 1793
  · exact kumstaticRange_1763.get (by omega) (by omega)
  exact kumstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
