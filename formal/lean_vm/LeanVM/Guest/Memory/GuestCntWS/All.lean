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
public import LeanVM.Guest.Memory.GuestCntWS.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 1803, kuschkIdx j = true := by
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
  by_cases h5 : j < 132
  · exact kusstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 159
  · exact kusstaticRange_132.get (by omega) (by omega)
  by_cases h7 : j < 185
  · exact kusstaticRange_159.get (by omega) (by omega)
  by_cases h8 : j < 209
  · exact kusstaticRange_185.get (by omega) (by omega)
  by_cases h9 : j < 235
  · exact kusstaticRange_209.get (by omega) (by omega)
  by_cases h10 : j < 263
  · exact kusstaticRange_235.get (by omega) (by omega)
  by_cases h11 : j < 293
  · exact kusstaticRange_263.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kusstaticRange_293.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kusstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kusstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kusstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 323
  · exact kusstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 353
  · exact kusstaticRange_323.get (by omega) (by omega)
  by_cases h18 : j < 383
  · exact kusstaticRange_353.get (by omega) (by omega)
  by_cases h19 : j < 413
  · exact kusstaticRange_383.get (by omega) (by omega)
  by_cases h20 : j < 443
  · exact kusstaticRange_413.get (by omega) (by omega)
  by_cases h21 : j < 473
  · exact kusstaticRange_443.get (by omega) (by omega)
  by_cases h22 : j < 503
  · exact kusstaticRange_473.get (by omega) (by omega)
  by_cases h23 : j < 533
  · exact kusstaticRange_503.get (by omega) (by omega)
  by_cases h24 : j < 563
  · exact kusstaticRange_533.get (by omega) (by omega)
  by_cases h25 : j < 593
  · exact kusstaticRange_563.get (by omega) (by omega)
  by_cases h26 : j < 623
  · exact kusstaticRange_593.get (by omega) (by omega)
  by_cases h27 : j < 653
  · exact kusstaticRange_623.get (by omega) (by omega)
  by_cases h28 : j < 683
  · exact kusstaticRange_653.get (by omega) (by omega)
  by_cases h29 : j < 713
  · exact kusstaticRange_683.get (by omega) (by omega)
  by_cases h30 : j < 743
  · exact kusstaticRange_713.get (by omega) (by omega)
  by_cases h31 : j < 773
  · exact kusstaticRange_743.get (by omega) (by omega)
  by_cases h32 : j < 803
  · exact kusstaticRange_773.get (by omega) (by omega)
  by_cases h33 : j < 833
  · exact kusstaticRange_803.get (by omega) (by omega)
  by_cases h34 : j < 863
  · exact kusstaticRange_833.get (by omega) (by omega)
  by_cases h35 : j < 893
  · exact kusstaticRange_863.get (by omega) (by omega)
  by_cases h36 : j < 923
  · exact kusstaticRange_893.get (by omega) (by omega)
  by_cases h37 : j < 953
  · exact kusstaticRange_923.get (by omega) (by omega)
  by_cases h38 : j < 983
  · exact kusstaticRange_953.get (by omega) (by omega)
  by_cases h39 : j < 1013
  · exact kusstaticRange_983.get (by omega) (by omega)
  by_cases h40 : j < 1043
  · exact kusstaticRange_1013.get (by omega) (by omega)
  by_cases h41 : j < 1073
  · exact kusstaticRange_1043.get (by omega) (by omega)
  by_cases h42 : j < 1103
  · exact kusstaticRange_1073.get (by omega) (by omega)
  by_cases h43 : j < 1133
  · exact kusstaticRange_1103.get (by omega) (by omega)
  by_cases h44 : j < 1163
  · exact kusstaticRange_1133.get (by omega) (by omega)
  by_cases h45 : j < 1193
  · exact kusstaticRange_1163.get (by omega) (by omega)
  by_cases h46 : j < 1223
  · exact kusstaticRange_1193.get (by omega) (by omega)
  by_cases h47 : j < 1253
  · exact kusstaticRange_1223.get (by omega) (by omega)
  by_cases h48 : j < 1283
  · exact kusstaticRange_1253.get (by omega) (by omega)
  by_cases h49 : j < 1313
  · exact kusstaticRange_1283.get (by omega) (by omega)
  by_cases h50 : j < 1343
  · exact kusstaticRange_1313.get (by omega) (by omega)
  by_cases h51 : j < 1373
  · exact kusstaticRange_1343.get (by omega) (by omega)
  by_cases h52 : j < 1403
  · exact kusstaticRange_1373.get (by omega) (by omega)
  by_cases h53 : j < 1433
  · exact kusstaticRange_1403.get (by omega) (by omega)
  by_cases h54 : j < 1463
  · exact kusstaticRange_1433.get (by omega) (by omega)
  by_cases h55 : j < 1493
  · exact kusstaticRange_1463.get (by omega) (by omega)
  by_cases h56 : j < 1523
  · exact kusstaticRange_1493.get (by omega) (by omega)
  by_cases h57 : j < 1553
  · exact kusstaticRange_1523.get (by omega) (by omega)
  by_cases h58 : j < 1583
  · exact kusstaticRange_1553.get (by omega) (by omega)
  by_cases h59 : j < 1613
  · exact kusstaticRange_1583.get (by omega) (by omega)
  by_cases h60 : j < 1643
  · exact kusstaticRange_1613.get (by omega) (by omega)
  by_cases h61 : j < 1673
  · exact kusstaticRange_1643.get (by omega) (by omega)
  by_cases h62 : j < 1703
  · exact kusstaticRange_1673.get (by omega) (by omega)
  by_cases h63 : j < 1733
  · exact kusstaticRange_1703.get (by omega) (by omega)
  by_cases h64 : j < 1763
  · exact kusstaticRange_1733.get (by omega) (by omega)
  by_cases h65 : j < 1793
  · exact kusstaticRange_1763.get (by omega) (by omega)
  exact kusstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
