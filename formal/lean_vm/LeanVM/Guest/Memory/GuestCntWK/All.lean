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
public import LeanVM.Guest.Memory.GuestCntWK.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 1803, kukchkIdx j = true := by
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
  by_cases h5 : j < 132
  · exact kukstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 159
  · exact kukstaticRange_132.get (by omega) (by omega)
  by_cases h7 : j < 185
  · exact kukstaticRange_159.get (by omega) (by omega)
  by_cases h8 : j < 209
  · exact kukstaticRange_185.get (by omega) (by omega)
  by_cases h9 : j < 235
  · exact kukstaticRange_209.get (by omega) (by omega)
  by_cases h10 : j < 263
  · exact kukstaticRange_235.get (by omega) (by omega)
  by_cases h11 : j < 293
  · exact kukstaticRange_263.get (by omega) (by omega)
  by_cases h12 : j < 313
  · exact kukstaticRange_293.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kukstaticRange_313.get (by omega) (by omega)
  by_cases h14 : j < 319
  · exact kukstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 321
  · exact kukstaticRange_319.get (by omega) (by omega)
  by_cases h16 : j < 323
  · exact kukstaticRange_321.get (by omega) (by omega)
  by_cases h17 : j < 353
  · exact kukstaticRange_323.get (by omega) (by omega)
  by_cases h18 : j < 383
  · exact kukstaticRange_353.get (by omega) (by omega)
  by_cases h19 : j < 413
  · exact kukstaticRange_383.get (by omega) (by omega)
  by_cases h20 : j < 443
  · exact kukstaticRange_413.get (by omega) (by omega)
  by_cases h21 : j < 473
  · exact kukstaticRange_443.get (by omega) (by omega)
  by_cases h22 : j < 503
  · exact kukstaticRange_473.get (by omega) (by omega)
  by_cases h23 : j < 533
  · exact kukstaticRange_503.get (by omega) (by omega)
  by_cases h24 : j < 563
  · exact kukstaticRange_533.get (by omega) (by omega)
  by_cases h25 : j < 593
  · exact kukstaticRange_563.get (by omega) (by omega)
  by_cases h26 : j < 623
  · exact kukstaticRange_593.get (by omega) (by omega)
  by_cases h27 : j < 653
  · exact kukstaticRange_623.get (by omega) (by omega)
  by_cases h28 : j < 683
  · exact kukstaticRange_653.get (by omega) (by omega)
  by_cases h29 : j < 713
  · exact kukstaticRange_683.get (by omega) (by omega)
  by_cases h30 : j < 743
  · exact kukstaticRange_713.get (by omega) (by omega)
  by_cases h31 : j < 773
  · exact kukstaticRange_743.get (by omega) (by omega)
  by_cases h32 : j < 803
  · exact kukstaticRange_773.get (by omega) (by omega)
  by_cases h33 : j < 833
  · exact kukstaticRange_803.get (by omega) (by omega)
  by_cases h34 : j < 863
  · exact kukstaticRange_833.get (by omega) (by omega)
  by_cases h35 : j < 893
  · exact kukstaticRange_863.get (by omega) (by omega)
  by_cases h36 : j < 923
  · exact kukstaticRange_893.get (by omega) (by omega)
  by_cases h37 : j < 953
  · exact kukstaticRange_923.get (by omega) (by omega)
  by_cases h38 : j < 983
  · exact kukstaticRange_953.get (by omega) (by omega)
  by_cases h39 : j < 1013
  · exact kukstaticRange_983.get (by omega) (by omega)
  by_cases h40 : j < 1043
  · exact kukstaticRange_1013.get (by omega) (by omega)
  by_cases h41 : j < 1073
  · exact kukstaticRange_1043.get (by omega) (by omega)
  by_cases h42 : j < 1103
  · exact kukstaticRange_1073.get (by omega) (by omega)
  by_cases h43 : j < 1133
  · exact kukstaticRange_1103.get (by omega) (by omega)
  by_cases h44 : j < 1163
  · exact kukstaticRange_1133.get (by omega) (by omega)
  by_cases h45 : j < 1193
  · exact kukstaticRange_1163.get (by omega) (by omega)
  by_cases h46 : j < 1223
  · exact kukstaticRange_1193.get (by omega) (by omega)
  by_cases h47 : j < 1253
  · exact kukstaticRange_1223.get (by omega) (by omega)
  by_cases h48 : j < 1283
  · exact kukstaticRange_1253.get (by omega) (by omega)
  by_cases h49 : j < 1313
  · exact kukstaticRange_1283.get (by omega) (by omega)
  by_cases h50 : j < 1343
  · exact kukstaticRange_1313.get (by omega) (by omega)
  by_cases h51 : j < 1373
  · exact kukstaticRange_1343.get (by omega) (by omega)
  by_cases h52 : j < 1403
  · exact kukstaticRange_1373.get (by omega) (by omega)
  by_cases h53 : j < 1433
  · exact kukstaticRange_1403.get (by omega) (by omega)
  by_cases h54 : j < 1463
  · exact kukstaticRange_1433.get (by omega) (by omega)
  by_cases h55 : j < 1493
  · exact kukstaticRange_1463.get (by omega) (by omega)
  by_cases h56 : j < 1523
  · exact kukstaticRange_1493.get (by omega) (by omega)
  by_cases h57 : j < 1553
  · exact kukstaticRange_1523.get (by omega) (by omega)
  by_cases h58 : j < 1583
  · exact kukstaticRange_1553.get (by omega) (by omega)
  by_cases h59 : j < 1613
  · exact kukstaticRange_1583.get (by omega) (by omega)
  by_cases h60 : j < 1643
  · exact kukstaticRange_1613.get (by omega) (by omega)
  by_cases h61 : j < 1673
  · exact kukstaticRange_1643.get (by omega) (by omega)
  by_cases h62 : j < 1703
  · exact kukstaticRange_1673.get (by omega) (by omega)
  by_cases h63 : j < 1733
  · exact kukstaticRange_1703.get (by omega) (by omega)
  by_cases h64 : j < 1763
  · exact kukstaticRange_1733.get (by omega) (by omega)
  by_cases h65 : j < 1793
  · exact kukstaticRange_1763.get (by omega) (by omega)
  exact kukstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
