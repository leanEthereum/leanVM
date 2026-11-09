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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 991, kujchkIdx j = true := by
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
  by_cases h5 : j < 129
  · exact kujstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kujstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kujstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 207
  · exact kujstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 233
  · exact kujstaticRange_207.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kujstaticRange_233.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kujstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kujstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kujstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 323
  · exact kujstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 353
  · exact kujstaticRange_323.get (by omega) (by omega)
  by_cases h16 : j < 383
  · exact kujstaticRange_353.get (by omega) (by omega)
  by_cases h17 : j < 413
  · exact kujstaticRange_383.get (by omega) (by omega)
  by_cases h18 : j < 443
  · exact kujstaticRange_413.get (by omega) (by omega)
  by_cases h19 : j < 473
  · exact kujstaticRange_443.get (by omega) (by omega)
  by_cases h20 : j < 503
  · exact kujstaticRange_473.get (by omega) (by omega)
  by_cases h21 : j < 533
  · exact kujstaticRange_503.get (by omega) (by omega)
  by_cases h22 : j < 563
  · exact kujstaticRange_533.get (by omega) (by omega)
  by_cases h23 : j < 593
  · exact kujstaticRange_563.get (by omega) (by omega)
  by_cases h24 : j < 623
  · exact kujstaticRange_593.get (by omega) (by omega)
  by_cases h25 : j < 653
  · exact kujstaticRange_623.get (by omega) (by omega)
  by_cases h26 : j < 683
  · exact kujstaticRange_653.get (by omega) (by omega)
  by_cases h27 : j < 713
  · exact kujstaticRange_683.get (by omega) (by omega)
  by_cases h28 : j < 743
  · exact kujstaticRange_713.get (by omega) (by omega)
  by_cases h29 : j < 773
  · exact kujstaticRange_743.get (by omega) (by omega)
  by_cases h30 : j < 803
  · exact kujstaticRange_773.get (by omega) (by omega)
  by_cases h31 : j < 833
  · exact kujstaticRange_803.get (by omega) (by omega)
  by_cases h32 : j < 863
  · exact kujstaticRange_833.get (by omega) (by omega)
  by_cases h33 : j < 893
  · exact kujstaticRange_863.get (by omega) (by omega)
  by_cases h34 : j < 923
  · exact kujstaticRange_893.get (by omega) (by omega)
  by_cases h35 : j < 953
  · exact kujstaticRange_923.get (by omega) (by omega)
  by_cases h36 : j < 983
  · exact kujstaticRange_953.get (by omega) (by omega)
  exact kujstaticRange_983.get (by omega) (by omega)

end
end LeanVM.Guest
