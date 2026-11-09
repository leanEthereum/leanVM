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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 991, kuschkIdx j = true := by
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
  by_cases h5 : j < 129
  · exact kusstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kusstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kusstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 207
  · exact kusstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 233
  · exact kusstaticRange_207.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kusstaticRange_233.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kusstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kusstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kusstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 323
  · exact kusstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 353
  · exact kusstaticRange_323.get (by omega) (by omega)
  by_cases h16 : j < 383
  · exact kusstaticRange_353.get (by omega) (by omega)
  by_cases h17 : j < 413
  · exact kusstaticRange_383.get (by omega) (by omega)
  by_cases h18 : j < 443
  · exact kusstaticRange_413.get (by omega) (by omega)
  by_cases h19 : j < 473
  · exact kusstaticRange_443.get (by omega) (by omega)
  by_cases h20 : j < 503
  · exact kusstaticRange_473.get (by omega) (by omega)
  by_cases h21 : j < 533
  · exact kusstaticRange_503.get (by omega) (by omega)
  by_cases h22 : j < 563
  · exact kusstaticRange_533.get (by omega) (by omega)
  by_cases h23 : j < 593
  · exact kusstaticRange_563.get (by omega) (by omega)
  by_cases h24 : j < 623
  · exact kusstaticRange_593.get (by omega) (by omega)
  by_cases h25 : j < 653
  · exact kusstaticRange_623.get (by omega) (by omega)
  by_cases h26 : j < 683
  · exact kusstaticRange_653.get (by omega) (by omega)
  by_cases h27 : j < 713
  · exact kusstaticRange_683.get (by omega) (by omega)
  by_cases h28 : j < 743
  · exact kusstaticRange_713.get (by omega) (by omega)
  by_cases h29 : j < 773
  · exact kusstaticRange_743.get (by omega) (by omega)
  by_cases h30 : j < 803
  · exact kusstaticRange_773.get (by omega) (by omega)
  by_cases h31 : j < 833
  · exact kusstaticRange_803.get (by omega) (by omega)
  by_cases h32 : j < 863
  · exact kusstaticRange_833.get (by omega) (by omega)
  by_cases h33 : j < 893
  · exact kusstaticRange_863.get (by omega) (by omega)
  by_cases h34 : j < 923
  · exact kusstaticRange_893.get (by omega) (by omega)
  by_cases h35 : j < 953
  · exact kusstaticRange_923.get (by omega) (by omega)
  by_cases h36 : j < 983
  · exact kusstaticRange_953.get (by omega) (by omega)
  exact kusstaticRange_983.get (by omega) (by omega)

end
end LeanVM.Guest
