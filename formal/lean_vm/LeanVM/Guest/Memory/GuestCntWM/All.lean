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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 991, kumchkIdx j = true := by
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
  by_cases h5 : j < 129
  · exact kumstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kumstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kumstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 207
  · exact kumstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 233
  · exact kumstaticRange_207.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kumstaticRange_233.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kumstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kumstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kumstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 323
  · exact kumstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 353
  · exact kumstaticRange_323.get (by omega) (by omega)
  by_cases h16 : j < 383
  · exact kumstaticRange_353.get (by omega) (by omega)
  by_cases h17 : j < 413
  · exact kumstaticRange_383.get (by omega) (by omega)
  by_cases h18 : j < 443
  · exact kumstaticRange_413.get (by omega) (by omega)
  by_cases h19 : j < 473
  · exact kumstaticRange_443.get (by omega) (by omega)
  by_cases h20 : j < 503
  · exact kumstaticRange_473.get (by omega) (by omega)
  by_cases h21 : j < 533
  · exact kumstaticRange_503.get (by omega) (by omega)
  by_cases h22 : j < 563
  · exact kumstaticRange_533.get (by omega) (by omega)
  by_cases h23 : j < 593
  · exact kumstaticRange_563.get (by omega) (by omega)
  by_cases h24 : j < 623
  · exact kumstaticRange_593.get (by omega) (by omega)
  by_cases h25 : j < 653
  · exact kumstaticRange_623.get (by omega) (by omega)
  by_cases h26 : j < 683
  · exact kumstaticRange_653.get (by omega) (by omega)
  by_cases h27 : j < 713
  · exact kumstaticRange_683.get (by omega) (by omega)
  by_cases h28 : j < 743
  · exact kumstaticRange_713.get (by omega) (by omega)
  by_cases h29 : j < 773
  · exact kumstaticRange_743.get (by omega) (by omega)
  by_cases h30 : j < 803
  · exact kumstaticRange_773.get (by omega) (by omega)
  by_cases h31 : j < 833
  · exact kumstaticRange_803.get (by omega) (by omega)
  by_cases h32 : j < 863
  · exact kumstaticRange_833.get (by omega) (by omega)
  by_cases h33 : j < 893
  · exact kumstaticRange_863.get (by omega) (by omega)
  by_cases h34 : j < 923
  · exact kumstaticRange_893.get (by omega) (by omega)
  by_cases h35 : j < 953
  · exact kumstaticRange_923.get (by omega) (by omega)
  by_cases h36 : j < 983
  · exact kumstaticRange_953.get (by omega) (by omega)
  exact kumstaticRange_983.get (by omega) (by omega)

end
end LeanVM.Guest
