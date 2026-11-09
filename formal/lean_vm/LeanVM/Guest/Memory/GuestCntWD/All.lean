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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 991, kudchkIdx j = true := by
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
  by_cases h5 : j < 129
  · exact kudstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kudstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kudstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 207
  · exact kudstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 233
  · exact kudstaticRange_207.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kudstaticRange_233.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kudstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kudstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kudstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 323
  · exact kudstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 353
  · exact kudstaticRange_323.get (by omega) (by omega)
  by_cases h16 : j < 383
  · exact kudstaticRange_353.get (by omega) (by omega)
  by_cases h17 : j < 413
  · exact kudstaticRange_383.get (by omega) (by omega)
  by_cases h18 : j < 443
  · exact kudstaticRange_413.get (by omega) (by omega)
  by_cases h19 : j < 473
  · exact kudstaticRange_443.get (by omega) (by omega)
  by_cases h20 : j < 503
  · exact kudstaticRange_473.get (by omega) (by omega)
  by_cases h21 : j < 533
  · exact kudstaticRange_503.get (by omega) (by omega)
  by_cases h22 : j < 563
  · exact kudstaticRange_533.get (by omega) (by omega)
  by_cases h23 : j < 593
  · exact kudstaticRange_563.get (by omega) (by omega)
  by_cases h24 : j < 623
  · exact kudstaticRange_593.get (by omega) (by omega)
  by_cases h25 : j < 653
  · exact kudstaticRange_623.get (by omega) (by omega)
  by_cases h26 : j < 683
  · exact kudstaticRange_653.get (by omega) (by omega)
  by_cases h27 : j < 713
  · exact kudstaticRange_683.get (by omega) (by omega)
  by_cases h28 : j < 743
  · exact kudstaticRange_713.get (by omega) (by omega)
  by_cases h29 : j < 773
  · exact kudstaticRange_743.get (by omega) (by omega)
  by_cases h30 : j < 803
  · exact kudstaticRange_773.get (by omega) (by omega)
  by_cases h31 : j < 833
  · exact kudstaticRange_803.get (by omega) (by omega)
  by_cases h32 : j < 863
  · exact kudstaticRange_833.get (by omega) (by omega)
  by_cases h33 : j < 893
  · exact kudstaticRange_863.get (by omega) (by omega)
  by_cases h34 : j < 923
  · exact kudstaticRange_893.get (by omega) (by omega)
  by_cases h35 : j < 953
  · exact kudstaticRange_923.get (by omega) (by omega)
  by_cases h36 : j < 983
  · exact kudstaticRange_953.get (by omega) (by omega)
  exact kudstaticRange_983.get (by omega) (by omega)

end
end LeanVM.Guest
