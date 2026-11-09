/-
  LeanVM.Guest.Memory.GuestCntWX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntWX.Part00
public import LeanVM.Guest.Memory.GuestCntWX.Part01
public import LeanVM.Guest.Memory.GuestCntWX.Part02
public import LeanVM.Guest.Memory.GuestCntWX.Part03
public import LeanVM.Guest.Memory.GuestCntWX.Part04
public import LeanVM.Guest.Memory.GuestCntWX.Part05

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuxchkIdx_all : ∀ j < 991, kuxchkIdx j = true := by
  intro j hj
  by_cases h0 : j < 11
  · exact kuxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kuxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kuxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 74
  · exact kuxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 104
  · exact kuxstaticRange_74.get (by omega) (by omega)
  by_cases h5 : j < 129
  · exact kuxstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kuxstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kuxstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 207
  · exact kuxstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 233
  · exact kuxstaticRange_207.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kuxstaticRange_233.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kuxstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kuxstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kuxstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 323
  · exact kuxstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 353
  · exact kuxstaticRange_323.get (by omega) (by omega)
  by_cases h16 : j < 383
  · exact kuxstaticRange_353.get (by omega) (by omega)
  by_cases h17 : j < 413
  · exact kuxstaticRange_383.get (by omega) (by omega)
  by_cases h18 : j < 443
  · exact kuxstaticRange_413.get (by omega) (by omega)
  by_cases h19 : j < 473
  · exact kuxstaticRange_443.get (by omega) (by omega)
  by_cases h20 : j < 503
  · exact kuxstaticRange_473.get (by omega) (by omega)
  by_cases h21 : j < 533
  · exact kuxstaticRange_503.get (by omega) (by omega)
  by_cases h22 : j < 563
  · exact kuxstaticRange_533.get (by omega) (by omega)
  by_cases h23 : j < 593
  · exact kuxstaticRange_563.get (by omega) (by omega)
  by_cases h24 : j < 623
  · exact kuxstaticRange_593.get (by omega) (by omega)
  by_cases h25 : j < 653
  · exact kuxstaticRange_623.get (by omega) (by omega)
  by_cases h26 : j < 683
  · exact kuxstaticRange_653.get (by omega) (by omega)
  by_cases h27 : j < 713
  · exact kuxstaticRange_683.get (by omega) (by omega)
  by_cases h28 : j < 743
  · exact kuxstaticRange_713.get (by omega) (by omega)
  by_cases h29 : j < 773
  · exact kuxstaticRange_743.get (by omega) (by omega)
  by_cases h30 : j < 803
  · exact kuxstaticRange_773.get (by omega) (by omega)
  by_cases h31 : j < 833
  · exact kuxstaticRange_803.get (by omega) (by omega)
  by_cases h32 : j < 863
  · exact kuxstaticRange_833.get (by omega) (by omega)
  by_cases h33 : j < 893
  · exact kuxstaticRange_863.get (by omega) (by omega)
  by_cases h34 : j < 923
  · exact kuxstaticRange_893.get (by omega) (by omega)
  by_cases h35 : j < 953
  · exact kuxstaticRange_923.get (by omega) (by omega)
  by_cases h36 : j < 983
  · exact kuxstaticRange_953.get (by omega) (by omega)
  exact kuxstaticRange_983.get (by omega) (by omega)

end
end LeanVM.Guest
