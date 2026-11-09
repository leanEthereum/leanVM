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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 991, kukchkIdx j = true := by
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
  by_cases h5 : j < 129
  · exact kukstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 156
  · exact kukstaticRange_129.get (by omega) (by omega)
  by_cases h7 : j < 182
  · exact kukstaticRange_156.get (by omega) (by omega)
  by_cases h8 : j < 207
  · exact kukstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 233
  · exact kukstaticRange_207.get (by omega) (by omega)
  by_cases h10 : j < 261
  · exact kukstaticRange_233.get (by omega) (by omega)
  by_cases h11 : j < 291
  · exact kukstaticRange_261.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kukstaticRange_291.get (by omega) (by omega)
  by_cases h13 : j < 316
  · exact kukstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 323
  · exact kukstaticRange_316.get (by omega) (by omega)
  by_cases h15 : j < 353
  · exact kukstaticRange_323.get (by omega) (by omega)
  by_cases h16 : j < 383
  · exact kukstaticRange_353.get (by omega) (by omega)
  by_cases h17 : j < 413
  · exact kukstaticRange_383.get (by omega) (by omega)
  by_cases h18 : j < 443
  · exact kukstaticRange_413.get (by omega) (by omega)
  by_cases h19 : j < 473
  · exact kukstaticRange_443.get (by omega) (by omega)
  by_cases h20 : j < 503
  · exact kukstaticRange_473.get (by omega) (by omega)
  by_cases h21 : j < 533
  · exact kukstaticRange_503.get (by omega) (by omega)
  by_cases h22 : j < 563
  · exact kukstaticRange_533.get (by omega) (by omega)
  by_cases h23 : j < 593
  · exact kukstaticRange_563.get (by omega) (by omega)
  by_cases h24 : j < 623
  · exact kukstaticRange_593.get (by omega) (by omega)
  by_cases h25 : j < 653
  · exact kukstaticRange_623.get (by omega) (by omega)
  by_cases h26 : j < 683
  · exact kukstaticRange_653.get (by omega) (by omega)
  by_cases h27 : j < 713
  · exact kukstaticRange_683.get (by omega) (by omega)
  by_cases h28 : j < 743
  · exact kukstaticRange_713.get (by omega) (by omega)
  by_cases h29 : j < 773
  · exact kukstaticRange_743.get (by omega) (by omega)
  by_cases h30 : j < 803
  · exact kukstaticRange_773.get (by omega) (by omega)
  by_cases h31 : j < 833
  · exact kukstaticRange_803.get (by omega) (by omega)
  by_cases h32 : j < 863
  · exact kukstaticRange_833.get (by omega) (by omega)
  by_cases h33 : j < 893
  · exact kukstaticRange_863.get (by omega) (by omega)
  by_cases h34 : j < 923
  · exact kukstaticRange_893.get (by omega) (by omega)
  by_cases h35 : j < 953
  · exact kukstaticRange_923.get (by omega) (by omega)
  by_cases h36 : j < 983
  · exact kukstaticRange_953.get (by omega) (by omega)
  exact kukstaticRange_983.get (by omega) (by omega)

end
end LeanVM.Guest
