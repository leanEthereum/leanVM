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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 1035, kuschkIdx j = true := by
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
  by_cases h8 : j < 206
  · exact kusstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kusstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kusstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kusstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kusstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kusstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 343
  · exact kusstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 349
  · exact kusstaticRange_343.get (by omega) (by omega)
  by_cases h16 : j < 355
  · exact kusstaticRange_349.get (by omega) (by omega)
  by_cases h17 : j < 385
  · exact kusstaticRange_355.get (by omega) (by omega)
  by_cases h18 : j < 415
  · exact kusstaticRange_385.get (by omega) (by omega)
  by_cases h19 : j < 445
  · exact kusstaticRange_415.get (by omega) (by omega)
  by_cases h20 : j < 475
  · exact kusstaticRange_445.get (by omega) (by omega)
  by_cases h21 : j < 505
  · exact kusstaticRange_475.get (by omega) (by omega)
  by_cases h22 : j < 535
  · exact kusstaticRange_505.get (by omega) (by omega)
  by_cases h23 : j < 565
  · exact kusstaticRange_535.get (by omega) (by omega)
  by_cases h24 : j < 595
  · exact kusstaticRange_565.get (by omega) (by omega)
  by_cases h25 : j < 625
  · exact kusstaticRange_595.get (by omega) (by omega)
  by_cases h26 : j < 655
  · exact kusstaticRange_625.get (by omega) (by omega)
  by_cases h27 : j < 685
  · exact kusstaticRange_655.get (by omega) (by omega)
  by_cases h28 : j < 715
  · exact kusstaticRange_685.get (by omega) (by omega)
  by_cases h29 : j < 745
  · exact kusstaticRange_715.get (by omega) (by omega)
  by_cases h30 : j < 775
  · exact kusstaticRange_745.get (by omega) (by omega)
  by_cases h31 : j < 805
  · exact kusstaticRange_775.get (by omega) (by omega)
  by_cases h32 : j < 835
  · exact kusstaticRange_805.get (by omega) (by omega)
  by_cases h33 : j < 865
  · exact kusstaticRange_835.get (by omega) (by omega)
  by_cases h34 : j < 895
  · exact kusstaticRange_865.get (by omega) (by omega)
  by_cases h35 : j < 925
  · exact kusstaticRange_895.get (by omega) (by omega)
  by_cases h36 : j < 955
  · exact kusstaticRange_925.get (by omega) (by omega)
  by_cases h37 : j < 985
  · exact kusstaticRange_955.get (by omega) (by omega)
  by_cases h38 : j < 1015
  · exact kusstaticRange_985.get (by omega) (by omega)
  exact kusstaticRange_1015.get (by omega) (by omega)

end
end LeanVM.Guest
