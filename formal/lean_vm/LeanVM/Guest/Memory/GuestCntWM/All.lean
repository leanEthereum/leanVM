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

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 1035, kumchkIdx j = true := by
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
  by_cases h8 : j < 206
  · exact kumstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kumstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kumstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kumstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kumstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kumstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 343
  · exact kumstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 349
  · exact kumstaticRange_343.get (by omega) (by omega)
  by_cases h16 : j < 355
  · exact kumstaticRange_349.get (by omega) (by omega)
  by_cases h17 : j < 385
  · exact kumstaticRange_355.get (by omega) (by omega)
  by_cases h18 : j < 415
  · exact kumstaticRange_385.get (by omega) (by omega)
  by_cases h19 : j < 445
  · exact kumstaticRange_415.get (by omega) (by omega)
  by_cases h20 : j < 475
  · exact kumstaticRange_445.get (by omega) (by omega)
  by_cases h21 : j < 505
  · exact kumstaticRange_475.get (by omega) (by omega)
  by_cases h22 : j < 535
  · exact kumstaticRange_505.get (by omega) (by omega)
  by_cases h23 : j < 565
  · exact kumstaticRange_535.get (by omega) (by omega)
  by_cases h24 : j < 595
  · exact kumstaticRange_565.get (by omega) (by omega)
  by_cases h25 : j < 625
  · exact kumstaticRange_595.get (by omega) (by omega)
  by_cases h26 : j < 655
  · exact kumstaticRange_625.get (by omega) (by omega)
  by_cases h27 : j < 685
  · exact kumstaticRange_655.get (by omega) (by omega)
  by_cases h28 : j < 715
  · exact kumstaticRange_685.get (by omega) (by omega)
  by_cases h29 : j < 745
  · exact kumstaticRange_715.get (by omega) (by omega)
  by_cases h30 : j < 775
  · exact kumstaticRange_745.get (by omega) (by omega)
  by_cases h31 : j < 805
  · exact kumstaticRange_775.get (by omega) (by omega)
  by_cases h32 : j < 835
  · exact kumstaticRange_805.get (by omega) (by omega)
  by_cases h33 : j < 865
  · exact kumstaticRange_835.get (by omega) (by omega)
  by_cases h34 : j < 895
  · exact kumstaticRange_865.get (by omega) (by omega)
  by_cases h35 : j < 925
  · exact kumstaticRange_895.get (by omega) (by omega)
  by_cases h36 : j < 955
  · exact kumstaticRange_925.get (by omega) (by omega)
  by_cases h37 : j < 985
  · exact kumstaticRange_955.get (by omega) (by omega)
  by_cases h38 : j < 1015
  · exact kumstaticRange_985.get (by omega) (by omega)
  exact kumstaticRange_1015.get (by omega) (by omega)

end
end LeanVM.Guest
