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
public import LeanVM.Guest.Memory.GuestCntWJ.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 1035, kujchkIdx j = true := by
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
  by_cases h8 : j < 206
  · exact kujstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kujstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kujstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kujstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kujstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kujstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 343
  · exact kujstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 349
  · exact kujstaticRange_343.get (by omega) (by omega)
  by_cases h16 : j < 355
  · exact kujstaticRange_349.get (by omega) (by omega)
  by_cases h17 : j < 385
  · exact kujstaticRange_355.get (by omega) (by omega)
  by_cases h18 : j < 415
  · exact kujstaticRange_385.get (by omega) (by omega)
  by_cases h19 : j < 445
  · exact kujstaticRange_415.get (by omega) (by omega)
  by_cases h20 : j < 475
  · exact kujstaticRange_445.get (by omega) (by omega)
  by_cases h21 : j < 505
  · exact kujstaticRange_475.get (by omega) (by omega)
  by_cases h22 : j < 535
  · exact kujstaticRange_505.get (by omega) (by omega)
  by_cases h23 : j < 565
  · exact kujstaticRange_535.get (by omega) (by omega)
  by_cases h24 : j < 595
  · exact kujstaticRange_565.get (by omega) (by omega)
  by_cases h25 : j < 625
  · exact kujstaticRange_595.get (by omega) (by omega)
  by_cases h26 : j < 655
  · exact kujstaticRange_625.get (by omega) (by omega)
  by_cases h27 : j < 685
  · exact kujstaticRange_655.get (by omega) (by omega)
  by_cases h28 : j < 715
  · exact kujstaticRange_685.get (by omega) (by omega)
  by_cases h29 : j < 745
  · exact kujstaticRange_715.get (by omega) (by omega)
  by_cases h30 : j < 775
  · exact kujstaticRange_745.get (by omega) (by omega)
  by_cases h31 : j < 805
  · exact kujstaticRange_775.get (by omega) (by omega)
  by_cases h32 : j < 835
  · exact kujstaticRange_805.get (by omega) (by omega)
  by_cases h33 : j < 865
  · exact kujstaticRange_835.get (by omega) (by omega)
  by_cases h34 : j < 895
  · exact kujstaticRange_865.get (by omega) (by omega)
  by_cases h35 : j < 925
  · exact kujstaticRange_895.get (by omega) (by omega)
  by_cases h36 : j < 955
  · exact kujstaticRange_925.get (by omega) (by omega)
  by_cases h37 : j < 985
  · exact kujstaticRange_955.get (by omega) (by omega)
  by_cases h38 : j < 1015
  · exact kujstaticRange_985.get (by omega) (by omega)
  exact kujstaticRange_1015.get (by omega) (by omega)

end
end LeanVM.Guest
