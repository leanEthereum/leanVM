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
public import LeanVM.Guest.Memory.GuestCntWX.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuxchkIdx_all : ∀ j < 1035, kuxchkIdx j = true := by
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
  by_cases h8 : j < 206
  · exact kuxstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kuxstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kuxstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kuxstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kuxstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kuxstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 343
  · exact kuxstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 349
  · exact kuxstaticRange_343.get (by omega) (by omega)
  by_cases h16 : j < 355
  · exact kuxstaticRange_349.get (by omega) (by omega)
  by_cases h17 : j < 385
  · exact kuxstaticRange_355.get (by omega) (by omega)
  by_cases h18 : j < 415
  · exact kuxstaticRange_385.get (by omega) (by omega)
  by_cases h19 : j < 445
  · exact kuxstaticRange_415.get (by omega) (by omega)
  by_cases h20 : j < 475
  · exact kuxstaticRange_445.get (by omega) (by omega)
  by_cases h21 : j < 505
  · exact kuxstaticRange_475.get (by omega) (by omega)
  by_cases h22 : j < 535
  · exact kuxstaticRange_505.get (by omega) (by omega)
  by_cases h23 : j < 565
  · exact kuxstaticRange_535.get (by omega) (by omega)
  by_cases h24 : j < 595
  · exact kuxstaticRange_565.get (by omega) (by omega)
  by_cases h25 : j < 625
  · exact kuxstaticRange_595.get (by omega) (by omega)
  by_cases h26 : j < 655
  · exact kuxstaticRange_625.get (by omega) (by omega)
  by_cases h27 : j < 685
  · exact kuxstaticRange_655.get (by omega) (by omega)
  by_cases h28 : j < 715
  · exact kuxstaticRange_685.get (by omega) (by omega)
  by_cases h29 : j < 745
  · exact kuxstaticRange_715.get (by omega) (by omega)
  by_cases h30 : j < 775
  · exact kuxstaticRange_745.get (by omega) (by omega)
  by_cases h31 : j < 805
  · exact kuxstaticRange_775.get (by omega) (by omega)
  by_cases h32 : j < 835
  · exact kuxstaticRange_805.get (by omega) (by omega)
  by_cases h33 : j < 865
  · exact kuxstaticRange_835.get (by omega) (by omega)
  by_cases h34 : j < 895
  · exact kuxstaticRange_865.get (by omega) (by omega)
  by_cases h35 : j < 925
  · exact kuxstaticRange_895.get (by omega) (by omega)
  by_cases h36 : j < 955
  · exact kuxstaticRange_925.get (by omega) (by omega)
  by_cases h37 : j < 985
  · exact kuxstaticRange_955.get (by omega) (by omega)
  by_cases h38 : j < 1015
  · exact kuxstaticRange_985.get (by omega) (by omega)
  exact kuxstaticRange_1015.get (by omega) (by omega)

end
end LeanVM.Guest
