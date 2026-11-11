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
public import LeanVM.Guest.Memory.GuestCntWD.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 1035, kudchkIdx j = true := by
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
  by_cases h8 : j < 206
  · exact kudstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kudstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kudstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kudstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kudstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kudstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 343
  · exact kudstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 349
  · exact kudstaticRange_343.get (by omega) (by omega)
  by_cases h16 : j < 355
  · exact kudstaticRange_349.get (by omega) (by omega)
  by_cases h17 : j < 385
  · exact kudstaticRange_355.get (by omega) (by omega)
  by_cases h18 : j < 415
  · exact kudstaticRange_385.get (by omega) (by omega)
  by_cases h19 : j < 445
  · exact kudstaticRange_415.get (by omega) (by omega)
  by_cases h20 : j < 475
  · exact kudstaticRange_445.get (by omega) (by omega)
  by_cases h21 : j < 505
  · exact kudstaticRange_475.get (by omega) (by omega)
  by_cases h22 : j < 535
  · exact kudstaticRange_505.get (by omega) (by omega)
  by_cases h23 : j < 565
  · exact kudstaticRange_535.get (by omega) (by omega)
  by_cases h24 : j < 595
  · exact kudstaticRange_565.get (by omega) (by omega)
  by_cases h25 : j < 625
  · exact kudstaticRange_595.get (by omega) (by omega)
  by_cases h26 : j < 655
  · exact kudstaticRange_625.get (by omega) (by omega)
  by_cases h27 : j < 685
  · exact kudstaticRange_655.get (by omega) (by omega)
  by_cases h28 : j < 715
  · exact kudstaticRange_685.get (by omega) (by omega)
  by_cases h29 : j < 745
  · exact kudstaticRange_715.get (by omega) (by omega)
  by_cases h30 : j < 775
  · exact kudstaticRange_745.get (by omega) (by omega)
  by_cases h31 : j < 805
  · exact kudstaticRange_775.get (by omega) (by omega)
  by_cases h32 : j < 835
  · exact kudstaticRange_805.get (by omega) (by omega)
  by_cases h33 : j < 865
  · exact kudstaticRange_835.get (by omega) (by omega)
  by_cases h34 : j < 895
  · exact kudstaticRange_865.get (by omega) (by omega)
  by_cases h35 : j < 925
  · exact kudstaticRange_895.get (by omega) (by omega)
  by_cases h36 : j < 955
  · exact kudstaticRange_925.get (by omega) (by omega)
  by_cases h37 : j < 985
  · exact kudstaticRange_955.get (by omega) (by omega)
  by_cases h38 : j < 1015
  · exact kudstaticRange_985.get (by omega) (by omega)
  exact kudstaticRange_1015.get (by omega) (by omega)

end
end LeanVM.Guest
