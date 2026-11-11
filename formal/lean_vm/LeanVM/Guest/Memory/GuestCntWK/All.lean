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
public import LeanVM.Guest.Memory.GuestCntWK.Part06

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 1035, kukchkIdx j = true := by
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
  by_cases h8 : j < 206
  · exact kukstaticRange_182.get (by omega) (by omega)
  by_cases h9 : j < 232
  · exact kukstaticRange_206.get (by omega) (by omega)
  by_cases h10 : j < 260
  · exact kukstaticRange_232.get (by omega) (by omega)
  by_cases h11 : j < 290
  · exact kukstaticRange_260.get (by omega) (by omega)
  by_cases h12 : j < 320
  · exact kukstaticRange_290.get (by omega) (by omega)
  by_cases h13 : j < 337
  · exact kukstaticRange_320.get (by omega) (by omega)
  by_cases h14 : j < 343
  · exact kukstaticRange_337.get (by omega) (by omega)
  by_cases h15 : j < 349
  · exact kukstaticRange_343.get (by omega) (by omega)
  by_cases h16 : j < 355
  · exact kukstaticRange_349.get (by omega) (by omega)
  by_cases h17 : j < 385
  · exact kukstaticRange_355.get (by omega) (by omega)
  by_cases h18 : j < 415
  · exact kukstaticRange_385.get (by omega) (by omega)
  by_cases h19 : j < 445
  · exact kukstaticRange_415.get (by omega) (by omega)
  by_cases h20 : j < 475
  · exact kukstaticRange_445.get (by omega) (by omega)
  by_cases h21 : j < 505
  · exact kukstaticRange_475.get (by omega) (by omega)
  by_cases h22 : j < 535
  · exact kukstaticRange_505.get (by omega) (by omega)
  by_cases h23 : j < 565
  · exact kukstaticRange_535.get (by omega) (by omega)
  by_cases h24 : j < 595
  · exact kukstaticRange_565.get (by omega) (by omega)
  by_cases h25 : j < 625
  · exact kukstaticRange_595.get (by omega) (by omega)
  by_cases h26 : j < 655
  · exact kukstaticRange_625.get (by omega) (by omega)
  by_cases h27 : j < 685
  · exact kukstaticRange_655.get (by omega) (by omega)
  by_cases h28 : j < 715
  · exact kukstaticRange_685.get (by omega) (by omega)
  by_cases h29 : j < 745
  · exact kukstaticRange_715.get (by omega) (by omega)
  by_cases h30 : j < 775
  · exact kukstaticRange_745.get (by omega) (by omega)
  by_cases h31 : j < 805
  · exact kukstaticRange_775.get (by omega) (by omega)
  by_cases h32 : j < 835
  · exact kukstaticRange_805.get (by omega) (by omega)
  by_cases h33 : j < 865
  · exact kukstaticRange_835.get (by omega) (by omega)
  by_cases h34 : j < 895
  · exact kukstaticRange_865.get (by omega) (by omega)
  by_cases h35 : j < 925
  · exact kukstaticRange_895.get (by omega) (by omega)
  by_cases h36 : j < 955
  · exact kukstaticRange_925.get (by omega) (by omega)
  by_cases h37 : j < 985
  · exact kukstaticRange_955.get (by omega) (by omega)
  by_cases h38 : j < 1015
  · exact kukstaticRange_985.get (by omega) (by omega)
  exact kukstaticRange_1015.get (by omega) (by omega)

end
end LeanVM.Guest
