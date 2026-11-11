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
public import LeanVM.Guest.Memory.GuestCntWX.Part07
public import LeanVM.Guest.Memory.GuestCntWX.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuxchkIdx_all : ∀ j < 1535, kuxchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kuxstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kuxstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kuxstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kuxstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kuxstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 259
  · exact kuxstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 289
  · exact kuxstaticRange_259.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kuxstaticRange_289.get (by omega) (by omega)
  by_cases h13 : j < 312
  · exact kuxstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kuxstaticRange_312.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kuxstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kuxstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kuxstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kuxstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kuxstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kuxstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kuxstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kuxstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kuxstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kuxstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kuxstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kuxstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kuxstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kuxstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kuxstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kuxstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kuxstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kuxstaticRange_825.get (by omega) (by omega)
  by_cases h33 : j < 885
  · exact kuxstaticRange_855.get (by omega) (by omega)
  by_cases h34 : j < 915
  · exact kuxstaticRange_885.get (by omega) (by omega)
  by_cases h35 : j < 945
  · exact kuxstaticRange_915.get (by omega) (by omega)
  by_cases h36 : j < 975
  · exact kuxstaticRange_945.get (by omega) (by omega)
  by_cases h37 : j < 1005
  · exact kuxstaticRange_975.get (by omega) (by omega)
  by_cases h38 : j < 1035
  · exact kuxstaticRange_1005.get (by omega) (by omega)
  by_cases h39 : j < 1065
  · exact kuxstaticRange_1035.get (by omega) (by omega)
  by_cases h40 : j < 1095
  · exact kuxstaticRange_1065.get (by omega) (by omega)
  by_cases h41 : j < 1125
  · exact kuxstaticRange_1095.get (by omega) (by omega)
  by_cases h42 : j < 1155
  · exact kuxstaticRange_1125.get (by omega) (by omega)
  by_cases h43 : j < 1185
  · exact kuxstaticRange_1155.get (by omega) (by omega)
  by_cases h44 : j < 1215
  · exact kuxstaticRange_1185.get (by omega) (by omega)
  by_cases h45 : j < 1245
  · exact kuxstaticRange_1215.get (by omega) (by omega)
  by_cases h46 : j < 1275
  · exact kuxstaticRange_1245.get (by omega) (by omega)
  by_cases h47 : j < 1305
  · exact kuxstaticRange_1275.get (by omega) (by omega)
  by_cases h48 : j < 1335
  · exact kuxstaticRange_1305.get (by omega) (by omega)
  by_cases h49 : j < 1365
  · exact kuxstaticRange_1335.get (by omega) (by omega)
  by_cases h50 : j < 1395
  · exact kuxstaticRange_1365.get (by omega) (by omega)
  by_cases h51 : j < 1425
  · exact kuxstaticRange_1395.get (by omega) (by omega)
  by_cases h52 : j < 1455
  · exact kuxstaticRange_1425.get (by omega) (by omega)
  by_cases h53 : j < 1485
  · exact kuxstaticRange_1455.get (by omega) (by omega)
  by_cases h54 : j < 1515
  · exact kuxstaticRange_1485.get (by omega) (by omega)
  exact kuxstaticRange_1515.get (by omega) (by omega)

end
end LeanVM.Guest
