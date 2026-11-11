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
public import LeanVM.Guest.Memory.GuestCntWD.Part07
public import LeanVM.Guest.Memory.GuestCntWD.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kudchkIdx_all : ∀ j < 1535, kudchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kudstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kudstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kudstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kudstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kudstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 259
  · exact kudstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 289
  · exact kudstaticRange_259.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kudstaticRange_289.get (by omega) (by omega)
  by_cases h13 : j < 312
  · exact kudstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kudstaticRange_312.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kudstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kudstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kudstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kudstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kudstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kudstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kudstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kudstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kudstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kudstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kudstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kudstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kudstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kudstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kudstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kudstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kudstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kudstaticRange_825.get (by omega) (by omega)
  by_cases h33 : j < 885
  · exact kudstaticRange_855.get (by omega) (by omega)
  by_cases h34 : j < 915
  · exact kudstaticRange_885.get (by omega) (by omega)
  by_cases h35 : j < 945
  · exact kudstaticRange_915.get (by omega) (by omega)
  by_cases h36 : j < 975
  · exact kudstaticRange_945.get (by omega) (by omega)
  by_cases h37 : j < 1005
  · exact kudstaticRange_975.get (by omega) (by omega)
  by_cases h38 : j < 1035
  · exact kudstaticRange_1005.get (by omega) (by omega)
  by_cases h39 : j < 1065
  · exact kudstaticRange_1035.get (by omega) (by omega)
  by_cases h40 : j < 1095
  · exact kudstaticRange_1065.get (by omega) (by omega)
  by_cases h41 : j < 1125
  · exact kudstaticRange_1095.get (by omega) (by omega)
  by_cases h42 : j < 1155
  · exact kudstaticRange_1125.get (by omega) (by omega)
  by_cases h43 : j < 1185
  · exact kudstaticRange_1155.get (by omega) (by omega)
  by_cases h44 : j < 1215
  · exact kudstaticRange_1185.get (by omega) (by omega)
  by_cases h45 : j < 1245
  · exact kudstaticRange_1215.get (by omega) (by omega)
  by_cases h46 : j < 1275
  · exact kudstaticRange_1245.get (by omega) (by omega)
  by_cases h47 : j < 1305
  · exact kudstaticRange_1275.get (by omega) (by omega)
  by_cases h48 : j < 1335
  · exact kudstaticRange_1305.get (by omega) (by omega)
  by_cases h49 : j < 1365
  · exact kudstaticRange_1335.get (by omega) (by omega)
  by_cases h50 : j < 1395
  · exact kudstaticRange_1365.get (by omega) (by omega)
  by_cases h51 : j < 1425
  · exact kudstaticRange_1395.get (by omega) (by omega)
  by_cases h52 : j < 1455
  · exact kudstaticRange_1425.get (by omega) (by omega)
  by_cases h53 : j < 1485
  · exact kudstaticRange_1455.get (by omega) (by omega)
  by_cases h54 : j < 1515
  · exact kudstaticRange_1485.get (by omega) (by omega)
  exact kudstaticRange_1515.get (by omega) (by omega)

end
end LeanVM.Guest
