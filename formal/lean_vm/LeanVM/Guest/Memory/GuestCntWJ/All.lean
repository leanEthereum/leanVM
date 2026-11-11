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
public import LeanVM.Guest.Memory.GuestCntWJ.Part07
public import LeanVM.Guest.Memory.GuestCntWJ.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kujchkIdx_all : ∀ j < 1535, kujchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kujstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kujstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kujstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kujstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kujstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 259
  · exact kujstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 289
  · exact kujstaticRange_259.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kujstaticRange_289.get (by omega) (by omega)
  by_cases h13 : j < 312
  · exact kujstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kujstaticRange_312.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kujstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kujstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kujstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kujstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kujstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kujstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kujstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kujstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kujstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kujstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kujstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kujstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kujstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kujstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kujstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kujstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kujstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kujstaticRange_825.get (by omega) (by omega)
  by_cases h33 : j < 885
  · exact kujstaticRange_855.get (by omega) (by omega)
  by_cases h34 : j < 915
  · exact kujstaticRange_885.get (by omega) (by omega)
  by_cases h35 : j < 945
  · exact kujstaticRange_915.get (by omega) (by omega)
  by_cases h36 : j < 975
  · exact kujstaticRange_945.get (by omega) (by omega)
  by_cases h37 : j < 1005
  · exact kujstaticRange_975.get (by omega) (by omega)
  by_cases h38 : j < 1035
  · exact kujstaticRange_1005.get (by omega) (by omega)
  by_cases h39 : j < 1065
  · exact kujstaticRange_1035.get (by omega) (by omega)
  by_cases h40 : j < 1095
  · exact kujstaticRange_1065.get (by omega) (by omega)
  by_cases h41 : j < 1125
  · exact kujstaticRange_1095.get (by omega) (by omega)
  by_cases h42 : j < 1155
  · exact kujstaticRange_1125.get (by omega) (by omega)
  by_cases h43 : j < 1185
  · exact kujstaticRange_1155.get (by omega) (by omega)
  by_cases h44 : j < 1215
  · exact kujstaticRange_1185.get (by omega) (by omega)
  by_cases h45 : j < 1245
  · exact kujstaticRange_1215.get (by omega) (by omega)
  by_cases h46 : j < 1275
  · exact kujstaticRange_1245.get (by omega) (by omega)
  by_cases h47 : j < 1305
  · exact kujstaticRange_1275.get (by omega) (by omega)
  by_cases h48 : j < 1335
  · exact kujstaticRange_1305.get (by omega) (by omega)
  by_cases h49 : j < 1365
  · exact kujstaticRange_1335.get (by omega) (by omega)
  by_cases h50 : j < 1395
  · exact kujstaticRange_1365.get (by omega) (by omega)
  by_cases h51 : j < 1425
  · exact kujstaticRange_1395.get (by omega) (by omega)
  by_cases h52 : j < 1455
  · exact kujstaticRange_1425.get (by omega) (by omega)
  by_cases h53 : j < 1485
  · exact kujstaticRange_1455.get (by omega) (by omega)
  by_cases h54 : j < 1515
  · exact kujstaticRange_1485.get (by omega) (by omega)
  exact kujstaticRange_1515.get (by omega) (by omega)

end
end LeanVM.Guest
