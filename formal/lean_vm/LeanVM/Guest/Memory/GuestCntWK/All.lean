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
public import LeanVM.Guest.Memory.GuestCntWK.Part07
public import LeanVM.Guest.Memory.GuestCntWK.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kukchkIdx_all : ∀ j < 1535, kukchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kukstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kukstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kukstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kukstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kukstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 259
  · exact kukstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 289
  · exact kukstaticRange_259.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kukstaticRange_289.get (by omega) (by omega)
  by_cases h13 : j < 312
  · exact kukstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kukstaticRange_312.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kukstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kukstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kukstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kukstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kukstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kukstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kukstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kukstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kukstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kukstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kukstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kukstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kukstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kukstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kukstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kukstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kukstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kukstaticRange_825.get (by omega) (by omega)
  by_cases h33 : j < 885
  · exact kukstaticRange_855.get (by omega) (by omega)
  by_cases h34 : j < 915
  · exact kukstaticRange_885.get (by omega) (by omega)
  by_cases h35 : j < 945
  · exact kukstaticRange_915.get (by omega) (by omega)
  by_cases h36 : j < 975
  · exact kukstaticRange_945.get (by omega) (by omega)
  by_cases h37 : j < 1005
  · exact kukstaticRange_975.get (by omega) (by omega)
  by_cases h38 : j < 1035
  · exact kukstaticRange_1005.get (by omega) (by omega)
  by_cases h39 : j < 1065
  · exact kukstaticRange_1035.get (by omega) (by omega)
  by_cases h40 : j < 1095
  · exact kukstaticRange_1065.get (by omega) (by omega)
  by_cases h41 : j < 1125
  · exact kukstaticRange_1095.get (by omega) (by omega)
  by_cases h42 : j < 1155
  · exact kukstaticRange_1125.get (by omega) (by omega)
  by_cases h43 : j < 1185
  · exact kukstaticRange_1155.get (by omega) (by omega)
  by_cases h44 : j < 1215
  · exact kukstaticRange_1185.get (by omega) (by omega)
  by_cases h45 : j < 1245
  · exact kukstaticRange_1215.get (by omega) (by omega)
  by_cases h46 : j < 1275
  · exact kukstaticRange_1245.get (by omega) (by omega)
  by_cases h47 : j < 1305
  · exact kukstaticRange_1275.get (by omega) (by omega)
  by_cases h48 : j < 1335
  · exact kukstaticRange_1305.get (by omega) (by omega)
  by_cases h49 : j < 1365
  · exact kukstaticRange_1335.get (by omega) (by omega)
  by_cases h50 : j < 1395
  · exact kukstaticRange_1365.get (by omega) (by omega)
  by_cases h51 : j < 1425
  · exact kukstaticRange_1395.get (by omega) (by omega)
  by_cases h52 : j < 1455
  · exact kukstaticRange_1425.get (by omega) (by omega)
  by_cases h53 : j < 1485
  · exact kukstaticRange_1455.get (by omega) (by omega)
  by_cases h54 : j < 1515
  · exact kukstaticRange_1485.get (by omega) (by omega)
  exact kukstaticRange_1515.get (by omega) (by omega)

end
end LeanVM.Guest
