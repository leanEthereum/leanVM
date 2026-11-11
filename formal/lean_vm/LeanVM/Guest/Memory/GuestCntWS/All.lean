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
public import LeanVM.Guest.Memory.GuestCntWS.Part07
public import LeanVM.Guest.Memory.GuestCntWS.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kuschkIdx_all : ∀ j < 1535, kuschkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kusstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kusstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kusstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kusstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kusstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 259
  · exact kusstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 289
  · exact kusstaticRange_259.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kusstaticRange_289.get (by omega) (by omega)
  by_cases h13 : j < 312
  · exact kusstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kusstaticRange_312.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kusstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kusstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kusstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kusstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kusstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kusstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kusstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kusstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kusstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kusstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kusstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kusstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kusstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kusstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kusstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kusstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kusstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kusstaticRange_825.get (by omega) (by omega)
  by_cases h33 : j < 885
  · exact kusstaticRange_855.get (by omega) (by omega)
  by_cases h34 : j < 915
  · exact kusstaticRange_885.get (by omega) (by omega)
  by_cases h35 : j < 945
  · exact kusstaticRange_915.get (by omega) (by omega)
  by_cases h36 : j < 975
  · exact kusstaticRange_945.get (by omega) (by omega)
  by_cases h37 : j < 1005
  · exact kusstaticRange_975.get (by omega) (by omega)
  by_cases h38 : j < 1035
  · exact kusstaticRange_1005.get (by omega) (by omega)
  by_cases h39 : j < 1065
  · exact kusstaticRange_1035.get (by omega) (by omega)
  by_cases h40 : j < 1095
  · exact kusstaticRange_1065.get (by omega) (by omega)
  by_cases h41 : j < 1125
  · exact kusstaticRange_1095.get (by omega) (by omega)
  by_cases h42 : j < 1155
  · exact kusstaticRange_1125.get (by omega) (by omega)
  by_cases h43 : j < 1185
  · exact kusstaticRange_1155.get (by omega) (by omega)
  by_cases h44 : j < 1215
  · exact kusstaticRange_1185.get (by omega) (by omega)
  by_cases h45 : j < 1245
  · exact kusstaticRange_1215.get (by omega) (by omega)
  by_cases h46 : j < 1275
  · exact kusstaticRange_1245.get (by omega) (by omega)
  by_cases h47 : j < 1305
  · exact kusstaticRange_1275.get (by omega) (by omega)
  by_cases h48 : j < 1335
  · exact kusstaticRange_1305.get (by omega) (by omega)
  by_cases h49 : j < 1365
  · exact kusstaticRange_1335.get (by omega) (by omega)
  by_cases h50 : j < 1395
  · exact kusstaticRange_1365.get (by omega) (by omega)
  by_cases h51 : j < 1425
  · exact kusstaticRange_1395.get (by omega) (by omega)
  by_cases h52 : j < 1455
  · exact kusstaticRange_1425.get (by omega) (by omega)
  by_cases h53 : j < 1485
  · exact kusstaticRange_1455.get (by omega) (by omega)
  by_cases h54 : j < 1515
  · exact kusstaticRange_1485.get (by omega) (by omega)
  exact kusstaticRange_1515.get (by omega) (by omega)

end
end LeanVM.Guest
