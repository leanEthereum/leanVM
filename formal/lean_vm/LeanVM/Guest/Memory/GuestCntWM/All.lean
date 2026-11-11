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
public import LeanVM.Guest.Memory.GuestCntWM.Part07
public import LeanVM.Guest.Memory.GuestCntWM.Part08

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

theorem kumchkIdx_all : ∀ j < 1535, kumchkIdx j = true := by
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
  by_cases h5 : j < 128
  · exact kumstaticRange_104.get (by omega) (by omega)
  by_cases h6 : j < 155
  · exact kumstaticRange_128.get (by omega) (by omega)
  by_cases h7 : j < 181
  · exact kumstaticRange_155.get (by omega) (by omega)
  by_cases h8 : j < 205
  · exact kumstaticRange_181.get (by omega) (by omega)
  by_cases h9 : j < 231
  · exact kumstaticRange_205.get (by omega) (by omega)
  by_cases h10 : j < 259
  · exact kumstaticRange_231.get (by omega) (by omega)
  by_cases h11 : j < 289
  · exact kumstaticRange_259.get (by omega) (by omega)
  by_cases h12 : j < 309
  · exact kumstaticRange_289.get (by omega) (by omega)
  by_cases h13 : j < 312
  · exact kumstaticRange_309.get (by omega) (by omega)
  by_cases h14 : j < 315
  · exact kumstaticRange_312.get (by omega) (by omega)
  by_cases h15 : j < 345
  · exact kumstaticRange_315.get (by omega) (by omega)
  by_cases h16 : j < 375
  · exact kumstaticRange_345.get (by omega) (by omega)
  by_cases h17 : j < 405
  · exact kumstaticRange_375.get (by omega) (by omega)
  by_cases h18 : j < 435
  · exact kumstaticRange_405.get (by omega) (by omega)
  by_cases h19 : j < 465
  · exact kumstaticRange_435.get (by omega) (by omega)
  by_cases h20 : j < 495
  · exact kumstaticRange_465.get (by omega) (by omega)
  by_cases h21 : j < 525
  · exact kumstaticRange_495.get (by omega) (by omega)
  by_cases h22 : j < 555
  · exact kumstaticRange_525.get (by omega) (by omega)
  by_cases h23 : j < 585
  · exact kumstaticRange_555.get (by omega) (by omega)
  by_cases h24 : j < 615
  · exact kumstaticRange_585.get (by omega) (by omega)
  by_cases h25 : j < 645
  · exact kumstaticRange_615.get (by omega) (by omega)
  by_cases h26 : j < 675
  · exact kumstaticRange_645.get (by omega) (by omega)
  by_cases h27 : j < 705
  · exact kumstaticRange_675.get (by omega) (by omega)
  by_cases h28 : j < 735
  · exact kumstaticRange_705.get (by omega) (by omega)
  by_cases h29 : j < 765
  · exact kumstaticRange_735.get (by omega) (by omega)
  by_cases h30 : j < 795
  · exact kumstaticRange_765.get (by omega) (by omega)
  by_cases h31 : j < 825
  · exact kumstaticRange_795.get (by omega) (by omega)
  by_cases h32 : j < 855
  · exact kumstaticRange_825.get (by omega) (by omega)
  by_cases h33 : j < 885
  · exact kumstaticRange_855.get (by omega) (by omega)
  by_cases h34 : j < 915
  · exact kumstaticRange_885.get (by omega) (by omega)
  by_cases h35 : j < 945
  · exact kumstaticRange_915.get (by omega) (by omega)
  by_cases h36 : j < 975
  · exact kumstaticRange_945.get (by omega) (by omega)
  by_cases h37 : j < 1005
  · exact kumstaticRange_975.get (by omega) (by omega)
  by_cases h38 : j < 1035
  · exact kumstaticRange_1005.get (by omega) (by omega)
  by_cases h39 : j < 1065
  · exact kumstaticRange_1035.get (by omega) (by omega)
  by_cases h40 : j < 1095
  · exact kumstaticRange_1065.get (by omega) (by omega)
  by_cases h41 : j < 1125
  · exact kumstaticRange_1095.get (by omega) (by omega)
  by_cases h42 : j < 1155
  · exact kumstaticRange_1125.get (by omega) (by omega)
  by_cases h43 : j < 1185
  · exact kumstaticRange_1155.get (by omega) (by omega)
  by_cases h44 : j < 1215
  · exact kumstaticRange_1185.get (by omega) (by omega)
  by_cases h45 : j < 1245
  · exact kumstaticRange_1215.get (by omega) (by omega)
  by_cases h46 : j < 1275
  · exact kumstaticRange_1245.get (by omega) (by omega)
  by_cases h47 : j < 1305
  · exact kumstaticRange_1275.get (by omega) (by omega)
  by_cases h48 : j < 1335
  · exact kumstaticRange_1305.get (by omega) (by omega)
  by_cases h49 : j < 1365
  · exact kumstaticRange_1335.get (by omega) (by omega)
  by_cases h50 : j < 1395
  · exact kumstaticRange_1365.get (by omega) (by omega)
  by_cases h51 : j < 1425
  · exact kumstaticRange_1395.get (by omega) (by omega)
  by_cases h52 : j < 1455
  · exact kumstaticRange_1425.get (by omega) (by omega)
  by_cases h53 : j < 1485
  · exact kumstaticRange_1455.get (by omega) (by omega)
  by_cases h54 : j < 1515
  · exact kumstaticRange_1485.get (by omega) (by omega)
  exact kumstaticRange_1515.get (by omega) (by omega)

end
end LeanVM.Guest
