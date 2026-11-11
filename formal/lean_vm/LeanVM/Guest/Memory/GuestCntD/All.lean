/-
  LeanVM.Guest.Memory.GuestCntD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntD.Part00
public import LeanVM.Guest.Memory.GuestCntD.Part01
public import LeanVM.Guest.Memory.GuestCntD.Part02
public import LeanVM.Guest.Memory.GuestCntD.Part03
public import LeanVM.Guest.Memory.GuestCntD.Part04
public import LeanVM.Guest.Memory.GuestCntD.Part05
public import LeanVM.Guest.Memory.GuestCntD.Part06
public import LeanVM.Guest.Memory.GuestCntD.Part07
public import LeanVM.Guest.Memory.GuestCntD.Part08
public import LeanVM.Guest.Memory.GuestCntD.Part09
public import LeanVM.Guest.Memory.GuestCntD.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdchkIdx_19 : kwdchkIdx 19 = true := by
  have hb : blockB (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwdsplit_19_0.1 rfl kwdsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwdsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwdsplit_19_96]
    rfl
  exact kwdchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwdchkIdx_all : ∀ j < 1601, kwdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwdchkIdx_19
  by_cases h0 : j < 11
  · exact kwdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwdstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwdstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwdstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwdstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwdstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwdstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwdstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwdstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwdstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwdstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwdstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwdstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwdstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 337
  · exact kwdstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 340
  · exact kwdstaticRange_337.get (by omega) (by omega)
  by_cases h16 : j < 343
  · exact kwdstaticRange_340.get (by omega) (by omega)
  by_cases h17 : j < 345
  · exact kwdstaticRange_343.get (by omega) (by omega)
  by_cases h18 : j < 375
  · exact kwdstaticRange_345.get (by omega) (by omega)
  by_cases h19 : j < 405
  · exact kwdstaticRange_375.get (by omega) (by omega)
  by_cases h20 : j < 435
  · exact kwdstaticRange_405.get (by omega) (by omega)
  by_cases h21 : j < 465
  · exact kwdstaticRange_435.get (by omega) (by omega)
  by_cases h22 : j < 495
  · exact kwdstaticRange_465.get (by omega) (by omega)
  by_cases h23 : j < 525
  · exact kwdstaticRange_495.get (by omega) (by omega)
  by_cases h24 : j < 555
  · exact kwdstaticRange_525.get (by omega) (by omega)
  by_cases h25 : j < 585
  · exact kwdstaticRange_555.get (by omega) (by omega)
  by_cases h26 : j < 615
  · exact kwdstaticRange_585.get (by omega) (by omega)
  by_cases h27 : j < 645
  · exact kwdstaticRange_615.get (by omega) (by omega)
  by_cases h28 : j < 675
  · exact kwdstaticRange_645.get (by omega) (by omega)
  by_cases h29 : j < 705
  · exact kwdstaticRange_675.get (by omega) (by omega)
  by_cases h30 : j < 735
  · exact kwdstaticRange_705.get (by omega) (by omega)
  by_cases h31 : j < 765
  · exact kwdstaticRange_735.get (by omega) (by omega)
  by_cases h32 : j < 795
  · exact kwdstaticRange_765.get (by omega) (by omega)
  by_cases h33 : j < 825
  · exact kwdstaticRange_795.get (by omega) (by omega)
  by_cases h34 : j < 855
  · exact kwdstaticRange_825.get (by omega) (by omega)
  by_cases h35 : j < 885
  · exact kwdstaticRange_855.get (by omega) (by omega)
  by_cases h36 : j < 915
  · exact kwdstaticRange_885.get (by omega) (by omega)
  by_cases h37 : j < 945
  · exact kwdstaticRange_915.get (by omega) (by omega)
  by_cases h38 : j < 975
  · exact kwdstaticRange_945.get (by omega) (by omega)
  by_cases h39 : j < 1005
  · exact kwdstaticRange_975.get (by omega) (by omega)
  by_cases h40 : j < 1035
  · exact kwdstaticRange_1005.get (by omega) (by omega)
  by_cases h41 : j < 1065
  · exact kwdstaticRange_1035.get (by omega) (by omega)
  by_cases h42 : j < 1095
  · exact kwdstaticRange_1065.get (by omega) (by omega)
  by_cases h43 : j < 1125
  · exact kwdstaticRange_1095.get (by omega) (by omega)
  by_cases h44 : j < 1155
  · exact kwdstaticRange_1125.get (by omega) (by omega)
  by_cases h45 : j < 1185
  · exact kwdstaticRange_1155.get (by omega) (by omega)
  by_cases h46 : j < 1215
  · exact kwdstaticRange_1185.get (by omega) (by omega)
  by_cases h47 : j < 1245
  · exact kwdstaticRange_1215.get (by omega) (by omega)
  by_cases h48 : j < 1275
  · exact kwdstaticRange_1245.get (by omega) (by omega)
  by_cases h49 : j < 1305
  · exact kwdstaticRange_1275.get (by omega) (by omega)
  by_cases h50 : j < 1335
  · exact kwdstaticRange_1305.get (by omega) (by omega)
  by_cases h51 : j < 1365
  · exact kwdstaticRange_1335.get (by omega) (by omega)
  by_cases h52 : j < 1395
  · exact kwdstaticRange_1365.get (by omega) (by omega)
  by_cases h53 : j < 1425
  · exact kwdstaticRange_1395.get (by omega) (by omega)
  by_cases h54 : j < 1455
  · exact kwdstaticRange_1425.get (by omega) (by omega)
  by_cases h55 : j < 1485
  · exact kwdstaticRange_1455.get (by omega) (by omega)
  by_cases h56 : j < 1515
  · exact kwdstaticRange_1485.get (by omega) (by omega)
  by_cases h57 : j < 1545
  · exact kwdstaticRange_1515.get (by omega) (by omega)
  by_cases h58 : j < 1575
  · exact kwdstaticRange_1545.get (by omega) (by omega)
  exact kwdstaticRange_1575.get (by omega) (by omega)

end
end LeanVM.Guest
