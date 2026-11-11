/-
  LeanVM.Guest.Memory.GuestCntS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntS.Part00
public import LeanVM.Guest.Memory.GuestCntS.Part01
public import LeanVM.Guest.Memory.GuestCntS.Part02
public import LeanVM.Guest.Memory.GuestCntS.Part03
public import LeanVM.Guest.Memory.GuestCntS.Part04
public import LeanVM.Guest.Memory.GuestCntS.Part05
public import LeanVM.Guest.Memory.GuestCntS.Part06
public import LeanVM.Guest.Memory.GuestCntS.Part07
public import LeanVM.Guest.Memory.GuestCntS.Part08
public import LeanVM.Guest.Memory.GuestCntS.Part09
public import LeanVM.Guest.Memory.GuestCntS.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwschkIdx_19 : kwschkIdx 19 = true := by
  have hb : blockB (kwslookJ 19) (kwsomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwssplit_19_0.1 rfl kwssplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwssplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwssplit_19_96]
    rfl
  exact kwschkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwschkIdx_all : ∀ j < 1601, kwschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwschkIdx_19
  by_cases h0 : j < 11
  · exact kwsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwsstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwsstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwsstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwsstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwsstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwsstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwsstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwsstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwsstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwsstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwsstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwsstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwsstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 337
  · exact kwsstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 340
  · exact kwsstaticRange_337.get (by omega) (by omega)
  by_cases h16 : j < 343
  · exact kwsstaticRange_340.get (by omega) (by omega)
  by_cases h17 : j < 345
  · exact kwsstaticRange_343.get (by omega) (by omega)
  by_cases h18 : j < 375
  · exact kwsstaticRange_345.get (by omega) (by omega)
  by_cases h19 : j < 405
  · exact kwsstaticRange_375.get (by omega) (by omega)
  by_cases h20 : j < 435
  · exact kwsstaticRange_405.get (by omega) (by omega)
  by_cases h21 : j < 465
  · exact kwsstaticRange_435.get (by omega) (by omega)
  by_cases h22 : j < 495
  · exact kwsstaticRange_465.get (by omega) (by omega)
  by_cases h23 : j < 525
  · exact kwsstaticRange_495.get (by omega) (by omega)
  by_cases h24 : j < 555
  · exact kwsstaticRange_525.get (by omega) (by omega)
  by_cases h25 : j < 585
  · exact kwsstaticRange_555.get (by omega) (by omega)
  by_cases h26 : j < 615
  · exact kwsstaticRange_585.get (by omega) (by omega)
  by_cases h27 : j < 645
  · exact kwsstaticRange_615.get (by omega) (by omega)
  by_cases h28 : j < 675
  · exact kwsstaticRange_645.get (by omega) (by omega)
  by_cases h29 : j < 705
  · exact kwsstaticRange_675.get (by omega) (by omega)
  by_cases h30 : j < 735
  · exact kwsstaticRange_705.get (by omega) (by omega)
  by_cases h31 : j < 765
  · exact kwsstaticRange_735.get (by omega) (by omega)
  by_cases h32 : j < 795
  · exact kwsstaticRange_765.get (by omega) (by omega)
  by_cases h33 : j < 825
  · exact kwsstaticRange_795.get (by omega) (by omega)
  by_cases h34 : j < 855
  · exact kwsstaticRange_825.get (by omega) (by omega)
  by_cases h35 : j < 885
  · exact kwsstaticRange_855.get (by omega) (by omega)
  by_cases h36 : j < 915
  · exact kwsstaticRange_885.get (by omega) (by omega)
  by_cases h37 : j < 945
  · exact kwsstaticRange_915.get (by omega) (by omega)
  by_cases h38 : j < 975
  · exact kwsstaticRange_945.get (by omega) (by omega)
  by_cases h39 : j < 1005
  · exact kwsstaticRange_975.get (by omega) (by omega)
  by_cases h40 : j < 1035
  · exact kwsstaticRange_1005.get (by omega) (by omega)
  by_cases h41 : j < 1065
  · exact kwsstaticRange_1035.get (by omega) (by omega)
  by_cases h42 : j < 1095
  · exact kwsstaticRange_1065.get (by omega) (by omega)
  by_cases h43 : j < 1125
  · exact kwsstaticRange_1095.get (by omega) (by omega)
  by_cases h44 : j < 1155
  · exact kwsstaticRange_1125.get (by omega) (by omega)
  by_cases h45 : j < 1185
  · exact kwsstaticRange_1155.get (by omega) (by omega)
  by_cases h46 : j < 1215
  · exact kwsstaticRange_1185.get (by omega) (by omega)
  by_cases h47 : j < 1245
  · exact kwsstaticRange_1215.get (by omega) (by omega)
  by_cases h48 : j < 1275
  · exact kwsstaticRange_1245.get (by omega) (by omega)
  by_cases h49 : j < 1305
  · exact kwsstaticRange_1275.get (by omega) (by omega)
  by_cases h50 : j < 1335
  · exact kwsstaticRange_1305.get (by omega) (by omega)
  by_cases h51 : j < 1365
  · exact kwsstaticRange_1335.get (by omega) (by omega)
  by_cases h52 : j < 1395
  · exact kwsstaticRange_1365.get (by omega) (by omega)
  by_cases h53 : j < 1425
  · exact kwsstaticRange_1395.get (by omega) (by omega)
  by_cases h54 : j < 1455
  · exact kwsstaticRange_1425.get (by omega) (by omega)
  by_cases h55 : j < 1485
  · exact kwsstaticRange_1455.get (by omega) (by omega)
  by_cases h56 : j < 1515
  · exact kwsstaticRange_1485.get (by omega) (by omega)
  by_cases h57 : j < 1545
  · exact kwsstaticRange_1515.get (by omega) (by omega)
  by_cases h58 : j < 1575
  · exact kwsstaticRange_1545.get (by omega) (by omega)
  exact kwsstaticRange_1575.get (by omega) (by omega)

end
end LeanVM.Guest
