/-
  LeanVM.Guest.Memory.GuestCntK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntK.Part00
public import LeanVM.Guest.Memory.GuestCntK.Part01
public import LeanVM.Guest.Memory.GuestCntK.Part02
public import LeanVM.Guest.Memory.GuestCntK.Part03
public import LeanVM.Guest.Memory.GuestCntK.Part04
public import LeanVM.Guest.Memory.GuestCntK.Part05
public import LeanVM.Guest.Memory.GuestCntK.Part06
public import LeanVM.Guest.Memory.GuestCntK.Part07
public import LeanVM.Guest.Memory.GuestCntK.Part08
public import LeanVM.Guest.Memory.GuestCntK.Part09
public import LeanVM.Guest.Memory.GuestCntK.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkchkIdx_19 : kwkchkIdx 19 = true := by
  have hb : blockB (kwklookJ 19) (kwkomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwksplit_19_0.1 rfl kwksplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwksplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwksplit_19_96]
    rfl
  exact kwkchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwkchkIdx_all : ∀ j < 1601, kwkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwkchkIdx_19
  by_cases h0 : j < 11
  · exact kwkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwkstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwkstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwkstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwkstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwkstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwkstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwkstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwkstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwkstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwkstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwkstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwkstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwkstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 337
  · exact kwkstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 340
  · exact kwkstaticRange_337.get (by omega) (by omega)
  by_cases h16 : j < 343
  · exact kwkstaticRange_340.get (by omega) (by omega)
  by_cases h17 : j < 345
  · exact kwkstaticRange_343.get (by omega) (by omega)
  by_cases h18 : j < 375
  · exact kwkstaticRange_345.get (by omega) (by omega)
  by_cases h19 : j < 405
  · exact kwkstaticRange_375.get (by omega) (by omega)
  by_cases h20 : j < 435
  · exact kwkstaticRange_405.get (by omega) (by omega)
  by_cases h21 : j < 465
  · exact kwkstaticRange_435.get (by omega) (by omega)
  by_cases h22 : j < 495
  · exact kwkstaticRange_465.get (by omega) (by omega)
  by_cases h23 : j < 525
  · exact kwkstaticRange_495.get (by omega) (by omega)
  by_cases h24 : j < 555
  · exact kwkstaticRange_525.get (by omega) (by omega)
  by_cases h25 : j < 585
  · exact kwkstaticRange_555.get (by omega) (by omega)
  by_cases h26 : j < 615
  · exact kwkstaticRange_585.get (by omega) (by omega)
  by_cases h27 : j < 645
  · exact kwkstaticRange_615.get (by omega) (by omega)
  by_cases h28 : j < 675
  · exact kwkstaticRange_645.get (by omega) (by omega)
  by_cases h29 : j < 705
  · exact kwkstaticRange_675.get (by omega) (by omega)
  by_cases h30 : j < 735
  · exact kwkstaticRange_705.get (by omega) (by omega)
  by_cases h31 : j < 765
  · exact kwkstaticRange_735.get (by omega) (by omega)
  by_cases h32 : j < 795
  · exact kwkstaticRange_765.get (by omega) (by omega)
  by_cases h33 : j < 825
  · exact kwkstaticRange_795.get (by omega) (by omega)
  by_cases h34 : j < 855
  · exact kwkstaticRange_825.get (by omega) (by omega)
  by_cases h35 : j < 885
  · exact kwkstaticRange_855.get (by omega) (by omega)
  by_cases h36 : j < 915
  · exact kwkstaticRange_885.get (by omega) (by omega)
  by_cases h37 : j < 945
  · exact kwkstaticRange_915.get (by omega) (by omega)
  by_cases h38 : j < 975
  · exact kwkstaticRange_945.get (by omega) (by omega)
  by_cases h39 : j < 1005
  · exact kwkstaticRange_975.get (by omega) (by omega)
  by_cases h40 : j < 1035
  · exact kwkstaticRange_1005.get (by omega) (by omega)
  by_cases h41 : j < 1065
  · exact kwkstaticRange_1035.get (by omega) (by omega)
  by_cases h42 : j < 1095
  · exact kwkstaticRange_1065.get (by omega) (by omega)
  by_cases h43 : j < 1125
  · exact kwkstaticRange_1095.get (by omega) (by omega)
  by_cases h44 : j < 1155
  · exact kwkstaticRange_1125.get (by omega) (by omega)
  by_cases h45 : j < 1185
  · exact kwkstaticRange_1155.get (by omega) (by omega)
  by_cases h46 : j < 1215
  · exact kwkstaticRange_1185.get (by omega) (by omega)
  by_cases h47 : j < 1245
  · exact kwkstaticRange_1215.get (by omega) (by omega)
  by_cases h48 : j < 1275
  · exact kwkstaticRange_1245.get (by omega) (by omega)
  by_cases h49 : j < 1305
  · exact kwkstaticRange_1275.get (by omega) (by omega)
  by_cases h50 : j < 1335
  · exact kwkstaticRange_1305.get (by omega) (by omega)
  by_cases h51 : j < 1365
  · exact kwkstaticRange_1335.get (by omega) (by omega)
  by_cases h52 : j < 1395
  · exact kwkstaticRange_1365.get (by omega) (by omega)
  by_cases h53 : j < 1425
  · exact kwkstaticRange_1395.get (by omega) (by omega)
  by_cases h54 : j < 1455
  · exact kwkstaticRange_1425.get (by omega) (by omega)
  by_cases h55 : j < 1485
  · exact kwkstaticRange_1455.get (by omega) (by omega)
  by_cases h56 : j < 1515
  · exact kwkstaticRange_1485.get (by omega) (by omega)
  by_cases h57 : j < 1545
  · exact kwkstaticRange_1515.get (by omega) (by omega)
  by_cases h58 : j < 1575
  · exact kwkstaticRange_1545.get (by omega) (by omega)
  exact kwkstaticRange_1575.get (by omega) (by omega)

end
end LeanVM.Guest
