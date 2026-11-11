/-
  LeanVM.Guest.Memory.GuestCntJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntJ.Part00
public import LeanVM.Guest.Memory.GuestCntJ.Part01
public import LeanVM.Guest.Memory.GuestCntJ.Part02
public import LeanVM.Guest.Memory.GuestCntJ.Part03
public import LeanVM.Guest.Memory.GuestCntJ.Part04
public import LeanVM.Guest.Memory.GuestCntJ.Part05
public import LeanVM.Guest.Memory.GuestCntJ.Part06
public import LeanVM.Guest.Memory.GuestCntJ.Part07
public import LeanVM.Guest.Memory.GuestCntJ.Part08
public import LeanVM.Guest.Memory.GuestCntJ.Part09
public import LeanVM.Guest.Memory.GuestCntJ.Part10

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjchkIdx_19 : kwjchkIdx 19 = true := by
  have hb : blockB (kwjlookJ 19) (kwjomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwjsplit_19_0.1 rfl kwjsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwjsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwjsplit_19_96]
    rfl
  exact kwjchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwjchkIdx_all : ∀ j < 1601, kwjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwjchkIdx_19
  by_cases h0 : j < 11
  · exact kwjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwjstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwjstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwjstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwjstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwjstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwjstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwjstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwjstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwjstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwjstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwjstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwjstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 337
  · exact kwjstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 340
  · exact kwjstaticRange_337.get (by omega) (by omega)
  by_cases h16 : j < 343
  · exact kwjstaticRange_340.get (by omega) (by omega)
  by_cases h17 : j < 345
  · exact kwjstaticRange_343.get (by omega) (by omega)
  by_cases h18 : j < 375
  · exact kwjstaticRange_345.get (by omega) (by omega)
  by_cases h19 : j < 405
  · exact kwjstaticRange_375.get (by omega) (by omega)
  by_cases h20 : j < 435
  · exact kwjstaticRange_405.get (by omega) (by omega)
  by_cases h21 : j < 465
  · exact kwjstaticRange_435.get (by omega) (by omega)
  by_cases h22 : j < 495
  · exact kwjstaticRange_465.get (by omega) (by omega)
  by_cases h23 : j < 525
  · exact kwjstaticRange_495.get (by omega) (by omega)
  by_cases h24 : j < 555
  · exact kwjstaticRange_525.get (by omega) (by omega)
  by_cases h25 : j < 585
  · exact kwjstaticRange_555.get (by omega) (by omega)
  by_cases h26 : j < 615
  · exact kwjstaticRange_585.get (by omega) (by omega)
  by_cases h27 : j < 645
  · exact kwjstaticRange_615.get (by omega) (by omega)
  by_cases h28 : j < 675
  · exact kwjstaticRange_645.get (by omega) (by omega)
  by_cases h29 : j < 705
  · exact kwjstaticRange_675.get (by omega) (by omega)
  by_cases h30 : j < 735
  · exact kwjstaticRange_705.get (by omega) (by omega)
  by_cases h31 : j < 765
  · exact kwjstaticRange_735.get (by omega) (by omega)
  by_cases h32 : j < 795
  · exact kwjstaticRange_765.get (by omega) (by omega)
  by_cases h33 : j < 825
  · exact kwjstaticRange_795.get (by omega) (by omega)
  by_cases h34 : j < 855
  · exact kwjstaticRange_825.get (by omega) (by omega)
  by_cases h35 : j < 885
  · exact kwjstaticRange_855.get (by omega) (by omega)
  by_cases h36 : j < 915
  · exact kwjstaticRange_885.get (by omega) (by omega)
  by_cases h37 : j < 945
  · exact kwjstaticRange_915.get (by omega) (by omega)
  by_cases h38 : j < 975
  · exact kwjstaticRange_945.get (by omega) (by omega)
  by_cases h39 : j < 1005
  · exact kwjstaticRange_975.get (by omega) (by omega)
  by_cases h40 : j < 1035
  · exact kwjstaticRange_1005.get (by omega) (by omega)
  by_cases h41 : j < 1065
  · exact kwjstaticRange_1035.get (by omega) (by omega)
  by_cases h42 : j < 1095
  · exact kwjstaticRange_1065.get (by omega) (by omega)
  by_cases h43 : j < 1125
  · exact kwjstaticRange_1095.get (by omega) (by omega)
  by_cases h44 : j < 1155
  · exact kwjstaticRange_1125.get (by omega) (by omega)
  by_cases h45 : j < 1185
  · exact kwjstaticRange_1155.get (by omega) (by omega)
  by_cases h46 : j < 1215
  · exact kwjstaticRange_1185.get (by omega) (by omega)
  by_cases h47 : j < 1245
  · exact kwjstaticRange_1215.get (by omega) (by omega)
  by_cases h48 : j < 1275
  · exact kwjstaticRange_1245.get (by omega) (by omega)
  by_cases h49 : j < 1305
  · exact kwjstaticRange_1275.get (by omega) (by omega)
  by_cases h50 : j < 1335
  · exact kwjstaticRange_1305.get (by omega) (by omega)
  by_cases h51 : j < 1365
  · exact kwjstaticRange_1335.get (by omega) (by omega)
  by_cases h52 : j < 1395
  · exact kwjstaticRange_1365.get (by omega) (by omega)
  by_cases h53 : j < 1425
  · exact kwjstaticRange_1395.get (by omega) (by omega)
  by_cases h54 : j < 1455
  · exact kwjstaticRange_1425.get (by omega) (by omega)
  by_cases h55 : j < 1485
  · exact kwjstaticRange_1455.get (by omega) (by omega)
  by_cases h56 : j < 1515
  · exact kwjstaticRange_1485.get (by omega) (by omega)
  by_cases h57 : j < 1545
  · exact kwjstaticRange_1515.get (by omega) (by omega)
  by_cases h58 : j < 1575
  · exact kwjstaticRange_1545.get (by omega) (by omega)
  exact kwjstaticRange_1575.get (by omega) (by omega)

end
end LeanVM.Guest
