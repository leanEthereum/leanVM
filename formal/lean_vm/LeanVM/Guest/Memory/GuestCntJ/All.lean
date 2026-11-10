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
public import LeanVM.Guest.Memory.GuestCntJ.Part11

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

theorem kwjchkIdx_all : ∀ j < 1803, kwjchkIdx j = true := by
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
  by_cases h14 : j < 314
  · exact kwjstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 317
  · exact kwjstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 320
  · exact kwjstaticRange_317.get (by omega) (by omega)
  by_cases h17 : j < 322
  · exact kwjstaticRange_320.get (by omega) (by omega)
  by_cases h18 : j < 352
  · exact kwjstaticRange_322.get (by omega) (by omega)
  by_cases h19 : j < 382
  · exact kwjstaticRange_352.get (by omega) (by omega)
  by_cases h20 : j < 412
  · exact kwjstaticRange_382.get (by omega) (by omega)
  by_cases h21 : j < 442
  · exact kwjstaticRange_412.get (by omega) (by omega)
  by_cases h22 : j < 472
  · exact kwjstaticRange_442.get (by omega) (by omega)
  by_cases h23 : j < 502
  · exact kwjstaticRange_472.get (by omega) (by omega)
  by_cases h24 : j < 532
  · exact kwjstaticRange_502.get (by omega) (by omega)
  by_cases h25 : j < 562
  · exact kwjstaticRange_532.get (by omega) (by omega)
  by_cases h26 : j < 592
  · exact kwjstaticRange_562.get (by omega) (by omega)
  by_cases h27 : j < 622
  · exact kwjstaticRange_592.get (by omega) (by omega)
  by_cases h28 : j < 652
  · exact kwjstaticRange_622.get (by omega) (by omega)
  by_cases h29 : j < 682
  · exact kwjstaticRange_652.get (by omega) (by omega)
  by_cases h30 : j < 712
  · exact kwjstaticRange_682.get (by omega) (by omega)
  by_cases h31 : j < 742
  · exact kwjstaticRange_712.get (by omega) (by omega)
  by_cases h32 : j < 772
  · exact kwjstaticRange_742.get (by omega) (by omega)
  by_cases h33 : j < 802
  · exact kwjstaticRange_772.get (by omega) (by omega)
  by_cases h34 : j < 832
  · exact kwjstaticRange_802.get (by omega) (by omega)
  by_cases h35 : j < 862
  · exact kwjstaticRange_832.get (by omega) (by omega)
  by_cases h36 : j < 892
  · exact kwjstaticRange_862.get (by omega) (by omega)
  by_cases h37 : j < 922
  · exact kwjstaticRange_892.get (by omega) (by omega)
  by_cases h38 : j < 952
  · exact kwjstaticRange_922.get (by omega) (by omega)
  by_cases h39 : j < 982
  · exact kwjstaticRange_952.get (by omega) (by omega)
  by_cases h40 : j < 1012
  · exact kwjstaticRange_982.get (by omega) (by omega)
  by_cases h41 : j < 1042
  · exact kwjstaticRange_1012.get (by omega) (by omega)
  by_cases h42 : j < 1072
  · exact kwjstaticRange_1042.get (by omega) (by omega)
  by_cases h43 : j < 1102
  · exact kwjstaticRange_1072.get (by omega) (by omega)
  by_cases h44 : j < 1132
  · exact kwjstaticRange_1102.get (by omega) (by omega)
  by_cases h45 : j < 1162
  · exact kwjstaticRange_1132.get (by omega) (by omega)
  by_cases h46 : j < 1192
  · exact kwjstaticRange_1162.get (by omega) (by omega)
  by_cases h47 : j < 1222
  · exact kwjstaticRange_1192.get (by omega) (by omega)
  by_cases h48 : j < 1252
  · exact kwjstaticRange_1222.get (by omega) (by omega)
  by_cases h49 : j < 1282
  · exact kwjstaticRange_1252.get (by omega) (by omega)
  by_cases h50 : j < 1312
  · exact kwjstaticRange_1282.get (by omega) (by omega)
  by_cases h51 : j < 1342
  · exact kwjstaticRange_1312.get (by omega) (by omega)
  by_cases h52 : j < 1372
  · exact kwjstaticRange_1342.get (by omega) (by omega)
  by_cases h53 : j < 1402
  · exact kwjstaticRange_1372.get (by omega) (by omega)
  by_cases h54 : j < 1432
  · exact kwjstaticRange_1402.get (by omega) (by omega)
  by_cases h55 : j < 1462
  · exact kwjstaticRange_1432.get (by omega) (by omega)
  by_cases h56 : j < 1492
  · exact kwjstaticRange_1462.get (by omega) (by omega)
  by_cases h57 : j < 1522
  · exact kwjstaticRange_1492.get (by omega) (by omega)
  by_cases h58 : j < 1552
  · exact kwjstaticRange_1522.get (by omega) (by omega)
  by_cases h59 : j < 1582
  · exact kwjstaticRange_1552.get (by omega) (by omega)
  by_cases h60 : j < 1612
  · exact kwjstaticRange_1582.get (by omega) (by omega)
  by_cases h61 : j < 1642
  · exact kwjstaticRange_1612.get (by omega) (by omega)
  by_cases h62 : j < 1672
  · exact kwjstaticRange_1642.get (by omega) (by omega)
  by_cases h63 : j < 1702
  · exact kwjstaticRange_1672.get (by omega) (by omega)
  by_cases h64 : j < 1732
  · exact kwjstaticRange_1702.get (by omega) (by omega)
  by_cases h65 : j < 1762
  · exact kwjstaticRange_1732.get (by omega) (by omega)
  by_cases h66 : j < 1792
  · exact kwjstaticRange_1762.get (by omega) (by omega)
  exact kwjstaticRange_1792.get (by omega) (by omega)

end
end LeanVM.Guest
