/-
  LeanVM.Guest.Memory.GuestCntX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntX.Part00
public import LeanVM.Guest.Memory.GuestCntX.Part01
public import LeanVM.Guest.Memory.GuestCntX.Part02
public import LeanVM.Guest.Memory.GuestCntX.Part03
public import LeanVM.Guest.Memory.GuestCntX.Part04
public import LeanVM.Guest.Memory.GuestCntX.Part05
public import LeanVM.Guest.Memory.GuestCntX.Part06
public import LeanVM.Guest.Memory.GuestCntX.Part07
public import LeanVM.Guest.Memory.GuestCntX.Part08
public import LeanVM.Guest.Memory.GuestCntX.Part09
public import LeanVM.Guest.Memory.GuestCntX.Part10
public import LeanVM.Guest.Memory.GuestCntX.Part11

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxchkIdx_19 : kwxchkIdx 19 = true := by
  have hb : blockB (kwxlookJ 19) (kwxomLookJ 19) false [] Data.core19.params Data.core19.name ([], []) Data.core19.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core19.body)]
    rw [blockB_dropE _ _ _ 0 96 96 kwxsplit_19_0.1 rfl kwxsplit_19_0.2.2,
      ← blockR_eq ((Data.core19.body.drop 0).take 96), kwxsplit_19_0.2.1]
    rw [← blockR_eq (Data.core19.body.drop 96), kwxsplit_19_96]
    rfl
  exact kwxchkIdx_of_split (fn := Data.core19) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwxchkIdx_all : ∀ j < 1803, kwxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 19
  · subst h1000; exact kwxchkIdx_19
  by_cases h0 : j < 11
  · exact kwxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kwxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 19
  · exact kwxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 36
  · exact kwxstaticRange_20.get (by omega) (by omega)
  by_cases h4 : j < 37
  · exact kwxstaticRange_36.get (by omega) (by omega)
  by_cases h5 : j < 67
  · exact kwxstaticRange_37.get (by omega) (by omega)
  by_cases h6 : j < 97
  · exact kwxstaticRange_67.get (by omega) (by omega)
  by_cases h7 : j < 127
  · exact kwxstaticRange_97.get (by omega) (by omega)
  by_cases h8 : j < 157
  · exact kwxstaticRange_127.get (by omega) (by omega)
  by_cases h9 : j < 187
  · exact kwxstaticRange_157.get (by omega) (by omega)
  by_cases h10 : j < 217
  · exact kwxstaticRange_187.get (by omega) (by omega)
  by_cases h11 : j < 247
  · exact kwxstaticRange_217.get (by omega) (by omega)
  by_cases h12 : j < 277
  · exact kwxstaticRange_247.get (by omega) (by omega)
  by_cases h13 : j < 307
  · exact kwxstaticRange_277.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kwxstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 317
  · exact kwxstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 320
  · exact kwxstaticRange_317.get (by omega) (by omega)
  by_cases h17 : j < 322
  · exact kwxstaticRange_320.get (by omega) (by omega)
  by_cases h18 : j < 352
  · exact kwxstaticRange_322.get (by omega) (by omega)
  by_cases h19 : j < 382
  · exact kwxstaticRange_352.get (by omega) (by omega)
  by_cases h20 : j < 412
  · exact kwxstaticRange_382.get (by omega) (by omega)
  by_cases h21 : j < 442
  · exact kwxstaticRange_412.get (by omega) (by omega)
  by_cases h22 : j < 472
  · exact kwxstaticRange_442.get (by omega) (by omega)
  by_cases h23 : j < 502
  · exact kwxstaticRange_472.get (by omega) (by omega)
  by_cases h24 : j < 532
  · exact kwxstaticRange_502.get (by omega) (by omega)
  by_cases h25 : j < 562
  · exact kwxstaticRange_532.get (by omega) (by omega)
  by_cases h26 : j < 592
  · exact kwxstaticRange_562.get (by omega) (by omega)
  by_cases h27 : j < 622
  · exact kwxstaticRange_592.get (by omega) (by omega)
  by_cases h28 : j < 652
  · exact kwxstaticRange_622.get (by omega) (by omega)
  by_cases h29 : j < 682
  · exact kwxstaticRange_652.get (by omega) (by omega)
  by_cases h30 : j < 712
  · exact kwxstaticRange_682.get (by omega) (by omega)
  by_cases h31 : j < 742
  · exact kwxstaticRange_712.get (by omega) (by omega)
  by_cases h32 : j < 772
  · exact kwxstaticRange_742.get (by omega) (by omega)
  by_cases h33 : j < 802
  · exact kwxstaticRange_772.get (by omega) (by omega)
  by_cases h34 : j < 832
  · exact kwxstaticRange_802.get (by omega) (by omega)
  by_cases h35 : j < 862
  · exact kwxstaticRange_832.get (by omega) (by omega)
  by_cases h36 : j < 892
  · exact kwxstaticRange_862.get (by omega) (by omega)
  by_cases h37 : j < 922
  · exact kwxstaticRange_892.get (by omega) (by omega)
  by_cases h38 : j < 952
  · exact kwxstaticRange_922.get (by omega) (by omega)
  by_cases h39 : j < 982
  · exact kwxstaticRange_952.get (by omega) (by omega)
  by_cases h40 : j < 1012
  · exact kwxstaticRange_982.get (by omega) (by omega)
  by_cases h41 : j < 1042
  · exact kwxstaticRange_1012.get (by omega) (by omega)
  by_cases h42 : j < 1072
  · exact kwxstaticRange_1042.get (by omega) (by omega)
  by_cases h43 : j < 1102
  · exact kwxstaticRange_1072.get (by omega) (by omega)
  by_cases h44 : j < 1132
  · exact kwxstaticRange_1102.get (by omega) (by omega)
  by_cases h45 : j < 1162
  · exact kwxstaticRange_1132.get (by omega) (by omega)
  by_cases h46 : j < 1192
  · exact kwxstaticRange_1162.get (by omega) (by omega)
  by_cases h47 : j < 1222
  · exact kwxstaticRange_1192.get (by omega) (by omega)
  by_cases h48 : j < 1252
  · exact kwxstaticRange_1222.get (by omega) (by omega)
  by_cases h49 : j < 1282
  · exact kwxstaticRange_1252.get (by omega) (by omega)
  by_cases h50 : j < 1312
  · exact kwxstaticRange_1282.get (by omega) (by omega)
  by_cases h51 : j < 1342
  · exact kwxstaticRange_1312.get (by omega) (by omega)
  by_cases h52 : j < 1372
  · exact kwxstaticRange_1342.get (by omega) (by omega)
  by_cases h53 : j < 1402
  · exact kwxstaticRange_1372.get (by omega) (by omega)
  by_cases h54 : j < 1432
  · exact kwxstaticRange_1402.get (by omega) (by omega)
  by_cases h55 : j < 1462
  · exact kwxstaticRange_1432.get (by omega) (by omega)
  by_cases h56 : j < 1492
  · exact kwxstaticRange_1462.get (by omega) (by omega)
  by_cases h57 : j < 1522
  · exact kwxstaticRange_1492.get (by omega) (by omega)
  by_cases h58 : j < 1552
  · exact kwxstaticRange_1522.get (by omega) (by omega)
  by_cases h59 : j < 1582
  · exact kwxstaticRange_1552.get (by omega) (by omega)
  by_cases h60 : j < 1612
  · exact kwxstaticRange_1582.get (by omega) (by omega)
  by_cases h61 : j < 1642
  · exact kwxstaticRange_1612.get (by omega) (by omega)
  by_cases h62 : j < 1672
  · exact kwxstaticRange_1642.get (by omega) (by omega)
  by_cases h63 : j < 1702
  · exact kwxstaticRange_1672.get (by omega) (by omega)
  by_cases h64 : j < 1732
  · exact kwxstaticRange_1702.get (by omega) (by omega)
  by_cases h65 : j < 1762
  · exact kwxstaticRange_1732.get (by omega) (by omega)
  by_cases h66 : j < 1792
  · exact kwxstaticRange_1762.get (by omega) (by omega)
  exact kwxstaticRange_1792.get (by omega) (by omega)

end
end LeanVM.Guest
