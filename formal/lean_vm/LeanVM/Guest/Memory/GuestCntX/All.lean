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

theorem kwxchkIdx_all : ∀ j < 1752, kwxchkIdx j = true := by
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
  by_cases h14 : j < 313
  · exact kwxstaticRange_307.get (by omega) (by omega)
  by_cases h15 : j < 316
  · exact kwxstaticRange_313.get (by omega) (by omega)
  by_cases h16 : j < 319
  · exact kwxstaticRange_316.get (by omega) (by omega)
  by_cases h17 : j < 321
  · exact kwxstaticRange_319.get (by omega) (by omega)
  by_cases h18 : j < 351
  · exact kwxstaticRange_321.get (by omega) (by omega)
  by_cases h19 : j < 381
  · exact kwxstaticRange_351.get (by omega) (by omega)
  by_cases h20 : j < 411
  · exact kwxstaticRange_381.get (by omega) (by omega)
  by_cases h21 : j < 441
  · exact kwxstaticRange_411.get (by omega) (by omega)
  by_cases h22 : j < 471
  · exact kwxstaticRange_441.get (by omega) (by omega)
  by_cases h23 : j < 501
  · exact kwxstaticRange_471.get (by omega) (by omega)
  by_cases h24 : j < 531
  · exact kwxstaticRange_501.get (by omega) (by omega)
  by_cases h25 : j < 561
  · exact kwxstaticRange_531.get (by omega) (by omega)
  by_cases h26 : j < 591
  · exact kwxstaticRange_561.get (by omega) (by omega)
  by_cases h27 : j < 621
  · exact kwxstaticRange_591.get (by omega) (by omega)
  by_cases h28 : j < 651
  · exact kwxstaticRange_621.get (by omega) (by omega)
  by_cases h29 : j < 681
  · exact kwxstaticRange_651.get (by omega) (by omega)
  by_cases h30 : j < 711
  · exact kwxstaticRange_681.get (by omega) (by omega)
  by_cases h31 : j < 741
  · exact kwxstaticRange_711.get (by omega) (by omega)
  by_cases h32 : j < 771
  · exact kwxstaticRange_741.get (by omega) (by omega)
  by_cases h33 : j < 801
  · exact kwxstaticRange_771.get (by omega) (by omega)
  by_cases h34 : j < 831
  · exact kwxstaticRange_801.get (by omega) (by omega)
  by_cases h35 : j < 861
  · exact kwxstaticRange_831.get (by omega) (by omega)
  by_cases h36 : j < 891
  · exact kwxstaticRange_861.get (by omega) (by omega)
  by_cases h37 : j < 921
  · exact kwxstaticRange_891.get (by omega) (by omega)
  by_cases h38 : j < 951
  · exact kwxstaticRange_921.get (by omega) (by omega)
  by_cases h39 : j < 981
  · exact kwxstaticRange_951.get (by omega) (by omega)
  by_cases h40 : j < 1011
  · exact kwxstaticRange_981.get (by omega) (by omega)
  by_cases h41 : j < 1041
  · exact kwxstaticRange_1011.get (by omega) (by omega)
  by_cases h42 : j < 1071
  · exact kwxstaticRange_1041.get (by omega) (by omega)
  by_cases h43 : j < 1101
  · exact kwxstaticRange_1071.get (by omega) (by omega)
  by_cases h44 : j < 1131
  · exact kwxstaticRange_1101.get (by omega) (by omega)
  by_cases h45 : j < 1161
  · exact kwxstaticRange_1131.get (by omega) (by omega)
  by_cases h46 : j < 1191
  · exact kwxstaticRange_1161.get (by omega) (by omega)
  by_cases h47 : j < 1221
  · exact kwxstaticRange_1191.get (by omega) (by omega)
  by_cases h48 : j < 1251
  · exact kwxstaticRange_1221.get (by omega) (by omega)
  by_cases h49 : j < 1281
  · exact kwxstaticRange_1251.get (by omega) (by omega)
  by_cases h50 : j < 1311
  · exact kwxstaticRange_1281.get (by omega) (by omega)
  by_cases h51 : j < 1341
  · exact kwxstaticRange_1311.get (by omega) (by omega)
  by_cases h52 : j < 1371
  · exact kwxstaticRange_1341.get (by omega) (by omega)
  by_cases h53 : j < 1401
  · exact kwxstaticRange_1371.get (by omega) (by omega)
  by_cases h54 : j < 1431
  · exact kwxstaticRange_1401.get (by omega) (by omega)
  by_cases h55 : j < 1461
  · exact kwxstaticRange_1431.get (by omega) (by omega)
  by_cases h56 : j < 1491
  · exact kwxstaticRange_1461.get (by omega) (by omega)
  by_cases h57 : j < 1521
  · exact kwxstaticRange_1491.get (by omega) (by omega)
  by_cases h58 : j < 1551
  · exact kwxstaticRange_1521.get (by omega) (by omega)
  by_cases h59 : j < 1581
  · exact kwxstaticRange_1551.get (by omega) (by omega)
  by_cases h60 : j < 1611
  · exact kwxstaticRange_1581.get (by omega) (by omega)
  by_cases h61 : j < 1641
  · exact kwxstaticRange_1611.get (by omega) (by omega)
  by_cases h62 : j < 1671
  · exact kwxstaticRange_1641.get (by omega) (by omega)
  by_cases h63 : j < 1701
  · exact kwxstaticRange_1671.get (by omega) (by omega)
  by_cases h64 : j < 1731
  · exact kwxstaticRange_1701.get (by omega) (by omega)
  exact kwxstaticRange_1731.get (by omega) (by omega)

end
end LeanVM.Guest
