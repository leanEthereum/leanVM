/-
  LeanVM.Guest.Memory.GuestCntB.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntB.Part00
public import LeanVM.Guest.Memory.GuestCntB.Part01
public import LeanVM.Guest.Memory.GuestCntB.Part02
public import LeanVM.Guest.Memory.GuestCntB.Part03
public import LeanVM.Guest.Memory.GuestCntB.Part04
public import LeanVM.Guest.Memory.GuestCntB.Part05
public import LeanVM.Guest.Memory.GuestCntB.Part06
public import LeanVM.Guest.Memory.GuestCntB.Part07
public import LeanVM.Guest.Memory.GuestCntB.Part08
public import LeanVM.Guest.Memory.GuestCntB.Part09
public import LeanVM.Guest.Memory.GuestCntB.Part10
public import LeanVM.Guest.Memory.GuestCntB.Part11

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwbchkIdx_16 : kwbchkIdx 16 = true := by
  have hb : blockB (kwblookJ 16) (kwbomLookJ 16) false [] Data.core16.params Data.core16.name ([], []) Data.core16.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core16.body)]
    rw [blockB_drop' _ _ 0 222 222 kwbsplit_16_0.1 rfl, ← blockR_eq ((Data.core16.body.drop 0).take 222), kwbsplit_16_0.2]
    rw [blockB_drop' _ _ 222 276 498 kwbsplit_16_222.1 rfl, ← blockR_eq ((Data.core16.body.drop 222).take 276), kwbsplit_16_222.2]
    rw [← blockR_eq (Data.core16.body.drop 498), kwbsplit_16_498]
    rfl
  exact kwbchkIdx_of_split (fn := Data.core16) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwbchkIdx_17 : kwbchkIdx 17 = true := by
  have hb : blockB (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name ([], []) Data.core17.body = some (⟨112, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core17.body)]
    rw [blockB_drop' _ _ 0 220 220 kwbsplit_17_0.1 rfl, ← blockR_eq ((Data.core17.body.drop 0).take 220), kwbsplit_17_0.2]
    rw [blockB_drop' _ _ 220 1 221 kwbsplit_17_220.1 rfl, ← blockR_eq ((Data.core17.body.drop 220).take 1), kwbsplit_17_220.2]
    rw [blockB_drop' _ _ 221 11 232 kwbsplit_17_221.1 rfl, ← blockR_eq ((Data.core17.body.drop 221).take 11), kwbsplit_17_221.2]
    rw [blockB_drop' _ _ 232 1 233 kwbsplit_17_232.1 rfl, ← blockR_eq ((Data.core17.body.drop 232).take 1), kwbsplit_17_232.2]
    rw [blockB_drop' _ _ 233 27 260 kwbsplit_17_233.1 rfl, ← blockR_eq ((Data.core17.body.drop 233).take 27), kwbsplit_17_233.2]
    rw [blockB_drop' _ _ 260 1 261 kwbsplit_17_260.1 rfl, ← blockR_eq ((Data.core17.body.drop 260).take 1), kwbsplit_17_260.2]
    rw [blockB_drop' _ _ 261 11 272 kwbsplit_17_261.1 rfl, ← blockR_eq ((Data.core17.body.drop 261).take 11), kwbsplit_17_261.2]
    rw [blockB_drop' _ _ 272 1 273 kwbsplit_17_272.1 rfl, ← blockR_eq ((Data.core17.body.drop 272).take 1), kwbsplit_17_272.2]
    rw [blockB_drop' _ _ 273 27 300 kwbsplit_17_273.1 rfl, ← blockR_eq ((Data.core17.body.drop 273).take 27), kwbsplit_17_273.2]
    rw [blockB_drop' _ _ 300 1 301 kwbsplit_17_300.1 rfl, ← blockR_eq ((Data.core17.body.drop 300).take 1), kwbsplit_17_300.2]
    rw [blockB_drop' _ _ 301 11 312 kwbsplit_17_301.1 rfl, ← blockR_eq ((Data.core17.body.drop 301).take 11), kwbsplit_17_301.2]
    rw [blockB_drop' _ _ 312 1 313 kwbsplit_17_312.1 rfl, ← blockR_eq ((Data.core17.body.drop 312).take 1), kwbsplit_17_312.2]
    rw [blockB_drop' _ _ 313 27 340 kwbsplit_17_313.1 rfl, ← blockR_eq ((Data.core17.body.drop 313).take 27), kwbsplit_17_313.2]
    rw [blockB_drop' _ _ 340 1 341 kwbsplit_17_340.1 rfl, ← blockR_eq ((Data.core17.body.drop 340).take 1), kwbsplit_17_340.2]
    rw [blockB_drop' _ _ 341 11 352 kwbsplit_17_341.1 rfl, ← blockR_eq ((Data.core17.body.drop 341).take 11), kwbsplit_17_341.2]
    rw [blockB_drop' _ _ 352 1 353 kwbsplit_17_352.1 rfl, ← blockR_eq ((Data.core17.body.drop 352).take 1), kwbsplit_17_352.2]
    rw [blockB_drop' _ _ 353 27 380 kwbsplit_17_353.1 rfl, ← blockR_eq ((Data.core17.body.drop 353).take 27), kwbsplit_17_353.2]
    rw [blockB_drop' _ _ 380 1 381 kwbsplit_17_380.1 rfl, ← blockR_eq ((Data.core17.body.drop 380).take 1), kwbsplit_17_380.2]
    rw [blockB_drop' _ _ 381 11 392 kwbsplit_17_381.1 rfl, ← blockR_eq ((Data.core17.body.drop 381).take 11), kwbsplit_17_381.2]
    rw [blockB_drop' _ _ 392 1 393 kwbsplit_17_392.1 rfl, ← blockR_eq ((Data.core17.body.drop 392).take 1), kwbsplit_17_392.2]
    rw [blockB_drop' _ _ 393 27 420 kwbsplit_17_393.1 rfl, ← blockR_eq ((Data.core17.body.drop 393).take 27), kwbsplit_17_393.2]
    rw [blockB_drop' _ _ 420 1 421 kwbsplit_17_420.1 rfl, ← blockR_eq ((Data.core17.body.drop 420).take 1), kwbsplit_17_420.2]
    rw [blockB_drop' _ _ 421 11 432 kwbsplit_17_421.1 rfl, ← blockR_eq ((Data.core17.body.drop 421).take 11), kwbsplit_17_421.2]
    rw [blockB_drop' _ _ 432 1 433 kwbsplit_17_432.1 rfl, ← blockR_eq ((Data.core17.body.drop 432).take 1), kwbsplit_17_432.2]
    rw [blockB_drop' _ _ 433 27 460 kwbsplit_17_433.1 rfl, ← blockR_eq ((Data.core17.body.drop 433).take 27), kwbsplit_17_433.2]
    rw [blockB_drop' _ _ 460 1 461 kwbsplit_17_460.1 rfl, ← blockR_eq ((Data.core17.body.drop 460).take 1), kwbsplit_17_460.2]
    rw [blockB_drop' _ _ 461 11 472 kwbsplit_17_461.1 rfl, ← blockR_eq ((Data.core17.body.drop 461).take 11), kwbsplit_17_461.2]
    rw [blockB_drop' _ _ 472 1 473 kwbsplit_17_472.1 rfl, ← blockR_eq ((Data.core17.body.drop 472).take 1), kwbsplit_17_472.2]
    rw [blockB_drop' _ _ 473 27 500 kwbsplit_17_473.1 rfl, ← blockR_eq ((Data.core17.body.drop 473).take 27), kwbsplit_17_473.2]
    rw [blockB_drop' _ _ 500 1 501 kwbsplit_17_500.1 rfl, ← blockR_eq ((Data.core17.body.drop 500).take 1), kwbsplit_17_500.2]
    rw [blockB_drop' _ _ 501 11 512 kwbsplit_17_501.1 rfl, ← blockR_eq ((Data.core17.body.drop 501).take 11), kwbsplit_17_501.2]
    rw [blockB_drop' _ _ 512 1 513 kwbsplit_17_512.1 rfl, ← blockR_eq ((Data.core17.body.drop 512).take 1), kwbsplit_17_512.2]
    rw [blockB_drop' _ _ 513 264 777 kwbsplit_17_513.1 rfl, ← blockR_eq ((Data.core17.body.drop 513).take 264), kwbsplit_17_513.2]
    rw [← blockR_eq (Data.core17.body.drop 777), kwbsplit_17_777]
    rfl
  exact kwbchkIdx_of_split (fn := Data.core17) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwbchkIdx_all : ∀ j < 1043, kwbchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 16
  · subst h1000; exact kwbchkIdx_16
  by_cases h1001 : j = 17
  · subst h1001; exact kwbchkIdx_17
  by_cases h0 : j < 16
  · exact kwbstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 48
  · exact kwbstaticRange_18.get (by omega) (by omega)
  by_cases h2 : j < 78
  · exact kwbstaticRange_48.get (by omega) (by omega)
  by_cases h3 : j < 108
  · exact kwbstaticRange_78.get (by omega) (by omega)
  by_cases h4 : j < 138
  · exact kwbstaticRange_108.get (by omega) (by omega)
  by_cases h5 : j < 168
  · exact kwbstaticRange_138.get (by omega) (by omega)
  by_cases h6 : j < 198
  · exact kwbstaticRange_168.get (by omega) (by omega)
  by_cases h7 : j < 228
  · exact kwbstaticRange_198.get (by omega) (by omega)
  by_cases h8 : j < 256
  · exact kwbstaticRange_228.get (by omega) (by omega)
  by_cases h9 : j < 284
  · exact kwbstaticRange_256.get (by omega) (by omega)
  by_cases h10 : j < 312
  · exact kwbstaticRange_284.get (by omega) (by omega)
  by_cases h11 : j < 340
  · exact kwbstaticRange_312.get (by omega) (by omega)
  by_cases h12 : j < 368
  · exact kwbstaticRange_340.get (by omega) (by omega)
  by_cases h13 : j < 396
  · exact kwbstaticRange_368.get (by omega) (by omega)
  by_cases h14 : j < 424
  · exact kwbstaticRange_396.get (by omega) (by omega)
  by_cases h15 : j < 452
  · exact kwbstaticRange_424.get (by omega) (by omega)
  by_cases h16 : j < 482
  · exact kwbstaticRange_452.get (by omega) (by omega)
  by_cases h17 : j < 512
  · exact kwbstaticRange_482.get (by omega) (by omega)
  by_cases h18 : j < 542
  · exact kwbstaticRange_512.get (by omega) (by omega)
  by_cases h19 : j < 571
  · exact kwbstaticRange_542.get (by omega) (by omega)
  by_cases h20 : j < 601
  · exact kwbstaticRange_571.get (by omega) (by omega)
  by_cases h21 : j < 631
  · exact kwbstaticRange_601.get (by omega) (by omega)
  by_cases h22 : j < 661
  · exact kwbstaticRange_631.get (by omega) (by omega)
  by_cases h23 : j < 691
  · exact kwbstaticRange_661.get (by omega) (by omega)
  by_cases h24 : j < 721
  · exact kwbstaticRange_691.get (by omega) (by omega)
  by_cases h25 : j < 751
  · exact kwbstaticRange_721.get (by omega) (by omega)
  by_cases h26 : j < 781
  · exact kwbstaticRange_751.get (by omega) (by omega)
  by_cases h27 : j < 811
  · exact kwbstaticRange_781.get (by omega) (by omega)
  by_cases h28 : j < 841
  · exact kwbstaticRange_811.get (by omega) (by omega)
  by_cases h29 : j < 871
  · exact kwbstaticRange_841.get (by omega) (by omega)
  by_cases h30 : j < 901
  · exact kwbstaticRange_871.get (by omega) (by omega)
  by_cases h31 : j < 931
  · exact kwbstaticRange_901.get (by omega) (by omega)
  by_cases h32 : j < 961
  · exact kwbstaticRange_931.get (by omega) (by omega)
  by_cases h33 : j < 991
  · exact kwbstaticRange_961.get (by omega) (by omega)
  by_cases h34 : j < 1021
  · exact kwbstaticRange_991.get (by omega) (by omega)
  exact kwbstaticRange_1021.get (by omega) (by omega)

end
end LeanVM.Guest
