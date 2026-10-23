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
theorem kwxchkIdx_16 : kwxchkIdx 16 = true := by
  have hb : blockB (kwxlookJ 16) (kwxomLookJ 16) false [] Data.core16.params Data.core16.name ([], []) Data.core16.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core16.body)]
    rw [blockB_drop' _ _ 0 222 222 kwxsplit_16_0.1 rfl, ← blockR_eq ((Data.core16.body.drop 0).take 222), kwxsplit_16_0.2]
    rw [blockB_drop' _ _ 222 276 498 kwxsplit_16_222.1 rfl, ← blockR_eq ((Data.core16.body.drop 222).take 276), kwxsplit_16_222.2]
    rw [← blockR_eq (Data.core16.body.drop 498), kwxsplit_16_498]
    rfl
  exact kwxchkIdx_of_split (fn := Data.core16) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwxchkIdx_17 : kwxchkIdx 17 = true := by
  have hb : blockB (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ([], []) Data.core17.body = some (⟨96, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core17.body)]
    rw [blockB_drop' _ _ 0 220 220 kwxsplit_17_0.1 rfl, ← blockR_eq ((Data.core17.body.drop 0).take 220), kwxsplit_17_0.2]
    rw [blockB_drop' _ _ 220 1 221 kwxsplit_17_220.1 rfl, ← blockR_eq ((Data.core17.body.drop 220).take 1), kwxsplit_17_220.2]
    rw [blockB_drop' _ _ 221 11 232 kwxsplit_17_221.1 rfl, ← blockR_eq ((Data.core17.body.drop 221).take 11), kwxsplit_17_221.2]
    rw [blockB_drop' _ _ 232 1 233 kwxsplit_17_232.1 rfl, ← blockR_eq ((Data.core17.body.drop 232).take 1), kwxsplit_17_232.2]
    rw [blockB_drop' _ _ 233 27 260 kwxsplit_17_233.1 rfl, ← blockR_eq ((Data.core17.body.drop 233).take 27), kwxsplit_17_233.2]
    rw [blockB_drop' _ _ 260 1 261 kwxsplit_17_260.1 rfl, ← blockR_eq ((Data.core17.body.drop 260).take 1), kwxsplit_17_260.2]
    rw [blockB_drop' _ _ 261 11 272 kwxsplit_17_261.1 rfl, ← blockR_eq ((Data.core17.body.drop 261).take 11), kwxsplit_17_261.2]
    rw [blockB_drop' _ _ 272 1 273 kwxsplit_17_272.1 rfl, ← blockR_eq ((Data.core17.body.drop 272).take 1), kwxsplit_17_272.2]
    rw [blockB_drop' _ _ 273 27 300 kwxsplit_17_273.1 rfl, ← blockR_eq ((Data.core17.body.drop 273).take 27), kwxsplit_17_273.2]
    rw [blockB_drop' _ _ 300 1 301 kwxsplit_17_300.1 rfl, ← blockR_eq ((Data.core17.body.drop 300).take 1), kwxsplit_17_300.2]
    rw [blockB_drop' _ _ 301 11 312 kwxsplit_17_301.1 rfl, ← blockR_eq ((Data.core17.body.drop 301).take 11), kwxsplit_17_301.2]
    rw [blockB_drop' _ _ 312 1 313 kwxsplit_17_312.1 rfl, ← blockR_eq ((Data.core17.body.drop 312).take 1), kwxsplit_17_312.2]
    rw [blockB_drop' _ _ 313 27 340 kwxsplit_17_313.1 rfl, ← blockR_eq ((Data.core17.body.drop 313).take 27), kwxsplit_17_313.2]
    rw [blockB_drop' _ _ 340 1 341 kwxsplit_17_340.1 rfl, ← blockR_eq ((Data.core17.body.drop 340).take 1), kwxsplit_17_340.2]
    rw [blockB_drop' _ _ 341 11 352 kwxsplit_17_341.1 rfl, ← blockR_eq ((Data.core17.body.drop 341).take 11), kwxsplit_17_341.2]
    rw [blockB_drop' _ _ 352 1 353 kwxsplit_17_352.1 rfl, ← blockR_eq ((Data.core17.body.drop 352).take 1), kwxsplit_17_352.2]
    rw [blockB_drop' _ _ 353 27 380 kwxsplit_17_353.1 rfl, ← blockR_eq ((Data.core17.body.drop 353).take 27), kwxsplit_17_353.2]
    rw [blockB_drop' _ _ 380 1 381 kwxsplit_17_380.1 rfl, ← blockR_eq ((Data.core17.body.drop 380).take 1), kwxsplit_17_380.2]
    rw [blockB_drop' _ _ 381 11 392 kwxsplit_17_381.1 rfl, ← blockR_eq ((Data.core17.body.drop 381).take 11), kwxsplit_17_381.2]
    rw [blockB_drop' _ _ 392 1 393 kwxsplit_17_392.1 rfl, ← blockR_eq ((Data.core17.body.drop 392).take 1), kwxsplit_17_392.2]
    rw [blockB_drop' _ _ 393 27 420 kwxsplit_17_393.1 rfl, ← blockR_eq ((Data.core17.body.drop 393).take 27), kwxsplit_17_393.2]
    rw [blockB_drop' _ _ 420 1 421 kwxsplit_17_420.1 rfl, ← blockR_eq ((Data.core17.body.drop 420).take 1), kwxsplit_17_420.2]
    rw [blockB_drop' _ _ 421 11 432 kwxsplit_17_421.1 rfl, ← blockR_eq ((Data.core17.body.drop 421).take 11), kwxsplit_17_421.2]
    rw [blockB_drop' _ _ 432 1 433 kwxsplit_17_432.1 rfl, ← blockR_eq ((Data.core17.body.drop 432).take 1), kwxsplit_17_432.2]
    rw [blockB_drop' _ _ 433 27 460 kwxsplit_17_433.1 rfl, ← blockR_eq ((Data.core17.body.drop 433).take 27), kwxsplit_17_433.2]
    rw [blockB_drop' _ _ 460 1 461 kwxsplit_17_460.1 rfl, ← blockR_eq ((Data.core17.body.drop 460).take 1), kwxsplit_17_460.2]
    rw [blockB_drop' _ _ 461 11 472 kwxsplit_17_461.1 rfl, ← blockR_eq ((Data.core17.body.drop 461).take 11), kwxsplit_17_461.2]
    rw [blockB_drop' _ _ 472 1 473 kwxsplit_17_472.1 rfl, ← blockR_eq ((Data.core17.body.drop 472).take 1), kwxsplit_17_472.2]
    rw [blockB_drop' _ _ 473 27 500 kwxsplit_17_473.1 rfl, ← blockR_eq ((Data.core17.body.drop 473).take 27), kwxsplit_17_473.2]
    rw [blockB_drop' _ _ 500 1 501 kwxsplit_17_500.1 rfl, ← blockR_eq ((Data.core17.body.drop 500).take 1), kwxsplit_17_500.2]
    rw [blockB_drop' _ _ 501 11 512 kwxsplit_17_501.1 rfl, ← blockR_eq ((Data.core17.body.drop 501).take 11), kwxsplit_17_501.2]
    rw [blockB_drop' _ _ 512 1 513 kwxsplit_17_512.1 rfl, ← blockR_eq ((Data.core17.body.drop 512).take 1), kwxsplit_17_512.2]
    rw [blockB_drop' _ _ 513 264 777 kwxsplit_17_513.1 rfl, ← blockR_eq ((Data.core17.body.drop 513).take 264), kwxsplit_17_513.2]
    rw [← blockR_eq (Data.core17.body.drop 777), kwxsplit_17_777]
    rfl
  exact kwxchkIdx_of_split (fn := Data.core17) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwxchkIdx_all : ∀ j < 1043, kwxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 16
  · subst h1000; exact kwxchkIdx_16
  by_cases h1001 : j = 17
  · subst h1001; exact kwxchkIdx_17
  by_cases h0 : j < 16
  · exact kwxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 48
  · exact kwxstaticRange_18.get (by omega) (by omega)
  by_cases h2 : j < 78
  · exact kwxstaticRange_48.get (by omega) (by omega)
  by_cases h3 : j < 108
  · exact kwxstaticRange_78.get (by omega) (by omega)
  by_cases h4 : j < 138
  · exact kwxstaticRange_108.get (by omega) (by omega)
  by_cases h5 : j < 168
  · exact kwxstaticRange_138.get (by omega) (by omega)
  by_cases h6 : j < 198
  · exact kwxstaticRange_168.get (by omega) (by omega)
  by_cases h7 : j < 228
  · exact kwxstaticRange_198.get (by omega) (by omega)
  by_cases h8 : j < 256
  · exact kwxstaticRange_228.get (by omega) (by omega)
  by_cases h9 : j < 284
  · exact kwxstaticRange_256.get (by omega) (by omega)
  by_cases h10 : j < 312
  · exact kwxstaticRange_284.get (by omega) (by omega)
  by_cases h11 : j < 340
  · exact kwxstaticRange_312.get (by omega) (by omega)
  by_cases h12 : j < 368
  · exact kwxstaticRange_340.get (by omega) (by omega)
  by_cases h13 : j < 396
  · exact kwxstaticRange_368.get (by omega) (by omega)
  by_cases h14 : j < 424
  · exact kwxstaticRange_396.get (by omega) (by omega)
  by_cases h15 : j < 452
  · exact kwxstaticRange_424.get (by omega) (by omega)
  by_cases h16 : j < 482
  · exact kwxstaticRange_452.get (by omega) (by omega)
  by_cases h17 : j < 512
  · exact kwxstaticRange_482.get (by omega) (by omega)
  by_cases h18 : j < 542
  · exact kwxstaticRange_512.get (by omega) (by omega)
  by_cases h19 : j < 571
  · exact kwxstaticRange_542.get (by omega) (by omega)
  by_cases h20 : j < 601
  · exact kwxstaticRange_571.get (by omega) (by omega)
  by_cases h21 : j < 631
  · exact kwxstaticRange_601.get (by omega) (by omega)
  by_cases h22 : j < 661
  · exact kwxstaticRange_631.get (by omega) (by omega)
  by_cases h23 : j < 691
  · exact kwxstaticRange_661.get (by omega) (by omega)
  by_cases h24 : j < 721
  · exact kwxstaticRange_691.get (by omega) (by omega)
  by_cases h25 : j < 751
  · exact kwxstaticRange_721.get (by omega) (by omega)
  by_cases h26 : j < 781
  · exact kwxstaticRange_751.get (by omega) (by omega)
  by_cases h27 : j < 811
  · exact kwxstaticRange_781.get (by omega) (by omega)
  by_cases h28 : j < 841
  · exact kwxstaticRange_811.get (by omega) (by omega)
  by_cases h29 : j < 871
  · exact kwxstaticRange_841.get (by omega) (by omega)
  by_cases h30 : j < 901
  · exact kwxstaticRange_871.get (by omega) (by omega)
  by_cases h31 : j < 931
  · exact kwxstaticRange_901.get (by omega) (by omega)
  by_cases h32 : j < 961
  · exact kwxstaticRange_931.get (by omega) (by omega)
  by_cases h33 : j < 991
  · exact kwxstaticRange_961.get (by omega) (by omega)
  by_cases h34 : j < 1021
  · exact kwxstaticRange_991.get (by omega) (by omega)
  exact kwxstaticRange_1021.get (by omega) (by omega)

end
end LeanVM.Guest
