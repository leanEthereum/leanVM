/-
  LeanVM.Guest.Memory.GuestCntM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntM.Part00
public import LeanVM.Guest.Memory.GuestCntM.Part01
public import LeanVM.Guest.Memory.GuestCntM.Part02
public import LeanVM.Guest.Memory.GuestCntM.Part03
public import LeanVM.Guest.Memory.GuestCntM.Part04
public import LeanVM.Guest.Memory.GuestCntM.Part05
public import LeanVM.Guest.Memory.GuestCntM.Part06
public import LeanVM.Guest.Memory.GuestCntM.Part07
public import LeanVM.Guest.Memory.GuestCntM.Part08
public import LeanVM.Guest.Memory.GuestCntM.Part09
public import LeanVM.Guest.Memory.GuestCntM.Part10
public import LeanVM.Guest.Memory.GuestCntM.Part11

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmchkIdx_16 : kwmchkIdx 16 = true := by
  have hb : blockB (kwmlookJ 16) (kwmomLookJ 16) false [] Data.core16.params Data.core16.name ([], []) Data.core16.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core16.body)]
    rw [blockB_drop' _ _ 0 222 222 kwmsplit_16_0.1 rfl, ← blockR_eq ((Data.core16.body.drop 0).take 222), kwmsplit_16_0.2]
    rw [blockB_drop' _ _ 222 276 498 kwmsplit_16_222.1 rfl, ← blockR_eq ((Data.core16.body.drop 222).take 276), kwmsplit_16_222.2]
    rw [← blockR_eq (Data.core16.body.drop 498), kwmsplit_16_498]
    rfl
  exact kwmchkIdx_of_split (fn := Data.core16) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwmchkIdx_17 : kwmchkIdx 17 = true := by
  have hb : blockB (kwmlookJ 17) (kwmomLookJ 17) false [] Data.core17.params Data.core17.name ([], []) Data.core17.body = some (⟨16, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core17.body)]
    rw [blockB_drop' _ _ 0 220 220 kwmsplit_17_0.1 rfl, ← blockR_eq ((Data.core17.body.drop 0).take 220), kwmsplit_17_0.2]
    rw [blockB_drop' _ _ 220 1 221 kwmsplit_17_220.1 rfl, ← blockR_eq ((Data.core17.body.drop 220).take 1), kwmsplit_17_220.2]
    rw [blockB_drop' _ _ 221 11 232 kwmsplit_17_221.1 rfl, ← blockR_eq ((Data.core17.body.drop 221).take 11), kwmsplit_17_221.2]
    rw [blockB_drop' _ _ 232 1 233 kwmsplit_17_232.1 rfl, ← blockR_eq ((Data.core17.body.drop 232).take 1), kwmsplit_17_232.2]
    rw [blockB_drop' _ _ 233 27 260 kwmsplit_17_233.1 rfl, ← blockR_eq ((Data.core17.body.drop 233).take 27), kwmsplit_17_233.2]
    rw [blockB_drop' _ _ 260 1 261 kwmsplit_17_260.1 rfl, ← blockR_eq ((Data.core17.body.drop 260).take 1), kwmsplit_17_260.2]
    rw [blockB_drop' _ _ 261 11 272 kwmsplit_17_261.1 rfl, ← blockR_eq ((Data.core17.body.drop 261).take 11), kwmsplit_17_261.2]
    rw [blockB_drop' _ _ 272 1 273 kwmsplit_17_272.1 rfl, ← blockR_eq ((Data.core17.body.drop 272).take 1), kwmsplit_17_272.2]
    rw [blockB_drop' _ _ 273 27 300 kwmsplit_17_273.1 rfl, ← blockR_eq ((Data.core17.body.drop 273).take 27), kwmsplit_17_273.2]
    rw [blockB_drop' _ _ 300 1 301 kwmsplit_17_300.1 rfl, ← blockR_eq ((Data.core17.body.drop 300).take 1), kwmsplit_17_300.2]
    rw [blockB_drop' _ _ 301 11 312 kwmsplit_17_301.1 rfl, ← blockR_eq ((Data.core17.body.drop 301).take 11), kwmsplit_17_301.2]
    rw [blockB_drop' _ _ 312 1 313 kwmsplit_17_312.1 rfl, ← blockR_eq ((Data.core17.body.drop 312).take 1), kwmsplit_17_312.2]
    rw [blockB_drop' _ _ 313 27 340 kwmsplit_17_313.1 rfl, ← blockR_eq ((Data.core17.body.drop 313).take 27), kwmsplit_17_313.2]
    rw [blockB_drop' _ _ 340 1 341 kwmsplit_17_340.1 rfl, ← blockR_eq ((Data.core17.body.drop 340).take 1), kwmsplit_17_340.2]
    rw [blockB_drop' _ _ 341 11 352 kwmsplit_17_341.1 rfl, ← blockR_eq ((Data.core17.body.drop 341).take 11), kwmsplit_17_341.2]
    rw [blockB_drop' _ _ 352 1 353 kwmsplit_17_352.1 rfl, ← blockR_eq ((Data.core17.body.drop 352).take 1), kwmsplit_17_352.2]
    rw [blockB_drop' _ _ 353 27 380 kwmsplit_17_353.1 rfl, ← blockR_eq ((Data.core17.body.drop 353).take 27), kwmsplit_17_353.2]
    rw [blockB_drop' _ _ 380 1 381 kwmsplit_17_380.1 rfl, ← blockR_eq ((Data.core17.body.drop 380).take 1), kwmsplit_17_380.2]
    rw [blockB_drop' _ _ 381 11 392 kwmsplit_17_381.1 rfl, ← blockR_eq ((Data.core17.body.drop 381).take 11), kwmsplit_17_381.2]
    rw [blockB_drop' _ _ 392 1 393 kwmsplit_17_392.1 rfl, ← blockR_eq ((Data.core17.body.drop 392).take 1), kwmsplit_17_392.2]
    rw [blockB_drop' _ _ 393 27 420 kwmsplit_17_393.1 rfl, ← blockR_eq ((Data.core17.body.drop 393).take 27), kwmsplit_17_393.2]
    rw [blockB_drop' _ _ 420 1 421 kwmsplit_17_420.1 rfl, ← blockR_eq ((Data.core17.body.drop 420).take 1), kwmsplit_17_420.2]
    rw [blockB_drop' _ _ 421 11 432 kwmsplit_17_421.1 rfl, ← blockR_eq ((Data.core17.body.drop 421).take 11), kwmsplit_17_421.2]
    rw [blockB_drop' _ _ 432 1 433 kwmsplit_17_432.1 rfl, ← blockR_eq ((Data.core17.body.drop 432).take 1), kwmsplit_17_432.2]
    rw [blockB_drop' _ _ 433 27 460 kwmsplit_17_433.1 rfl, ← blockR_eq ((Data.core17.body.drop 433).take 27), kwmsplit_17_433.2]
    rw [blockB_drop' _ _ 460 1 461 kwmsplit_17_460.1 rfl, ← blockR_eq ((Data.core17.body.drop 460).take 1), kwmsplit_17_460.2]
    rw [blockB_drop' _ _ 461 11 472 kwmsplit_17_461.1 rfl, ← blockR_eq ((Data.core17.body.drop 461).take 11), kwmsplit_17_461.2]
    rw [blockB_drop' _ _ 472 1 473 kwmsplit_17_472.1 rfl, ← blockR_eq ((Data.core17.body.drop 472).take 1), kwmsplit_17_472.2]
    rw [blockB_drop' _ _ 473 27 500 kwmsplit_17_473.1 rfl, ← blockR_eq ((Data.core17.body.drop 473).take 27), kwmsplit_17_473.2]
    rw [blockB_drop' _ _ 500 1 501 kwmsplit_17_500.1 rfl, ← blockR_eq ((Data.core17.body.drop 500).take 1), kwmsplit_17_500.2]
    rw [blockB_drop' _ _ 501 11 512 kwmsplit_17_501.1 rfl, ← blockR_eq ((Data.core17.body.drop 501).take 11), kwmsplit_17_501.2]
    rw [blockB_drop' _ _ 512 1 513 kwmsplit_17_512.1 rfl, ← blockR_eq ((Data.core17.body.drop 512).take 1), kwmsplit_17_512.2]
    rw [blockB_drop' _ _ 513 264 777 kwmsplit_17_513.1 rfl, ← blockR_eq ((Data.core17.body.drop 513).take 264), kwmsplit_17_513.2]
    rw [← blockR_eq (Data.core17.body.drop 777), kwmsplit_17_777]
    rfl
  exact kwmchkIdx_of_split (fn := Data.core17) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwmchkIdx_all : ∀ j < 1043, kwmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 16
  · subst h1000; exact kwmchkIdx_16
  by_cases h1001 : j = 17
  · subst h1001; exact kwmchkIdx_17
  by_cases h0 : j < 16
  · exact kwmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 48
  · exact kwmstaticRange_18.get (by omega) (by omega)
  by_cases h2 : j < 78
  · exact kwmstaticRange_48.get (by omega) (by omega)
  by_cases h3 : j < 108
  · exact kwmstaticRange_78.get (by omega) (by omega)
  by_cases h4 : j < 138
  · exact kwmstaticRange_108.get (by omega) (by omega)
  by_cases h5 : j < 168
  · exact kwmstaticRange_138.get (by omega) (by omega)
  by_cases h6 : j < 198
  · exact kwmstaticRange_168.get (by omega) (by omega)
  by_cases h7 : j < 228
  · exact kwmstaticRange_198.get (by omega) (by omega)
  by_cases h8 : j < 256
  · exact kwmstaticRange_228.get (by omega) (by omega)
  by_cases h9 : j < 284
  · exact kwmstaticRange_256.get (by omega) (by omega)
  by_cases h10 : j < 312
  · exact kwmstaticRange_284.get (by omega) (by omega)
  by_cases h11 : j < 340
  · exact kwmstaticRange_312.get (by omega) (by omega)
  by_cases h12 : j < 368
  · exact kwmstaticRange_340.get (by omega) (by omega)
  by_cases h13 : j < 396
  · exact kwmstaticRange_368.get (by omega) (by omega)
  by_cases h14 : j < 424
  · exact kwmstaticRange_396.get (by omega) (by omega)
  by_cases h15 : j < 452
  · exact kwmstaticRange_424.get (by omega) (by omega)
  by_cases h16 : j < 482
  · exact kwmstaticRange_452.get (by omega) (by omega)
  by_cases h17 : j < 512
  · exact kwmstaticRange_482.get (by omega) (by omega)
  by_cases h18 : j < 542
  · exact kwmstaticRange_512.get (by omega) (by omega)
  by_cases h19 : j < 571
  · exact kwmstaticRange_542.get (by omega) (by omega)
  by_cases h20 : j < 601
  · exact kwmstaticRange_571.get (by omega) (by omega)
  by_cases h21 : j < 631
  · exact kwmstaticRange_601.get (by omega) (by omega)
  by_cases h22 : j < 661
  · exact kwmstaticRange_631.get (by omega) (by omega)
  by_cases h23 : j < 691
  · exact kwmstaticRange_661.get (by omega) (by omega)
  by_cases h24 : j < 721
  · exact kwmstaticRange_691.get (by omega) (by omega)
  by_cases h25 : j < 751
  · exact kwmstaticRange_721.get (by omega) (by omega)
  by_cases h26 : j < 781
  · exact kwmstaticRange_751.get (by omega) (by omega)
  by_cases h27 : j < 811
  · exact kwmstaticRange_781.get (by omega) (by omega)
  by_cases h28 : j < 841
  · exact kwmstaticRange_811.get (by omega) (by omega)
  by_cases h29 : j < 871
  · exact kwmstaticRange_841.get (by omega) (by omega)
  by_cases h30 : j < 901
  · exact kwmstaticRange_871.get (by omega) (by omega)
  by_cases h31 : j < 931
  · exact kwmstaticRange_901.get (by omega) (by omega)
  by_cases h32 : j < 961
  · exact kwmstaticRange_931.get (by omega) (by omega)
  by_cases h33 : j < 991
  · exact kwmstaticRange_961.get (by omega) (by omega)
  by_cases h34 : j < 1021
  · exact kwmstaticRange_991.get (by omega) (by omega)
  exact kwmstaticRange_1021.get (by omega) (by omega)

end
end LeanVM.Guest
