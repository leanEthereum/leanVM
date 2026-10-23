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
public import LeanVM.Guest.Memory.GuestCntS.Part11

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwschkIdx_16 : kwschkIdx 16 = true := by
  have hb : blockB (kwslookJ 16) (kwsomLookJ 16) false [] Data.core16.params Data.core16.name ([], []) Data.core16.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core16.body)]
    rw [blockB_drop' _ _ 0 222 222 kwssplit_16_0.1 rfl, ← blockR_eq ((Data.core16.body.drop 0).take 222), kwssplit_16_0.2]
    rw [blockB_drop' _ _ 222 276 498 kwssplit_16_222.1 rfl, ← blockR_eq ((Data.core16.body.drop 222).take 276), kwssplit_16_222.2]
    rw [← blockR_eq (Data.core16.body.drop 498), kwssplit_16_498]
    rfl
  exact kwschkIdx_of_split (fn := Data.core16) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kwschkIdx_17 : kwschkIdx 17 = true := by
  have hb : blockB (kwslookJ 17) (kwsomLookJ 17) false [] Data.core17.params Data.core17.name ([], []) Data.core17.body = some (⟨224, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core17.body)]
    rw [blockB_drop' _ _ 0 220 220 kwssplit_17_0.1 rfl, ← blockR_eq ((Data.core17.body.drop 0).take 220), kwssplit_17_0.2]
    rw [blockB_drop' _ _ 220 1 221 kwssplit_17_220.1 rfl, ← blockR_eq ((Data.core17.body.drop 220).take 1), kwssplit_17_220.2]
    rw [blockB_drop' _ _ 221 11 232 kwssplit_17_221.1 rfl, ← blockR_eq ((Data.core17.body.drop 221).take 11), kwssplit_17_221.2]
    rw [blockB_drop' _ _ 232 1 233 kwssplit_17_232.1 rfl, ← blockR_eq ((Data.core17.body.drop 232).take 1), kwssplit_17_232.2]
    rw [blockB_drop' _ _ 233 27 260 kwssplit_17_233.1 rfl, ← blockR_eq ((Data.core17.body.drop 233).take 27), kwssplit_17_233.2]
    rw [blockB_drop' _ _ 260 1 261 kwssplit_17_260.1 rfl, ← blockR_eq ((Data.core17.body.drop 260).take 1), kwssplit_17_260.2]
    rw [blockB_drop' _ _ 261 11 272 kwssplit_17_261.1 rfl, ← blockR_eq ((Data.core17.body.drop 261).take 11), kwssplit_17_261.2]
    rw [blockB_drop' _ _ 272 1 273 kwssplit_17_272.1 rfl, ← blockR_eq ((Data.core17.body.drop 272).take 1), kwssplit_17_272.2]
    rw [blockB_drop' _ _ 273 27 300 kwssplit_17_273.1 rfl, ← blockR_eq ((Data.core17.body.drop 273).take 27), kwssplit_17_273.2]
    rw [blockB_drop' _ _ 300 1 301 kwssplit_17_300.1 rfl, ← blockR_eq ((Data.core17.body.drop 300).take 1), kwssplit_17_300.2]
    rw [blockB_drop' _ _ 301 11 312 kwssplit_17_301.1 rfl, ← blockR_eq ((Data.core17.body.drop 301).take 11), kwssplit_17_301.2]
    rw [blockB_drop' _ _ 312 1 313 kwssplit_17_312.1 rfl, ← blockR_eq ((Data.core17.body.drop 312).take 1), kwssplit_17_312.2]
    rw [blockB_drop' _ _ 313 27 340 kwssplit_17_313.1 rfl, ← blockR_eq ((Data.core17.body.drop 313).take 27), kwssplit_17_313.2]
    rw [blockB_drop' _ _ 340 1 341 kwssplit_17_340.1 rfl, ← blockR_eq ((Data.core17.body.drop 340).take 1), kwssplit_17_340.2]
    rw [blockB_drop' _ _ 341 11 352 kwssplit_17_341.1 rfl, ← blockR_eq ((Data.core17.body.drop 341).take 11), kwssplit_17_341.2]
    rw [blockB_drop' _ _ 352 1 353 kwssplit_17_352.1 rfl, ← blockR_eq ((Data.core17.body.drop 352).take 1), kwssplit_17_352.2]
    rw [blockB_drop' _ _ 353 27 380 kwssplit_17_353.1 rfl, ← blockR_eq ((Data.core17.body.drop 353).take 27), kwssplit_17_353.2]
    rw [blockB_drop' _ _ 380 1 381 kwssplit_17_380.1 rfl, ← blockR_eq ((Data.core17.body.drop 380).take 1), kwssplit_17_380.2]
    rw [blockB_drop' _ _ 381 11 392 kwssplit_17_381.1 rfl, ← blockR_eq ((Data.core17.body.drop 381).take 11), kwssplit_17_381.2]
    rw [blockB_drop' _ _ 392 1 393 kwssplit_17_392.1 rfl, ← blockR_eq ((Data.core17.body.drop 392).take 1), kwssplit_17_392.2]
    rw [blockB_drop' _ _ 393 27 420 kwssplit_17_393.1 rfl, ← blockR_eq ((Data.core17.body.drop 393).take 27), kwssplit_17_393.2]
    rw [blockB_drop' _ _ 420 1 421 kwssplit_17_420.1 rfl, ← blockR_eq ((Data.core17.body.drop 420).take 1), kwssplit_17_420.2]
    rw [blockB_drop' _ _ 421 11 432 kwssplit_17_421.1 rfl, ← blockR_eq ((Data.core17.body.drop 421).take 11), kwssplit_17_421.2]
    rw [blockB_drop' _ _ 432 1 433 kwssplit_17_432.1 rfl, ← blockR_eq ((Data.core17.body.drop 432).take 1), kwssplit_17_432.2]
    rw [blockB_drop' _ _ 433 27 460 kwssplit_17_433.1 rfl, ← blockR_eq ((Data.core17.body.drop 433).take 27), kwssplit_17_433.2]
    rw [blockB_drop' _ _ 460 1 461 kwssplit_17_460.1 rfl, ← blockR_eq ((Data.core17.body.drop 460).take 1), kwssplit_17_460.2]
    rw [blockB_drop' _ _ 461 11 472 kwssplit_17_461.1 rfl, ← blockR_eq ((Data.core17.body.drop 461).take 11), kwssplit_17_461.2]
    rw [blockB_drop' _ _ 472 1 473 kwssplit_17_472.1 rfl, ← blockR_eq ((Data.core17.body.drop 472).take 1), kwssplit_17_472.2]
    rw [blockB_drop' _ _ 473 27 500 kwssplit_17_473.1 rfl, ← blockR_eq ((Data.core17.body.drop 473).take 27), kwssplit_17_473.2]
    rw [blockB_drop' _ _ 500 1 501 kwssplit_17_500.1 rfl, ← blockR_eq ((Data.core17.body.drop 500).take 1), kwssplit_17_500.2]
    rw [blockB_drop' _ _ 501 11 512 kwssplit_17_501.1 rfl, ← blockR_eq ((Data.core17.body.drop 501).take 11), kwssplit_17_501.2]
    rw [blockB_drop' _ _ 512 1 513 kwssplit_17_512.1 rfl, ← blockR_eq ((Data.core17.body.drop 512).take 1), kwssplit_17_512.2]
    rw [blockB_drop' _ _ 513 264 777 kwssplit_17_513.1 rfl, ← blockR_eq ((Data.core17.body.drop 513).take 264), kwssplit_17_513.2]
    rw [← blockR_eq (Data.core17.body.drop 777), kwssplit_17_777]
    rfl
  exact kwschkIdx_of_split (fn := Data.core17) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kwschkIdx_all : ∀ j < 1043, kwschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 16
  · subst h1000; exact kwschkIdx_16
  by_cases h1001 : j = 17
  · subst h1001; exact kwschkIdx_17
  by_cases h0 : j < 16
  · exact kwsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 48
  · exact kwsstaticRange_18.get (by omega) (by omega)
  by_cases h2 : j < 78
  · exact kwsstaticRange_48.get (by omega) (by omega)
  by_cases h3 : j < 108
  · exact kwsstaticRange_78.get (by omega) (by omega)
  by_cases h4 : j < 138
  · exact kwsstaticRange_108.get (by omega) (by omega)
  by_cases h5 : j < 168
  · exact kwsstaticRange_138.get (by omega) (by omega)
  by_cases h6 : j < 198
  · exact kwsstaticRange_168.get (by omega) (by omega)
  by_cases h7 : j < 228
  · exact kwsstaticRange_198.get (by omega) (by omega)
  by_cases h8 : j < 256
  · exact kwsstaticRange_228.get (by omega) (by omega)
  by_cases h9 : j < 284
  · exact kwsstaticRange_256.get (by omega) (by omega)
  by_cases h10 : j < 312
  · exact kwsstaticRange_284.get (by omega) (by omega)
  by_cases h11 : j < 340
  · exact kwsstaticRange_312.get (by omega) (by omega)
  by_cases h12 : j < 368
  · exact kwsstaticRange_340.get (by omega) (by omega)
  by_cases h13 : j < 396
  · exact kwsstaticRange_368.get (by omega) (by omega)
  by_cases h14 : j < 424
  · exact kwsstaticRange_396.get (by omega) (by omega)
  by_cases h15 : j < 452
  · exact kwsstaticRange_424.get (by omega) (by omega)
  by_cases h16 : j < 482
  · exact kwsstaticRange_452.get (by omega) (by omega)
  by_cases h17 : j < 512
  · exact kwsstaticRange_482.get (by omega) (by omega)
  by_cases h18 : j < 542
  · exact kwsstaticRange_512.get (by omega) (by omega)
  by_cases h19 : j < 571
  · exact kwsstaticRange_542.get (by omega) (by omega)
  by_cases h20 : j < 601
  · exact kwsstaticRange_571.get (by omega) (by omega)
  by_cases h21 : j < 631
  · exact kwsstaticRange_601.get (by omega) (by omega)
  by_cases h22 : j < 661
  · exact kwsstaticRange_631.get (by omega) (by omega)
  by_cases h23 : j < 691
  · exact kwsstaticRange_661.get (by omega) (by omega)
  by_cases h24 : j < 721
  · exact kwsstaticRange_691.get (by omega) (by omega)
  by_cases h25 : j < 751
  · exact kwsstaticRange_721.get (by omega) (by omega)
  by_cases h26 : j < 781
  · exact kwsstaticRange_751.get (by omega) (by omega)
  by_cases h27 : j < 811
  · exact kwsstaticRange_781.get (by omega) (by omega)
  by_cases h28 : j < 841
  · exact kwsstaticRange_811.get (by omega) (by omega)
  by_cases h29 : j < 871
  · exact kwsstaticRange_841.get (by omega) (by omega)
  by_cases h30 : j < 901
  · exact kwsstaticRange_871.get (by omega) (by omega)
  by_cases h31 : j < 931
  · exact kwsstaticRange_901.get (by omega) (by omega)
  by_cases h32 : j < 961
  · exact kwsstaticRange_931.get (by omega) (by omega)
  by_cases h33 : j < 991
  · exact kwsstaticRange_961.get (by omega) (by omega)
  by_cases h34 : j < 1021
  · exact kwsstaticRange_991.get (by omega) (by omega)
  exact kwsstaticRange_1021.get (by omega) (by omega)

end
end LeanVM.Guest
