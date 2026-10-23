/-
  LeanVM.Guest.Memory.GuestWords.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestWords.Part00
public import LeanVM.Guest.Memory.GuestWords.Part01
public import LeanVM.Guest.Memory.GuestWords.Part02
public import LeanVM.Guest.Memory.GuestWords.Part03
public import LeanVM.Guest.Memory.GuestWords.Part04
public import LeanVM.Guest.Memory.GuestWords.Part05
public import LeanVM.Guest.Memory.GuestWords.Part06
public import LeanVM.Guest.Memory.GuestWords.Part07
public import LeanVM.Guest.Memory.GuestWords.Part08
public import LeanVM.Guest.Memory.GuestWords.Part09
public import LeanVM.Guest.Memory.GuestWords.Part10
public import LeanVM.Guest.Memory.GuestWords.Part11
public import LeanVM.Guest.Memory.GuestWords.Part12
public import LeanVM.Guest.Memory.GuestWords.Part13
public import LeanVM.Guest.Memory.GuestWords.Part14
public import LeanVM.Guest.Memory.GuestWords.Part15
public import LeanVM.Guest.Memory.GuestWords.Part16
public import LeanVM.Guest.Memory.GuestWords.Part17
public import LeanVM.Guest.Memory.GuestWords.Part18
public import LeanVM.Guest.Memory.GuestWords.Part19
public import LeanVM.Guest.Memory.GuestWords.Part20
public import LeanVM.Guest.Memory.GuestWords.Part21
public import LeanVM.Guest.Memory.GuestWords.Part22
public import LeanVM.Guest.Memory.GuestWords.Part23

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wchkIdx_16 : wchkIdx 16 = true := by
  have hb : blockB (wlookJ 16) (womLookJ 16) true [] Data.core16.params Data.core16.name ([], []) Data.core16.body = some (⟨0, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core16.body)]
    rw [blockB_drop' _ _ 0 222 222 wsplit_16_0.1 rfl, ← blockR_eq ((Data.core16.body.drop 0).take 222), wsplit_16_0.2]
    rw [blockB_drop' _ _ 222 276 498 wsplit_16_222.1 rfl, ← blockR_eq ((Data.core16.body.drop 222).take 276), wsplit_16_222.2]
    rw [← blockR_eq (Data.core16.body.drop 498), wsplit_16_498]
    rfl
  exact wchkIdx_of_split (fn := Data.core16) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem wchkIdx_17 : wchkIdx 17 = true := by
  have hb : blockB (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ([], []) Data.core17.body = some (⟨784, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core17.body)]
    rw [blockB_drop' _ _ 0 220 220 wsplit_17_0.1 rfl, ← blockR_eq ((Data.core17.body.drop 0).take 220), wsplit_17_0.2]
    rw [blockB_drop' _ _ 220 1 221 wsplit_17_220.1 rfl, ← blockR_eq ((Data.core17.body.drop 220).take 1), wsplit_17_220.2]
    rw [blockB_drop' _ _ 221 11 232 wsplit_17_221.1 rfl, ← blockR_eq ((Data.core17.body.drop 221).take 11), wsplit_17_221.2]
    rw [blockB_drop' _ _ 232 1 233 wsplit_17_232.1 rfl, ← blockR_eq ((Data.core17.body.drop 232).take 1), wsplit_17_232.2]
    rw [blockB_drop' _ _ 233 27 260 wsplit_17_233.1 rfl, ← blockR_eq ((Data.core17.body.drop 233).take 27), wsplit_17_233.2]
    rw [blockB_drop' _ _ 260 1 261 wsplit_17_260.1 rfl, ← blockR_eq ((Data.core17.body.drop 260).take 1), wsplit_17_260.2]
    rw [blockB_drop' _ _ 261 11 272 wsplit_17_261.1 rfl, ← blockR_eq ((Data.core17.body.drop 261).take 11), wsplit_17_261.2]
    rw [blockB_drop' _ _ 272 1 273 wsplit_17_272.1 rfl, ← blockR_eq ((Data.core17.body.drop 272).take 1), wsplit_17_272.2]
    rw [blockB_drop' _ _ 273 27 300 wsplit_17_273.1 rfl, ← blockR_eq ((Data.core17.body.drop 273).take 27), wsplit_17_273.2]
    rw [blockB_drop' _ _ 300 1 301 wsplit_17_300.1 rfl, ← blockR_eq ((Data.core17.body.drop 300).take 1), wsplit_17_300.2]
    rw [blockB_drop' _ _ 301 11 312 wsplit_17_301.1 rfl, ← blockR_eq ((Data.core17.body.drop 301).take 11), wsplit_17_301.2]
    rw [blockB_drop' _ _ 312 1 313 wsplit_17_312.1 rfl, ← blockR_eq ((Data.core17.body.drop 312).take 1), wsplit_17_312.2]
    rw [blockB_drop' _ _ 313 27 340 wsplit_17_313.1 rfl, ← blockR_eq ((Data.core17.body.drop 313).take 27), wsplit_17_313.2]
    rw [blockB_drop' _ _ 340 1 341 wsplit_17_340.1 rfl, ← blockR_eq ((Data.core17.body.drop 340).take 1), wsplit_17_340.2]
    rw [blockB_drop' _ _ 341 11 352 wsplit_17_341.1 rfl, ← blockR_eq ((Data.core17.body.drop 341).take 11), wsplit_17_341.2]
    rw [blockB_drop' _ _ 352 1 353 wsplit_17_352.1 rfl, ← blockR_eq ((Data.core17.body.drop 352).take 1), wsplit_17_352.2]
    rw [blockB_drop' _ _ 353 27 380 wsplit_17_353.1 rfl, ← blockR_eq ((Data.core17.body.drop 353).take 27), wsplit_17_353.2]
    rw [blockB_drop' _ _ 380 1 381 wsplit_17_380.1 rfl, ← blockR_eq ((Data.core17.body.drop 380).take 1), wsplit_17_380.2]
    rw [blockB_drop' _ _ 381 11 392 wsplit_17_381.1 rfl, ← blockR_eq ((Data.core17.body.drop 381).take 11), wsplit_17_381.2]
    rw [blockB_drop' _ _ 392 1 393 wsplit_17_392.1 rfl, ← blockR_eq ((Data.core17.body.drop 392).take 1), wsplit_17_392.2]
    rw [blockB_drop' _ _ 393 27 420 wsplit_17_393.1 rfl, ← blockR_eq ((Data.core17.body.drop 393).take 27), wsplit_17_393.2]
    rw [blockB_drop' _ _ 420 1 421 wsplit_17_420.1 rfl, ← blockR_eq ((Data.core17.body.drop 420).take 1), wsplit_17_420.2]
    rw [blockB_drop' _ _ 421 11 432 wsplit_17_421.1 rfl, ← blockR_eq ((Data.core17.body.drop 421).take 11), wsplit_17_421.2]
    rw [blockB_drop' _ _ 432 1 433 wsplit_17_432.1 rfl, ← blockR_eq ((Data.core17.body.drop 432).take 1), wsplit_17_432.2]
    rw [blockB_drop' _ _ 433 27 460 wsplit_17_433.1 rfl, ← blockR_eq ((Data.core17.body.drop 433).take 27), wsplit_17_433.2]
    rw [blockB_drop' _ _ 460 1 461 wsplit_17_460.1 rfl, ← blockR_eq ((Data.core17.body.drop 460).take 1), wsplit_17_460.2]
    rw [blockB_drop' _ _ 461 11 472 wsplit_17_461.1 rfl, ← blockR_eq ((Data.core17.body.drop 461).take 11), wsplit_17_461.2]
    rw [blockB_drop' _ _ 472 1 473 wsplit_17_472.1 rfl, ← blockR_eq ((Data.core17.body.drop 472).take 1), wsplit_17_472.2]
    rw [blockB_drop' _ _ 473 27 500 wsplit_17_473.1 rfl, ← blockR_eq ((Data.core17.body.drop 473).take 27), wsplit_17_473.2]
    rw [blockB_drop' _ _ 500 1 501 wsplit_17_500.1 rfl, ← blockR_eq ((Data.core17.body.drop 500).take 1), wsplit_17_500.2]
    rw [blockB_drop' _ _ 501 11 512 wsplit_17_501.1 rfl, ← blockR_eq ((Data.core17.body.drop 501).take 11), wsplit_17_501.2]
    rw [blockB_drop' _ _ 512 1 513 wsplit_17_512.1 rfl, ← blockR_eq ((Data.core17.body.drop 512).take 1), wsplit_17_512.2]
    rw [blockB_drop' _ _ 513 264 777 wsplit_17_513.1 rfl, ← blockR_eq ((Data.core17.body.drop 513).take 264), wsplit_17_513.2]
    rw [← blockR_eq (Data.core17.body.drop 777), wsplit_17_777]
    rfl
  exact wchkIdx_of_split (fn := Data.core17) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem wchkIdx_all : ∀ j < 1043, wchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 16
  · subst h1000; exact wchkIdx_16
  by_cases h1001 : j = 17
  · subst h1001; exact wchkIdx_17
  by_cases h0 : j < 11
  · exact wstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 12
  · exact wstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 14
  · exact wstaticRange_12.get (by omega) (by omega)
  by_cases h3 : j < 15
  · exact wstaticRange_14.get (by omega) (by omega)
  by_cases h4 : j < 16
  · exact wstaticRange_15.get (by omega) (by omega)
  by_cases h5 : j < 25
  · exact wstaticRange_18.get (by omega) (by omega)
  by_cases h6 : j < 41
  · exact wstaticRange_25.get (by omega) (by omega)
  by_cases h7 : j < 66
  · exact wstaticRange_41.get (by omega) (by omega)
  by_cases h8 : j < 89
  · exact wstaticRange_66.get (by omega) (by omega)
  by_cases h9 : j < 113
  · exact wstaticRange_89.get (by omega) (by omega)
  by_cases h10 : j < 137
  · exact wstaticRange_113.get (by omega) (by omega)
  by_cases h11 : j < 160
  · exact wstaticRange_137.get (by omega) (by omega)
  by_cases h12 : j < 177
  · exact wstaticRange_160.get (by omega) (by omega)
  by_cases h13 : j < 178
  · exact wstaticRange_177.get (by omega) (by omega)
  by_cases h14 : j < 179
  · exact wstaticRange_178.get (by omega) (by omega)
  by_cases h15 : j < 180
  · exact wstaticRange_179.get (by omega) (by omega)
  by_cases h16 : j < 181
  · exact wstaticRange_180.get (by omega) (by omega)
  by_cases h17 : j < 182
  · exact wstaticRange_181.get (by omega) (by omega)
  by_cases h18 : j < 183
  · exact wstaticRange_182.get (by omega) (by omega)
  by_cases h19 : j < 184
  · exact wstaticRange_183.get (by omega) (by omega)
  by_cases h20 : j < 186
  · exact wstaticRange_184.get (by omega) (by omega)
  by_cases h21 : j < 187
  · exact wstaticRange_186.get (by omega) (by omega)
  by_cases h22 : j < 188
  · exact wstaticRange_187.get (by omega) (by omega)
  by_cases h23 : j < 189
  · exact wstaticRange_188.get (by omega) (by omega)
  by_cases h24 : j < 190
  · exact wstaticRange_189.get (by omega) (by omega)
  by_cases h25 : j < 191
  · exact wstaticRange_190.get (by omega) (by omega)
  by_cases h26 : j < 193
  · exact wstaticRange_191.get (by omega) (by omega)
  by_cases h27 : j < 194
  · exact wstaticRange_193.get (by omega) (by omega)
  by_cases h28 : j < 195
  · exact wstaticRange_194.get (by omega) (by omega)
  by_cases h29 : j < 196
  · exact wstaticRange_195.get (by omega) (by omega)
  by_cases h30 : j < 197
  · exact wstaticRange_196.get (by omega) (by omega)
  by_cases h31 : j < 198
  · exact wstaticRange_197.get (by omega) (by omega)
  by_cases h32 : j < 200
  · exact wstaticRange_198.get (by omega) (by omega)
  by_cases h33 : j < 201
  · exact wstaticRange_200.get (by omega) (by omega)
  by_cases h34 : j < 202
  · exact wstaticRange_201.get (by omega) (by omega)
  by_cases h35 : j < 203
  · exact wstaticRange_202.get (by omega) (by omega)
  by_cases h36 : j < 204
  · exact wstaticRange_203.get (by omega) (by omega)
  by_cases h37 : j < 214
  · exact wstaticRange_204.get (by omega) (by omega)
  by_cases h38 : j < 242
  · exact wstaticRange_214.get (by omega) (by omega)
  by_cases h39 : j < 270
  · exact wstaticRange_242.get (by omega) (by omega)
  by_cases h40 : j < 298
  · exact wstaticRange_270.get (by omega) (by omega)
  by_cases h41 : j < 326
  · exact wstaticRange_298.get (by omega) (by omega)
  by_cases h42 : j < 354
  · exact wstaticRange_326.get (by omega) (by omega)
  by_cases h43 : j < 382
  · exact wstaticRange_354.get (by omega) (by omega)
  by_cases h44 : j < 410
  · exact wstaticRange_382.get (by omega) (by omega)
  by_cases h45 : j < 438
  · exact wstaticRange_410.get (by omega) (by omega)
  by_cases h46 : j < 465
  · exact wstaticRange_438.get (by omega) (by omega)
  by_cases h47 : j < 491
  · exact wstaticRange_465.get (by omega) (by omega)
  by_cases h48 : j < 515
  · exact wstaticRange_491.get (by omega) (by omega)
  by_cases h49 : j < 534
  · exact wstaticRange_515.get (by omega) (by omega)
  by_cases h50 : j < 547
  · exact wstaticRange_534.get (by omega) (by omega)
  by_cases h51 : j < 566
  · exact wstaticRange_547.get (by omega) (by omega)
  by_cases h52 : j < 582
  · exact wstaticRange_566.get (by omega) (by omega)
  by_cases h53 : j < 604
  · exact wstaticRange_582.get (by omega) (by omega)
  by_cases h54 : j < 626
  · exact wstaticRange_604.get (by omega) (by omega)
  by_cases h55 : j < 648
  · exact wstaticRange_626.get (by omega) (by omega)
  by_cases h56 : j < 670
  · exact wstaticRange_648.get (by omega) (by omega)
  by_cases h57 : j < 692
  · exact wstaticRange_670.get (by omega) (by omega)
  by_cases h58 : j < 713
  · exact wstaticRange_692.get (by omega) (by omega)
  by_cases h59 : j < 734
  · exact wstaticRange_713.get (by omega) (by omega)
  by_cases h60 : j < 756
  · exact wstaticRange_734.get (by omega) (by omega)
  by_cases h61 : j < 777
  · exact wstaticRange_756.get (by omega) (by omega)
  by_cases h62 : j < 798
  · exact wstaticRange_777.get (by omega) (by omega)
  by_cases h63 : j < 819
  · exact wstaticRange_798.get (by omega) (by omega)
  by_cases h64 : j < 841
  · exact wstaticRange_819.get (by omega) (by omega)
  by_cases h65 : j < 862
  · exact wstaticRange_841.get (by omega) (by omega)
  by_cases h66 : j < 883
  · exact wstaticRange_862.get (by omega) (by omega)
  by_cases h67 : j < 905
  · exact wstaticRange_883.get (by omega) (by omega)
  by_cases h68 : j < 924
  · exact wstaticRange_905.get (by omega) (by omega)
  by_cases h69 : j < 948
  · exact wstaticRange_924.get (by omega) (by omega)
  by_cases h70 : j < 971
  · exact wstaticRange_948.get (by omega) (by omega)
  by_cases h71 : j < 987
  · exact wstaticRange_971.get (by omega) (by omega)
  by_cases h72 : j < 1003
  · exact wstaticRange_987.get (by omega) (by omega)
  by_cases h73 : j < 1019
  · exact wstaticRange_1003.get (by omega) (by omega)
  by_cases h74 : j < 1034
  · exact wstaticRange_1019.get (by omega) (by omega)
  exact wstaticRange_1034.get (by omega) (by omega)

end
end LeanVM.Guest
