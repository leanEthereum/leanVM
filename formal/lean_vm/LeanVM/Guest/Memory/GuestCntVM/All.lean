/-
  LeanVM.Guest.Memory.GuestCntVM.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVM.Part00
public import LeanVM.Guest.Memory.GuestCntVM.Part01
public import LeanVM.Guest.Memory.GuestCntVM.Part02
public import LeanVM.Guest.Memory.GuestCntVM.Part03
public import LeanVM.Guest.Memory.GuestCntVM.Part04
public import LeanVM.Guest.Memory.GuestCntVM.Part05
public import LeanVM.Guest.Memory.GuestCntVM.Part06
public import LeanVM.Guest.Memory.GuestCntVM.Part07
public import LeanVM.Guest.Memory.GuestCntVM.Part08
public import LeanVM.Guest.Memory.GuestCntVM.Part09
public import LeanVM.Guest.Memory.GuestCntVM.Part10
public import LeanVM.Guest.Memory.GuestCntVM.Part11
public import LeanVM.Guest.Memory.GuestCntVM.Part12
public import LeanVM.Guest.Memory.GuestCntVM.Part13
public import LeanVM.Guest.Memory.GuestCntVM.Part14

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmchkIdx_315 : kvmchkIdx 315 = true := by
  have hb : blockB (kvmlookJ 315) (kvmomLookJ 315) false [] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨64765, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [← blockR_eq (Data.core315.body.drop 0), kvmsplit_315_0]
  exact kvmchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_316 : kvmchkIdx 316 = true := by
  have hb : blockB (kvmlookJ 316) (kvmomLookJ 316) false [] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨66289, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [← blockR_eq (Data.core316.body.drop 0), kvmsplit_316_0]
  exact kvmchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvmchkIdx_all : ∀ j < 1535, kvmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 315
  · subst h1000; exact kvmchkIdx_315
  by_cases h1001 : j = 316
  · subst h1001; exact kvmchkIdx_316
  by_cases h0 : j < 11
  · exact kvmstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvmstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvmstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvmstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvmstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvmstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvmstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvmstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvmstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvmstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvmstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 307
  · exact kvmstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 308
  · exact kvmstaticRange_307.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kvmstaticRange_308.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kvmstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvmstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvmstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 313
  · exact kvmstaticRange_312.get (by omega) (by omega)
  by_cases h18 : j < 314
  · exact kvmstaticRange_313.get (by omega) (by omega)
  by_cases h19 : j < 315
  · exact kvmstaticRange_314.get (by omega) (by omega)
  by_cases h20 : j < 338
  · exact kvmstaticRange_317.get (by omega) (by omega)
  by_cases h21 : j < 360
  · exact kvmstaticRange_338.get (by omega) (by omega)
  by_cases h22 : j < 383
  · exact kvmstaticRange_360.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvmstaticRange_383.get (by omega) (by omega)
  by_cases h24 : j < 427
  · exact kvmstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 450
  · exact kvmstaticRange_427.get (by omega) (by omega)
  by_cases h26 : j < 472
  · exact kvmstaticRange_450.get (by omega) (by omega)
  by_cases h27 : j < 494
  · exact kvmstaticRange_472.get (by omega) (by omega)
  by_cases h28 : j < 516
  · exact kvmstaticRange_494.get (by omega) (by omega)
  by_cases h29 : j < 538
  · exact kvmstaticRange_516.get (by omega) (by omega)
  by_cases h30 : j < 560
  · exact kvmstaticRange_538.get (by omega) (by omega)
  by_cases h31 : j < 582
  · exact kvmstaticRange_560.get (by omega) (by omega)
  by_cases h32 : j < 604
  · exact kvmstaticRange_582.get (by omega) (by omega)
  by_cases h33 : j < 626
  · exact kvmstaticRange_604.get (by omega) (by omega)
  by_cases h34 : j < 647
  · exact kvmstaticRange_626.get (by omega) (by omega)
  by_cases h35 : j < 669
  · exact kvmstaticRange_647.get (by omega) (by omega)
  by_cases h36 : j < 690
  · exact kvmstaticRange_669.get (by omega) (by omega)
  by_cases h37 : j < 712
  · exact kvmstaticRange_690.get (by omega) (by omega)
  by_cases h38 : j < 733
  · exact kvmstaticRange_712.get (by omega) (by omega)
  by_cases h39 : j < 755
  · exact kvmstaticRange_733.get (by omega) (by omega)
  by_cases h40 : j < 776
  · exact kvmstaticRange_755.get (by omega) (by omega)
  by_cases h41 : j < 798
  · exact kvmstaticRange_776.get (by omega) (by omega)
  by_cases h42 : j < 819
  · exact kvmstaticRange_798.get (by omega) (by omega)
  by_cases h43 : j < 841
  · exact kvmstaticRange_819.get (by omega) (by omega)
  by_cases h44 : j < 862
  · exact kvmstaticRange_841.get (by omega) (by omega)
  by_cases h45 : j < 884
  · exact kvmstaticRange_862.get (by omega) (by omega)
  by_cases h46 : j < 905
  · exact kvmstaticRange_884.get (by omega) (by omega)
  by_cases h47 : j < 927
  · exact kvmstaticRange_905.get (by omega) (by omega)
  by_cases h48 : j < 951
  · exact kvmstaticRange_927.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvmstaticRange_951.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvmstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1015
  · exact kvmstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1036
  · exact kvmstaticRange_1015.get (by omega) (by omega)
  by_cases h53 : j < 1057
  · exact kvmstaticRange_1036.get (by omega) (by omega)
  by_cases h54 : j < 1078
  · exact kvmstaticRange_1057.get (by omega) (by omega)
  by_cases h55 : j < 1099
  · exact kvmstaticRange_1078.get (by omega) (by omega)
  by_cases h56 : j < 1120
  · exact kvmstaticRange_1099.get (by omega) (by omega)
  by_cases h57 : j < 1141
  · exact kvmstaticRange_1120.get (by omega) (by omega)
  by_cases h58 : j < 1162
  · exact kvmstaticRange_1141.get (by omega) (by omega)
  by_cases h59 : j < 1184
  · exact kvmstaticRange_1162.get (by omega) (by omega)
  by_cases h60 : j < 1203
  · exact kvmstaticRange_1184.get (by omega) (by omega)
  by_cases h61 : j < 1224
  · exact kvmstaticRange_1203.get (by omega) (by omega)
  by_cases h62 : j < 1245
  · exact kvmstaticRange_1224.get (by omega) (by omega)
  by_cases h63 : j < 1266
  · exact kvmstaticRange_1245.get (by omega) (by omega)
  by_cases h64 : j < 1287
  · exact kvmstaticRange_1266.get (by omega) (by omega)
  by_cases h65 : j < 1308
  · exact kvmstaticRange_1287.get (by omega) (by omega)
  by_cases h66 : j < 1329
  · exact kvmstaticRange_1308.get (by omega) (by omega)
  by_cases h67 : j < 1350
  · exact kvmstaticRange_1329.get (by omega) (by omega)
  by_cases h68 : j < 1371
  · exact kvmstaticRange_1350.get (by omega) (by omega)
  by_cases h69 : j < 1392
  · exact kvmstaticRange_1371.get (by omega) (by omega)
  by_cases h70 : j < 1413
  · exact kvmstaticRange_1392.get (by omega) (by omega)
  by_cases h71 : j < 1434
  · exact kvmstaticRange_1413.get (by omega) (by omega)
  by_cases h72 : j < 1448
  · exact kvmstaticRange_1434.get (by omega) (by omega)
  by_cases h73 : j < 1463
  · exact kvmstaticRange_1448.get (by omega) (by omega)
  by_cases h74 : j < 1479
  · exact kvmstaticRange_1463.get (by omega) (by omega)
  by_cases h75 : j < 1491
  · exact kvmstaticRange_1479.get (by omega) (by omega)
  by_cases h76 : j < 1503
  · exact kvmstaticRange_1491.get (by omega) (by omega)
  by_cases h77 : j < 1515
  · exact kvmstaticRange_1503.get (by omega) (by omega)
  by_cases h78 : j < 1525
  · exact kvmstaticRange_1515.get (by omega) (by omega)
  exact kvmstaticRange_1525.get (by omega) (by omega)

end
end LeanVM.Guest
