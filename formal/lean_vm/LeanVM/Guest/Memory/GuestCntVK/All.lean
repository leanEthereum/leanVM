/-
  LeanVM.Guest.Memory.GuestCntVK.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVK.Part00
public import LeanVM.Guest.Memory.GuestCntVK.Part01
public import LeanVM.Guest.Memory.GuestCntVK.Part02
public import LeanVM.Guest.Memory.GuestCntVK.Part03
public import LeanVM.Guest.Memory.GuestCntVK.Part04
public import LeanVM.Guest.Memory.GuestCntVK.Part05
public import LeanVM.Guest.Memory.GuestCntVK.Part06
public import LeanVM.Guest.Memory.GuestCntVK.Part07
public import LeanVM.Guest.Memory.GuestCntVK.Part08
public import LeanVM.Guest.Memory.GuestCntVK.Part09
public import LeanVM.Guest.Memory.GuestCntVK.Part10
public import LeanVM.Guest.Memory.GuestCntVK.Part11
public import LeanVM.Guest.Memory.GuestCntVK.Part12
public import LeanVM.Guest.Memory.GuestCntVK.Part13
public import LeanVM.Guest.Memory.GuestCntVK.Part14

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkchkIdx_315 : kvkchkIdx 315 = true := by
  have hb : blockB (kvklookJ 315) (kvkomLookJ 315) false [] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨8268, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [← blockR_eq (Data.core315.body.drop 0), kvksplit_315_0]
  exact kvkchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_316 : kvkchkIdx 316 = true := by
  have hb : blockB (kvklookJ 316) (kvkomLookJ 316) false [] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨8398, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [← blockR_eq (Data.core316.body.drop 0), kvksplit_316_0]
  exact kvkchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvkchkIdx_all : ∀ j < 1535, kvkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 315
  · subst h1000; exact kvkchkIdx_315
  by_cases h1001 : j = 316
  · subst h1001; exact kvkchkIdx_316
  by_cases h0 : j < 11
  · exact kvkstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvkstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvkstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvkstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvkstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvkstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvkstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvkstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvkstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvkstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvkstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 307
  · exact kvkstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 308
  · exact kvkstaticRange_307.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kvkstaticRange_308.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kvkstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvkstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvkstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 313
  · exact kvkstaticRange_312.get (by omega) (by omega)
  by_cases h18 : j < 314
  · exact kvkstaticRange_313.get (by omega) (by omega)
  by_cases h19 : j < 315
  · exact kvkstaticRange_314.get (by omega) (by omega)
  by_cases h20 : j < 338
  · exact kvkstaticRange_317.get (by omega) (by omega)
  by_cases h21 : j < 360
  · exact kvkstaticRange_338.get (by omega) (by omega)
  by_cases h22 : j < 383
  · exact kvkstaticRange_360.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvkstaticRange_383.get (by omega) (by omega)
  by_cases h24 : j < 427
  · exact kvkstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 450
  · exact kvkstaticRange_427.get (by omega) (by omega)
  by_cases h26 : j < 472
  · exact kvkstaticRange_450.get (by omega) (by omega)
  by_cases h27 : j < 494
  · exact kvkstaticRange_472.get (by omega) (by omega)
  by_cases h28 : j < 516
  · exact kvkstaticRange_494.get (by omega) (by omega)
  by_cases h29 : j < 538
  · exact kvkstaticRange_516.get (by omega) (by omega)
  by_cases h30 : j < 560
  · exact kvkstaticRange_538.get (by omega) (by omega)
  by_cases h31 : j < 582
  · exact kvkstaticRange_560.get (by omega) (by omega)
  by_cases h32 : j < 604
  · exact kvkstaticRange_582.get (by omega) (by omega)
  by_cases h33 : j < 626
  · exact kvkstaticRange_604.get (by omega) (by omega)
  by_cases h34 : j < 647
  · exact kvkstaticRange_626.get (by omega) (by omega)
  by_cases h35 : j < 669
  · exact kvkstaticRange_647.get (by omega) (by omega)
  by_cases h36 : j < 690
  · exact kvkstaticRange_669.get (by omega) (by omega)
  by_cases h37 : j < 712
  · exact kvkstaticRange_690.get (by omega) (by omega)
  by_cases h38 : j < 733
  · exact kvkstaticRange_712.get (by omega) (by omega)
  by_cases h39 : j < 755
  · exact kvkstaticRange_733.get (by omega) (by omega)
  by_cases h40 : j < 776
  · exact kvkstaticRange_755.get (by omega) (by omega)
  by_cases h41 : j < 798
  · exact kvkstaticRange_776.get (by omega) (by omega)
  by_cases h42 : j < 819
  · exact kvkstaticRange_798.get (by omega) (by omega)
  by_cases h43 : j < 841
  · exact kvkstaticRange_819.get (by omega) (by omega)
  by_cases h44 : j < 862
  · exact kvkstaticRange_841.get (by omega) (by omega)
  by_cases h45 : j < 884
  · exact kvkstaticRange_862.get (by omega) (by omega)
  by_cases h46 : j < 905
  · exact kvkstaticRange_884.get (by omega) (by omega)
  by_cases h47 : j < 927
  · exact kvkstaticRange_905.get (by omega) (by omega)
  by_cases h48 : j < 951
  · exact kvkstaticRange_927.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvkstaticRange_951.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvkstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1015
  · exact kvkstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1036
  · exact kvkstaticRange_1015.get (by omega) (by omega)
  by_cases h53 : j < 1057
  · exact kvkstaticRange_1036.get (by omega) (by omega)
  by_cases h54 : j < 1078
  · exact kvkstaticRange_1057.get (by omega) (by omega)
  by_cases h55 : j < 1099
  · exact kvkstaticRange_1078.get (by omega) (by omega)
  by_cases h56 : j < 1120
  · exact kvkstaticRange_1099.get (by omega) (by omega)
  by_cases h57 : j < 1141
  · exact kvkstaticRange_1120.get (by omega) (by omega)
  by_cases h58 : j < 1162
  · exact kvkstaticRange_1141.get (by omega) (by omega)
  by_cases h59 : j < 1184
  · exact kvkstaticRange_1162.get (by omega) (by omega)
  by_cases h60 : j < 1203
  · exact kvkstaticRange_1184.get (by omega) (by omega)
  by_cases h61 : j < 1224
  · exact kvkstaticRange_1203.get (by omega) (by omega)
  by_cases h62 : j < 1245
  · exact kvkstaticRange_1224.get (by omega) (by omega)
  by_cases h63 : j < 1266
  · exact kvkstaticRange_1245.get (by omega) (by omega)
  by_cases h64 : j < 1287
  · exact kvkstaticRange_1266.get (by omega) (by omega)
  by_cases h65 : j < 1308
  · exact kvkstaticRange_1287.get (by omega) (by omega)
  by_cases h66 : j < 1329
  · exact kvkstaticRange_1308.get (by omega) (by omega)
  by_cases h67 : j < 1350
  · exact kvkstaticRange_1329.get (by omega) (by omega)
  by_cases h68 : j < 1371
  · exact kvkstaticRange_1350.get (by omega) (by omega)
  by_cases h69 : j < 1392
  · exact kvkstaticRange_1371.get (by omega) (by omega)
  by_cases h70 : j < 1413
  · exact kvkstaticRange_1392.get (by omega) (by omega)
  by_cases h71 : j < 1434
  · exact kvkstaticRange_1413.get (by omega) (by omega)
  by_cases h72 : j < 1448
  · exact kvkstaticRange_1434.get (by omega) (by omega)
  by_cases h73 : j < 1463
  · exact kvkstaticRange_1448.get (by omega) (by omega)
  by_cases h74 : j < 1479
  · exact kvkstaticRange_1463.get (by omega) (by omega)
  by_cases h75 : j < 1491
  · exact kvkstaticRange_1479.get (by omega) (by omega)
  by_cases h76 : j < 1503
  · exact kvkstaticRange_1491.get (by omega) (by omega)
  by_cases h77 : j < 1515
  · exact kvkstaticRange_1503.get (by omega) (by omega)
  by_cases h78 : j < 1525
  · exact kvkstaticRange_1515.get (by omega) (by omega)
  exact kvkstaticRange_1525.get (by omega) (by omega)

end
end LeanVM.Guest
