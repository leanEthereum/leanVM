/-
  LeanVM.Guest.Memory.GuestCntVX.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVX.Part00
public import LeanVM.Guest.Memory.GuestCntVX.Part01
public import LeanVM.Guest.Memory.GuestCntVX.Part02
public import LeanVM.Guest.Memory.GuestCntVX.Part03
public import LeanVM.Guest.Memory.GuestCntVX.Part04
public import LeanVM.Guest.Memory.GuestCntVX.Part05
public import LeanVM.Guest.Memory.GuestCntVX.Part06
public import LeanVM.Guest.Memory.GuestCntVX.Part07
public import LeanVM.Guest.Memory.GuestCntVX.Part08
public import LeanVM.Guest.Memory.GuestCntVX.Part09
public import LeanVM.Guest.Memory.GuestCntVX.Part10
public import LeanVM.Guest.Memory.GuestCntVX.Part11
public import LeanVM.Guest.Memory.GuestCntVX.Part12
public import LeanVM.Guest.Memory.GuestCntVX.Part13
public import LeanVM.Guest.Memory.GuestCntVX.Part14

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxchkIdx_315 : kvxchkIdx 315 = true := by
  have hb : blockB (kvxlookJ 315) (kvxomLookJ 315) false [] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨55819, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [← blockR_eq (Data.core315.body.drop 0), kvxsplit_315_0]
  exact kvxchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvxchkIdx_316 : kvxchkIdx 316 = true := by
  have hb : blockB (kvxlookJ 316) (kvxomLookJ 316) false [] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨56909, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [← blockR_eq (Data.core316.body.drop 0), kvxsplit_316_0]
  exact kvxchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvxchkIdx_all : ∀ j < 1535, kvxchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 315
  · subst h1000; exact kvxchkIdx_315
  by_cases h1001 : j = 316
  · subst h1001; exact kvxchkIdx_316
  by_cases h0 : j < 11
  · exact kvxstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvxstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvxstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvxstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvxstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvxstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvxstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvxstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvxstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvxstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvxstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 307
  · exact kvxstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 308
  · exact kvxstaticRange_307.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kvxstaticRange_308.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kvxstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvxstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvxstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 313
  · exact kvxstaticRange_312.get (by omega) (by omega)
  by_cases h18 : j < 314
  · exact kvxstaticRange_313.get (by omega) (by omega)
  by_cases h19 : j < 315
  · exact kvxstaticRange_314.get (by omega) (by omega)
  by_cases h20 : j < 338
  · exact kvxstaticRange_317.get (by omega) (by omega)
  by_cases h21 : j < 360
  · exact kvxstaticRange_338.get (by omega) (by omega)
  by_cases h22 : j < 383
  · exact kvxstaticRange_360.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvxstaticRange_383.get (by omega) (by omega)
  by_cases h24 : j < 427
  · exact kvxstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 450
  · exact kvxstaticRange_427.get (by omega) (by omega)
  by_cases h26 : j < 472
  · exact kvxstaticRange_450.get (by omega) (by omega)
  by_cases h27 : j < 494
  · exact kvxstaticRange_472.get (by omega) (by omega)
  by_cases h28 : j < 516
  · exact kvxstaticRange_494.get (by omega) (by omega)
  by_cases h29 : j < 538
  · exact kvxstaticRange_516.get (by omega) (by omega)
  by_cases h30 : j < 560
  · exact kvxstaticRange_538.get (by omega) (by omega)
  by_cases h31 : j < 582
  · exact kvxstaticRange_560.get (by omega) (by omega)
  by_cases h32 : j < 604
  · exact kvxstaticRange_582.get (by omega) (by omega)
  by_cases h33 : j < 626
  · exact kvxstaticRange_604.get (by omega) (by omega)
  by_cases h34 : j < 647
  · exact kvxstaticRange_626.get (by omega) (by omega)
  by_cases h35 : j < 669
  · exact kvxstaticRange_647.get (by omega) (by omega)
  by_cases h36 : j < 690
  · exact kvxstaticRange_669.get (by omega) (by omega)
  by_cases h37 : j < 712
  · exact kvxstaticRange_690.get (by omega) (by omega)
  by_cases h38 : j < 733
  · exact kvxstaticRange_712.get (by omega) (by omega)
  by_cases h39 : j < 755
  · exact kvxstaticRange_733.get (by omega) (by omega)
  by_cases h40 : j < 776
  · exact kvxstaticRange_755.get (by omega) (by omega)
  by_cases h41 : j < 798
  · exact kvxstaticRange_776.get (by omega) (by omega)
  by_cases h42 : j < 819
  · exact kvxstaticRange_798.get (by omega) (by omega)
  by_cases h43 : j < 841
  · exact kvxstaticRange_819.get (by omega) (by omega)
  by_cases h44 : j < 862
  · exact kvxstaticRange_841.get (by omega) (by omega)
  by_cases h45 : j < 884
  · exact kvxstaticRange_862.get (by omega) (by omega)
  by_cases h46 : j < 905
  · exact kvxstaticRange_884.get (by omega) (by omega)
  by_cases h47 : j < 927
  · exact kvxstaticRange_905.get (by omega) (by omega)
  by_cases h48 : j < 951
  · exact kvxstaticRange_927.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvxstaticRange_951.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvxstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1015
  · exact kvxstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1036
  · exact kvxstaticRange_1015.get (by omega) (by omega)
  by_cases h53 : j < 1057
  · exact kvxstaticRange_1036.get (by omega) (by omega)
  by_cases h54 : j < 1078
  · exact kvxstaticRange_1057.get (by omega) (by omega)
  by_cases h55 : j < 1099
  · exact kvxstaticRange_1078.get (by omega) (by omega)
  by_cases h56 : j < 1120
  · exact kvxstaticRange_1099.get (by omega) (by omega)
  by_cases h57 : j < 1141
  · exact kvxstaticRange_1120.get (by omega) (by omega)
  by_cases h58 : j < 1162
  · exact kvxstaticRange_1141.get (by omega) (by omega)
  by_cases h59 : j < 1184
  · exact kvxstaticRange_1162.get (by omega) (by omega)
  by_cases h60 : j < 1203
  · exact kvxstaticRange_1184.get (by omega) (by omega)
  by_cases h61 : j < 1224
  · exact kvxstaticRange_1203.get (by omega) (by omega)
  by_cases h62 : j < 1245
  · exact kvxstaticRange_1224.get (by omega) (by omega)
  by_cases h63 : j < 1266
  · exact kvxstaticRange_1245.get (by omega) (by omega)
  by_cases h64 : j < 1287
  · exact kvxstaticRange_1266.get (by omega) (by omega)
  by_cases h65 : j < 1308
  · exact kvxstaticRange_1287.get (by omega) (by omega)
  by_cases h66 : j < 1329
  · exact kvxstaticRange_1308.get (by omega) (by omega)
  by_cases h67 : j < 1350
  · exact kvxstaticRange_1329.get (by omega) (by omega)
  by_cases h68 : j < 1371
  · exact kvxstaticRange_1350.get (by omega) (by omega)
  by_cases h69 : j < 1392
  · exact kvxstaticRange_1371.get (by omega) (by omega)
  by_cases h70 : j < 1413
  · exact kvxstaticRange_1392.get (by omega) (by omega)
  by_cases h71 : j < 1434
  · exact kvxstaticRange_1413.get (by omega) (by omega)
  by_cases h72 : j < 1448
  · exact kvxstaticRange_1434.get (by omega) (by omega)
  by_cases h73 : j < 1463
  · exact kvxstaticRange_1448.get (by omega) (by omega)
  by_cases h74 : j < 1479
  · exact kvxstaticRange_1463.get (by omega) (by omega)
  by_cases h75 : j < 1491
  · exact kvxstaticRange_1479.get (by omega) (by omega)
  by_cases h76 : j < 1503
  · exact kvxstaticRange_1491.get (by omega) (by omega)
  by_cases h77 : j < 1515
  · exact kvxstaticRange_1503.get (by omega) (by omega)
  by_cases h78 : j < 1525
  · exact kvxstaticRange_1515.get (by omega) (by omega)
  exact kvxstaticRange_1525.get (by omega) (by omega)

end
end LeanVM.Guest
