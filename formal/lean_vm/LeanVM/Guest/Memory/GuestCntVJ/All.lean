/-
  LeanVM.Guest.Memory.GuestCntVJ.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVJ.Part00
public import LeanVM.Guest.Memory.GuestCntVJ.Part01
public import LeanVM.Guest.Memory.GuestCntVJ.Part02
public import LeanVM.Guest.Memory.GuestCntVJ.Part03
public import LeanVM.Guest.Memory.GuestCntVJ.Part04
public import LeanVM.Guest.Memory.GuestCntVJ.Part05
public import LeanVM.Guest.Memory.GuestCntVJ.Part06
public import LeanVM.Guest.Memory.GuestCntVJ.Part07
public import LeanVM.Guest.Memory.GuestCntVJ.Part08
public import LeanVM.Guest.Memory.GuestCntVJ.Part09
public import LeanVM.Guest.Memory.GuestCntVJ.Part10
public import LeanVM.Guest.Memory.GuestCntVJ.Part11
public import LeanVM.Guest.Memory.GuestCntVJ.Part12
public import LeanVM.Guest.Memory.GuestCntVJ.Part13
public import LeanVM.Guest.Memory.GuestCntVJ.Part14

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjchkIdx_315 : kvjchkIdx 315 = true := by
  have hb : blockB (kvjlookJ 315) (kvjomLookJ 315) false [] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨15304, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [← blockR_eq (Data.core315.body.drop 0), kvjsplit_315_0]
  exact kvjchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvjchkIdx_316 : kvjchkIdx 316 = true := by
  have hb : blockB (kvjlookJ 316) (kvjomLookJ 316) false [] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨15490, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [← blockR_eq (Data.core316.body.drop 0), kvjsplit_316_0]
  exact kvjchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvjchkIdx_all : ∀ j < 1535, kvjchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 315
  · subst h1000; exact kvjchkIdx_315
  by_cases h1001 : j = 316
  · subst h1001; exact kvjchkIdx_316
  by_cases h0 : j < 11
  · exact kvjstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvjstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvjstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvjstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvjstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvjstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvjstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvjstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvjstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvjstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvjstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 307
  · exact kvjstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 308
  · exact kvjstaticRange_307.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kvjstaticRange_308.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kvjstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvjstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvjstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 313
  · exact kvjstaticRange_312.get (by omega) (by omega)
  by_cases h18 : j < 314
  · exact kvjstaticRange_313.get (by omega) (by omega)
  by_cases h19 : j < 315
  · exact kvjstaticRange_314.get (by omega) (by omega)
  by_cases h20 : j < 338
  · exact kvjstaticRange_317.get (by omega) (by omega)
  by_cases h21 : j < 360
  · exact kvjstaticRange_338.get (by omega) (by omega)
  by_cases h22 : j < 383
  · exact kvjstaticRange_360.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvjstaticRange_383.get (by omega) (by omega)
  by_cases h24 : j < 427
  · exact kvjstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 450
  · exact kvjstaticRange_427.get (by omega) (by omega)
  by_cases h26 : j < 472
  · exact kvjstaticRange_450.get (by omega) (by omega)
  by_cases h27 : j < 494
  · exact kvjstaticRange_472.get (by omega) (by omega)
  by_cases h28 : j < 516
  · exact kvjstaticRange_494.get (by omega) (by omega)
  by_cases h29 : j < 538
  · exact kvjstaticRange_516.get (by omega) (by omega)
  by_cases h30 : j < 560
  · exact kvjstaticRange_538.get (by omega) (by omega)
  by_cases h31 : j < 582
  · exact kvjstaticRange_560.get (by omega) (by omega)
  by_cases h32 : j < 604
  · exact kvjstaticRange_582.get (by omega) (by omega)
  by_cases h33 : j < 626
  · exact kvjstaticRange_604.get (by omega) (by omega)
  by_cases h34 : j < 647
  · exact kvjstaticRange_626.get (by omega) (by omega)
  by_cases h35 : j < 669
  · exact kvjstaticRange_647.get (by omega) (by omega)
  by_cases h36 : j < 690
  · exact kvjstaticRange_669.get (by omega) (by omega)
  by_cases h37 : j < 712
  · exact kvjstaticRange_690.get (by omega) (by omega)
  by_cases h38 : j < 733
  · exact kvjstaticRange_712.get (by omega) (by omega)
  by_cases h39 : j < 755
  · exact kvjstaticRange_733.get (by omega) (by omega)
  by_cases h40 : j < 776
  · exact kvjstaticRange_755.get (by omega) (by omega)
  by_cases h41 : j < 798
  · exact kvjstaticRange_776.get (by omega) (by omega)
  by_cases h42 : j < 819
  · exact kvjstaticRange_798.get (by omega) (by omega)
  by_cases h43 : j < 841
  · exact kvjstaticRange_819.get (by omega) (by omega)
  by_cases h44 : j < 862
  · exact kvjstaticRange_841.get (by omega) (by omega)
  by_cases h45 : j < 884
  · exact kvjstaticRange_862.get (by omega) (by omega)
  by_cases h46 : j < 905
  · exact kvjstaticRange_884.get (by omega) (by omega)
  by_cases h47 : j < 927
  · exact kvjstaticRange_905.get (by omega) (by omega)
  by_cases h48 : j < 951
  · exact kvjstaticRange_927.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvjstaticRange_951.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvjstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1015
  · exact kvjstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1036
  · exact kvjstaticRange_1015.get (by omega) (by omega)
  by_cases h53 : j < 1057
  · exact kvjstaticRange_1036.get (by omega) (by omega)
  by_cases h54 : j < 1078
  · exact kvjstaticRange_1057.get (by omega) (by omega)
  by_cases h55 : j < 1099
  · exact kvjstaticRange_1078.get (by omega) (by omega)
  by_cases h56 : j < 1120
  · exact kvjstaticRange_1099.get (by omega) (by omega)
  by_cases h57 : j < 1141
  · exact kvjstaticRange_1120.get (by omega) (by omega)
  by_cases h58 : j < 1162
  · exact kvjstaticRange_1141.get (by omega) (by omega)
  by_cases h59 : j < 1184
  · exact kvjstaticRange_1162.get (by omega) (by omega)
  by_cases h60 : j < 1203
  · exact kvjstaticRange_1184.get (by omega) (by omega)
  by_cases h61 : j < 1224
  · exact kvjstaticRange_1203.get (by omega) (by omega)
  by_cases h62 : j < 1245
  · exact kvjstaticRange_1224.get (by omega) (by omega)
  by_cases h63 : j < 1266
  · exact kvjstaticRange_1245.get (by omega) (by omega)
  by_cases h64 : j < 1287
  · exact kvjstaticRange_1266.get (by omega) (by omega)
  by_cases h65 : j < 1308
  · exact kvjstaticRange_1287.get (by omega) (by omega)
  by_cases h66 : j < 1329
  · exact kvjstaticRange_1308.get (by omega) (by omega)
  by_cases h67 : j < 1350
  · exact kvjstaticRange_1329.get (by omega) (by omega)
  by_cases h68 : j < 1371
  · exact kvjstaticRange_1350.get (by omega) (by omega)
  by_cases h69 : j < 1392
  · exact kvjstaticRange_1371.get (by omega) (by omega)
  by_cases h70 : j < 1413
  · exact kvjstaticRange_1392.get (by omega) (by omega)
  by_cases h71 : j < 1434
  · exact kvjstaticRange_1413.get (by omega) (by omega)
  by_cases h72 : j < 1448
  · exact kvjstaticRange_1434.get (by omega) (by omega)
  by_cases h73 : j < 1463
  · exact kvjstaticRange_1448.get (by omega) (by omega)
  by_cases h74 : j < 1479
  · exact kvjstaticRange_1463.get (by omega) (by omega)
  by_cases h75 : j < 1491
  · exact kvjstaticRange_1479.get (by omega) (by omega)
  by_cases h76 : j < 1503
  · exact kvjstaticRange_1491.get (by omega) (by omega)
  by_cases h77 : j < 1515
  · exact kvjstaticRange_1503.get (by omega) (by omega)
  by_cases h78 : j < 1525
  · exact kvjstaticRange_1515.get (by omega) (by omega)
  exact kvjstaticRange_1525.get (by omega) (by omega)

end
end LeanVM.Guest
