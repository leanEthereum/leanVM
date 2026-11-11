/-
  LeanVM.Guest.Memory.GuestCntVD.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVD.Part00
public import LeanVM.Guest.Memory.GuestCntVD.Part01
public import LeanVM.Guest.Memory.GuestCntVD.Part02
public import LeanVM.Guest.Memory.GuestCntVD.Part03
public import LeanVM.Guest.Memory.GuestCntVD.Part04
public import LeanVM.Guest.Memory.GuestCntVD.Part05
public import LeanVM.Guest.Memory.GuestCntVD.Part06
public import LeanVM.Guest.Memory.GuestCntVD.Part07
public import LeanVM.Guest.Memory.GuestCntVD.Part08
public import LeanVM.Guest.Memory.GuestCntVD.Part09
public import LeanVM.Guest.Memory.GuestCntVD.Part10
public import LeanVM.Guest.Memory.GuestCntVD.Part11
public import LeanVM.Guest.Memory.GuestCntVD.Part12
public import LeanVM.Guest.Memory.GuestCntVD.Part13
public import LeanVM.Guest.Memory.GuestCntVD.Part14

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdchkIdx_315 : kvdchkIdx 315 = true := by
  have hb : blockB (kvdlookJ 315) (kvdomLookJ 315) false [] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨23860, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [← blockR_eq (Data.core315.body.drop 0), kvdsplit_315_0]
  exact kvdchkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvdchkIdx_316 : kvdchkIdx 316 = true := by
  have hb : blockB (kvdlookJ 316) (kvdomLookJ 316) false [] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨25077, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [← blockR_eq (Data.core316.body.drop 0), kvdsplit_316_0]
  exact kvdchkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvdchkIdx_all : ∀ j < 1535, kvdchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 315
  · subst h1000; exact kvdchkIdx_315
  by_cases h1001 : j = 316
  · subst h1001; exact kvdchkIdx_316
  by_cases h0 : j < 11
  · exact kvdstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvdstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvdstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvdstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvdstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvdstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvdstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvdstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvdstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvdstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvdstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 307
  · exact kvdstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 308
  · exact kvdstaticRange_307.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kvdstaticRange_308.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kvdstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvdstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvdstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 313
  · exact kvdstaticRange_312.get (by omega) (by omega)
  by_cases h18 : j < 314
  · exact kvdstaticRange_313.get (by omega) (by omega)
  by_cases h19 : j < 315
  · exact kvdstaticRange_314.get (by omega) (by omega)
  by_cases h20 : j < 338
  · exact kvdstaticRange_317.get (by omega) (by omega)
  by_cases h21 : j < 360
  · exact kvdstaticRange_338.get (by omega) (by omega)
  by_cases h22 : j < 383
  · exact kvdstaticRange_360.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvdstaticRange_383.get (by omega) (by omega)
  by_cases h24 : j < 427
  · exact kvdstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 450
  · exact kvdstaticRange_427.get (by omega) (by omega)
  by_cases h26 : j < 472
  · exact kvdstaticRange_450.get (by omega) (by omega)
  by_cases h27 : j < 494
  · exact kvdstaticRange_472.get (by omega) (by omega)
  by_cases h28 : j < 516
  · exact kvdstaticRange_494.get (by omega) (by omega)
  by_cases h29 : j < 538
  · exact kvdstaticRange_516.get (by omega) (by omega)
  by_cases h30 : j < 560
  · exact kvdstaticRange_538.get (by omega) (by omega)
  by_cases h31 : j < 582
  · exact kvdstaticRange_560.get (by omega) (by omega)
  by_cases h32 : j < 604
  · exact kvdstaticRange_582.get (by omega) (by omega)
  by_cases h33 : j < 626
  · exact kvdstaticRange_604.get (by omega) (by omega)
  by_cases h34 : j < 647
  · exact kvdstaticRange_626.get (by omega) (by omega)
  by_cases h35 : j < 669
  · exact kvdstaticRange_647.get (by omega) (by omega)
  by_cases h36 : j < 690
  · exact kvdstaticRange_669.get (by omega) (by omega)
  by_cases h37 : j < 712
  · exact kvdstaticRange_690.get (by omega) (by omega)
  by_cases h38 : j < 733
  · exact kvdstaticRange_712.get (by omega) (by omega)
  by_cases h39 : j < 755
  · exact kvdstaticRange_733.get (by omega) (by omega)
  by_cases h40 : j < 776
  · exact kvdstaticRange_755.get (by omega) (by omega)
  by_cases h41 : j < 798
  · exact kvdstaticRange_776.get (by omega) (by omega)
  by_cases h42 : j < 819
  · exact kvdstaticRange_798.get (by omega) (by omega)
  by_cases h43 : j < 841
  · exact kvdstaticRange_819.get (by omega) (by omega)
  by_cases h44 : j < 862
  · exact kvdstaticRange_841.get (by omega) (by omega)
  by_cases h45 : j < 884
  · exact kvdstaticRange_862.get (by omega) (by omega)
  by_cases h46 : j < 905
  · exact kvdstaticRange_884.get (by omega) (by omega)
  by_cases h47 : j < 927
  · exact kvdstaticRange_905.get (by omega) (by omega)
  by_cases h48 : j < 951
  · exact kvdstaticRange_927.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvdstaticRange_951.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvdstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1015
  · exact kvdstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1036
  · exact kvdstaticRange_1015.get (by omega) (by omega)
  by_cases h53 : j < 1057
  · exact kvdstaticRange_1036.get (by omega) (by omega)
  by_cases h54 : j < 1078
  · exact kvdstaticRange_1057.get (by omega) (by omega)
  by_cases h55 : j < 1099
  · exact kvdstaticRange_1078.get (by omega) (by omega)
  by_cases h56 : j < 1120
  · exact kvdstaticRange_1099.get (by omega) (by omega)
  by_cases h57 : j < 1141
  · exact kvdstaticRange_1120.get (by omega) (by omega)
  by_cases h58 : j < 1162
  · exact kvdstaticRange_1141.get (by omega) (by omega)
  by_cases h59 : j < 1184
  · exact kvdstaticRange_1162.get (by omega) (by omega)
  by_cases h60 : j < 1203
  · exact kvdstaticRange_1184.get (by omega) (by omega)
  by_cases h61 : j < 1224
  · exact kvdstaticRange_1203.get (by omega) (by omega)
  by_cases h62 : j < 1245
  · exact kvdstaticRange_1224.get (by omega) (by omega)
  by_cases h63 : j < 1266
  · exact kvdstaticRange_1245.get (by omega) (by omega)
  by_cases h64 : j < 1287
  · exact kvdstaticRange_1266.get (by omega) (by omega)
  by_cases h65 : j < 1308
  · exact kvdstaticRange_1287.get (by omega) (by omega)
  by_cases h66 : j < 1329
  · exact kvdstaticRange_1308.get (by omega) (by omega)
  by_cases h67 : j < 1350
  · exact kvdstaticRange_1329.get (by omega) (by omega)
  by_cases h68 : j < 1371
  · exact kvdstaticRange_1350.get (by omega) (by omega)
  by_cases h69 : j < 1392
  · exact kvdstaticRange_1371.get (by omega) (by omega)
  by_cases h70 : j < 1413
  · exact kvdstaticRange_1392.get (by omega) (by omega)
  by_cases h71 : j < 1434
  · exact kvdstaticRange_1413.get (by omega) (by omega)
  by_cases h72 : j < 1448
  · exact kvdstaticRange_1434.get (by omega) (by omega)
  by_cases h73 : j < 1463
  · exact kvdstaticRange_1448.get (by omega) (by omega)
  by_cases h74 : j < 1479
  · exact kvdstaticRange_1463.get (by omega) (by omega)
  by_cases h75 : j < 1491
  · exact kvdstaticRange_1479.get (by omega) (by omega)
  by_cases h76 : j < 1503
  · exact kvdstaticRange_1491.get (by omega) (by omega)
  by_cases h77 : j < 1515
  · exact kvdstaticRange_1503.get (by omega) (by omega)
  by_cases h78 : j < 1525
  · exact kvdstaticRange_1515.get (by omega) (by omega)
  exact kvdstaticRange_1525.get (by omega) (by omega)

end
end LeanVM.Guest
