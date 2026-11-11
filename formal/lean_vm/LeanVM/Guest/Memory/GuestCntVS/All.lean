/-
  LeanVM.Guest.Memory.GuestCntVS.All

  Every function of the guest's core IR passes the static check.
-/

module

public import LeanVM.Guest.Memory.GuestCntVS.Part00
public import LeanVM.Guest.Memory.GuestCntVS.Part01
public import LeanVM.Guest.Memory.GuestCntVS.Part02
public import LeanVM.Guest.Memory.GuestCntVS.Part03
public import LeanVM.Guest.Memory.GuestCntVS.Part04
public import LeanVM.Guest.Memory.GuestCntVS.Part05
public import LeanVM.Guest.Memory.GuestCntVS.Part06
public import LeanVM.Guest.Memory.GuestCntVS.Part07
public import LeanVM.Guest.Memory.GuestCntVS.Part08
public import LeanVM.Guest.Memory.GuestCntVS.Part09
public import LeanVM.Guest.Memory.GuestCntVS.Part10
public import LeanVM.Guest.Memory.GuestCntVS.Part11
public import LeanVM.Guest.Memory.GuestCntVS.Part12
public import LeanVM.Guest.Memory.GuestCntVS.Part13
public import LeanVM.Guest.Memory.GuestCntVS.Part14

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvschkIdx_315 : kvschkIdx 315 = true := by
  have hb : blockB (kvslookJ 315) (kvsomLookJ 315) false [] Data.core315.params Data.core315.name ([], []) Data.core315.body = some (⟨10869, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core315.body)]
    rw [← blockR_eq (Data.core315.body.drop 0), kvssplit_315_0]
  exact kvschkIdx_of_split (fn := Data.core315) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_316 : kvschkIdx 316 = true := by
  have hb : blockB (kvslookJ 316) (kvsomLookJ 316) false [] Data.core316.params Data.core316.name ([], []) Data.core316.body = some (⟨11481, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core316.body)]
    rw [← blockR_eq (Data.core316.body.drop 0), kvssplit_316_0]
  exact kvschkIdx_of_split (fn := Data.core316) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvschkIdx_all : ∀ j < 1535, kvschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 315
  · subst h1000; exact kvschkIdx_315
  by_cases h1001 : j = 316
  · subst h1001; exact kvschkIdx_316
  by_cases h0 : j < 11
  · exact kvsstaticRange_0.get (by omega) (by omega)
  by_cases h1 : j < 18
  · exact kvsstaticRange_11.get (by omega) (by omega)
  by_cases h2 : j < 48
  · exact kvsstaticRange_18.get (by omega) (by omega)
  by_cases h3 : j < 78
  · exact kvsstaticRange_48.get (by omega) (by omega)
  by_cases h4 : j < 108
  · exact kvsstaticRange_78.get (by omega) (by omega)
  by_cases h5 : j < 138
  · exact kvsstaticRange_108.get (by omega) (by omega)
  by_cases h6 : j < 168
  · exact kvsstaticRange_138.get (by omega) (by omega)
  by_cases h7 : j < 198
  · exact kvsstaticRange_168.get (by omega) (by omega)
  by_cases h8 : j < 228
  · exact kvsstaticRange_198.get (by omega) (by omega)
  by_cases h9 : j < 258
  · exact kvsstaticRange_228.get (by omega) (by omega)
  by_cases h10 : j < 288
  · exact kvsstaticRange_258.get (by omega) (by omega)
  by_cases h11 : j < 307
  · exact kvsstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 308
  · exact kvsstaticRange_307.get (by omega) (by omega)
  by_cases h13 : j < 309
  · exact kvsstaticRange_308.get (by omega) (by omega)
  by_cases h14 : j < 310
  · exact kvsstaticRange_309.get (by omega) (by omega)
  by_cases h15 : j < 311
  · exact kvsstaticRange_310.get (by omega) (by omega)
  by_cases h16 : j < 312
  · exact kvsstaticRange_311.get (by omega) (by omega)
  by_cases h17 : j < 313
  · exact kvsstaticRange_312.get (by omega) (by omega)
  by_cases h18 : j < 314
  · exact kvsstaticRange_313.get (by omega) (by omega)
  by_cases h19 : j < 315
  · exact kvsstaticRange_314.get (by omega) (by omega)
  by_cases h20 : j < 338
  · exact kvsstaticRange_317.get (by omega) (by omega)
  by_cases h21 : j < 360
  · exact kvsstaticRange_338.get (by omega) (by omega)
  by_cases h22 : j < 383
  · exact kvsstaticRange_360.get (by omega) (by omega)
  by_cases h23 : j < 397
  · exact kvsstaticRange_383.get (by omega) (by omega)
  by_cases h24 : j < 427
  · exact kvsstaticRange_397.get (by omega) (by omega)
  by_cases h25 : j < 450
  · exact kvsstaticRange_427.get (by omega) (by omega)
  by_cases h26 : j < 472
  · exact kvsstaticRange_450.get (by omega) (by omega)
  by_cases h27 : j < 494
  · exact kvsstaticRange_472.get (by omega) (by omega)
  by_cases h28 : j < 516
  · exact kvsstaticRange_494.get (by omega) (by omega)
  by_cases h29 : j < 538
  · exact kvsstaticRange_516.get (by omega) (by omega)
  by_cases h30 : j < 560
  · exact kvsstaticRange_538.get (by omega) (by omega)
  by_cases h31 : j < 582
  · exact kvsstaticRange_560.get (by omega) (by omega)
  by_cases h32 : j < 604
  · exact kvsstaticRange_582.get (by omega) (by omega)
  by_cases h33 : j < 626
  · exact kvsstaticRange_604.get (by omega) (by omega)
  by_cases h34 : j < 647
  · exact kvsstaticRange_626.get (by omega) (by omega)
  by_cases h35 : j < 669
  · exact kvsstaticRange_647.get (by omega) (by omega)
  by_cases h36 : j < 690
  · exact kvsstaticRange_669.get (by omega) (by omega)
  by_cases h37 : j < 712
  · exact kvsstaticRange_690.get (by omega) (by omega)
  by_cases h38 : j < 733
  · exact kvsstaticRange_712.get (by omega) (by omega)
  by_cases h39 : j < 755
  · exact kvsstaticRange_733.get (by omega) (by omega)
  by_cases h40 : j < 776
  · exact kvsstaticRange_755.get (by omega) (by omega)
  by_cases h41 : j < 798
  · exact kvsstaticRange_776.get (by omega) (by omega)
  by_cases h42 : j < 819
  · exact kvsstaticRange_798.get (by omega) (by omega)
  by_cases h43 : j < 841
  · exact kvsstaticRange_819.get (by omega) (by omega)
  by_cases h44 : j < 862
  · exact kvsstaticRange_841.get (by omega) (by omega)
  by_cases h45 : j < 884
  · exact kvsstaticRange_862.get (by omega) (by omega)
  by_cases h46 : j < 905
  · exact kvsstaticRange_884.get (by omega) (by omega)
  by_cases h47 : j < 927
  · exact kvsstaticRange_905.get (by omega) (by omega)
  by_cases h48 : j < 951
  · exact kvsstaticRange_927.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvsstaticRange_951.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvsstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1015
  · exact kvsstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1036
  · exact kvsstaticRange_1015.get (by omega) (by omega)
  by_cases h53 : j < 1057
  · exact kvsstaticRange_1036.get (by omega) (by omega)
  by_cases h54 : j < 1078
  · exact kvsstaticRange_1057.get (by omega) (by omega)
  by_cases h55 : j < 1099
  · exact kvsstaticRange_1078.get (by omega) (by omega)
  by_cases h56 : j < 1120
  · exact kvsstaticRange_1099.get (by omega) (by omega)
  by_cases h57 : j < 1141
  · exact kvsstaticRange_1120.get (by omega) (by omega)
  by_cases h58 : j < 1162
  · exact kvsstaticRange_1141.get (by omega) (by omega)
  by_cases h59 : j < 1184
  · exact kvsstaticRange_1162.get (by omega) (by omega)
  by_cases h60 : j < 1203
  · exact kvsstaticRange_1184.get (by omega) (by omega)
  by_cases h61 : j < 1224
  · exact kvsstaticRange_1203.get (by omega) (by omega)
  by_cases h62 : j < 1245
  · exact kvsstaticRange_1224.get (by omega) (by omega)
  by_cases h63 : j < 1266
  · exact kvsstaticRange_1245.get (by omega) (by omega)
  by_cases h64 : j < 1287
  · exact kvsstaticRange_1266.get (by omega) (by omega)
  by_cases h65 : j < 1308
  · exact kvsstaticRange_1287.get (by omega) (by omega)
  by_cases h66 : j < 1329
  · exact kvsstaticRange_1308.get (by omega) (by omega)
  by_cases h67 : j < 1350
  · exact kvsstaticRange_1329.get (by omega) (by omega)
  by_cases h68 : j < 1371
  · exact kvsstaticRange_1350.get (by omega) (by omega)
  by_cases h69 : j < 1392
  · exact kvsstaticRange_1371.get (by omega) (by omega)
  by_cases h70 : j < 1413
  · exact kvsstaticRange_1392.get (by omega) (by omega)
  by_cases h71 : j < 1434
  · exact kvsstaticRange_1413.get (by omega) (by omega)
  by_cases h72 : j < 1448
  · exact kvsstaticRange_1434.get (by omega) (by omega)
  by_cases h73 : j < 1463
  · exact kvsstaticRange_1448.get (by omega) (by omega)
  by_cases h74 : j < 1479
  · exact kvsstaticRange_1463.get (by omega) (by omega)
  by_cases h75 : j < 1491
  · exact kvsstaticRange_1479.get (by omega) (by omega)
  by_cases h76 : j < 1503
  · exact kvsstaticRange_1491.get (by omega) (by omega)
  by_cases h77 : j < 1515
  · exact kvsstaticRange_1503.get (by omega) (by omega)
  by_cases h78 : j < 1525
  · exact kvsstaticRange_1515.get (by omega) (by omega)
  exact kvsstaticRange_1525.get (by omega) (by omega)

end
end LeanVM.Guest
