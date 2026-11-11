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
public import LeanVM.Guest.Memory.GuestCntVS.Part15

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvschkIdx_319 : kvschkIdx 319 = true := by
  have hb : blockB (kvslookJ 319) (kvsomLookJ 319) false [] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨10869, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [← blockR_eq (Data.core319.body.drop 0), kvssplit_319_0]
  exact kvschkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_320 : kvschkIdx 320 = true := by
  have hb : blockB (kvslookJ 320) (kvsomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨11481, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvssplit_320_0]
  exact kvschkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_321 : kvschkIdx 321 = true := by
  have hb : blockB (kvslookJ 321) (kvsomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨12232, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvssplit_321_0]
  exact kvschkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvschkIdx_322 : kvschkIdx 322 = true := by
  have hb : blockB (kvslookJ 322) (kvsomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨12789, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvssplit_322_0]
  exact kvschkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvschkIdx_all : ∀ j < 1752, kvschkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 319
  · subst h1000; exact kvschkIdx_319
  by_cases h1001 : j = 320
  · subst h1001; exact kvschkIdx_320
  by_cases h1002 : j = 321
  · subst h1002; exact kvschkIdx_321
  by_cases h1003 : j = 322
  · subst h1003; exact kvschkIdx_322
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
  by_cases h11 : j < 311
  · exact kvsstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 312
  · exact kvsstaticRange_311.get (by omega) (by omega)
  by_cases h13 : j < 313
  · exact kvsstaticRange_312.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kvsstaticRange_313.get (by omega) (by omega)
  by_cases h15 : j < 315
  · exact kvsstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kvsstaticRange_315.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvsstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvsstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 319
  · exact kvsstaticRange_318.get (by omega) (by omega)
  by_cases h20 : j < 344
  · exact kvsstaticRange_323.get (by omega) (by omega)
  by_cases h21 : j < 366
  · exact kvsstaticRange_344.get (by omega) (by omega)
  by_cases h22 : j < 389
  · exact kvsstaticRange_366.get (by omega) (by omega)
  by_cases h23 : j < 403
  · exact kvsstaticRange_389.get (by omega) (by omega)
  by_cases h24 : j < 433
  · exact kvsstaticRange_403.get (by omega) (by omega)
  by_cases h25 : j < 456
  · exact kvsstaticRange_433.get (by omega) (by omega)
  by_cases h26 : j < 478
  · exact kvsstaticRange_456.get (by omega) (by omega)
  by_cases h27 : j < 500
  · exact kvsstaticRange_478.get (by omega) (by omega)
  by_cases h28 : j < 522
  · exact kvsstaticRange_500.get (by omega) (by omega)
  by_cases h29 : j < 544
  · exact kvsstaticRange_522.get (by omega) (by omega)
  by_cases h30 : j < 566
  · exact kvsstaticRange_544.get (by omega) (by omega)
  by_cases h31 : j < 588
  · exact kvsstaticRange_566.get (by omega) (by omega)
  by_cases h32 : j < 610
  · exact kvsstaticRange_588.get (by omega) (by omega)
  by_cases h33 : j < 632
  · exact kvsstaticRange_610.get (by omega) (by omega)
  by_cases h34 : j < 653
  · exact kvsstaticRange_632.get (by omega) (by omega)
  by_cases h35 : j < 675
  · exact kvsstaticRange_653.get (by omega) (by omega)
  by_cases h36 : j < 696
  · exact kvsstaticRange_675.get (by omega) (by omega)
  by_cases h37 : j < 718
  · exact kvsstaticRange_696.get (by omega) (by omega)
  by_cases h38 : j < 739
  · exact kvsstaticRange_718.get (by omega) (by omega)
  by_cases h39 : j < 761
  · exact kvsstaticRange_739.get (by omega) (by omega)
  by_cases h40 : j < 782
  · exact kvsstaticRange_761.get (by omega) (by omega)
  by_cases h41 : j < 804
  · exact kvsstaticRange_782.get (by omega) (by omega)
  by_cases h42 : j < 825
  · exact kvsstaticRange_804.get (by omega) (by omega)
  by_cases h43 : j < 847
  · exact kvsstaticRange_825.get (by omega) (by omega)
  by_cases h44 : j < 868
  · exact kvsstaticRange_847.get (by omega) (by omega)
  by_cases h45 : j < 890
  · exact kvsstaticRange_868.get (by omega) (by omega)
  by_cases h46 : j < 911
  · exact kvsstaticRange_890.get (by omega) (by omega)
  by_cases h47 : j < 932
  · exact kvsstaticRange_911.get (by omega) (by omega)
  by_cases h48 : j < 953
  · exact kvsstaticRange_932.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvsstaticRange_953.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvsstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1016
  · exact kvsstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1039
  · exact kvsstaticRange_1016.get (by omega) (by omega)
  by_cases h53 : j < 1063
  · exact kvsstaticRange_1039.get (by omega) (by omega)
  by_cases h54 : j < 1086
  · exact kvsstaticRange_1063.get (by omega) (by omega)
  by_cases h55 : j < 1106
  · exact kvsstaticRange_1086.get (by omega) (by omega)
  by_cases h56 : j < 1127
  · exact kvsstaticRange_1106.get (by omega) (by omega)
  by_cases h57 : j < 1148
  · exact kvsstaticRange_1127.get (by omega) (by omega)
  by_cases h58 : j < 1169
  · exact kvsstaticRange_1148.get (by omega) (by omega)
  by_cases h59 : j < 1190
  · exact kvsstaticRange_1169.get (by omega) (by omega)
  by_cases h60 : j < 1211
  · exact kvsstaticRange_1190.get (by omega) (by omega)
  by_cases h61 : j < 1232
  · exact kvsstaticRange_1211.get (by omega) (by omega)
  by_cases h62 : j < 1254
  · exact kvsstaticRange_1232.get (by omega) (by omega)
  by_cases h63 : j < 1275
  · exact kvsstaticRange_1254.get (by omega) (by omega)
  by_cases h64 : j < 1296
  · exact kvsstaticRange_1275.get (by omega) (by omega)
  by_cases h65 : j < 1315
  · exact kvsstaticRange_1296.get (by omega) (by omega)
  by_cases h66 : j < 1336
  · exact kvsstaticRange_1315.get (by omega) (by omega)
  by_cases h67 : j < 1357
  · exact kvsstaticRange_1336.get (by omega) (by omega)
  by_cases h68 : j < 1378
  · exact kvsstaticRange_1357.get (by omega) (by omega)
  by_cases h69 : j < 1399
  · exact kvsstaticRange_1378.get (by omega) (by omega)
  by_cases h70 : j < 1420
  · exact kvsstaticRange_1399.get (by omega) (by omega)
  by_cases h71 : j < 1441
  · exact kvsstaticRange_1420.get (by omega) (by omega)
  by_cases h72 : j < 1461
  · exact kvsstaticRange_1441.get (by omega) (by omega)
  by_cases h73 : j < 1482
  · exact kvsstaticRange_1461.get (by omega) (by omega)
  by_cases h74 : j < 1503
  · exact kvsstaticRange_1482.get (by omega) (by omega)
  by_cases h75 : j < 1524
  · exact kvsstaticRange_1503.get (by omega) (by omega)
  by_cases h76 : j < 1545
  · exact kvsstaticRange_1524.get (by omega) (by omega)
  by_cases h77 : j < 1566
  · exact kvsstaticRange_1545.get (by omega) (by omega)
  by_cases h78 : j < 1587
  · exact kvsstaticRange_1566.get (by omega) (by omega)
  by_cases h79 : j < 1607
  · exact kvsstaticRange_1587.get (by omega) (by omega)
  by_cases h80 : j < 1628
  · exact kvsstaticRange_1607.get (by omega) (by omega)
  by_cases h81 : j < 1645
  · exact kvsstaticRange_1628.get (by omega) (by omega)
  by_cases h82 : j < 1661
  · exact kvsstaticRange_1645.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvsstaticRange_1661.get (by omega) (by omega)
  by_cases h84 : j < 1687
  · exact kvsstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1700
  · exact kvsstaticRange_1687.get (by omega) (by omega)
  by_cases h86 : j < 1712
  · exact kvsstaticRange_1700.get (by omega) (by omega)
  by_cases h87 : j < 1724
  · exact kvsstaticRange_1712.get (by omega) (by omega)
  by_cases h88 : j < 1733
  · exact kvsstaticRange_1724.get (by omega) (by omega)
  by_cases h89 : j < 1744
  · exact kvsstaticRange_1733.get (by omega) (by omega)
  exact kvsstaticRange_1744.get (by omega) (by omega)

end
end LeanVM.Guest
