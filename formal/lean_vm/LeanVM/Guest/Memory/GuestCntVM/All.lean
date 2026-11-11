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
public import LeanVM.Guest.Memory.GuestCntVM.Part15

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmchkIdx_319 : kvmchkIdx 319 = true := by
  have hb : blockB (kvmlookJ 319) (kvmomLookJ 319) false [] Data.core319.params Data.core319.name ([], []) Data.core319.body = some (⟨64765, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core319.body)]
    rw [← blockR_eq (Data.core319.body.drop 0), kvmsplit_319_0]
  exact kvmchkIdx_of_split (fn := Data.core319) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_320 : kvmchkIdx 320 = true := by
  have hb : blockB (kvmlookJ 320) (kvmomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨66289, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvmsplit_320_0]
  exact kvmchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_321 : kvmchkIdx 321 = true := by
  have hb : blockB (kvmlookJ 321) (kvmomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨67125, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvmsplit_321_0]
  exact kvmchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_322 : kvmchkIdx 322 = true := by
  have hb : blockB (kvmlookJ 322) (kvmomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨71631, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvmsplit_322_0]
  exact kvmchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvmchkIdx_all : ∀ j < 1752, kvmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 319
  · subst h1000; exact kvmchkIdx_319
  by_cases h1001 : j = 320
  · subst h1001; exact kvmchkIdx_320
  by_cases h1002 : j = 321
  · subst h1002; exact kvmchkIdx_321
  by_cases h1003 : j = 322
  · subst h1003; exact kvmchkIdx_322
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
  by_cases h11 : j < 311
  · exact kvmstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 312
  · exact kvmstaticRange_311.get (by omega) (by omega)
  by_cases h13 : j < 313
  · exact kvmstaticRange_312.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kvmstaticRange_313.get (by omega) (by omega)
  by_cases h15 : j < 315
  · exact kvmstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kvmstaticRange_315.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvmstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvmstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 319
  · exact kvmstaticRange_318.get (by omega) (by omega)
  by_cases h20 : j < 344
  · exact kvmstaticRange_323.get (by omega) (by omega)
  by_cases h21 : j < 366
  · exact kvmstaticRange_344.get (by omega) (by omega)
  by_cases h22 : j < 389
  · exact kvmstaticRange_366.get (by omega) (by omega)
  by_cases h23 : j < 403
  · exact kvmstaticRange_389.get (by omega) (by omega)
  by_cases h24 : j < 433
  · exact kvmstaticRange_403.get (by omega) (by omega)
  by_cases h25 : j < 456
  · exact kvmstaticRange_433.get (by omega) (by omega)
  by_cases h26 : j < 478
  · exact kvmstaticRange_456.get (by omega) (by omega)
  by_cases h27 : j < 500
  · exact kvmstaticRange_478.get (by omega) (by omega)
  by_cases h28 : j < 522
  · exact kvmstaticRange_500.get (by omega) (by omega)
  by_cases h29 : j < 544
  · exact kvmstaticRange_522.get (by omega) (by omega)
  by_cases h30 : j < 566
  · exact kvmstaticRange_544.get (by omega) (by omega)
  by_cases h31 : j < 588
  · exact kvmstaticRange_566.get (by omega) (by omega)
  by_cases h32 : j < 610
  · exact kvmstaticRange_588.get (by omega) (by omega)
  by_cases h33 : j < 632
  · exact kvmstaticRange_610.get (by omega) (by omega)
  by_cases h34 : j < 653
  · exact kvmstaticRange_632.get (by omega) (by omega)
  by_cases h35 : j < 675
  · exact kvmstaticRange_653.get (by omega) (by omega)
  by_cases h36 : j < 696
  · exact kvmstaticRange_675.get (by omega) (by omega)
  by_cases h37 : j < 718
  · exact kvmstaticRange_696.get (by omega) (by omega)
  by_cases h38 : j < 739
  · exact kvmstaticRange_718.get (by omega) (by omega)
  by_cases h39 : j < 761
  · exact kvmstaticRange_739.get (by omega) (by omega)
  by_cases h40 : j < 782
  · exact kvmstaticRange_761.get (by omega) (by omega)
  by_cases h41 : j < 804
  · exact kvmstaticRange_782.get (by omega) (by omega)
  by_cases h42 : j < 825
  · exact kvmstaticRange_804.get (by omega) (by omega)
  by_cases h43 : j < 847
  · exact kvmstaticRange_825.get (by omega) (by omega)
  by_cases h44 : j < 868
  · exact kvmstaticRange_847.get (by omega) (by omega)
  by_cases h45 : j < 890
  · exact kvmstaticRange_868.get (by omega) (by omega)
  by_cases h46 : j < 911
  · exact kvmstaticRange_890.get (by omega) (by omega)
  by_cases h47 : j < 932
  · exact kvmstaticRange_911.get (by omega) (by omega)
  by_cases h48 : j < 953
  · exact kvmstaticRange_932.get (by omega) (by omega)
  by_cases h49 : j < 974
  · exact kvmstaticRange_953.get (by omega) (by omega)
  by_cases h50 : j < 995
  · exact kvmstaticRange_974.get (by omega) (by omega)
  by_cases h51 : j < 1016
  · exact kvmstaticRange_995.get (by omega) (by omega)
  by_cases h52 : j < 1039
  · exact kvmstaticRange_1016.get (by omega) (by omega)
  by_cases h53 : j < 1063
  · exact kvmstaticRange_1039.get (by omega) (by omega)
  by_cases h54 : j < 1086
  · exact kvmstaticRange_1063.get (by omega) (by omega)
  by_cases h55 : j < 1106
  · exact kvmstaticRange_1086.get (by omega) (by omega)
  by_cases h56 : j < 1127
  · exact kvmstaticRange_1106.get (by omega) (by omega)
  by_cases h57 : j < 1148
  · exact kvmstaticRange_1127.get (by omega) (by omega)
  by_cases h58 : j < 1169
  · exact kvmstaticRange_1148.get (by omega) (by omega)
  by_cases h59 : j < 1190
  · exact kvmstaticRange_1169.get (by omega) (by omega)
  by_cases h60 : j < 1211
  · exact kvmstaticRange_1190.get (by omega) (by omega)
  by_cases h61 : j < 1232
  · exact kvmstaticRange_1211.get (by omega) (by omega)
  by_cases h62 : j < 1254
  · exact kvmstaticRange_1232.get (by omega) (by omega)
  by_cases h63 : j < 1275
  · exact kvmstaticRange_1254.get (by omega) (by omega)
  by_cases h64 : j < 1296
  · exact kvmstaticRange_1275.get (by omega) (by omega)
  by_cases h65 : j < 1315
  · exact kvmstaticRange_1296.get (by omega) (by omega)
  by_cases h66 : j < 1336
  · exact kvmstaticRange_1315.get (by omega) (by omega)
  by_cases h67 : j < 1357
  · exact kvmstaticRange_1336.get (by omega) (by omega)
  by_cases h68 : j < 1378
  · exact kvmstaticRange_1357.get (by omega) (by omega)
  by_cases h69 : j < 1399
  · exact kvmstaticRange_1378.get (by omega) (by omega)
  by_cases h70 : j < 1420
  · exact kvmstaticRange_1399.get (by omega) (by omega)
  by_cases h71 : j < 1441
  · exact kvmstaticRange_1420.get (by omega) (by omega)
  by_cases h72 : j < 1461
  · exact kvmstaticRange_1441.get (by omega) (by omega)
  by_cases h73 : j < 1482
  · exact kvmstaticRange_1461.get (by omega) (by omega)
  by_cases h74 : j < 1503
  · exact kvmstaticRange_1482.get (by omega) (by omega)
  by_cases h75 : j < 1524
  · exact kvmstaticRange_1503.get (by omega) (by omega)
  by_cases h76 : j < 1545
  · exact kvmstaticRange_1524.get (by omega) (by omega)
  by_cases h77 : j < 1566
  · exact kvmstaticRange_1545.get (by omega) (by omega)
  by_cases h78 : j < 1587
  · exact kvmstaticRange_1566.get (by omega) (by omega)
  by_cases h79 : j < 1607
  · exact kvmstaticRange_1587.get (by omega) (by omega)
  by_cases h80 : j < 1628
  · exact kvmstaticRange_1607.get (by omega) (by omega)
  by_cases h81 : j < 1645
  · exact kvmstaticRange_1628.get (by omega) (by omega)
  by_cases h82 : j < 1661
  · exact kvmstaticRange_1645.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvmstaticRange_1661.get (by omega) (by omega)
  by_cases h84 : j < 1687
  · exact kvmstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1700
  · exact kvmstaticRange_1687.get (by omega) (by omega)
  by_cases h86 : j < 1712
  · exact kvmstaticRange_1700.get (by omega) (by omega)
  by_cases h87 : j < 1724
  · exact kvmstaticRange_1712.get (by omega) (by omega)
  by_cases h88 : j < 1733
  · exact kvmstaticRange_1724.get (by omega) (by omega)
  by_cases h89 : j < 1744
  · exact kvmstaticRange_1733.get (by omega) (by omega)
  exact kvmstaticRange_1744.get (by omega) (by omega)

end
end LeanVM.Guest
