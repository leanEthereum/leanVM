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
public import LeanVM.Guest.Memory.GuestCntVK.Part15
public import LeanVM.Guest.Memory.GuestCntVK.Part16

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkchkIdx_320 : kvkchkIdx 320 = true := by
  have hb : blockB (kvklookJ 320) (kvkomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨8268, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvksplit_320_0]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_321 : kvkchkIdx 321 = true := by
  have hb : blockB (kvklookJ 321) (kvkomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨8398, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvksplit_321_0]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_322 : kvkchkIdx 322 = true := by
  have hb : blockB (kvklookJ 322) (kvkomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨8746, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvksplit_322_0]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvkchkIdx_323 : kvkchkIdx 323 = true := by
  have hb : blockB (kvklookJ 323) (kvkomLookJ 323) false [] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨10591, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [← blockR_eq (Data.core323.body.drop 0), kvksplit_323_0]
    rfl
  exact kvkchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvkchkIdx_all : ∀ j < 1803, kvkchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 320
  · subst h1000; exact kvkchkIdx_320
  by_cases h1001 : j = 321
  · subst h1001; exact kvkchkIdx_321
  by_cases h1002 : j = 322
  · subst h1002; exact kvkchkIdx_322
  by_cases h1003 : j = 323
  · subst h1003; exact kvkchkIdx_323
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
  by_cases h11 : j < 311
  · exact kvkstaticRange_288.get (by omega) (by omega)
  by_cases h12 : j < 312
  · exact kvkstaticRange_311.get (by omega) (by omega)
  by_cases h13 : j < 313
  · exact kvkstaticRange_312.get (by omega) (by omega)
  by_cases h14 : j < 314
  · exact kvkstaticRange_313.get (by omega) (by omega)
  by_cases h15 : j < 315
  · exact kvkstaticRange_314.get (by omega) (by omega)
  by_cases h16 : j < 316
  · exact kvkstaticRange_315.get (by omega) (by omega)
  by_cases h17 : j < 317
  · exact kvkstaticRange_316.get (by omega) (by omega)
  by_cases h18 : j < 318
  · exact kvkstaticRange_317.get (by omega) (by omega)
  by_cases h19 : j < 319
  · exact kvkstaticRange_318.get (by omega) (by omega)
  by_cases h20 : j < 320
  · exact kvkstaticRange_319.get (by omega) (by omega)
  by_cases h21 : j < 345
  · exact kvkstaticRange_324.get (by omega) (by omega)
  by_cases h22 : j < 367
  · exact kvkstaticRange_345.get (by omega) (by omega)
  by_cases h23 : j < 390
  · exact kvkstaticRange_367.get (by omega) (by omega)
  by_cases h24 : j < 404
  · exact kvkstaticRange_390.get (by omega) (by omega)
  by_cases h25 : j < 434
  · exact kvkstaticRange_404.get (by omega) (by omega)
  by_cases h26 : j < 456
  · exact kvkstaticRange_434.get (by omega) (by omega)
  by_cases h27 : j < 478
  · exact kvkstaticRange_456.get (by omega) (by omega)
  by_cases h28 : j < 500
  · exact kvkstaticRange_478.get (by omega) (by omega)
  by_cases h29 : j < 522
  · exact kvkstaticRange_500.get (by omega) (by omega)
  by_cases h30 : j < 544
  · exact kvkstaticRange_522.get (by omega) (by omega)
  by_cases h31 : j < 566
  · exact kvkstaticRange_544.get (by omega) (by omega)
  by_cases h32 : j < 588
  · exact kvkstaticRange_566.get (by omega) (by omega)
  by_cases h33 : j < 610
  · exact kvkstaticRange_588.get (by omega) (by omega)
  by_cases h34 : j < 632
  · exact kvkstaticRange_610.get (by omega) (by omega)
  by_cases h35 : j < 654
  · exact kvkstaticRange_632.get (by omega) (by omega)
  by_cases h36 : j < 675
  · exact kvkstaticRange_654.get (by omega) (by omega)
  by_cases h37 : j < 697
  · exact kvkstaticRange_675.get (by omega) (by omega)
  by_cases h38 : j < 718
  · exact kvkstaticRange_697.get (by omega) (by omega)
  by_cases h39 : j < 740
  · exact kvkstaticRange_718.get (by omega) (by omega)
  by_cases h40 : j < 761
  · exact kvkstaticRange_740.get (by omega) (by omega)
  by_cases h41 : j < 783
  · exact kvkstaticRange_761.get (by omega) (by omega)
  by_cases h42 : j < 804
  · exact kvkstaticRange_783.get (by omega) (by omega)
  by_cases h43 : j < 826
  · exact kvkstaticRange_804.get (by omega) (by omega)
  by_cases h44 : j < 847
  · exact kvkstaticRange_826.get (by omega) (by omega)
  by_cases h45 : j < 869
  · exact kvkstaticRange_847.get (by omega) (by omega)
  by_cases h46 : j < 890
  · exact kvkstaticRange_869.get (by omega) (by omega)
  by_cases h47 : j < 912
  · exact kvkstaticRange_890.get (by omega) (by omega)
  by_cases h48 : j < 933
  · exact kvkstaticRange_912.get (by omega) (by omega)
  by_cases h49 : j < 954
  · exact kvkstaticRange_933.get (by omega) (by omega)
  by_cases h50 : j < 975
  · exact kvkstaticRange_954.get (by omega) (by omega)
  by_cases h51 : j < 996
  · exact kvkstaticRange_975.get (by omega) (by omega)
  by_cases h52 : j < 1018
  · exact kvkstaticRange_996.get (by omega) (by omega)
  by_cases h53 : j < 1039
  · exact kvkstaticRange_1018.get (by omega) (by omega)
  by_cases h54 : j < 1061
  · exact kvkstaticRange_1039.get (by omega) (by omega)
  by_cases h55 : j < 1085
  · exact kvkstaticRange_1061.get (by omega) (by omega)
  by_cases h56 : j < 1108
  · exact kvkstaticRange_1085.get (by omega) (by omega)
  by_cases h57 : j < 1127
  · exact kvkstaticRange_1108.get (by omega) (by omega)
  by_cases h58 : j < 1148
  · exact kvkstaticRange_1127.get (by omega) (by omega)
  by_cases h59 : j < 1168
  · exact kvkstaticRange_1148.get (by omega) (by omega)
  by_cases h60 : j < 1190
  · exact kvkstaticRange_1168.get (by omega) (by omega)
  by_cases h61 : j < 1211
  · exact kvkstaticRange_1190.get (by omega) (by omega)
  by_cases h62 : j < 1233
  · exact kvkstaticRange_1211.get (by omega) (by omega)
  by_cases h63 : j < 1254
  · exact kvkstaticRange_1233.get (by omega) (by omega)
  by_cases h64 : j < 1275
  · exact kvkstaticRange_1254.get (by omega) (by omega)
  by_cases h65 : j < 1296
  · exact kvkstaticRange_1275.get (by omega) (by omega)
  by_cases h66 : j < 1317
  · exact kvkstaticRange_1296.get (by omega) (by omega)
  by_cases h67 : j < 1339
  · exact kvkstaticRange_1317.get (by omega) (by omega)
  by_cases h68 : j < 1360
  · exact kvkstaticRange_1339.get (by omega) (by omega)
  by_cases h69 : j < 1381
  · exact kvkstaticRange_1360.get (by omega) (by omega)
  by_cases h70 : j < 1402
  · exact kvkstaticRange_1381.get (by omega) (by omega)
  by_cases h71 : j < 1423
  · exact kvkstaticRange_1402.get (by omega) (by omega)
  by_cases h72 : j < 1444
  · exact kvkstaticRange_1423.get (by omega) (by omega)
  by_cases h73 : j < 1465
  · exact kvkstaticRange_1444.get (by omega) (by omega)
  by_cases h74 : j < 1486
  · exact kvkstaticRange_1465.get (by omega) (by omega)
  by_cases h75 : j < 1507
  · exact kvkstaticRange_1486.get (by omega) (by omega)
  by_cases h76 : j < 1528
  · exact kvkstaticRange_1507.get (by omega) (by omega)
  by_cases h77 : j < 1549
  · exact kvkstaticRange_1528.get (by omega) (by omega)
  by_cases h78 : j < 1570
  · exact kvkstaticRange_1549.get (by omega) (by omega)
  by_cases h79 : j < 1591
  · exact kvkstaticRange_1570.get (by omega) (by omega)
  by_cases h80 : j < 1612
  · exact kvkstaticRange_1591.get (by omega) (by omega)
  by_cases h81 : j < 1633
  · exact kvkstaticRange_1612.get (by omega) (by omega)
  by_cases h82 : j < 1653
  · exact kvkstaticRange_1633.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvkstaticRange_1653.get (by omega) (by omega)
  by_cases h84 : j < 1692
  · exact kvkstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1707
  · exact kvkstaticRange_1692.get (by omega) (by omega)
  by_cases h86 : j < 1720
  · exact kvkstaticRange_1707.get (by omega) (by omega)
  by_cases h87 : j < 1735
  · exact kvkstaticRange_1720.get (by omega) (by omega)
  by_cases h88 : j < 1747
  · exact kvkstaticRange_1735.get (by omega) (by omega)
  by_cases h89 : j < 1759
  · exact kvkstaticRange_1747.get (by omega) (by omega)
  by_cases h90 : j < 1771
  · exact kvkstaticRange_1759.get (by omega) (by omega)
  by_cases h91 : j < 1782
  · exact kvkstaticRange_1771.get (by omega) (by omega)
  by_cases h92 : j < 1793
  · exact kvkstaticRange_1782.get (by omega) (by omega)
  exact kvkstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
