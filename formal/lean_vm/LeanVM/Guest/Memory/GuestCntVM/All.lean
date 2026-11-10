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
public import LeanVM.Guest.Memory.GuestCntVM.Part16

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmchkIdx_320 : kvmchkIdx 320 = true := by
  have hb : blockB (kvmlookJ 320) (kvmomLookJ 320) false [] Data.core320.params Data.core320.name ([], []) Data.core320.body = some (⟨64765, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core320.body)]
    rw [← blockR_eq (Data.core320.body.drop 0), kvmsplit_320_0]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core320) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_321 : kvmchkIdx 321 = true := by
  have hb : blockB (kvmlookJ 321) (kvmomLookJ 321) false [] Data.core321.params Data.core321.name ([], []) Data.core321.body = some (⟨66289, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core321.body)]
    rw [← blockR_eq (Data.core321.body.drop 0), kvmsplit_321_0]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core321) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_322 : kvmchkIdx 322 = true := by
  have hb : blockB (kvmlookJ 322) (kvmomLookJ 322) false [] Data.core322.params Data.core322.name ([], []) Data.core322.body = some (⟨67125, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core322.body)]
    rw [← blockR_eq (Data.core322.body.drop 0), kvmsplit_322_0]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core322) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem kvmchkIdx_323 : kvmchkIdx 323 = true := by
  have hb : blockB (kvmlookJ 323) (kvmomLookJ 323) false [] Data.core323.params Data.core323.name ([], []) Data.core323.body = some (⟨71631, []⟩, []) := by
    rw [← List.drop_zero (l := Data.core323.body)]
    rw [← blockR_eq (Data.core323.body.drop 0), kvmsplit_323_0]
    rfl
  exact kvmchkIdx_of_split (fn := Data.core323) rfl rfl (by decide +kernel) hb (by decide +kernel) (by decide +kernel)

theorem kvmchkIdx_all : ∀ j < 1803, kvmchkIdx j = true := by
  intro j hj
  by_cases h1000 : j = 320
  · subst h1000; exact kvmchkIdx_320
  by_cases h1001 : j = 321
  · subst h1001; exact kvmchkIdx_321
  by_cases h1002 : j = 322
  · subst h1002; exact kvmchkIdx_322
  by_cases h1003 : j = 323
  · subst h1003; exact kvmchkIdx_323
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
  by_cases h20 : j < 320
  · exact kvmstaticRange_319.get (by omega) (by omega)
  by_cases h21 : j < 345
  · exact kvmstaticRange_324.get (by omega) (by omega)
  by_cases h22 : j < 367
  · exact kvmstaticRange_345.get (by omega) (by omega)
  by_cases h23 : j < 390
  · exact kvmstaticRange_367.get (by omega) (by omega)
  by_cases h24 : j < 404
  · exact kvmstaticRange_390.get (by omega) (by omega)
  by_cases h25 : j < 434
  · exact kvmstaticRange_404.get (by omega) (by omega)
  by_cases h26 : j < 456
  · exact kvmstaticRange_434.get (by omega) (by omega)
  by_cases h27 : j < 478
  · exact kvmstaticRange_456.get (by omega) (by omega)
  by_cases h28 : j < 500
  · exact kvmstaticRange_478.get (by omega) (by omega)
  by_cases h29 : j < 522
  · exact kvmstaticRange_500.get (by omega) (by omega)
  by_cases h30 : j < 544
  · exact kvmstaticRange_522.get (by omega) (by omega)
  by_cases h31 : j < 566
  · exact kvmstaticRange_544.get (by omega) (by omega)
  by_cases h32 : j < 588
  · exact kvmstaticRange_566.get (by omega) (by omega)
  by_cases h33 : j < 610
  · exact kvmstaticRange_588.get (by omega) (by omega)
  by_cases h34 : j < 632
  · exact kvmstaticRange_610.get (by omega) (by omega)
  by_cases h35 : j < 654
  · exact kvmstaticRange_632.get (by omega) (by omega)
  by_cases h36 : j < 675
  · exact kvmstaticRange_654.get (by omega) (by omega)
  by_cases h37 : j < 697
  · exact kvmstaticRange_675.get (by omega) (by omega)
  by_cases h38 : j < 718
  · exact kvmstaticRange_697.get (by omega) (by omega)
  by_cases h39 : j < 740
  · exact kvmstaticRange_718.get (by omega) (by omega)
  by_cases h40 : j < 761
  · exact kvmstaticRange_740.get (by omega) (by omega)
  by_cases h41 : j < 783
  · exact kvmstaticRange_761.get (by omega) (by omega)
  by_cases h42 : j < 804
  · exact kvmstaticRange_783.get (by omega) (by omega)
  by_cases h43 : j < 826
  · exact kvmstaticRange_804.get (by omega) (by omega)
  by_cases h44 : j < 847
  · exact kvmstaticRange_826.get (by omega) (by omega)
  by_cases h45 : j < 869
  · exact kvmstaticRange_847.get (by omega) (by omega)
  by_cases h46 : j < 890
  · exact kvmstaticRange_869.get (by omega) (by omega)
  by_cases h47 : j < 912
  · exact kvmstaticRange_890.get (by omega) (by omega)
  by_cases h48 : j < 933
  · exact kvmstaticRange_912.get (by omega) (by omega)
  by_cases h49 : j < 954
  · exact kvmstaticRange_933.get (by omega) (by omega)
  by_cases h50 : j < 975
  · exact kvmstaticRange_954.get (by omega) (by omega)
  by_cases h51 : j < 996
  · exact kvmstaticRange_975.get (by omega) (by omega)
  by_cases h52 : j < 1018
  · exact kvmstaticRange_996.get (by omega) (by omega)
  by_cases h53 : j < 1039
  · exact kvmstaticRange_1018.get (by omega) (by omega)
  by_cases h54 : j < 1061
  · exact kvmstaticRange_1039.get (by omega) (by omega)
  by_cases h55 : j < 1085
  · exact kvmstaticRange_1061.get (by omega) (by omega)
  by_cases h56 : j < 1108
  · exact kvmstaticRange_1085.get (by omega) (by omega)
  by_cases h57 : j < 1127
  · exact kvmstaticRange_1108.get (by omega) (by omega)
  by_cases h58 : j < 1148
  · exact kvmstaticRange_1127.get (by omega) (by omega)
  by_cases h59 : j < 1168
  · exact kvmstaticRange_1148.get (by omega) (by omega)
  by_cases h60 : j < 1190
  · exact kvmstaticRange_1168.get (by omega) (by omega)
  by_cases h61 : j < 1211
  · exact kvmstaticRange_1190.get (by omega) (by omega)
  by_cases h62 : j < 1233
  · exact kvmstaticRange_1211.get (by omega) (by omega)
  by_cases h63 : j < 1254
  · exact kvmstaticRange_1233.get (by omega) (by omega)
  by_cases h64 : j < 1275
  · exact kvmstaticRange_1254.get (by omega) (by omega)
  by_cases h65 : j < 1296
  · exact kvmstaticRange_1275.get (by omega) (by omega)
  by_cases h66 : j < 1317
  · exact kvmstaticRange_1296.get (by omega) (by omega)
  by_cases h67 : j < 1339
  · exact kvmstaticRange_1317.get (by omega) (by omega)
  by_cases h68 : j < 1360
  · exact kvmstaticRange_1339.get (by omega) (by omega)
  by_cases h69 : j < 1381
  · exact kvmstaticRange_1360.get (by omega) (by omega)
  by_cases h70 : j < 1402
  · exact kvmstaticRange_1381.get (by omega) (by omega)
  by_cases h71 : j < 1423
  · exact kvmstaticRange_1402.get (by omega) (by omega)
  by_cases h72 : j < 1444
  · exact kvmstaticRange_1423.get (by omega) (by omega)
  by_cases h73 : j < 1465
  · exact kvmstaticRange_1444.get (by omega) (by omega)
  by_cases h74 : j < 1486
  · exact kvmstaticRange_1465.get (by omega) (by omega)
  by_cases h75 : j < 1507
  · exact kvmstaticRange_1486.get (by omega) (by omega)
  by_cases h76 : j < 1528
  · exact kvmstaticRange_1507.get (by omega) (by omega)
  by_cases h77 : j < 1549
  · exact kvmstaticRange_1528.get (by omega) (by omega)
  by_cases h78 : j < 1570
  · exact kvmstaticRange_1549.get (by omega) (by omega)
  by_cases h79 : j < 1591
  · exact kvmstaticRange_1570.get (by omega) (by omega)
  by_cases h80 : j < 1612
  · exact kvmstaticRange_1591.get (by omega) (by omega)
  by_cases h81 : j < 1633
  · exact kvmstaticRange_1612.get (by omega) (by omega)
  by_cases h82 : j < 1653
  · exact kvmstaticRange_1633.get (by omega) (by omega)
  by_cases h83 : j < 1674
  · exact kvmstaticRange_1653.get (by omega) (by omega)
  by_cases h84 : j < 1692
  · exact kvmstaticRange_1674.get (by omega) (by omega)
  by_cases h85 : j < 1707
  · exact kvmstaticRange_1692.get (by omega) (by omega)
  by_cases h86 : j < 1720
  · exact kvmstaticRange_1707.get (by omega) (by omega)
  by_cases h87 : j < 1735
  · exact kvmstaticRange_1720.get (by omega) (by omega)
  by_cases h88 : j < 1747
  · exact kvmstaticRange_1735.get (by omega) (by omega)
  by_cases h89 : j < 1759
  · exact kvmstaticRange_1747.get (by omega) (by omega)
  by_cases h90 : j < 1771
  · exact kvmstaticRange_1759.get (by omega) (by omega)
  by_cases h91 : j < 1782
  · exact kvmstaticRange_1771.get (by omega) (by omega)
  by_cases h92 : j < 1793
  · exact kvmstaticRange_1782.get (by omega) (by omega)
  exact kvmstaticRange_1793.get (by omega) (by omega)

end
end LeanVM.Guest
