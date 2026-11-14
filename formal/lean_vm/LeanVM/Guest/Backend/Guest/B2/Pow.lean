/-
  LeanVM.Guest.Backend.Guest.B2.Pow

  The guest's powers of `g` (`Data.powTree`) are powers of `g`, from the kernel's checks of its
  subtrees (`Guest/Checked/Pow00..07`) alone.
-/

module

public import LeanVM.Guest.Checked.Pow00
public import LeanVM.Guest.Checked.Pow01
public import LeanVM.Guest.Checked.Pow02
public import LeanVM.Guest.Checked.Pow03
public import LeanVM.Guest.Checked.Pow04
public import LeanVM.Guest.Checked.Pow05
public import LeanVM.Guest.Checked.Pow06
public import LeanVM.Guest.Checked.Pow07

/-!
# The powers of `g`

`Checked.powTree_ok` (in `Guest/Checked.lean`, which also imports every function's certificate
check) composes the checks of `Data.powTree`'s 64 subtrees with its 63 top nodes. `powTree_okW`
does the same from the subtrees' modules only, which check the power table and nothing of a
certificate.
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Guest LeanVM.Guest.Exec LeanVM.Guest.Checked

@[expose] public section

/-- **Every power of `g` the guest names is one**, without the certificates' checks. -/
theorem powTree_okW : Data.powTree.OkW := by
  unfold Data.powTree
  repeat' first
      | with_reducible exact powT0_ok
      | with_reducible exact powT1_ok
      | with_reducible exact powT2_ok
      | with_reducible exact powT3_ok
      | with_reducible exact powT4_ok
      | with_reducible exact powT5_ok
      | with_reducible exact powT6_ok
      | with_reducible exact powT7_ok
      | with_reducible exact powT8_ok
      | with_reducible exact powT9_ok
      | with_reducible exact powT10_ok
      | with_reducible exact powT11_ok
      | with_reducible exact powT12_ok
      | with_reducible exact powT13_ok
      | with_reducible exact powT14_ok
      | with_reducible exact powT15_ok
      | with_reducible exact powT16_ok
      | with_reducible exact powT17_ok
      | with_reducible exact powT18_ok
      | with_reducible exact powT19_ok
      | with_reducible exact powT20_ok
      | with_reducible exact powT21_ok
      | with_reducible exact powT22_ok
      | with_reducible exact powT23_ok
      | with_reducible exact powT24_ok
      | with_reducible exact powT25_ok
      | with_reducible exact powT26_ok
      | with_reducible exact powT27_ok
      | with_reducible exact powT28_ok
      | with_reducible exact powT29_ok
      | with_reducible exact powT30_ok
      | with_reducible exact powT31_ok
      | with_reducible exact powT32_ok
      | with_reducible exact powT33_ok
      | with_reducible exact powT34_ok
      | with_reducible exact powT35_ok
      | with_reducible exact powT36_ok
      | with_reducible exact powT37_ok
      | with_reducible exact powT38_ok
      | with_reducible exact powT39_ok
      | with_reducible exact powT40_ok
      | with_reducible exact powT41_ok
      | with_reducible exact powT42_ok
      | with_reducible exact powT43_ok
      | with_reducible exact powT44_ok
      | with_reducible exact powT45_ok
      | with_reducible exact powT46_ok
      | with_reducible exact powT47_ok
      | with_reducible exact powT48_ok
      | with_reducible exact powT49_ok
      | with_reducible exact powT50_ok
      | with_reducible exact powT51_ok
      | with_reducible exact powT52_ok
      | with_reducible exact powT53_ok
      | with_reducible exact powT54_ok
      | with_reducible exact powT55_ok
      | with_reducible exact powT56_ok
      | with_reducible exact powT57_ok
      | with_reducible exact powT58_ok
      | with_reducible exact powT59_ok
      | with_reducible exact powT60_ok
      | with_reducible exact powT61_ok
      | with_reducible exact powT62_ok
      | with_reducible exact powT63_ok
      | refine ⟨by decide, gpowW_of_beq (by decide +kernel), ?_, ?_⟩

theorem powTree_ok : Data.powTree.Ok := PowTree.ok_of_okW powTree_okW

end
end LeanVM.Guest.Backend.B2
