module

public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Layer

/-!
# `verify_keccak`: the twelve layers

`b16` to `b39`: `stepLayer` for `j` from `0` to `11`, from `AtL 0` (`k + NativeRustcVmArm.Vm.VerifyKeccak.b16Offset`) to `AtL 12`
(`k + NativeRustcVmArm.Vm.VerifyKeccak.b40Offset`), `stepLayers`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

/-- **Layers `0` to `5`.** -/
theorem stepLayers0 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hvl : ∀ a s c, Spec (Labels.label NativeRustcVmArm.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c))
    {m : MachineData} {sj : TState} {cj first : KeccakClaimW} {c : EW}
    (hl : AtL a s cs inst output m0 m 0 sj cj first c)
    (cont : ∀ m' sj' cj', AtL a s cs inst output m0 m' 6 sj' cj' first c →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b28Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b16Offset)⟩ := by
  refine stepLayer hp h hn hvl (j := 0) (by decide) (b16_in_code.trans hp.1 (by simp [b16]))
    run_b16 rfl (b17_in_code.trans hp.1 (by simp [b17])) run_b17 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condX0 hx) hl fun m1 s1 c1 hl1 ↦ ?_
  refine stepLayer hp h hn hvl (j := 1) (by decide) (b18_in_code.trans hp.1 (by simp [b18]))
    run_b18 rfl (b19_in_code.trans hp.1 (by simp [b19])) run_b19 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl1 fun m2 s2 c2 hl2 ↦ ?_
  refine stepLayer hp h hn hvl (j := 2) (by decide) (b20_in_code.trans hp.1 (by simp [b20]))
    run_b20 rfl (b21_in_code.trans hp.1 (by simp [b21])) run_b21 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl2 fun m3 s3 c3 hl3 ↦ ?_
  refine stepLayer hp h hn hvl (j := 3) (by decide) (b22_in_code.trans hp.1 (by simp [b22]))
    run_b22 rfl (b23_in_code.trans hp.1 (by simp [b23])) run_b23 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl3 fun m4 s4 c4 hl4 ↦ ?_
  refine stepLayer hp h hn hvl (j := 4) (by decide) (b24_in_code.trans hp.1 (by simp [b24]))
    run_b24 rfl (b25_in_code.trans hp.1 (by simp [b25])) run_b25 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl4 fun m5 s5 c5 hl5 ↦ ?_
  exact stepLayer hp h hn hvl (j := 5) (by decide) (b26_in_code.trans hp.1 (by simp [b26]))
    run_b26 rfl (b27_in_code.trans hp.1 (by simp [b27])) run_b27 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl5 cont

/-- **Layers `6` to `11`.** -/
theorem stepLayers6 (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hvl : ∀ a s c, Spec (Labels.label NativeRustcVmArm.Vm.VerifyLayer.entryLabel) (VerifyLayerPre a s c)
      (VerifyLayerPost a s c))
    {m : MachineData} {sj : TState} {cj first : KeccakClaimW} {c : EW}
    (hl : AtL a s cs inst output m0 m 6 sj cj first c)
    (cont : ∀ m' sj' cj', AtL a s cs inst output m0 m' 12 sj' cj' first c →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b40Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b28Offset)⟩ := by
  refine stepLayer hp h hn hvl (j := 6) (by decide) (b28_in_code.trans hp.1 (by simp [b28]))
    run_b28 rfl (b29_in_code.trans hp.1 (by simp [b29])) run_b29 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl fun m1 s1 c1 hl1 ↦ ?_
  refine stepLayer hp h hn hvl (j := 7) (by decide) (b30_in_code.trans hp.1 (by simp [b30]))
    run_b30 rfl (b31_in_code.trans hp.1 (by simp [b31])) run_b31 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl1 fun m2 s2 c2 hl2 ↦ ?_
  refine stepLayer hp h hn hvl (j := 8) (by decide) (b32_in_code.trans hp.1 (by simp [b32]))
    run_b32 rfl (b33_in_code.trans hp.1 (by simp [b33])) run_b33 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl2 fun m3 s3 c3 hl3 ↦ ?_
  refine stepLayer hp h hn hvl (j := 9) (by decide) (b34_in_code.trans hp.1 (by simp [b34]))
    run_b34 rfl (b35_in_code.trans hp.1 (by simp [b35])) run_b35 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl3 fun m4 s4 c4 hl4 ↦ ?_
  refine stepLayer hp h hn hvl (j := 10) (by decide) (b36_in_code.trans hp.1 (by simp [b36]))
    run_b36 rfl (b37_in_code.trans hp.1 (by simp [b37])) run_b37 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl4 fun m5 s5 c5 hl5 ↦ ?_
  exact stepLayer hp h hn hvl (j := 11) (by decide) (b38_in_code.trans hp.1 (by simp [b38]))
    run_b38 rfl (b39_in_code.trans hp.1 (by simp [b39])) run_b39 rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩ ⟨rfl, rfl, by decide, by decide⟩
    (fun _ _ hx ↦ condW0 hx) hl5 cont

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
