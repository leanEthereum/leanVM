module

public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.Seed.Names
public import NativeRustcVmArm.Top.Seed.Stage1
public import NativeRustcVmArm.Top.Seed.Stage2

/-!
# `seed` on AArch64

**`seed_spec`**: rustc's `seed`, placed anywhere in the program, meets its contract (`SeedPre`,
`SeedPost`) given the contracts of `keccak256_words::<fiat_shamir_iv's closure>`, `memset`,
`keccak_f` and `memcpy`. Its 240-byte frame (`Body`, the prologue's four slots at its bytes 208 to
239) holds the state from its byte 8: the IV (`keccak256_words`), zeros (`memset`; `stage1`), the
public input (`b2`); `keccak_f` permutes it in place and `memcpy` copies it to the output
(`stage2`); `b4` restores the registers.
-/

namespace NativeRustcVmArm.Top.Seed

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Seed NativeVm.Model

public section

variable [Host] {k : Nat}

/-- **`seed` meets its contract.** -/
theorem seed_spec (hp : Placed code k)
    (hkiv : Spec (Labels.label NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.entryLabel) Keccak256WordsIvPre Keccak256WordsIvPost)
    (hmemset : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hkf : Spec (Labels.label NativeRustcVmArm.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.Seed.entryLabel) SeedPre SeedPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  refine Eventually.bind (stage1 hp hkiv hmemset hpre) fun st4 ⟨hpc4, hS1⟩ ↦ ?_
  refine Eventually.bind (stage2 hp hkf hmemcpy hpre hpc4 hS1) fun st8 ⟨hpc8, hB8, hout⟩ ↦ ?_
  have g := geo_of hpre
  have hmap := hpre.1.2.2
  have hS : seedStack = 928 := rfl
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs928 := g.s
  have hF := g.F
  have hsb0 := g.sb
  have hFm : Mapped m0.dmem (frameOf m0) 240 :=
    Mapped.within hmap (by rw [hsb0]; omega) (by rw [hsb0, hF]; omega) (by rw [hsb0, hF]; omega)
  have hwf8 : (Env.ofMachine st8.data [(frameOf m0, 240)]).WF :=
    Env.wf_of ⟨⟨Mapped.kept hFm hB8.kept, show (frameOf m0).toNat + 240 ≤ 2 ^ 64 by omega⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm8 : Match (Env.ofMachine st8.data [(frameOf m0, 240)]) exitS st8.data :=
    match_ofMachine ⟨rfl, fun _ ↦ show (frameOf m0).toNat % 16 = 0 by have := g.al; omega,
      trivial⟩
      (show st8.data.regs.SP.toBitVec = frameOf m0 + BitVec.ofInt 64 0 by
        rw [hB8.sp]; simp [frameOf])
      trivial trivial trivial trivial
  refine exec_at (hb4 hp) run_b4 hwf8 hpc8 hm8 fun st9 hm9 hpc9 ↦ ?_
  have hr4 := b4_restores
  rw [after_eq run_b4] at hr4
  have hm4' := b4_mem
  rw [after_eq run_b4] at hm4'
  obtain ⟨hsv, hret, hdm9⟩ := hB8.ret hm9 hwf8 (by simp [slots]) hr4 hm4'
  refine Eventually.done _ ⟨hpc9.trans hret, fun w hw hbc P hP ↦ ?_, fun q hq ↦ ?_, hsv⟩
  · rw [hdm9]
    exact hout w hw hbc P hP
  · rw [hdm9]
    refine hB8.same q fun h ↦ hq (h.elim (fun hs ↦ Or.inr ?_) Or.inl)
    change InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 928) 928 q
    rw [inRange_below (by omega)]
    exact hs

end

end NativeRustcVmArm.Top.Seed
