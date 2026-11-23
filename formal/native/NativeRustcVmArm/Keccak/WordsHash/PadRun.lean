module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.WordsHash.Pad

/-!
# `keccak256_words::<hash_words's closure>`: from the padding to the epilogue

`pad_run`: from the padding block (`PadAt`), the padding block (`pad_exec`, `pad_lanes`) and the
call of `keccak_f` (`call_kf`) take the machine to the epilogue with the lanes
`keccakF1600 (lastB m0)` (`EpiAt`); the lanes the padding block leaves are `lastB`'s
(`lane_lastB`).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcVm.Keccak Vm.Keccak256WordsOfHashWords

public section

/-- **The lanes before the last permutation.** -/
theorem lane_lastB (m0 : MachineData) {t : Nat} (ht : t = m0.regs.X2.toNat % 136 / 8) {i : Nat}
    (hi : i < 25) :
    (if i = 16 then pre (stA m0) (word m0) (base m0) 16 16 ^^^ word m0 (base m0 + 16) ^^^
        (if t = 16 then (1 : UInt64) <<< (8 * (m0.regs.X2.toNat % 136 % 8)).toUInt64 else 0) ^^^
        0x8000000000000000
      else if i = t then pre (stA m0) (word m0) (base m0) 16 i ^^^
        (1 : UInt64) <<< (8 * (m0.regs.X2.toNat % 136 % 8)).toUInt64
      else pre (stA m0) (word m0) (base m0) 16 i) = Keccak.lane (lastB m0) i := by
  have ht17 : t < 17 := by omega
  rw [lastB, Native.Keccak.Proof.lane_xorRate _ _ hi, padLane, ← ht]
  simp only [pre]
  by_cases h16 : i = 16
  · subst h16
    by_cases ht16 : t = 16
    · simp [ht16, UInt64.xor_assoc]
    · simp [ht16, Ne.symm ht16, UInt64.xor_assoc]
  · by_cases hit : i = t
    · subst hit
      simp [h16, show i < 17 by omega, show i < 16 by omega, UInt64.xor_assoc]
    · by_cases h17 : i < 17
      · simp [h16, hit, h17, show i < 16 by omega]
      · simp [h16, hit, h17, show ¬ i < 16 by omega]

variable [Host]

/-- **From the padding to the epilogue.** -/
theorem pad_run (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k)
    {m0 : MachineData} (g : Geo m0)
    (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack)
    {st : MachineState} (h : PadAt m0 k st) : Eventually (step1 Host.exe) (EpiAt m0 k) st := by
  obtain ⟨hc, hl, hx8, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx8 hpc
  subst hpc
  have hstk := g.stk
  have hlen := m0.regs.X2.toNat_lt
  have hnb : 136 * nb m0 ≤ m0.regs.X2.toNat := by unfold nb; omega
  have hr : m0.regs.X2.toNat - 136 * nb m0 = m0.regs.X2.toNat % 136 := by unfold nb; omega
  obtain ⟨t, ht⟩ : ∃ t, t = m0.regs.X2.toNat % 136 / 8 := ⟨_, rfl⟩
  have ht17 : t < 17 := by omega
  obtain ⟨S, hx, hmem, hsp, hx0, hregs⟩ := pad_exec t ht17
  let env := Env.ofMachine m [(frame m0, 288)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hx20 : (m.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 m0.regs.X2.toNat := by
    rw [hc.x20]; simp
  have hsub : BinOp.apply .sub .W64 (m.regs.getXReg .X20).toBitVec
      (BinOp.apply .mul .W64 (m.regs.getXReg .X24).toBitVec (BitVec.ofNat 64 136)) =
      BitVec.ofNat 64 (m0.regs.X2.toNat % 136) := by
    rw [hx20, hc.x24, sub_mul_val hnb, hr]
  have hm : Match env (startPad t) m := by
    refine match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial ⟨?_, trivial⟩
    show BinOp.apply .add .W64 (env.base 0 + BitVec.ofInt 64 8)
      (UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 (BinOp.apply .and .W64
        (BinOp.apply .sub .W64 (m.regs.getXReg .X20).toBitVec
          (BinOp.apply .mul .W64 (m.regs.getXReg .X24).toBitVec (BitVec.ofNat 64 136)))
        (BitVec.ofNat 64 18446744073709551608))) = env.base 0 + BitVec.ofInt 64 (8 + 8 * (t : Int))
    rw [hsub, and_val_aux _ (by omega), memExtE0, add64, ← ht,
      show (8 + 8 * (t : Int)) = ((8 + 8 * t : Nat) : Int) by omega, BitVec.ofInt_natCast,
      show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, BitVec.add_assoc, BitVec.ofNat_add]
  have hk : b76.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b76Offset) := b76_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk hx hwf hm fun st1 hm1 hpc1 => ?_
  have hc1 : Ctx m0 st1.data := ctx_step hstk hc hm1 hwf rfl hsp hregs fun w hw => by
    rw [hmem, padMem] at hw
    split at hw
    · rw [List.mem_singleton] at hw
      subst hw
      exact ⟨rfl, by decide⟩
    · rcases List.mem_pair.mp hw with rfl | rfl
      · exact ⟨rfl, by decide⟩
      · exact ⟨rfl, by simp only; omega⟩
  have hl1 : Lanes m0 st1.data (Keccak.lane (lastB m0)) := by
    refine lanes_congr (pad_lanes hm1 rfl ht17 hmem (fun i hi => hl i hi)
      (x8 := word m0 (base m0 + 16)) hx8 ?_) fun i hi => lane_lastB m0 ht hi
    show BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) (UnOp.apply (.ubfm 61 2) .W64
      (BinOp.apply .sub .W64 (m.regs.getXReg .X20).toBitVec
        (BinOp.apply .mul .W64 (m.regs.getXReg .X24).toBitVec (BitVec.ofNat 64 136)))) = _
    rw [hsub, low_val_aux _ (by omega)]
  have hx0' : st1.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 8 :=
    (hm1.regs .X0 _ hx0).trans (by simp [Sym.eval]; rfl)
  refine call_kf hkf hstk hrc hc1 hl1 hx0' hpc1 fun st2 hpc2 hc2 hl2 _ => .done _ ⟨hc2, hl2, ?_⟩
  rw [hpc2, Nat.add_assoc, b76_next]

end

end NativeRustcVmArm.WordsHash
