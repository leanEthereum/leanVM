module

public import NativeRustcVmX64.Keccak.WordsHash.Pad
public import NativeRustcVmX64.Code.Vm.KeccakF.Names

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): from the padding to the epilogue

`pad_run`: `padA` (lane 16's XOR, the padding word and offset), `padB t` (the padding word into
lane `t`), `padC` (`0x80` into byte 135) and the call of `keccak_f` (`call_kf`) take the machine
from the padding block to the epilogue with the lanes `keccakF1600 (lastB m0)` (`EpiAt`).
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (load_of_wordAt)
open Vm.Keccak256WordsOfHashWords

public section

variable [Host]

/-- **From the padding to the epilogue.** -/
theorem pad_run (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) NativeRustcVmX64.KeccakFPre
      NativeRustcVmX64.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) {st : MachineState}
    (h : ValAt m0 k (tailR4 m0) (stA m0) (17 * nb m0) 16 .rax NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset st) :
    Eventually (step1 Host.exe) (EpiAt m0 k) st := by
  obtain ⟨hc, hl, hrax, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hrax hpc
  subst hpc
  have hb82 := b82_in_code.trans hp.1 (List.cons_ne_nil _ _)
  rw [show b82 = padACode ++ (padBCode ++ padCCode) from rfl] at hb82
  obtain ⟨hkA, hkBC⟩ := List.IsInfixAt.append hb82
  obtain ⟨hkB, hkC⟩ := List.IsInfixAt.append hkBC
  rw [show k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset + padACode.length = k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset + padACode.length from rfl] at hkB hkC
  rw [show k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset + padACode.length + padBCode.length = k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset + padACode.length + padBCode.length from rfl] at hkC
  have hr136 : (m0.regs.get64 .rdx).toNat % 136 < 136 := Nat.mod_lt _ (by decide)
  obtain ⟨t, ht⟩ : ∃ t, t = (m0.regs.get64 .rdx).toNat % 136 / 8 := ⟨_, rfl⟩
  have ht17 : t < 17 := by omega
  -- `padA`
  obtain ⟨hwf, hm⟩ := main_env g.stk hc (vars := fun _ => 0) (ret := 0)
  have hr14 : m.regs.get64 .r14 = BitVec.ofNat 64 ((m0.regs.get64 .rdx).toNat % 136) :=
    hc.regs.2.2.2.1
  refine exec_then hkA padA hwf (fun _ h => by cases h) hm fun st1 hm1 hpc1 => ?_
  have hc1 : Ctx m0 (slotsH m0) [] 8 st1.data :=
    ctx_step g.stk (slotsH_low m0) hc hm1 hwf rfl rfl rfl trivial
  have hl1 : Lanes m0 st1.data.dmem (pre (stA m0) (word m0) (17 * nb m0) 17) := by
    have := lanes_stepB hm1 rfl (j := 16) rfl rfl hl
      (x := Keccak.lane (stA m0) 16 ^^^ word m0 (17 * nb m0 + 16)) (by
        show BinOp.apply .xor .W64
          ((Env.ofMachine m [(frame m0, 296)]).load 0 168 8) (m.regs.get64 .rax) = _
        rw [xor64, hrax, load_of_wordAt (r := 0) (off := 168) (hl 16 (by omega))]
        simp [pre])
    rwa [pre_succ] at this
  have h14 : st1.data.regs.get64 .r14 = BitVec.ofNat 64 (8 * t) := by
    rw [hm1.regs .r14 _ rfl]
    show BinOp.apply .and .W64 (m.regs.get64 .r14) (BitVec.ofNat 64 18446744073709551608) = _
    rw [hr14, and8_val _ hr136, ht]
  have hax : st1.data.regs.get64 .rax =
      ((1 : UInt64) <<< (8 * ((m0.regs.get64 .rdx).toNat % 136 % 8)).toUInt64).toBitVec := by
    rw [hm1.regs .rax _ rfl]
    show BinOp.apply .shl .W64 (BitVec.ofNat 64 1) (oct32 (m.regs.get64 .r14)) = _
    rw [hr14, padWord_val _ hr136]
  simp only [PcOk] at hpc1
  -- `padB t`
  obtain ⟨SB, hxB, hmemB, hrspB⟩ := padB_exec t ht17
  let env2 := Env.ofMachine st1.data [(frame m0, 296)]
  have hwf2 : env2.WF := frame_wf g.stk hc1.kept
  have hm2 : Match env2 (startPad t) st1.data := by
    refine match_ofMachine ⟨rfl, trivial⟩ ⟨rsp_eval hc1.rsp rfl, trivial⟩ trivial trivial
      ⟨?_, trivial⟩
    show BinOp.apply .add .W64 (env2.base 0 + BitVec.ofInt 64 8) (st1.data.regs.get64 .r14) =
      env2.base 0 + BitVec.ofInt 64 (8 + 8 * (t : Int))
    rw [h14, add64, show (8 + 8 * (t : Int)) = ((8 + 8 * t : Nat) : Int) by omega,
      BitVec.ofInt_natCast, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, BitVec.add_assoc,
      BitVec.ofNat_add]
  refine exec_at hkB hxB hwf2 (fun _ h => by cases h) hpc1 hm2 fun st2 hm2' hpc2 => ?_
  have hc2 : Ctx m0 (slotsH m0) [] 8 st2.data :=
    ctx_step g.stk (slotsH_low m0) hc1 hm2' hwf2 rfl hrspB (by rw [hmemB]; simp [bodyW]; omega)
      trivial
  have hl2 := lanes_stepB hm2' rfl (j := t)
    (v := .bin .xor .W64 (.load 0 (40 + 8 * t) 8) (.reg .rax)) (by rw [hmemB]; simp [firstOverlap])
    (by rw [hmemB]; simp [laneW]) hl1
    (x := pre (stA m0) (word m0) (17 * nb m0) 17 t ^^^
      (1 : UInt64) <<< (8 * ((m0.regs.get64 .rdx).toNat % 136 % 8)).toUInt64) (by
      show BinOp.apply .xor .W64 (env2.load 0 (40 + 8 * t) 8) (st1.data.regs.get64 .rax) = _
      rw [xor64, hax, load_of_wordAt (r := 0) (hl1 t (by omega))]
      rfl)
  simp only [PcOk] at hpc2
  -- `padC`, and the call
  obtain ⟨hwf3, hm3⟩ := main_env g.stk hc2 (vars := fun _ => 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b82Offset + padACode.length + padBCode.length + padCCode.length)).toBitVec)
  refine exec_at hkC padC hwf3 (fun _ _ => rfl) hpc2 hm3 fun st3 hm3' hpc3 => ?_
  have hc3 : Ctx m0 (slotsH m0) [] 0 st3.data :=
    ctx_step g.stk (slotsH_low m0) hc2 hm3' hwf3 rfl rfl (by decide) trivial
  have hl3 := lanes_xorb hm3' rfl rfl hl2
  have hrdi : st3.data.regs.get64 .rdi = frame m0 + BitVec.ofNat 64 40 := by
    rw [hm3'.regs .rdi _ rfl]
    simp [Sym.eval]
  refine call_kf hkf g.stk g.rc g.got (slotsH_low m0) hc3 (lanes_congr hl3 fun i hi =>
    lane_lastG _ _ _ _ ht hi) hrdi hpc3 fun st4 hpc4 hc4 hl4 _ => .done _ ⟨hc4, hl4, ?_⟩
  rw [hpc4]
  rfl

end

end NativeRustcVmX64.WordsHash
