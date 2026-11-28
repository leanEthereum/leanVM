module

public import NativeRustcVmX64.Keccak.WordsHash.Full
public import NativeRustcVmX64.Code.Vm.KeccakF.Names

/-!
# `keccak256_words::<hash_words's closure>` (x86-64): the end of a whole block, and the loop

`fullEnd`: after lane 16's word (`ValAt … 16 .rax`), lane 16's XOR and the call of `keccak_f`
(`fullXor`, `b8`, `call_kf`) and the next block's branch (`fullNext`, `b9`) take the machine to
the head of block `b + 1` or, after the last, to the last block's head (`TailStart`).
`full_loop`: by induction on the blocks left (`Sym.loop`).
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt load_of_wordAt)
open NativeRustcVm.Keccak (wordBlocks)
open Vm.Keccak256WordsOfHashWords

public section

/-- The next block's branch: taken after the last whole block. -/
theorem next_cmp {nb b : Nat} (hb : b < nb) (hnb : 17 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (17 * nb) == BitVec.ofNat 64 17 + BitVec.ofNat 64 (17 * b)) =
      decide (b + 1 = nb) := by
  have h2 : 17 + 17 * b < 2 ^ 64 := by omega
  rw [BitVec.ofNat_add_ofNat, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt h2] at this
    clear he
    omega
  · intro h
    congr 1
    omega

variable [Host]

/-- **The end of whole block `b`.** -/
theorem fullEnd (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) NativeRustcVmX64.KeccakFPre
      NativeRustcVmX64.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) {b : Nat} (hb : b < nb m0) {st : MachineState}
    (h : ValAt m0 k ((.rbx, BitVec.ofNat 64 (17 * b)) :: fullR m0) (wordBlocks (word m0) b) (17 * b)
      16 .rax NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b8Offset st) :
    Eventually (step1 Host.exe)
      (fun st' => FullHead m0 k (b + 1) st' ∨ TailStart m0 k st') st := by
  obtain ⟨hc, hl, hrax, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hrax hpc
  subst hpc
  have hle := nb_le g
  have hn := n_lt g
  -- lane 16's XOR, and the call
  let env := Env.ofMachine m [(frame m0, 296)] (fun _ => 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b9Offset)).toBitVec
  have hwf : env.WF := frame_wf g.stk hc.kept
  have hm : Match env startMain m :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨rsp_eval hc.rsp rfl, trivial⟩ trivial trivial trivial
  refine exec_then (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullXor hwf (fun _ _ => rfl) hm
    fun st1 hm1 hpc1 => ?_
  have hR1 : RegsAt st1.data
      ((.r12, BitVec.ofNat 64 (nW m0)) :: (.r15, ws m0) :: (.rbx, BitVec.ofNat 64 (17 * b)) ::
        fullR m0) :=
    regsAt_keep hm1 hc.regs (names := [.r12, .r15, .rbx, .r13, .rbp, .r14]) rfl (by decide +kernel)
  have hc1 : Ctx m0 (slotsH m0) _ 0 st1.data :=
    ctx_step g.stk (slotsH_low m0) hc hm1 hwf rfl rfl rfl hR1
  have hl1 : Lanes m0 st1.data.dmem (Keccak.lane (Native.Keccak.Proof.xorRate
      (wordBlocks (word m0) b) fun k => word m0 (17 * b + k))) := by
    have := lanes_stepB hm1 rfl (j := 16) rfl rfl hl
      (x := Keccak.lane (wordBlocks (word m0) b) 16 ^^^ word m0 (17 * b + 16)) (by
        show BinOp.apply .xor .W64 (env.load 0 168 8) (m.regs.get64 .rax) = _
        rw [xor64, hrax, load_of_wordAt (r := 0) (off := 168) (hl 16 (by omega))]
        simp [pre])
    rw [pre_succ] at this
    exact lanes_congr this fun i hi => pre_17 _ _ _ hi
  have hrdi : st1.data.regs.get64 .rdi = frame m0 + BitVec.ofNat 64 40 :=
    (hm1.regs .rdi _ rfl).trans hc.regs.2.2.2.2.1
  refine call_kf hkf g.stk g.rc g.got (slotsH_low m0) hc1 hl1 hrdi hpc1 fun st2 hpc2 hc2 hl2 hsv2 => ?_
  have hR2 := regsAt_saved hR1 hsv2 (names := [.r12, .r15, .rbx, .r13, .rbp, .r14]) rfl
    (by decide +kernel)
  -- the next block's branch
  obtain ⟨m2, pc2⟩ := st2
  simp only at hpc2 hc2 hl2 hR2
  rw [show k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b8Offset + b8.length = k + NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b9Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.b8_next]] at hpc2
  subst hpc2
  obtain ⟨hwf3, hm3⟩ := main_env g.stk hc2 (vars := fun _ => 0) (ret := 0)
  refine exec_then (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullNext hwf3
    (fun _ h => by cases h) hm3 fun st4 hm4 hpc4 => .done _ ?_
  have hl4 : Lanes m0 st4.data.dmem (Keccak.lane (wordBlocks (word m0) (b + 1))) :=
    lanes_keep hm4 rfl (fun w hw => by cases hw) hl2
  have hrbx : st4.data.regs.get64 .rbx = BitVec.ofNat 64 (17 * (b + 1)) := by
    rw [hm4.regs .rbx _ rfl]
    simp only [Sym.eval, add64, Env.ofMachine_regs, hR2.2.2.1, BitVec.ofNat_add_ofNat]
    congr 1
    omega
  have hcmp := next_cmp hb (by omega)
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, add64, Env.ofMachine_regs,
    hR2.2.2.1, hR2.2.2.2.1, hcmp] at hpc4
  by_cases hend : b + 1 = nb m0
  · right
    simp only [hend, decide_true, ↓reduceIte] at hpc4
    refine ⟨ctx_step g.stk (slotsH_low m0) hc2 hm4 hwf3 rfl rfl rfl
      ⟨(hm4.regs .r12 _ rfl).trans hR2.1, (hm4.regs .r15 _ rfl).trans hR2.2.1,
        (hm4.regs .r14 _ rfl).trans hR2.2.2.2.2.2.1, trivial⟩, ?_, ?_⟩
    · rw [stA, ← hend]; exact hl4
    · rw [hpc4]
      exact label_at hp b2_in_code rfl
  · left
    simp only [hend, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine ⟨ctx_step g.stk (slotsH_low m0) hc2 hm4 hwf3 rfl rfl rfl
      ⟨(hm4.regs .r12 _ rfl).trans hR2.1, (hm4.regs .r15 _ rfl).trans hR2.2.1, hrbx,
        (hm4.regs .r13 _ rfl).trans hR2.2.2.2.1, (hm4.regs .rbp _ rfl).trans hR2.2.2.2.2.1,
        (hm4.regs .r14 _ rfl).trans hR2.2.2.2.2.2.1, trivial⟩, hl4, by omega, hpc4⟩

/-- **The whole blocks' loop.** -/
theorem full_loop (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) NativeRustcVmX64.KeccakFPre
      NativeRustcVmX64.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) {b : Nat} {st : MachineState} (h : FullHead m0 k b st) :
    Eventually (step1 Host.exe) (TailStart m0 k) st :=
  Sym.loop (tr := step1 Host.exe) (Q := TailStart m0 k)
    (fun n st => ∃ b, n = nb m0 - b ∧ FullHead m0 k b st)
    (fun _ st ⟨b, hn, h⟩ => Eventually.bind (fullHead_step hp g h) fun _ h1 =>
      Eventually.bind (full_lanes hp g h.2.2.1 h1) fun _ h2 =>
      Eventually.mono (fullEnd hkf hp g h.2.2.1 h2) fun _ h3 => by
        rcases h3 with h3 | h3
        · exact .inr ⟨nb m0 - (b + 1), by have := h.2.2.1; omega, b + 1, rfl, h3⟩
        · exact .inl h3)
    ⟨b, rfl, h⟩

end

end NativeRustcVmX64.WordsHash
