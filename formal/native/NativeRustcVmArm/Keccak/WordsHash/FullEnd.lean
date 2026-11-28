module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.WordsHash.FullIter

/-!
# `keccak256_words::<hash_words's closure>`: the end of a whole block, and the loop

`fullEnd`: after the 16 lanes of whole block `b`, lane 16's word (`full16`), its XOR and the call
of `keccak_f` (`fullXor`, `call_kf`) and the next block's branch (`fullNext`) take the machine to
the head of block `b + 1` or, after the last, to the last block's head (`TailStart`).
`full_loop`: by induction on the blocks left. `tail_head`: from `TailStart` to the last block's
first lane.
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (wordAt_keep load_of_wordAt)
open NativeRustcVm.Keccak Vm.Keccak256WordsOfHashWords

public section

/-- The next block's branch: taken after the last whole block. -/
theorem next_cmp {m0 : MachineData} (g : Geo m0) {b : Nat} (hb : b < nb m0) :
    (BitVec.ofNat 64 (17 * nb m0) == BitVec.ofNat 64 (17 * b) + BitVec.ofNat 64 17) =
      decide (b + 1 = nb m0) := by
  have hlen := g.len
  have hnb : 17 * nb m0 < 2 ^ 64 := by have := m0.regs.X2.toNat_lt; unfold nb; omega
  rw [BitVec.ofNat_add_ofNat]
  by_cases h : b + 1 = nb m0
  · have e : 17 * nb m0 = 17 * b + 17 := by omega
    rw [e, beq_self_eq_true]
    exact (decide_eq_true h).symm
  · simp only [h, decide_false]
    rw [beq_eq_false_iff_ne]
    intro he
    have h2 : 17 * b + 17 < 2 ^ 64 := by omega
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt h2] at this
    exact h (by omega)

variable [Host]

/-- **The end of whole block `b`.** -/
theorem fullEnd (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 16 147 st) :
    Eventually (step1 Host.exe)
      (fun st' => FullLaneAt m0 k (b + 1) 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset st' ∨ TailStart m0 k st') st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  have hstk := g.stk
  have hin := full_in g hb
  -- lane 16's word
  obtain ⟨hat, hreg1, hap1⟩ := slice_region g hc (i0 := 17 * b) (c := 17) hin (by omega)
  let env1 := Env.ofMachine m [(frame m0, 288), (blockAddr m0 b, 136)]
  have hwf1 : env1.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, hreg1, trivial⟩
      (List.pairwise_pair.mpr hap1)
  have hm1 : Match env1 startFull m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide),
      trivial⟩ (by rw [hc.sp]; simp [Sym.eval]) ⟨hx26, trivial⟩ trivial trivial trivial
  refine exec_then (b21_in_code.trans hp.1 (List.cons_ne_nil _ _)) full16 hwf1 hm1
    fun st1 hm1' hpc1 => ?_
  have hc1 : Ctx m0 st1.data := ctx_step hstk hc hm1' hwf1 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ (fun w hw => by cases hw)
  have hl1 : Lanes m0 st1.data (pre (wordBlocks (word m0) b) (word m0) (17 * b) 16) :=
    fun i hi => wordAt_keep (r := 0) (sz := 288) hm1' rfl (by omega) rfl (hl i hi)
  have hx8 : (st1.data.regs.getXReg .X8).toBitVec = (word m0 (17 * b + 16)).toBitVec :=
    (hm1'.regs .X8 _ rfl).trans
      (load_word (r := 1) (i0 := 17 * b) (q := 16) rfl (by omega) fun t ht => slice_same g hc (by omega))
  have h25 : (st1.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b) := by
    rw [Match.reg_eq (r := .X25) hm1 hm1' rfl rfl]; exact hx25
  have h26 : (st1.data.regs.getXReg .X26).toBitVec = blockAddr m0 b + BitVec.ofInt 64 64 := by
    rw [Match.reg_eq (r := .X26) hm1 hm1' rfl rfl]; exact hx26
  -- lane 16's XOR, and the call
  obtain ⟨m1, pc1⟩ := st1
  simp only [PcOk] at hpc1 hc1 hl1 hx8 h25 h26
  subst hpc1
  let env2 := Env.ofMachine m1 [(frame m0, 288)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc1.kept, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm2 : Match env2 startMain m1 :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hc1.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_then (b22_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullXor hwf2 hm2
    fun st2 hm2' hpc2 => ?_
  have hc2 : Ctx m0 st2.data := ctx_step hstk hc1 hm2' hwf2 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact ⟨rfl, by decide⟩
  have hl2 : Lanes m0 st2.data (Keccak.lane (Native.Keccak.Proof.xorRate (wordBlocks (word m0) b)
      fun k => word m0 (17 * b + k))) := by
    have := lanes_step (j := 16) hm2' rfl (by omega) rfl hl1
      (x := Keccak.lane (wordBlocks (word m0) b) 16 ^^^ word m0 (17 * b + 16)) (by
        show BinOp.apply .eor .W64 (env2.load 0 (8 + 8 * 16) 8) (m1.regs.getXReg .X8).toBitVec = _
        rw [eor64, load_of_wordAt (r := 0) (hl1 16 (by omega)), hx8]
        simp [pre])
    rw [pre_succ _ _ _ _ rfl] at this
    exact lanes_congr this fun i hi => pre_17 _ _ _ hi
  have hx0 : st2.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 8 :=
    (hm2'.regs .X0 _ rfl).trans (by simp [Sym.eval]; rfl)
  have h25' : (st2.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b) := by
    rw [Match.reg_eq (r := .X25) hm2 hm2' rfl rfl]; exact h25
  have h26' : (st2.data.regs.getXReg .X26).toBitVec = blockAddr m0 b + BitVec.ofInt 64 64 := by
    rw [Match.reg_eq (r := .X26) hm2 hm2' rfl rfl]; exact h26
  refine call_kf hkf hstk hrc hc2 hl2 hx0 hpc2 fun st3 hpc3 hc3 hl3 hsv3 => ?_
  have h25'' : (st3.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b) := by
    rw [hsv3 .X25 rfl]; exact h25'
  have h26'' : (st3.data.regs.getXReg .X26).toBitVec = blockAddr m0 b + BitVec.ofInt 64 64 := by
    rw [hsv3 .X26 rfl]; exact h26'
  -- the next block's branch
  obtain ⟨m3, pc3⟩ := st3
  simp only at hpc3 hc3 hl3 h25'' h26''
  rw [NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b22_length, NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b22Length] at hpc3
  subst hpc3
  let env3 := Env.ofMachine m3 [(frame m0, 288)]
  have hwf3 : env3.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc3.kept, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm3 : Match env3 startMain m3 :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hc3.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_then (b23_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullNext hwf3 hm3
    fun st4 hm4 hpc4 => .done _ ?_
  have hc4 : Ctx m0 st4.data := ctx_step hstk hc3 hm4 hwf3 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ (fun w hw => by cases hw)
  have hl4 : Lanes m0 st4.data (Keccak.lane (wordBlocks (word m0) (b + 1))) :=
    fun i hi => wordAt_keep (r := 0) (sz := 288) hm4 rfl (by omega) rfl (hl3 i hi)
  have hlen := g.len
  have hcmp := next_cmp g hb
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64] at hpc4
  have hpc4' : st4.pc = if b + 1 = nb m0 then Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b2Offset) else Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset) := by
    rw [hpc4]
    show (if ((m3.regs.getXReg .X23).toBitVec == BinOp.apply .add .W64
      (m3.regs.getXReg .X25).toBitVec 17#64) = true then _ else _) = _
    rw [add64, hc3.x23, h25'', show (17#64 : BitVec 64) = BitVec.ofNat 64 17 from rfl, hcmp]
    by_cases h : b + 1 = nb m0
    · simp only [h, decide_true, ↓reduceIte]
      exact label_at hp b2_in_code rfl
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl
  have h25f : (st4.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * (b + 1)) := by
    rw [hm4.regs .X25 _ rfl]
    show BinOp.apply .add .W64 (m3.regs.getXReg .X25).toBitVec (BitVec.ofNat 64 17) = _
    rw [add64, h25'', BitVec.ofNat_add_ofNat, show 17 * b + 17 = 17 * (b + 1) by omega]
  have h26f : (st4.data.regs.getXReg .X26).toBitVec = blockAddr m0 (b + 1) + BitVec.ofInt 64 64 := by
    rw [hm4.regs .X26 _ rfl]
    show BinOp.apply .add .W64 (m3.regs.getXReg .X26).toBitVec (BitVec.ofNat 64 136) = _
    rw [add64, h26'', blockAddr_succ, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm
      (BitVec.ofInt 64 64)]
  by_cases h : b + 1 = nb m0
  · right
    refine ⟨hc4, ?_, ?_⟩
    · rw [stA, ← h]; exact hl4
    · rw [hpc4']
      simp [h]
  · left
    refine ⟨hc4, by rw [pre_zero]; exact hl4, h25f, h26f, by omega, ?_⟩
    rw [hpc4']
    simp [h]

end

end NativeRustcVmArm.WordsHash
