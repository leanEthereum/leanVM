module

public import NativeRustcVmArm.Keccak.WordsHash.Full
public import NativeRustcVmArm.Keccak.WordsHash.Tail

/-!
# `keccak256_words::<hash_words's closure>`: the whole blocks' loop

`full_loop`: from the loop's head before whole block `b` (`FullLaneAt m0 k b 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset`), the machine
inevitably reaches the last block's head (`TailStart`) with the lanes the whole blocks' state
`stA m0`. An iteration: the head's branch (`fullHead_step`), the 16 lanes (`fullStep{j}`, `fullL_step`),
lane 16's word, its XOR and the call of `keccak_f` (`call_kf`), and the next block's branch
(`fullEnd`). `tailHead`: from `TailStart` to the last block's first lane (`TailAt m0 k 0`).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (wordAt_keep)
open NativeRustcVm.Keccak

@[expose] public section

/-- **At the last block's head**: the lanes the whole blocks' state. -/
def TailStart [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (Keccak.lane (stA m0)) ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b2Offset)

end

public section

theorem blockAddr_succ (m0 : MachineData) (b : Nat) :
    blockAddr m0 (b + 1) = blockAddr m0 b + BitVec.ofNat 64 136 := by
  unfold blockAddr
  rw [show 8 * (17 * (b + 1)) = 8 * (17 * b) + 136 by omega, ← BitVec.ofNat_add_ofNat,
    BitVec.add_assoc]

variable [Host]

/-- The loop head's branch: block `b`'s first word is in the slice. -/
theorem fullHead_step {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 0 162) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  have hstk := g.stk
  have hin := full_in g hb
  let env := Env.ofMachine m [(frame m0, 288)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env startMain m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_then (Vm.Keccak256WordsOfHashWords.b24_in_code.trans hp.1 (List.cons_ne_nil _ _)) fullHead hwf hm fun st hm' hpc => .done _
    ⟨?_, ?_, ?_, ?_, hb, ?_⟩
  · exact ctx_step hstk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
      (fun w hw => by cases hw)
  · exact fun i hi => wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl (hl i hi)
  · rw [Match.reg_eq (r := .X25) hm hm' rfl rfl]; exact hx25
  · rw [Match.reg_eq (r := .X26) hm hm' rfl rfl]; exact hx26
  have h4 := m0.regs.X4.toNat_lt
  have e : m0.regs.X4.toBitVec = BitVec.ofNat 64 m0.regs.X4.toNat := by simp
  have : (BitVec.ofNat 64 (17 * b)).ult (BitVec.ofNat 64 m0.regs.X4.toNat) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
    omega
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64] at hpc
  rw [hpc]
  show (if (!((m.regs.getXReg .X25).toBitVec).ult (m.regs.getXReg .X22).toBitVec) = true then _
    else _) = _
  rw [hx25, hc.x22, e, this]
  rfl

theorem fullStep0 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 0 162 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 1 282) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 0) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b25_in_code.trans hp.1 (List.cons_ne_nil _ _)) full0 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b43_in_code rfl)

theorem fullStep1 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 1 282 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 2 290) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 1) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b43_in_code.trans hp.1 (List.cons_ne_nil _ _)) full1 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep2 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 2 290 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 3 298) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 2) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b44_in_code.trans hp.1 (List.cons_ne_nil _ _)) full2 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep3 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 3 298 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 4 306) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 3) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b45_in_code.trans hp.1 (List.cons_ne_nil _ _)) full3 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep4 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 4 306 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 5 314) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 4) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b46_in_code.trans hp.1 (List.cons_ne_nil _ _)) full4 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep5 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 5 314 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 6 322) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 5) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b47_in_code.trans hp.1 (List.cons_ne_nil _ _)) full5 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep6 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 6 322 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 7 330) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 6) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b48_in_code.trans hp.1 (List.cons_ne_nil _ _)) full6 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep7 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 7 330 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 8 338) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 7) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b49_in_code.trans hp.1 (List.cons_ne_nil _ _)) full7 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep8 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 8 338 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 9 346) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 8) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b50_in_code.trans hp.1 (List.cons_ne_nil _ _)) full8 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep9 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 9 346 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 10 354) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 9) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b51_in_code.trans hp.1 (List.cons_ne_nil _ _)) full9 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep10 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 10 354 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 11 362) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 10) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b52_in_code.trans hp.1 (List.cons_ne_nil _ _)) full10 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep11 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 11 362 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 12 370) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 11) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b53_in_code.trans hp.1 (List.cons_ne_nil _ _)) full11 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep12 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 12 370 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 13 378) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 12) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b54_in_code.trans hp.1 (List.cons_ne_nil _ _)) full12 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep13 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 13 378 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 14 386) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 13) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b55_in_code.trans hp.1 (List.cons_ne_nil _ _)) full13 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep14 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 14 386 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 15 394) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 14) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b56_in_code.trans hp.1 (List.cons_ne_nil _ _)) full14 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := false) rfl rfl

theorem fullStep15 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 15 394 st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 16 147) st := by
  obtain ⟨hc, hl, hx25, hx26, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx25 hx26 hpc
  subst hpc
  exact fullL_step (j := 15) g hb (by decide) hc hl hx25 hx26 (Vm.Keccak256WordsOfHashWords.b57_in_code.trans hp.1 (List.cons_ne_nil _ _)) full15 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b21_in_code rfl)

theorem full_lanes {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLaneAt m0 k b 0 NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b24Offset st) :
    Eventually (step1 Host.exe) (FullLaneAt m0 k b 16 147) st := by
  refine Eventually.bind (fullHead_step hp g h) fun st0 h0 => ?_
  refine Eventually.bind (fullStep0 hp g h0) fun st1 h1 => ?_
  refine Eventually.bind (fullStep1 hp g h1) fun st2 h2 => ?_
  refine Eventually.bind (fullStep2 hp g h2) fun st3 h3 => ?_
  refine Eventually.bind (fullStep3 hp g h3) fun st4 h4 => ?_
  refine Eventually.bind (fullStep4 hp g h4) fun st5 h5 => ?_
  refine Eventually.bind (fullStep5 hp g h5) fun st6 h6 => ?_
  refine Eventually.bind (fullStep6 hp g h6) fun st7 h7 => ?_
  refine Eventually.bind (fullStep7 hp g h7) fun st8 h8 => ?_
  refine Eventually.bind (fullStep8 hp g h8) fun st9 h9 => ?_
  refine Eventually.bind (fullStep9 hp g h9) fun st10 h10 => ?_
  refine Eventually.bind (fullStep10 hp g h10) fun st11 h11 => ?_
  refine Eventually.bind (fullStep11 hp g h11) fun st12 h12 => ?_
  refine Eventually.bind (fullStep12 hp g h12) fun st13 h13 => ?_
  refine Eventually.bind (fullStep13 hp g h13) fun st14 h14 => ?_
  refine Eventually.bind (fullStep14 hp g h14) fun st15 h15 => ?_
  refine Eventually.bind (fullStep15 hp g h15) fun st16 h16 => ?_
  exact .done _ h16

end

end NativeRustcVmArm.WordsHash
