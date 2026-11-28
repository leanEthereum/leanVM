module

public import NativeRustcVmX64.KeccakGkr.LinearTranspose.Cols

/-!
# `linear_transpose`: the output (x86-64)

`b15` sets the output loop's constants and pointers (`out_start`); for each lane `l`, `b16`
computes the two columns' addresses (`lane_cols`), the loop `b17` writes the output's element
`64 l + z` as `g`'s plus column `(l % 5 + 1) % 5`'s at `z` plus column `(l % 5 + 4) % 5`'s at
`(z + 1) % 64` (`out_step`), `b18` steps the lane (`out_lane_end`); `output` runs them all.
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' inRange_off_iff
  Mapped.keeps bytesAt_congr inRange_off_self)

@[expose] public section

/-- The output phase's context: the frame, memory changed only in `Out`, R14 the columns (R12 is
the loop's scratch). -/
structure OCtx (m0 : MachineData) (st : MachineData) : Prop where
  frame : Frame m0 64 slots 8 st
  same : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0)
  r14 : reg st .r14 = cA m0

/-- The output loop's constant registers. -/
structure OutRegs (m0 : MachineData) (l : Nat) (st : MachineData) : Prop where
  ctx : OCtx m0 st
  l_lt : l < 25
  rcx : reg st .rcx = BitVec.ofNat 64 l
  r8 : reg st .r8 = BitVec.ofNat 64 14757395258967641293
  r9 : reg st .r9 = BitVec.ofNat 64 4096
  rdi : reg st .rdi = BitVec.ofNat 64 0
  rsi : reg st .rsi = off (cA m0) 8
  rbx : reg st .rbx = off (oA m0) (8 + 1024 * l)
  r15 : reg st .r15 = off (gA m0) (8 + 1024 * l)

/-- **Lane `l`'s output head**: the lanes before it written. -/
structure OutLane (m0 : MachineData) (ws : Array EW) (l : Nat) (st : MachineData) : Prop where
  regs : OutRegs m0 l st
  g : ElemsAt st.dmem (gA m0) (gF ws) 1600
  c : ElemsAt st.dmem (cA m0) (cF ws) 320
  o : ElemsAt st.dmem (oA m0) (oF ws) (64 * l)

/-- **The output loop's head** in lane `l` after `z` elements. -/
structure OutHead (m0 : MachineData) (ws : Array EW) (l z : Nat) (st : MachineData) : Prop where
  lane : OutLane m0 ws l st
  z_lt : z < 64
  r10 : reg st .r10 = BitVec.ofNat 64 (z + 1)
  r11 : reg st .r11 = BitVec.ofNat 64 (16 * z)
  rax : reg st .rax = off (cA m0) (8 + 1024 * ca l)
  rdx : reg st .rdx = off (cA m0) (1024 * cb l)
  o : ElemsAt st.dmem (oA m0) (oF ws) (64 * l + z)

end

public section

variable {ws : Array EW} {m0 : MachineData}

theorem ca_lt (l : Nat) : ca l < 5 := Nat.mod_lt _ (by decide)
theorem cb_lt (l : Nat) : cb l < 5 := Nat.mod_lt _ (by decide)
theorem ca_ne_cb (l : Nat) : ca l ≠ cb l := by unfold ca cb; omega

/-- **A block without memory accesses** keeps the output phase's context. -/
theorem OCtx.of_regs [Labels] {d d' : MachineData} (hc : OCtx m0 d) (h : PreOk m0 ws) {S : SState}
    (hm : Match (Env.ofMachine d [] (fun _ ↦ 0) 0) S d') (hS : regOk S = true)
    (h14 : reg d' .r14 = reg d .r14) : OCtx m0 d' := by
  have hd : d'.dmem = d.dmem := hm.dmem_eq (Env.wf_nil _) (regOk_mem hS)
  exact ⟨Frame.keep hc.frame (by rw [hd]; exact fun _ h ↦ h) (hm.regs .rsp _ (regOk_rsp hS))
    (R := fun _ ↦ False) (fun q _ ↦ by rw [hd]) (fun _ h ↦ h.elim) (frame_nw h), hd ▸ hc.same,
    h14.trans hc.r14⟩

theorem OutRegs.keep {l : Nat} {st st' : MachineData} (h : OutRegs m0 l st) (hc : OCtx m0 st')
    (e : ∀ r ∈ [Reg64.rcx, .r8, .r9, .rdi, .rsi, .rbx, .r15], reg st' r = reg st r) :
    OutRegs m0 l st' :=
  ⟨hc, h.l_lt, (e .rcx (by simp)).trans h.rcx, (e .r8 (by simp)).trans h.r8,
    (e .r9 (by simp)).trans h.r9, (e .rdi (by simp)).trans h.rdi, (e .rsi (by simp)).trans h.rsi,
    (e .rbx (by simp)).trans h.rbx, (e .r15 (by simp)).trans h.r15⟩

variable [Host] {k : Nat}

/-- `b15`: lane `0`'s output head. -/
theorem out_start (hp : Placed code k) (h : PreOk m0 ws) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b15Offset)) (hI : CDone m0 ws st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b16Offset) ∧ OutLane m0 ws 0 s'.data)
      st := by
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) exit_b15 (Env.wf_nil _) nofun hpc
    (match_nil _) fun st' hm' hpc' ↦ ?_
  obtain ⟨hreg, hat, hrsi, hrbx, hr15, hrdi, hr8, hr9, hrcx⟩ := ok_b15
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) (regOk_mem hreg)
  have hc := OCtx.of_regs ⟨hI.ctx.frame, hI.ctx.same, hI.ctx.r14⟩ h hm' hreg
    (atoms_eq hm' hat (by simp))
  simp only [PcOk] at hpc'
  refine .done _ ⟨hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b15_next),
    ⟨⟨hc, by decide, hm'.regs .rcx _ hrcx, hm'.regs .r8 _ hr8, hm'.regs .r9 _ hr9,
      hm'.regs .rdi _ hrdi, ?_, ?_, ?_⟩, hd ▸ hI.g, hd ▸ hI.c, fun i hi ↦ absurd hi (by omega)⟩⟩
  · rw [show reg st'.data .rsi = _ from hm'.regs .rsi _ hrsi]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r14 = _ from hI.ctx.r14]
  · rw [show reg st'.data .rbx = _ from hm'.regs .rbx _ hrbx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .rbx = _ from hI.rbx, BitVec.add_comm]
  · rw [show reg st'.data .r15 = _ from hm'.regs .r15 _ hr15]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r15 = _ from hI.r15, BitVec.add_comm]

omit [Host] in
/-- `b16` run at lane `l`. -/
theorem b16_exec {l : Nat} (hl : l < 25) : ∃ S, exec b16 (s16 l) = some (S, .fall) ∧
    (regOk S && atoms S [.rsi, .r14, .r15, .rbx] && S.reg .rcx == some (.lit l) &&
    S.reg .r8 == some (.lit 14757395258967641293) && S.reg .r9 == some (.lit 4096) &&
    S.reg .rdi == some (.lit 0) && S.reg .r10 == some (.lit 1) && S.reg .r11 == some (.lit 0) &&
    isAddLit (S.reg .rax) .rsi (1024 * ((l % 5 + 1) % 5)) &&
    isAddLit (S.reg .rdx) .r14 (1024 * ((l % 5 + 4) % 5))) = true := by
  have h := ok_b16 l hl
  cases he : exec b16 (s16 l) with
  | none => rw [he] at h; cases h
  | some p =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨p.1, by rw [← h.1], h.2⟩

/-- **A lane's columns** (`b16`). -/
theorem lane_cols (hp : Placed code k) (h : PreOk m0 ws) {l : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b16Offset)) (hI : OutLane m0 ws l st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b17Offset) ∧
      OutHead m0 ws l 0 s'.data) st := by
  have hl := hI.regs.l_lt
  obtain ⟨S, hS, hok⟩ := b16_exec hl
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hreg, hat⟩, hrcx⟩, hr8⟩, hr9⟩, hrdi⟩, hr10⟩, hr11⟩, hrax⟩, hrdx⟩ := hok
  have hm : Match (Env.ofMachine st.data [] (fun _ ↦ 0) 0) (s16 l) st.data :=
    match_ofMachine trivial ⟨hI.regs.rcx, hI.regs.r8, hI.regs.r9, hI.regs.rdi, trivial⟩ trivial
      trivial trivial
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) hS (Env.wf_nil _) nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) (regOk_mem hreg)
  have hc := hI.regs.ctx.of_regs h hm' hreg (atoms_eq hm' hat (by simp))
  simp only [PcOk] at hpc'
  refine .done _ ⟨hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b16_next),
    ⟨⟨hI.regs.keep hc fun r hr ↦ ?_, hd ▸ hI.g, hd ▸ hI.c, hd ▸ hI.o⟩, by decide,
      hm'.regs .r10 _ hr10, hm'.regs .r11 _ hr11, ?_, ?_, by rw [hd]; exact hI.o⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hm'.regs .rcx _ hrcx).trans hI.regs.rcx.symm
    · exact (hm'.regs .r8 _ hr8).trans hI.regs.r8.symm
    · exact (hm'.regs .r9 _ hr9).trans hI.regs.r9.symm
    · exact (hm'.regs .rdi _ hrdi).trans hI.regs.rdi.symm
    · exact atoms_eq hm' hat (by simp)
    · exact atoms_eq hm' hat (by simp)
    · exact atoms_eq hm' hat (by simp)
  · rw [isAddLit_eval hm' hrax, Env.ofMachine_regs, show st.data.regs.get64 .rsi = _ from hI.regs.rsi,
      NativeRustcVm.Transcript.off_add]
  · rw [isAddLit_eval hm' hrdx, Env.ofMachine_regs, show st.data.regs.get64 .r14 = _ from
      hI.regs.ctx.r14]

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
