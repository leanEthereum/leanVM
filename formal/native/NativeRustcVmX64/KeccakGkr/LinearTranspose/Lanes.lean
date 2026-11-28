module

public import NativeRustcVmX64.KeccakGkr.LinearTranspose.Defs
public import NativeRustcVmX64.Code.Vm.KeccakPi.Names

/-!
# `linear_transpose`: `g`, lane by lane (x86-64)

The prologue (`b0`) pushes RBP to RBX and RAX, keeps the arguments in R12 (`w`), R15 (`g`), R14
(the columns), RBX (the output), RBP at `g + 24`, the lane R13 at `0` (`entry`, to `Head 0`).
For each lane `l` (`lane_head`): `b1` calls `keccak_pi(l)`, `b2` loads `ρ_l` and the source lane's
address `w + 1024 π(l)`; the copy loop (`b3`, `copy_step`) copies two elements per turn, position
`z` of lane `l` from position `(z + ρ_l) % 64` of lane `π(l)`; `b4` steps the lane (`lane_end`).
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)

@[expose] public section

/-- ρ of lane `l`. -/
abbrev rho (l : Nat) : Nat := keccakRhoW.getD l 0

/-- **A lane's head**: lanes before `l` copied into `g`. -/
structure Head (m0 : MachineData) (ws : Array EW) (l : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  l_lt : l < 25
  r13 : reg st .r13 = BitVec.ofNat 64 l
  rbp : reg st .rbp = off (gA m0) (24 + 1024 * l)
  r15 : reg st .r15 = gA m0
  rbx : reg st .rbx = oA m0
  g : ElemsAt st.dmem (gA m0) (gF ws) (64 * l)

/-- **The copy loop's head** in lane `l` after `t` pairs. -/
structure CopyHead (m0 : MachineData) (ws : Array EW) (l t : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  l_lt : l < 25
  t_lt : t < 32
  r13 : reg st .r13 = BitVec.ofNat 64 l
  rbp : reg st .rbp = off (gA m0) (24 + 1024 * l)
  r15 : reg st .r15 = gA m0
  rbx : reg st .rbx = oA m0
  rax : reg st .rax = off (wA m0) (1024 * keccakPi l)
  rcx : reg st .rcx = BitVec.ofNat 64 (rho l + 2 * t)
  rdx : reg st .rdx = BitVec.ofNat 64 (32 * t)
  g : ElemsAt st.dmem (gA m0) (gF ws) (64 * l + 2 * t)

/-- **`g` complete**. -/
structure GDone (m0 : MachineData) (ws : Array EW) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  r15 : reg st .r15 = gA m0
  rbx : reg st .rbx = oA m0
  g : ElemsAt st.dmem (gA m0) (gF ws) 1600

end

public section

variable {ws : Array EW} {m0 : MachineData}

theorem pi_lt {l : Nat} (hl : l < 25) : keccakPi l < 25 := by
  interval_cases l <;> decide

/-- The frame is the stack: `Out`. -/
theorem frame_out {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow m0 64) 64 q) : Out m0 q :=
  Or.inr (Or.inr (Or.inr (by rw [stack_eq]; exact hq)))

theorem frame_nw [Labels] (h : PreOk m0 ws) : NativeRustcVm.NoWrap (stackBelow m0 64) (64 + 8) :=
  frame_noWrap h.st (by rw [stack_eq])

/-- A range apart from the stack misses the frame and the return address. -/
theorem not_frame (h : StackOk m0 linearTransposeStack) {a q : BitVec 64} {N n : Nat}
    (hN : a.toNat + N ≤ 2 ^ 64)
    (hS : a.toNat + N ≤ (rspOf m0).toNat - 64 ∨ (rspOf m0).toNat + 8 ≤ a.toNat) (hn : n ≤ N)
    (hq : NativeRustcVm.InRange a n q) : ¬ NativeRustcVm.InRange (stackBelow m0 64) (64 + 8) q := by
  intro hf
  have hsb := stackBelow_toNat (m := m0) (n := 64) (by have := h.1; rw [stack_eq] at this; exact this)
  have h8 := h.2.1
  have h1 := h.1
  rw [stack_eq] at h1
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)] at hq
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hsb] at hf
  omega

variable [Host] {k : Nat}

/-- **The prologue** (`b0`): lane `0`'s head. -/
theorem entry (hp : Placed code k) (h : PreOk m0 ws) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b1Offset) ∧ Head m0 ws 0 s'.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b0Offset)⟩ := by
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 64) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨frame_mapped h.st (by rw [stack_eq]), frame_nw h⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1, Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b0_next, ?_⟩
  obtain ⟨hpro, hws1, hrbx, hr14, hr15, hr12, hrbp, hr13⟩ := ok_b0
  have hf1 : Frame m0 64 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 64) 64) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  refine ⟨⟨hf1, fun q hq ↦ hs1 q fun h' ↦ hq (frame_out h'), hm1.regs .r12 _ hr12,
    hm1.regs .r14 _ hr14⟩, by decide, hm1.regs .r13 _ hr13, ?_, hm1.regs .r15 _ hr15,
    hm1.regs .rbx _ hrbx, fun i hi ↦ absurd hi (by omega)⟩
  rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ hrbp]
  simp [Sym.eval, BinOp.apply]

/-- **A lane's start**: `keccak_pi`, `ρ`, the copy loop's head. -/
theorem lane_head (hp : Placed code k) (h : PreOk m0 ws)
    (hpi : Spec (Labels.label NativeRustcVmX64.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost) {l : Nat}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b1Offset)) (hI : Head m0 ws l st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b3Offset) ∧
      CopyHead m0 ws l 0 s'.data) st := by
  have hl := hI.l_lt
  have hnw := frame_nw h
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 64) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b1Offset + b1.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq])) hI.ctx.frame.kept, hnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf (fun _ _ ↦ rfl) hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hI.ctx.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hws1, hrdi, hat1⟩ := ok_b1
  have hf1 : Frame m0 64 slots 0 st1.data := Frame.of_block hI.ctx.frame hwf hm1 hmid1 slots_le
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 64) 8) :=
    sameOutside_low hwf hm1 (r := 0) rfl (by decide) hws1
  have hsp1 : rspOf st1.data = stackBelow m0 64 := by rw [hf1.sp, off_zero]
  have hX7 : reg st1.data .rdi = BitVec.ofNat 64 l := (hm1.regs .rdi _ hrdi).trans hI.r13
  have hat : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbx, .rbp], reg st1.data r = reg st.data r :=
    fun r hr ↦ atoms_eq hm1 hat1 hr
  refine call_then hpc1 hpi ⟨stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq]; rfl), by
      rw [hX7, toNat_ofNat_lt (by omega)]; exact hl⟩
    fun st2 hpc2 hrsp2 ⟨hpi2, hd2, hsv2⟩ ↦ ?_
  rw [hX7, toNat_ofNat_lt (by omega)] at hpi2
  have hf2 : Frame m0 64 slots 8 st2.data :=
    Frame.call_at hf1 hsv2 hrsp2 (R := fun _ ↦ False) (fun q _ ↦ by rw [hd2]) (fun _ _ _ _ h ↦ h)
      (fun _ _ h ↦ h)
  have hso2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (Out m0) := fun q hq ↦ by
    rw [hd2, hs1 q fun h' ↦ hq (frame_out (inRange_mono h' (by decide)))]
    exact hI.ctx.same q hq
  have hreg2 : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbx, .rbp], reg st2.data r = reg st.data r :=
    fun r hr ↦ (hsv2.1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      (hat r hr)
  -- `b2`: `ρ_l`, the source lane.
  have hrn := h.rn
  have hrS := h.rS
  have hsb := stackBelow_toNat (m := m0) (n := 64) h.sp.1
  have hsp := h.sp
  have hwf2 := frame_wf (m0 := m0) (d := st2.data) (F := 64) (rest := [(rhoAddr, 100)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq])) hf2.kept, hnw⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx; subst hx
      exact ⟨Mapped.keeps h.rM hf2.kept, by show _ + 100 ≤ _; omega⟩)
    (List.pairwise_pair.mpr (by
      show (stackBelow m0 64).toNat + (64 + 8) ≤ rhoAddr.toNat ∨
        rhoAddr.toNat + 100 ≤ (stackBelow m0 64).toNat
      rw [hsb]; omega))
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b1_next)) (match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hf2.rsp_eval, trivial⟩ ⟨rfl, trivial⟩
      ⟨by
        show (reg st2.data .r13).toNat < 25
        rw [hreg2 .r13 (by simp), hI.r13, toNat_ofNat_lt (by omega)]; exact hl, trivial⟩ trivial)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hrcx, hrax, hrdx, hat3⟩ := ok_b2
  have hf3 : Frame m0 64 slots 8 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hreg3 : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbx, .rbp], reg st3.data r = reg st.data r :=
    fun r hr ↦ (atoms_eq hm3 hat3 hr).trans (hreg2 r hr)
  have hrho : (frameEnv m0 st2.data 64 [(rhoAddr, 100)] (fun _ ↦ 0) 0).load 1 (4 * l) 4 =
      BitVec.ofNat 64 (rho l) :=
    load_rho rfl (rho_at h hso2) hl
  simp only [PcOk] at hpc3
  refine .done _ ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b2_next), ⟨⟨hf3, hd3 ▸ hso2, ?_, ?_⟩, hl, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (hreg3 .r12 (by simp)).trans hI.ctx.r12
  · exact (hreg3 .r14 (by simp)).trans hI.ctx.r14
  · exact (hreg3 .r13 (by simp)).trans hI.r13
  · exact (hreg3 .rbp (by simp)).trans hI.rbp
  · exact (hreg3 .r15 (by simp)).trans hI.r15
  · exact (hreg3 .rbx (by simp)).trans hI.rbx
  · rw [show reg st3.data .rax = _ from hm3.regs .rax _ hrax]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .r12 = _ from (hreg2 .r12 (by simp)).trans hI.ctx.r12]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have hpl := pi_lt hl
    rw [toNat_ext, BitVec.toNat_shiftLeft, low, BitVec.toNat_setWidth,
      show shiftCount .W32 (BitVec.ofNat 64 10) = 10 by decide,
      show (st2.data.regs.get64 .rax).toNat = keccakPi l from hpi2, Nat.shiftLeft_eq,
      BitVec.toNat_ofNat]
    simp only [Width.bits]
    omega
  · rw [show reg st3.data .rcx = _ from hm3.regs .rcx _ hrcx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .r13 = _ from (hreg2 .r13 (by simp)).trans hI.r13]
    rw [show (BitVec.ofNat 64 l * BitVec.ofNat 64 4).toNat = 4 * l by
      rw [BitVec.toNat_mul, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]; omega]
    rw [Nat.zero_add, hrho, Nat.mul_zero, Nat.add_zero]
  · rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ hrdx]; rfl
  · rw [hd3]
    exact hI.g.keep (fun q hq ↦ by rw [hd2]; exact hs1 q hq) (fun q hq hq' ↦
      not_frame h.st h.gn h.gS (by omega) hq (inRange_mono hq' (by omega)))
      (by have := h.gn; unfold NativeRustcVm.NoWrap; omega)

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
