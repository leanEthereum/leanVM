module

public import NativeRustcVmX64.KeccakGkr.LinearTranspose.Lanes

/-!
# `linear_transpose`: the copy loop and the lane loop (x86-64)

A turn of the copy loop (`b3`, `copy_step`) copies `g`'s elements `64 l + 2 t` and `64 l + 2 t + 1`
from lane `π(l)`'s positions `(ρ_l + 2 t) % 64` and `(ρ_l + 2 t + 1) % 64`; after lane `l`'s 32
turns `b4` steps the lane (`lane_end`); `lanes_loop` runs them all.
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)

@[expose] public section

/-- **A lane copied**. -/
structure LaneEnd (m0 : MachineData) (ws : Array EW) (l : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  l_lt : l < 25
  r13 : reg st .r13 = BitVec.ofNat 64 l
  rbp : reg st .rbp = off (gA m0) (24 + 1024 * l)
  r15 : reg st .r15 = gA m0
  rbx : reg st .rbx = oA m0
  g : ElemsAt st.dmem (gA m0) (gF ws) (64 * l + 64)

end

public section

variable {ws : Array EW} {m0 : MachineData}

/-- `g`'s element at a lane's position, the source's. -/
theorem gF_lane {l z : Nat} (hz : z < 64) :
    gF ws (64 * l + z) = ws.getD (64 * keccakPi l + (z + rho l) % 64) 0 := by
  simp only [gF, NativeRustcVm.KeccakGkr.gW]
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega]

variable [Host] {k : Nat}

/-- **A turn of the copy loop**. -/
theorem copy_step (hp : Placed code k) (h : PreOk m0 ws) {l t : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b3Offset)) (hI : CopyHead m0 ws l t st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (t + 1 < 32 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b3Offset) ∧
      CopyHead m0 ws l (t + 1) s'.data) ∨ (t + 1 = 32 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b4Offset) ∧
      LaneEnd m0 ws l s'.data)) st := by
  have hl := hI.l_lt
  have ht := hI.t_lt
  have hpl := pi_lt hl
  have hrl : rho l < 64 := rho_lt hl
  have hwn := h.wn
  have hgn := h.gn
  have hgw := h.gw
  set wl := off (wA m0) (1024 * keccakPi l) with hwl
  set ge := off (gA m0) (1024 * l + 32 * t) with hge
  have hwln : wl.toNat = (wA m0).toNat + 1024 * keccakPi l := toNat_off (by omega)
  have hgen : ge.toNat = (gA m0).toNat + (1024 * l + 32 * t) := toNat_off (by omega)
  have hwf : (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (mapped_off h.wM (by omega)) hI.ctx.frame.kept,
        by show wl.toNat + 1024 ≤ 2 ^ 64; omega⟩,
      ⟨Mapped.keeps (mapped_off h.gM (by omega)) hI.ctx.frame.kept,
        by show ge.toNat + 32 ≤ 2 ^ 64; omega⟩, trivial⟩
      (List.pairwise_pair.mpr (by show wl.toNat + 1024 ≤ ge.toNat ∨ ge.toNat + 32 ≤ wl.toNat; omega))
  have hrcx : (reg st.data .rcx).toNat = rho l + 2 * t := by
    rw [hI.rcx, toNat_ofNat_lt (by omega)]
  have hx1 : ((Sym.reg .rcx).eval (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0)).toNat
      = rho l + 2 * t := hrcx
  have hx2 : ((Sym.bin .add .W64 (.reg .rcx) (.lit 1)).eval
      (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0)).toNat = rho l + 2 * t + 1 := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [BitVec.toNat_add, show (st.data.regs.get64 .rcx).toNat = _ from hrcx,
      toNat_ofNat_lt (n := 1) (by decide)]
    omega
  have hp1 := posS_eval (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0) (.reg .rcx)
    (by rw [hx1]; omega)
  have hp2 := posS_eval (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0)
    (.bin .add .W64 (.reg .rcx) (.lit 1)) (by rw [hx2]; omega)
  rw [hx1] at hp1
  rw [hx2] at hp2
  have hm : Match (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0) copyS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨by
        show reg st.data .rax = wl + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; exact hI.rax, trivial⟩
      trivial ⟨by show ((posS (.reg .rcx)).eval _).toNat < 1009; rw [hp1]; omega,
        by show ((posS (.bin .add .W64 (.reg .rcx) (.lit 1))).eval _).toNat < 1009; rw [hp2]; omega,
        trivial⟩
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [show st.data.regs.get64 .rbp = _ from hI.rbp, show st.data.regs.get64 .rdx = _ from hI.rdx,
          show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
          show (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0).base 1 = ge from rfl,
          hge, NativeRustcVm.Transcript.off_add, NativeRustcVm.Transcript.off_add]
        congr 1; omega, trivial⟩
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hrsp, hat, hrdx, hrcx', hrax, hws, hw⟩ := ok_b3
  have hso : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange ge 32) :=
    sameOutside_region hwf hm' (r := 1) rfl hws
  have hgeg : ∀ q, NativeRustcVm.InRange ge 32 q → NativeRustcVm.InRange (gA m0) 25600 q :=
    fun q hq ↦ off_in (by unfold NativeRustcVm.NoWrap; omega) (by omega) hq
  have hf' : Frame m0 64 slots 8 st'.data :=
    Frame.keep hI.ctx.frame (hm'.kept hwf) (hm'.regs .rsp _ hrsp) hso
      (fun q hq ↦ not_frame h.st h.gn h.gS (le_refl _) (hgeg q hq)) (frame_nw h)
  have hso' : NativeRustcVm.SameOutside m0.dmem st'.data.dmem (Out m0) := fun q hq ↦ by
    rw [hso q fun h' ↦ hq (Or.inl (hgeg q h'))]
    exact hI.ctx.same q hq
  -- the two elements
  have hel : ∀ (u p : Nat) (x : Sym), p < 64 → u < 2 →
      (∀ i < 8, findWrite 1 (16 * u + i) (after b3 copyS).mem = some (.loadx 0 0 x 8, i)) →
      (∀ i < 8, findWrite 1 (16 * u + 8 + i) (after b3 copyS).mem = some (.loadx 0 8 x 8, i)) →
      (x.eval (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0)).toNat = 16 * p →
      NativeRustcVm.EWAt st'.data.dmem (off ge (16 * u)) (ws.getD (64 * keccakPi l + p) 0) := by
    intro u p x hp64 hu h0 h1 hpos
    have hsrc := NativeRustcVm.ewAt_iff.mp (w_at h hI.ctx.same (i := 64 * keccakPi l + p) (by omega))
    have e0 : (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0).load 0 (16 * p) 8 =
        (ws.getD (64 * keccakPi l + p) 0).c0.toBitVec := load_of_wordAt (by
      show NativeRustcVm.WordAt st.data.dmem (off wl (16 * p)) _
      rw [hwl, off_off, show 1024 * keccakPi l + 16 * p = 16 * (64 * keccakPi l + p) by omega]
      exact hsrc.1)
    have e1 : (Env.ofMachine st.data [(wl, 1024), (ge, 32)] (fun _ ↦ 0) 0).load 0 (8 + 16 * p) 8 =
        (ws.getD (64 * keccakPi l + p) 0).c1.toBitVec := load_of_wordAt (by
      show NativeRustcVm.WordAt st.data.dmem (off wl (8 + 16 * p)) _
      rw [hwl, off_off, show 1024 * keccakPi l + (8 + 16 * p) = 16 * (64 * keccakPi l + p) + 8 by
        omega, ← off_off]
      exact hsrc.2)
    have := Match.ewAt_write hm' (r := 1) (o := 16 * u) rfl (by omega) h0 h1
    simp only [Sym.eval, hpos, Nat.zero_add] at this
    rw [e0, e1] at this
    exact this
  have hw0 := hel 0 ((rho l + 2 * t) % 64) i1S (Nat.mod_lt _ (by decide)) (by decide)
    (fun i hi ↦ by simpa using (hw i hi).1) (fun i hi ↦ by simpa using (hw i hi).2.1)
    (by show ((posS (.reg .rcx)).eval _).toNat = _; rw [hp1])
  have hw1 := hel 1 ((rho l + 2 * t + 1) % 64) i2S (Nat.mod_lt _ (by decide)) (by decide)
    (fun i hi ↦ by simpa using (hw i hi).2.2.1) (fun i hi ↦ by
      have := (hw i hi).2.2.2; rw [show 16 * 1 + 8 + i = 24 + i by omega]; exact this)
    (by show ((posS (.bin .add .W64 (.reg .rcx) (.lit 1))).eval _).toNat = _; rw [hp2])
  have hg' : ElemsAt st'.data.dmem (gA m0) (gF ws) (64 * l + 2 * (t + 1)) := by
    rw [show 64 * l + 2 * (t + 1) = (64 * l + 2 * t) + 2 by omega]
    refine ElemsAt.grow hI.g (by omega) (by
      rw [show 16 * (64 * l + 2 * t) = 1024 * l + 32 * t by omega, show 16 * 2 = 32 from rfl]
      exact hso) fun j hj ↦ ?_
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [show 64 * l + 2 * t + 0 = 64 * l + 2 * t by omega, gF_lane (by omega),
        show 16 * (64 * l + 2 * t) = 1024 * l + 32 * t by omega,
        show 2 * t + rho l = rho l + 2 * t by omega]
      have := hw0
      rw [hge, off_off, Nat.mul_zero, Nat.add_zero] at this
      exact this
    · rw [show 64 * l + 2 * t + 1 = 64 * l + (2 * t + 1) by omega, gF_lane (by omega),
        show 16 * (64 * l + (2 * t + 1)) = 1024 * l + 32 * t + 16 * 1 by omega,
        show 2 * t + 1 + rho l = rho l + 2 * t + 1 by omega]
      have := hw1
      rw [hge, off_off] at this
      exact this
  have hreg : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15, .rbx, .rbp], reg st'.data r = reg st.data r :=
    fun r hr ↦ atoms_eq hm' hat hr
  have hctx : Ctx m0 st'.data := ⟨hf', hso', (hreg .r12 (by simp)).trans hI.ctx.r12,
    (hreg .r14 (by simp)).trans hI.ctx.r14⟩
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hpc'
  rw [show st.data.regs.get64 .rdx = _ from hI.rdx, add_ofNat', beq_ofNat (by omega) (by omega)]
    at hpc'
  by_cases hlast : t + 1 = 32
  · rw [decide_eq_true (show 32 + 32 * t = 1024 by omega)] at hpc'
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    refine .done _ (Or.inr ⟨hlast, hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b3_next), hctx, hl,
      (hreg .r13 (by simp)).trans hI.r13, (hreg .rbp (by simp)).trans hI.rbp,
      (hreg .r15 (by simp)).trans hI.r15, (hreg .rbx (by simp)).trans hI.rbx, ?_⟩)
    rw [show 64 * l + 64 = 64 * l + 2 * (t + 1) by omega]; exact hg'
  · rw [decide_eq_false (show ¬32 + 32 * t = 1024 by omega)] at hpc'
    simp only [Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨by omega, hpc'.trans (label_of_infix hp b3_in_code rfl), hctx, hl,
      by omega, (hreg .r13 (by simp)).trans hI.r13, (hreg .rbp (by simp)).trans hI.rbp,
      (hreg .r15 (by simp)).trans hI.r15, (hreg .rbx (by simp)).trans hI.rbx, ?_, ?_, ?_, hg'⟩)
    · rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
      show wl + BitVec.ofInt 64 0 = _
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    · rw [show reg st'.data .rcx = _ from hm'.regs .rcx _ hrcx']
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .rcx = _ from hI.rcx, add_ofNat']
      congr 1; omega
    · rw [show reg st'.data .rdx = _ from hm'.regs .rdx _ hrdx]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .rdx = _ from hI.rdx, add_ofNat']
      congr 1; omega

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
