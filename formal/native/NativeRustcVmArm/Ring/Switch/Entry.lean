module

public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Ring.Switch.Steps

/-!
# `ring_switch`: the prologue, the grind, the branch on its result

`stepEntry` (`b0`): the registers saved, `grind(13)`; `stepBranch` (`b1`): to the epilogue on
`None`, on to the challenges (`G1`) on `Some`.
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.RingSwitch

@[expose] public section

/-- **Between the calls**: the frame, the `RingW` in X19, `s` in X20, the `TState` in X21
representing `s1`. -/
structure G1 (a : DecArea) (s1 : TState) (m0 m : MachineData) : Prop where
  fr : SFr m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X2
  x20 : m.regs.getXReg .X20 = m0.regs.X1
  x21 : m.regs.getXReg .X21 = m0.regs.X0
  ts : TStateAt m.dmem (tA m0) a s1

end

public section

variable {m0 : MachineData} {a : DecArea} {s : TState}

/-- A byte a block wrote: in region 0's first `F` bytes. -/
theorem written_frame [Labels] {env : Env} {S : SState} {q b : BitVec 64} {F : Nat}
    (hq : Written env S q) (h0 : env.regions[0]? = some (b, F))
    (hm : S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ F)) = true) :
    b.toNat ≤ q.toNat ∧ q.toNat < b.toNat + F := by
  obtain ⟨w, hw, b', sz, hb, h1, h2⟩ := hq
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
  obtain ⟨hr, hn⟩ := hm w hw
  rw [hr, h0] at hb
  cases hb
  omega

theorem frame_within [Labels] (h : RingSwitchPre a s m0) {q : BitVec 64}
    (hq : (fb m0).toNat ≤ q.toNat ∧ q.toNat < (fb m0).toNat + 432) : Within m0 q := by
  have := fbN h
  have := hN h
  rw [stack_eq] at *
  exact .inl (by rw [Sym.inRange_iff (nw_stack h), base_toNat (hN h), stack_eq]; omega)

variable [Host] {k : Nat}

theorem hb {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hp : Placed code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **The prologue and the grind** (`b0`). -/
theorem stepEntry (hp : Placed code k) (h : RingSwitchPre a s m0)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {R : MachineState → Prop}
    (cont : ∀ m2, SFr m0 m2 → m2.regs.getXReg .X19 = m0.regs.X2 →
      m2.regs.getXReg .X20 = m0.regs.X1 → m2.regs.getXReg .X21 = m0.regs.X0 →
      m2.regs.X0 = okWord ((grind LeanVM.Parameters.Whir.batchGrindingBits).run s).isSome →
      NextAt m2.dmem (tA m0) a ((grind LeanVM.Parameters.Whir.batchGrindingBits).run s) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b1Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b0Offset)⟩ := by
  have hwf : (Env.ofMachine m0 [(fb m0, 432)]).WF :=
    Env.wf_of ⟨⟨frame_mapped h.1 (by decide), fbw h⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m0 [(fb m0, 432)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), trivial⟩
      (by
        show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (432 : Nat)
        rw [BitVec.ofInt_natCast, base_add_eq])
      trivial trivial trivial trivial
  refine exec_then (hb b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : SFr m0 st.data :=
    Fr.ofPrologue (rs := []) (hN h) (by decide) hm1 hwf rfl (by decide) slots_le (by decide)
      (fun r hr ↦ by
        simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have hts : TStateAt st.data.dmem (tA m0) a s :=
    ts_keep h h.2.2.1 (hm1.kept hwf) (hm1.sameOutside hwf) fun q hq ↦
      frame_within h (written_frame hq rfl (by decide))
  have e0 : st.data.regs.X0 = m0.regs.X0 := Match.reg_eq hm hm1 (r := .X0) rfl rfl
  have e1 : st.data.regs.X1 = 13 := reg_of hm1 (r := .X1) (v := .lit 13) rfl rfl
  have hbits : grindBits st.data = LeanVM.Parameters.Whir.batchGrindingBits := by
    unfold grindBits; rw [e1]; rfl
  refine Fr.leafAt hfr1 (hN h) (N' := grindStack) (by decide) keep_cs slots_le (outs_frame h)
    (hgr a s) hpc ⟨hfr1.stackOk h.1 (by decide) (by decide), rc_of h hfr1 (by decide), by
      show TStateAt _ st.data.regs.X0.toBitVec a s; rw [e0]; exact hts, by
      show TStateOk _ st.data.regs.X0.toBitVec a _; rw [e0]; exact tok_of h hfr1 (by decide),
      by rw [hbits]; decide⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq ↦ hq.elim
      (fun ht ↦ .inr (.inr (by rw [e0] at ht; exact ht))) .inl, hq.2.2.2⟩)
    fun m2 hfr2 hq hcs ↦ ?_
  obtain ⟨q0, qn, -, -⟩ := hq
  rw [hbits] at q0 qn
  rw [show k + NativeRustcVmArm.Vm.RingSwitch.b0Offset + b0.length = k + NativeRustcVmArm.Vm.RingSwitch.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingSwitch.b0_next]]
  refine cont m2 hfr2 ?_ ?_ ?_ q0 (by rw [show tA m0 = st.data.regs.X0.toBitVec by rw [e0]; rfl]; exact qn)
  · rw [hcs .X19 rfl]; exact reg_of hm1 (v := .reg .X2) rfl rfl
  · rw [hcs .X20 rfl]; exact reg_of hm1 (v := .reg .X1) rfl rfl
  · rw [hcs .X21 rfl]; exact reg_of hm1 (v := .reg .X0) rfl rfl

/-- **The branch on the grind** (`b1`): its value in X0, `okWord b`; the `TState` represents
`s1` when the grind succeeded. -/
theorem stepBranch (hp : Placed code k) (h : RingSwitchPre a s m0) {m : MachineData}
    (hfr : SFr m0 m) (h19 : m.regs.getXReg .X19 = m0.regs.X2)
    (h20 : m.regs.getXReg .X20 = m0.regs.X1) (h21 : m.regs.getXReg .X21 = m0.regs.X0)
    {s1 : TState} {b : Bool} (hts : b = true → TStateAt m.dmem (tA m0) a s1)
    (hx0 : m.regs.X0 = okWord b) {R : MachineState → Prop}
    (hnone : ∀ m', SFr m0 m' → m'.dmem = m.dmem → m'.regs.X0 = okWord b → b = false →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b6Offset)⟩)
    (hsome : ∀ m', G1 a s1 m0 m' → m'.regs.X0 = okWord b → b = true →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b2Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b1Offset)⟩ := by
  have hwf := envM_wf h hfr
  refine exec_then (hb b1_in_code (by simp [b1]) hp) run_b1 hwf (matchM h hfr)
    fun st hm1 hpc ↦ ?_
  have hfr1 : SFr m0 st.data :=
    hfr.ofBlock (matchM h hfr) hm1 hwf rfl rfl rfl (keep_ok (by decide) (by decide))
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have e0 : st.data.regs.X0 = m.regs.X0 := Match.reg_eq (matchM h hfr) hm1 (r := .X0) rfl rfl
  have e19 := (Match.reg_eq (matchM h hfr) hm1 (r := .X19) rfl rfl).trans h19
  have e20 := (Match.reg_eq (matchM h hfr) hm1 (r := .X20) rfl rfl).trans h20
  have e21 := (Match.reg_eq (matchM h hfr) hm1 (r := .X21) rfl rfl).trans h21
  obtain ⟨d, pc⟩ := st
  simp only at hfr1 hd e0 e19 e20 e21 hm1
  cases b
  · have hc : (!(low RegWidth.W32 (okWord false).toBitVec).getLsbD 0) = true := by decide
    simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs,
      show m.regs.getXReg .X0 = m.regs.X0 from rfl, hx0, hc, ↓reduceIte] at hpc
    subst hpc
    rw [show Labels.label NativeRustcVmArm.Vm.RingSwitch.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.RingSwitch.b6Offset) from hp.label (j := NativeRustcVmArm.Vm.RingSwitch.b6Offset) NativeRustcVmArm.Vm.RingSwitch.label_2_at]
    exact hnone d hfr1 hd (e0.trans hx0) rfl
  · have hc : (!(low RegWidth.W32 (okWord true).toBitVec).getLsbD 0) = false := by decide
    simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs,
      show m.regs.getXReg .X0 = m.regs.X0 from rfl, hx0, hc, Bool.false_eq_true,
      ↓reduceIte] at hpc
    subst hpc
    exact hsome d ⟨hfr1, e19, e20, e21, by rw [hd]; exact hts rfl⟩ (e0.trans hx0) rfl

end

end NativeRustcVmArm.Ring.Switch
