module

public import NativeRustcVmArm.Code.Vm.StackPoint.Names
public import NativeRustcVmArm.Ring.OptOut
public import NativeRustcVmArm.Ring.Column.Exec
public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `column_weight`: its frame, the prologue and `stack_point`

From the entry state `m0` (the `Option<EW>` at X0, the placement X1, X2, `point` X3, X4,
`stack_log` X5, `x` X6, X7): the frame (`CFr`: 1104 bytes, X19 to X21, X29, X30 saved from byte
`1056`, the stack point's 66 slots below), the state between the calls (`Mid`). `stepEntry`
(`b0`): the slots zeroed, `stack_point` into them.
-/

namespace NativeRustcVmArm.Ring.Column

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Vm.ColumnWeight NativeRustcVmArm.Whir

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(1056, .X29), (1072, .X30), (1080, .X21), (1088, .X20), (1096, .X19)]

/-- The callee-saved registers the prologue does not save. -/
def keep : List XReg := [.X22, .X23, .X24, .X25, .X26, .X27, .X28]

/-- The output's address. -/
def oA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec

/-- The frame (the output written by the last blocks only). -/
abbrev CFr (m0 m : MachineData) : Prop := Fr m0 1104 columnWeightStack slots keep (fun _ ↦ False) m

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 1104

/-- The environment after a call: the frame, the output. -/
abbrev envR (m0 m : MachineData) : Env := Env.ofMachine m [(fb m0, 1104), (oA m0, 24)]

/-- The stack point's length. -/
def nOf (m0 : MachineData) : Nat := m0.regs.X4.toNat + (m0.regs.X5.toNat - m0.regs.X1.toNat)

/-- The stack point. -/
def zOf (m0 : MachineData) : Array EW :=
  stackPoint (placementArg m0) (slice m0 m0.regs.X3 m0.regs.X4) m0.regs.X5.toNat

/-- **Between the calls**: the frame, the output in X19, `x` in X21, X20. -/
structure Mid (m0 m : MachineData) : Prop where
  fr : CFr m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : m.regs.getXReg .X20 = m0.regs.X7
  x21 : m.regs.getXReg .X21 = m0.regs.X6

end

public section

variable {m0 : MachineData}

theorem stack_eq : columnWeightStack = 1728 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1104 := by decide

theorem keep_cs : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem zOf_size : (zOf m0).size = nOf m0 := by
  simp [zOf, nOf, stackPoint, selectorPoint, slice, placementArg]

section
variable (h : ColumnWeightPre m0)
include h

theorem hN : columnWeightStack ≤ m0.regs.SP.toNat := h.1.2.1

theorem fbN : (fb m0).toNat = m0.regs.SP.toNat - 1104 :=
  base_toNat (by have := hN h; rw [stack_eq] at this; omega)

theorem fbw : NoWrap (fb m0) 1104 := base_noWrap (by have := hN h; rw [stack_eq] at this; omega)

theorem out_frame : Apart (oA m0) 24 (fb m0) 1104 := apart_frame (hN h) (by decide) h.2.2.2.1.2

/-- A range in the frame is apart from a callee's stack. -/
theorem apart_callee {m : MachineData} (hfr : CFr m0 m) {o n N' : Nat} (hon : o + n ≤ 1104)
    (hle : 1104 + N' ≤ columnWeightStack) :
    Apart (fb m0 + BitVec.ofNat 64 o) n (stackBelow m N') N' := by
  have h1 := fbN h
  have h2 := hN h
  have hSP := m0.regs.SP.toNat_lt
  rw [stackBelow_eq hfr.sp (by omega)]
  have h3 := base_toNat (m0 := m0) (F := 1104 + N') (by omega)
  unfold Apart
  rw [NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- Bytes apart from the stack are the entry's in every state of the frame. -/
theorem same_of {m : MachineData} (hfr : CFr m0 m) {a : BitVec 64} {n : Nat}
    (ha : Apart a n (stackBelow m0 columnWeightStack) columnWeightStack) (hw : NoWrap a n)
    {j : Nat} (hj : j < n) : m.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  hfr.same _ fun hq ↦ hq.elim (fun hq ↦ NativeRustcVm.Apart.not_inRange_add ha hw
    (base_noWrap (hN h)) hj hq) id

end

theorem envR_wf (h : ColumnWeightPre m0) {m : MachineData} (hfr : CFr m0 m) : (envR m0 m).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (frame_mapped h.1 (by decide) i hi), fbw h⟩,
    ⟨fun i hi ↦ hfr.kept _ (h.2.2.2.1.1.1 i hi), h.2.2.2.1.1.2⟩, trivial⟩
    (List.pairwise_pair.mpr (out_frame h).symm)

section
variable [Labels]

theorem matchR (h : ColumnWeightPre m0) {m : MachineData} (hM : Mid m0 m) :
    Match (envR m0 m) retS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), rfl,
      fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hM.fr.sp]; simp [Sym.eval])
    ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [hM.x19]; simp [Sym.eval, oA], trivial⟩
    trivial trivial trivial

theorem reg_of {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

end

theorem mem_low {S : SState} {F : Nat}
    (h : S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ F)) = true) :
    ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F := by
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

variable [Host] {k : Nat}

theorem hb {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hp : Placed code k) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **The prologue and `stack_point`** (`b0`). -/
theorem stepEntry (hp : Placed code k) (h : ColumnWeightPre m0)
    (hsp : Spec (Labels.label NativeRustcVmArm.Vm.StackPoint.entryLabel) StackPointPre StackPointPost)
    {R : MachineState → Prop}
    (cont : ∀ m2, Mid m0 m2 → (if nOf m0 ≤ 66 then m2.regs.X0 = 1 ∧ m2.regs.X1.toNat = nOf m0 ∧
        NativeRustcVm.EWsAt m2.dmem (fb m0) (zOf m0).toList else m2.regs.X0 = 0) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.ColumnWeight.b1Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.ColumnWeight.b0Offset)⟩ := by
  have hfw := fbw h
  have hfN := fbN h
  have hN' := hN h
  rw [stack_eq] at hN'
  have hSP := m0.regs.SP.toNat_lt
  have hwf : (Env.ofMachine m0 [(fb m0, 1104)]).WF :=
    Env.wf_of ⟨⟨frame_mapped h.1 (by decide), hfw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m0 [(fb m0, 1104)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), trivial⟩
      (by
        show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (1104 : Nat)
        rw [BitVec.ofInt_natCast, base_add_eq])
      trivial trivial trivial trivial
  refine exec_then (hb b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : CFr m0 st.data :=
    Fr.ofPrologue (rs := []) (hN h) (by decide) hm1 hwf rfl (by decide +kernel) slots_le
      (mem_low (by decide +kernel)) (fun r hr ↦ by
        simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have e0 : st.data.regs.X0 = m0.regs.X1 := reg_of hm1 (r := .X0) (v := .reg .X1) rfl rfl
  have e1 : st.data.regs.X1 = m0.regs.X2 := reg_of hm1 (r := .X1) (v := .reg .X2) rfl rfl
  have e2 : st.data.regs.X2 = m0.regs.X3 := reg_of hm1 (r := .X2) (v := .reg .X3) rfl rfl
  have e3 : st.data.regs.X3 = m0.regs.X4 := reg_of hm1 (r := .X3) (v := .reg .X4) rfl rfl
  have e4 : st.data.regs.X4 = m0.regs.X5 := reg_of hm1 (r := .X4) (v := .reg .X5) rfl rfl
  have e5 : st.data.regs.X5.toBitVec = fb m0 := by
    rw [show st.data.regs.X5 = st.data.regs.getXReg .X5 from rfl, hm1.regs .X5 (.ptr 0 0) rfl]
    simp [Sym.eval]
  -- the point, as at the entry
  have hpt := h.2.1
  have hpf : Apart (fb m0) 1104 m0.regs.X3.toBitVec (16 * m0.regs.X4.toNat) :=
    (apart_frame (hN h) (by decide) hpt.2).symm
  have hsl : slice st.data m0.regs.X3 m0.regs.X4 = slice m0 m0.regs.X3 m0.regs.X4 := by
    unfold slice
    rw [NativeRustcVm.ewsOf_congr fun j hj ↦ same_of h hfr1 hpt.2 hpt.1.2 hj]
  have hpre : StackPointPre st.data := by
    simp only [StackPointPre, SliceOk, Readable, OffStack, e2, e3, e5, stackPointOut]
    refine ⟨hfr1.stackOk h.1 (by decide) (by decide), ⟨⟨fun j hj ↦ hfr1.kept _ (hpt.1.1 j hj),
      hpt.1.2⟩, hfr1.apart (hN h) hpt.2 (by decide)⟩, ⟨fun j hj ↦ hfr1.kept _
      (frame_mapped h.1 (by decide) j (by omega)), by unfold NoWrap at *; omega⟩, ?_, ?_,
      h.2.2.2.2⟩
    · have := apart_callee h hfr1 (o := 0) (n := 16 * 66) (N' := stackPointStack) (by decide)
        (by decide)
      rwa [NativeRustcVm.addr_add_zero] at this
    · unfold Apart at *; omega
  refine Fr.leafIn hfr1 (hN h) (N' := stackPointStack) (lo := 0) (n := 1056) (by decide)
    (by decide) keep_cs (by decide) (fun _ h ↦ h.elim) hsp hpc hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ by
      rw [e5, NativeRustcVm.addr_add_zero] at *
      exact hq.elim (fun hq ↦ .inr (.inl hq)) .inl, hq.2.2⟩)
    fun m2 hfr2 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.ColumnWeight.b0Offset + b0.length = k + NativeRustcVmArm.Vm.ColumnWeight.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.ColumnWeight.b0_next]]
  refine cont m2 ⟨hfr2, ?_, ?_, ?_⟩ ?_
  · rw [hcs .X19 rfl]; exact reg_of hm1 (v := .reg .X0) rfl rfl
  · rw [hcs .X20 rfl]; exact reg_of hm1 (v := .reg .X7) rfl rfl
  · rw [hcs .X21 rfl]; exact reg_of hm1 (v := .reg .X6) rfl rfl
  · obtain ⟨hres, -, -⟩ := hq
    simp only [e0, e1, e2, e3, e4, e5, hsl, stackPointOut] at hres
    exact hres

end

end NativeRustcVmArm.Ring.Column
