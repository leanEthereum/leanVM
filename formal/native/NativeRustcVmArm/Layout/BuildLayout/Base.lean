module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Layout.BuildLayout.Lemmas

/-!
# `build_layout`: the state, the epilogue, the failures, the stores of the sizes

`b0` tests the bytecode's length `n` a power of two (`b19`: `0`). The prologue (`b1`) saves
X19-X30 in the 1360-byte frame and calls `bit_length(n)`; `b2` to `b8` check the sizes (a failure,
`b20`, `b21`: `0`, `fail`). Then the layout's sizes, heights and rows are stored (`b9` to `b15`,
each height a call of `bit_length`, `blk`), `column_kappas` fills the frame's `kappas`,
`placements_of` the layout's placements, `b18` stores the stack's log-size and `b21` returns `1`:
the model's `buildLayout`, its checks passed (`NativeVm.Math.Layout.buildLayout_eq`, `layoutF_facts`).
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BuildLayout
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript (off)
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

variable [Host] {k : Nat}

/-! ## The state -/

/-- The stack. -/
abbrev SS : Nat := buildLayoutStack
/-- The layout. -/
abbrev ll (m0 : MachineData) : BitVec 64 := m0.regs.X3.toBitVec
/-- The row counts' address. -/
abbrev rp (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec
/-- The row counts. -/
abbrev rowsOf (m0 : MachineData) : Array Nat := natsOf m0 m0.regs.X2 nTables
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 1360
/-- A body of `build_layout`. -/
abbrev Bd (m0 st : MachineData) : Prop := Body m0 1360 SS slots (ll m0) layoutBytes st

omit [Host] in
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1360 := by decide
omit [Host] in
theorem slots_top : ∀ p ∈ slots, 1360 - 96 ≤ p.1 ∧ p.1 + 8 ≤ 1360 := by decide

/-- `build_layout`'s postcondition, reached. -/
abbrev Post (bc : Array UInt64) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ BuildLayoutPost bc m0 st.data

/-- The facts of the precondition the blocks use. -/
structure Facts (bc : Array UInt64) (m0 : MachineData) : Prop where
  stack : StackOk m0 SS
  rod : RodataAt m0 SS
  size : m0.regs.X0.toNat = bc.size
  rr : Readable m0 (rp m0) 48
  ro : OffStack m0 (rp m0) 48 SS
  lr : Readable m0 (ll m0) layoutBytes
  lo : OffStack m0 (ll m0) layoutBytes SS
  lrod : RodataApart (ll m0) layoutBytes
  ap : Apart (rp m0) 48 (ll m0) layoutBytes

theorem Facts.of_pre {bc : Array UInt64} {m0 : MachineData} (h : BuildLayoutPre bc m0) :
    Facts bc m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem Facts.sp {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) :
    1360 ≤ m0.regs.SP.toNat := by
  have := hF.stack.2.1
  have : 1360 ≤ SS := by decide
  omega

theorem pc_of {pc : Int64} {a b : Nat} (h : pc = Host.addrOf a) (e : a = b) : pc = Host.addrOf b :=
  e ▸ h

/-! ## The epilogue -/

omit [Host] in
theorem and1 (x : UInt64) (h : x = 0 ∨ x = 1) :
    UInt64.ofBitVec (BinOp.apply .and .W32 x.toBitVec (BitVec.ofNat 64 1)) = x := by
  rcases h with rfl | rfl <;> rfl

/-- **The epilogue** `b21`: X0 (`0` or `1`) returned, the frame popped. -/
theorem epi (hp : Placed code k) {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b21Offset)) (hb : Bd m0 st.data)
    (hx : st.data.regs.X0 = 0 ∨ st.data.regs.X0 = 1) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ s.data.regs.X0 = st.data.regs.X0 ∧
      Changes m0 s.data SS (ll m0) layoutBytes ∧ Saved m0 s.data ∧ s.data.dmem = st.data.dmem) st := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hF.stack (by decide) (by decide)
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) run_b21 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(1272, .X30), by simp [slots], rfl⟩)
    (Arrays.after_eq run_b21 ▸ b21_restores).1 (Arrays.after_eq run_b21 ▸ b21_restores).2
  refine ⟨?_, ?_, fun q hq ↦ by rw [hdm]; exact hb.same q hq, hsaved, hdm⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · have h0 := hm'.regs .X0 _ rfl
    rw [show st'.data.regs.X0 = UInt64.ofBitVec _ from Arrays.toBitVec_eq h0]
    exact and1 _ hx

/-- **A failed check** (`.L11`): `b20`, `b21` return `0`. -/
theorem fail (hp : Placed code k) {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b20Offset)) (hb : Bd m0 st.data)
    (hr : buildLayout bc m0.regs.X1.toNat (rowsOf m0) = none) :
    Eventually (step1 Host.exe) (Post bc m0) st := by
  refine exec_at (infix_of b20_in_code (by simp [b20]) hp) run_b20 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hb1 := hb.of_block (match_nil _) hm1 (Env.wf_nil _) rfl (Arrays.after_eq run_b20 ▸ b20_keeps)
  have h0 : st1.data.regs.X0 = 0 := UInt64.toBitVec_inj.mp ((hm1.regs .X0 _ rfl).trans rfl)
  simp only [PcOk] at hpc1
  refine Eventually.mono (epi hp hF (pc_of hpc1 rfl) hb1 (.inl h0)) fun s ⟨h1, h2, h3, h4, _⟩ ↦
    ⟨h1, ?_, fun L hL ↦ absurd hL (by rw [hr]; nofun), h3, h4⟩
  rw [h2, h0, hr]; rfl

/-! ## The layout's first 120 bytes -/

/-- The layout's first 120 bytes, a region of a body's state. -/
theorem Facts.wf_lay {bc : Array UInt64} {m0 st : MachineData} (hF : Facts bc m0)
    (hb : Bd m0 st) : (Env.ofMachine st [(ll m0, 120)]).WF :=
  Arrays.wf_one (fun i hi ↦ hb.kept _ (hF.lr.1 i (by unfold layoutBytes placementBytes columnCountW; omega)))
    (NativeRustcVm.NoWrap.mono hF.lr.2 (by decide))

omit [Host] in
theorem satsub_eval (x : BitVec 64) {inst : Decidable (x.ult (BitVec.ofNat 64 1) = true)} :
    (@ite _ (x.ult (BitVec.ofNat 64 1) = true) inst (BitVec.ofNat 64 0) (x - BitVec.ofNat 64 1)).toNat =
      x.toNat - 1 := by
  rw [Arrays.ite_bool]
  by_cases h : x.toNat = 0
  · have : x.ult (BitVec.ofNat 64 1) = true := by simp [BitVec.ult, h]
    rw [this]; simp [h]
  · have : x.ult (BitVec.ofNat 64 1) = false := by simp [BitVec.ult]; omega
    rw [this, Bool.cond_false, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    simp

omit [Host] in
/-- A call of `bit_length` changes no byte. -/
theorem bl_same {st st' : MachineData} (h : BitLengthPost st st') : st'.dmem = st.dmem :=
  Std.ExtHashMap.ext_getElem? fun a ↦ by
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    exact h.2.1 a fun hr ↦ absurd hr (by unfold InRange bitLengthStack; omega)

/-- **A block storing two words of the layout, then `bit_length` of a row count less one.** -/
theorem blk (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) {bc : Array UInt64}
    {m0 : MachineData} (hF : Facts bc m0) {b : List Directive} {kb : Nat} {S₀ S' : SState}
    (hbk : b.IsInfixAt Host.prog kb) (hx : exec b S₀ = some (S', .call NativeRustcVmArm.Vm.BitLength.entryLabel))
    (hk : keepsAll S₀ { S' with mem := [] } keptRegs = true) (hin : InR0 S' 120 = true)
    {rs : List XReg} (hkeep : keepR S₀ S' rs = true) (hcs : ∀ r ∈ rs, calleeSaved r = true)
    {ws : List (Nat × UInt64)} (hws : ∀ p ∈ ws, p.1 + 8 ≤ 120)
    (hmiss : Misses S' (ws.map (·.1)) = true) {o1 o2 : Nat} {r1 r2 rr : XReg}
    (ho1 : o1 + 8 ≤ 120) (ho2 : o2 + 8 ≤ 120)
    (hw1 : ∀ i < 8, findWrite 0 (o1 + i) S'.mem = some (.reg r1, i))
    (hw2 : ∀ i < 8, findWrite 0 (o2 + i) S'.mem = some (.reg r2, i))
    (h0 : S'.reg .X0 = some (Sym.ite (SBool.cmp .ult .W64 (.reg rr) (.lit 1)) (.lit 0)
      (.bin .sub .W64 (.reg rr) (.lit 1))))
    {o21 : Int} (hx21 : S'.reg .X21 = some (.ptr 0 o21))
    {st : MachineState} (hpc : st.pc = Host.addrOf kb) (hbd : Bd m0 st.data)
    (hm : Match (Env.ofMachine st.data [(ll m0, 120)]) S₀ st.data)
    (hW : Ws st.data.dmem (ll m0) ws) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (kb + b.length) → Bd m0 st'.data →
      Ws st'.data.dmem (ll m0) ((o1, st.data.regs.getXReg r1) :: (o2, st.data.regs.getXReg r2) :: ws) →
      (∀ r ∈ rs, st'.data.regs.getXReg r = st.data.regs.getXReg r) →
      st'.data.regs.X0.toNat = bitLength ((st.data.regs.getXReg rr).toNat - 1) →
      st'.data.regs.X21.toBitVec = ll m0 + BitVec.ofInt 64 o21 →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := hF.wf_lay hbd
  refine exec_at hbk hx hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [InR0, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hin
  have hb1 : Bd m0 st1.data := Layout.Body.of_write' hbd hF.stack hm hm1 hwf
    (fun p hp ↦ NativeRustcVm.InRange.mono hp (NativeRustcVm.NoWrap.mono hF.lr.2 (by decide)) hF.lr.2
      (Nat.le_refl _) (by unfold layoutBytes placementBytes columnCountW; omega))
    hk hin (NativeRustcVm.Apart.mono_right hF.lo.symm (Nat.le_refl _) (by
      unfold layoutBytes placementBytes columnCountW; omega) |>.symm) slots_le (by decide)
  have hW1 : Ws st1.data.dmem (ll m0) ((o1, st.data.regs.getXReg r1) :: (o2, st.data.regs.getXReg r2) :: ws) :=
    Ws.cons (Arrays.wordAt_of_write hm1 ho1 hw1) (Ws.cons (Arrays.wordAt_of_write hm1 ho2 hw2)
      (Ws.keep hm1 hwf hws hW hmiss))
  have hr1 := Arrays.regs_eq_of hm hm1 rs hkeep
  have hx0 : st1.data.regs.X0.toNat = (st.data.regs.getXReg rr).toNat - 1 := by
    have := hm1.regs .X0 _ h0
    sym_simp at this
    show (st1.data.regs.getXReg .X0).toBitVec.toNat = _
    rw [this, satsub_eval]
    rfl
  refine call_then hpc1 hbl trivial fun st2 hpc2 hpost ↦ cont st2 hpc2 ?_ ?_ ?_ ?_ ?_
  · exact Body.of_call_stack (G := 96) hb1 hpost.2.1
      (fun p hp ↦ absurd hp (by unfold InRange bitLengthStack; omega)) hpost.2.2 slots_top (by decide) hF.sp
  · rw [bl_same hpost]; exact hW1
  · intro r hr; rw [hpost.2.2.1 r (hcs r hr)]; exact hr1 r hr
  · rw [hpost.1, hx0]
  · show (st2.data.regs.getXReg .X21).toBitVec = _
    rw [hpost.2.2.1 .X21 rfl, hm1.regs .X21 _ hx21]
    rfl

end

end NativeRustcVmArm.Layout.BuildLayout
