module

public import NativeRustcVmX64.Ring.Psi.Basic
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.RingPsi.Names

/-!
# `ring_psi` on x86-64

`ringPsi_spec`: rustc's `ring_psi(value, g)`, placed anywhere in the program, given `EW::mul`'s
contract, returns `ringPsi value g`. rustc unrolled the loop over `g`'s 8 elements into 15 calls
of `EW::mul` (the products `P j` and the squarings `W (j + 1)`), keeping partial sums in registers
and spills: block `j` runs from the template `t<j>` with the values `v<j>` to the call
(`NativeRustcVmX64.Ring.mulStep`); the last block sums and returns.
-/

namespace NativeRustcVmX64.Ring.Psi

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingPsi

/-- The values a block leaves: each link's symbolic value, evaluated. -/
macro "vtac0" : tactic => `(tactic|
  (simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval,
    NativeRustcVmX64.Field.Lin.xor_apply]) <;> and_intros <;>
    (first | rfl | exact fun _ h ↦ nomatch h))

/-- `vtac0` for every state and return address. -/
macro "vtac" : tactic => `(tactic| (intro m ret) <;> vtac0)

@[expose] public section

variable [Host]

/-- Before the block at `off`: the template `T` with the values `vals`. -/
def At (m0 : MachineData) (k off : Nat) (T : SState) (vals : Nat → BitVec 64)
    (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + off) ∧ Bnd m0 80 ringPsiStack (rsOf m0) noWr T vals st.data

end

public section

variable [Host] {k : Nat} {m0 : MachineData}

/-- **A block and its call of `EW::mul`.** -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : RingPsiPre m0) {ds : List Directive} {off off' : Nat} (hds : ds.IsInfixAt code off)
    (hne : ds ≠ []) (hoff : off + ds.length = off') {T T' S' : SState}
    {vals vals' : Nat → BitVec 64} (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hwr : S'.mem.all (writeOk 80 [88, 128] noWr) = true) (hsp : S'.reg .rsp = some (.ptr 0 0))
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ m ret, ∀ p ∈ L ++ LW, p.2.eval (envS m0 m 80 (rsOf m0) vals ret) = vals' p.1)
    (hres : ∀ m, Bnd m0 80 ringPsiStack (rsOf m0) noWr T vals m → ∀ ret mc,
      (∀ r v, S'.reg r = some v → reg mc r = v.eval (envS m0 m 80 (rsOf m0) vals ret)) →
      mulRes mc = (vals' 6, vals' 7))
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hsz : T'.regions = [88, 128]) (hfl : T'.flags = atomFlags) (hlab : T'.labels = [])
    (hal : T'.aliases = []) (hbd : T'.bounds = []) {st : MachineState}
    (h : At m0 k off T vals st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k off' T' vals') st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := h
  simp only at hpc hB
  subst hpc
  refine mulStep (hknown := hknown) (lay hpre) hmul (by decide) hB (hds.trans hp.1 hne) hrun hwr hsp hL hLW
    (hvals d) (fun i hi mc hR ↦ ?_) (fun i hi mc hR ↦ ?_) hsz hfl hlab
    (fun _ _ x r o h ↦ by rw [hal] at h; cases h) hbd
    fun st hpc' hB' ↦ .done _ ⟨by rw [hpc', Nat.add_assoc, hoff], hB'⟩
  · rw [hrax] at hi
    cases hi
    rw [hres d hB _ mc hR]
  · rw [hrdx] at hi
    cases hi
    rw [hres d hB _ mc hR]

omit [Host] in
theorem sum_c0 : c0 (0 + P m0 0 + P m0 1 + P m0 2 + P m0 3 + P m0 4 + P m0 5 + P m0 6 + P m0 7) =
    c0 (P m0 7) ^^^ s06c0 m0 := by
  simp only [EW.add_def, c0, s06c0, s45c0, s03c0, s01c0, UInt64.toBitVec_xor]
  rw [show (0 : EW).c0.toBitVec = 0#64 from rfl, BitVec.zero_xor]
  ac_rfl

omit [Host] in
theorem sum_c1 : c1 (0 + P m0 0 + P m0 1 + P m0 2 + P m0 3 + P m0 4 + P m0 5 + P m0 6 + P m0 7) =
    c1 (P m0 7) ^^^ s06c1 m0 := by
  simp only [EW.add_def, c1, s06c1, s45c1, s03c1, s01c1, UInt64.toBitVec_xor]
  rw [show (0 : EW).c1.toBitVec = 0#64 from rfl, BitVec.zero_xor]
  ac_rfl

/-- **`ring_psi`'s contract.** -/
theorem ringPsi_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.RingPsi.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.RingPsi.b0Offset) from hp.label NativeRustcVmX64.Vm.RingPsi.entry_at]
  have h0 : Bnd m0 80 ringPsiStack (rsOf m0) noWr t0 (fun _ ↦ 0) m0 :=
    start rfl fun ret ↦ ⟨(Field.frame_rsp 80 0).trans (BitVec.add_zero _) |>.symm, by
      show reg m0 .rdx = gA m0 + BitVec.ofInt 64 0
      simp, trivial⟩
  refine mulStep (lay hpre) hmul (by decide) h0 (b0_in_code.trans hp.1 (by simp [b0])) run_b0
    rfl rfl (T' := t1) (vals' := v1 m0) rfl rfl (fun ret ↦ by vtac0)
    (fun i hi mc hR ↦ ?_) (fun i hi mc hR ↦ ?_) rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st hpc hB ↦ ?_
  · cases hi
    exact congrArg Prod.fst (mulRes_of (x := gE m0 0) (y := W m0 0) hR rfl rfl rfl rfl
      (gl0 hpre h0 (j := 0) (by decide) _) (gl1 hpre h0 (j := 0) (by decide) _) rfl rfl)
  · cases hi
    exact congrArg Prod.snd (mulRes_of (x := gE m0 0) (y := W m0 0) hR rfl rfl rfl rfl
      (gl0 hpre h0 (j := 0) (by decide) _) (gl1 hpre h0 (j := 0) (by decide) _) rfl rfl)
  have h : At m0 k NativeRustcVmX64.Vm.RingPsi.b1Offset t1 (v1 m0) st := ⟨hpc, hB⟩
  clear hpc hB
  refine Eventually.bind (step hp hmul hpre b1_in_code (by simp [b1]) rfl (T' := t2)
    (vals' := v2 m0) run_b1 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := W m0 0) (y := W m0 0) hR rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b2_in_code (by simp [b2]) rfl (T' := t3)
    (vals' := v3 m0) run_b2 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := gE m0 1) (y := W m0 1) hR rfl rfl rfl rfl (gl0 hpre hB (j := 1) (by decide) ret) (gl1 hpre hB (j := 1) (by decide) ret) rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b3_in_code (by simp [b3]) rfl (T' := t4)
    (vals' := v4 m0) run_b3 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := W m0 1) (y := W m0 1) hR rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b4_in_code (by simp [b4]) rfl (T' := t5)
    (vals' := v5 m0) run_b4 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := gE m0 2) (y := W m0 2) hR rfl rfl rfl rfl (gl0 hpre hB (j := 2) (by decide) ret) (gl1 hpre hB (j := 2) (by decide) ret) rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b5_in_code (by simp [b5]) rfl (T' := t6)
    (vals' := v6 m0) run_b5 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := W m0 2) (y := W m0 2) hR rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b6_in_code (by simp [b6]) rfl (T' := t7)
    (vals' := v7 m0) run_b6 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := gE m0 3) (y := W m0 3) hR rfl rfl rfl rfl (gl0 hpre hB (j := 3) (by decide) ret) (gl1 hpre hB (j := 3) (by decide) ret) rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b7_in_code (by simp [b7]) rfl (T' := t8)
    (vals' := v8 m0) run_b7 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := W m0 3) (y := W m0 3) hR rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b8_in_code (by simp [b8]) rfl (T' := t9)
    (vals' := v9 m0) run_b8 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := gE m0 4) (y := W m0 4) hR rfl rfl rfl rfl (gl0 hpre hB (j := 4) (by decide) ret) (gl1 hpre hB (j := 4) (by decide) ret) rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b9_in_code (by simp [b9]) rfl (T' := t10)
    (vals' := v10 m0) run_b9 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := W m0 4) (y := W m0 4) hR rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b10_in_code (by simp [b10]) rfl (T' := t11)
    (vals' := v11 m0) run_b10 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := gE m0 5) (y := W m0 5) hR rfl rfl rfl rfl (gl0 hpre hB (j := 5) (by decide) ret) (gl1 hpre hB (j := 5) (by decide) ret) rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b11_in_code (by simp [b11]) rfl (T' := t12)
    (vals' := v12 m0) run_b11 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := W m0 5) (y := W m0 5) hR rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b12_in_code (by simp [b12]) rfl (T' := t13)
    (vals' := v13 m0) run_b12 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := gE m0 6) (y := W m0 6) hR rfl rfl rfl rfl (gl0 hpre hB (j := 6) (by decide) ret) (gl1 hpre hB (j := 6) (by decide) ret) rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b13_in_code (by simp [b13]) rfl (T' := t14)
    (vals' := v14 m0) run_b13 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := W m0 6) (y := W m0 6) hR rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  refine Eventually.bind (step hp hmul hpre b14_in_code (by simp [b14]) rfl (T' := t15)
    (vals' := v15 m0) run_b14 rfl rfl rfl rfl (by vtac)
    (fun m hB ret mc hR ↦ mulRes_of (x := gE m0 7) (y := W m0 7) hR rfl rfl rfl rfl (gl0 hpre hB (j := 7) (by decide) ret) (gl1 hpre hB (j := 7) (by decide) ret) rfl rfl) rfl rfl
    rfl rfl rfl rfl rfl h) fun st h ↦ ?_
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := h
  simp only at hpc hB
  subst hpc
  refine exitStep (lay hpre) hB (b15_in_code.trans hp.1 (by simp [b15])) run_b15 rfl rfl
    (fun r hr ↦ ?_) fun st hm hret hrsp hso hsv ↦ .done _ ⟨hret, hrsp, ?_, ?_, hsv⟩
  · cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr <;> exact ⟨_, rfl, rfl⟩
  · have e0 : reg st.data .rax = c0 (P m0 7) ^^^ s06c0 m0 := by
      rw [show reg st.data .rax = _ from hm.regs .rax _ rfl]
      simp only [Sym.eval, Field.Lin.xor_apply]
      rfl
    have e1 : reg st.data .rdx = c1 (P m0 7) ^^^ s06c1 m0 := by
      rw [show reg st.data .rdx = _ from hm.regs .rdx _ rfl]
      simp only [Sym.eval, Field.Lin.xor_apply]
      rfl
    show ewArg (reg st.data .rax) (reg st.data .rdx) = ringPsi (vE m0) (arr m0 (gA m0) ringWidth)
    rw [psi_eq, e0, e1, ← sum_c0, ← sum_c1]
    simp only [ewArg, c0, c1, UInt64.ofBitVec_toBitVec]
  · intro p hp'
    exact hso p fun hin ↦ hp' (hin.elim .inr fun ⟨_, _, he, _⟩ ↦ by cases he)

end

end NativeRustcVmX64.Ring.Psi
