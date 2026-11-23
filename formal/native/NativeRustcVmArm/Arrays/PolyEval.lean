module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Arrays.PolyEval.Exec

/-!
# `poly_eval` on AArch64

**`polyEval_spec`**: rustc's `poly_eval`, placed anywhere in the program, meets `PolyEvalPre`/
`PolyEvalPost` given `EW::mul`'s contract. The prologue (`b0`) saves X19-X24 and X30 in its
64-byte frame and points X21 at the last coefficient, X22 at `-16·len`; the loop (`b1`,
`EW::mul`, `b2`) takes the coefficients from the end, `acc·point + c` (`Inv`, Horner's rule as
`polyEval`'s `foldr`), until X22 reaches `0`: the loop is bottom-tested, so at least one
coefficient (`PolyEvalPre`); the epilogue (`b3`) returns the accumulator.
-/

namespace NativeRustcVmArm.Arrays.PolyEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PolyEval NativeVm.Model
open NativeRustcVm (ewsOf ewOf)

public section

/-- The coefficients at the entry. -/
abbrev coefs (m : MachineData) : List EW := ewsOf m.dmem m.regs.X0.toBitVec m.regs.X1.toNat
/-- Their number. -/
abbrev len (m : MachineData) : Nat := m.regs.X1.toNat
/-- The point. -/
abbrev pt (m : MachineData) : EW := ⟨m.regs.X2, m.regs.X3⟩

/-- Horner's rule on the last `t` coefficients. -/
def acc (m : MachineData) (t : Nat) : EW :=
  ((coefs m).drop (len m - t)).foldr (fun c acc ↦ acc * pt m + c) 0

theorem polyEval_eq_acc (m : MachineData) :
    polyEval (slice m m.regs.X0 m.regs.X1) (ewArg m.regs.X2 m.regs.X3) = acc m (len m) := by
  unfold slice acc polyEval
  rw [← Array.foldr_toList, Nat.sub_self, List.drop_zero]
  rfl

theorem lt_len {m : MachineData} {t : Nat} (h : t < len m) :
    len m - 1 - t < (coefs m).length := by
  simp only [coefs, len, NativeRustcVm.length_ewsOf] at h ⊢; omega

theorem acc_succ (m : MachineData) {t : Nat} (h : t < len m) :
    acc m (t + 1) = acc m t * pt m + (coefs m)[len m - 1 - t]'(lt_len h) := by
  unfold acc
  rw [show len m - (t + 1) = len m - 1 - t by omega,
    List.drop_eq_getElem_cons (lt_len h), List.foldr_cons,
    show len m - 1 - t + 1 = len m - t by omega]

/-- **The loop head** `.LPolyEval_1`, `t` coefficients folded. -/
structure Inv (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  body : Body m0 64 polyEvalStack slots 0 0 st
  lt : t < len m0
  x19 : st.regs.X19 = m0.regs.X3
  x20 : st.regs.X20 = m0.regs.X2
  x21 : st.regs.X21.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * (len m0 - 1 - t) + 8)
  x22 : st.regs.X22.toBitVec = 0#64 - BitVec.ofNat 64 (16 * (len m0 - t))
  acc : (⟨st.regs.X0, st.regs.X1⟩ : EW) = acc m0 t

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PolyEval.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PolyEval.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PolyEval.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PolyEval.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.PolyEval.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.PolyEval.entryOffset) NativeRustcVmArm.Vm.PolyEval.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.PolyEval.label_1 = Host.addrOf (k + NativeRustcVmArm.Vm.PolyEval.b1Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.PolyEval.b1Offset) NativeRustcVmArm.Vm.PolyEval.label_1_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ PolyEvalPost m0 st.data

/-- **The epilogue** `b3`: the accumulator returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : PolyEvalPre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PolyEval.b3Offset)) (hb : Body m0 64 polyEvalStack slots 0 0 st.data)
    (hacc : (⟨st.data.regs.X0, st.data.regs.X1⟩ : EW) = acc m0 (len m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hpre.1 (by decide) rfl
  refine exec_at (hb3 hp) run_b3 hwf hpc hm fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩)
    (after_eq run_b3 ▸ b3_restores) rfl
  refine ⟨?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · rw [polyEval_eq_acc, ← hacc]
    show (⟨st'.data.regs.getXReg .X0, st'.data.regs.getXReg .X1⟩ : EW) =
      ⟨st.data.regs.getXReg .X0, st.data.regs.getXReg .X1⟩
    rw [Match.reg_eq hm hm' rfl rfl, Match.reg_eq (r := .X1) hm hm' rfl rfl]
  · intro p hp'
    rw [hdm]
    exact hb.same p hp'

/-- **A turn of the loop**: `acc·point + c`, back at the head or out of the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PolyEvalPre m0) {t : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PolyEval.b1Offset)) (hI : Inv m0 t st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PolyEval.b1Offset) ∧ Inv m0 (t + 1) st'.data)) st := by
  obtain ⟨hS, h1, hrC, hoC⟩ := hpre
  have hlt := hI.lt
  have hL : len m0 = m0.regs.X1.toNat := rfl
  have hj : len m0 - 1 - t < m0.regs.X1.toNat := by omega
  have hnw : m0.regs.X0.toBitVec.toNat + 16 * m0.regs.X1.toNat ≤ 2 ^ 64 := hrC.2
  obtain ⟨st, pc⟩ := st
  -- the coefficient, the call
  refine load_step (lo := .X23) (hi' := .X24) (hb1 hp) run_b1 rfl rfl
    (after_eq run_b1 ▸ b1_facts.1) _ (after_eq run_b1 ▸ b1_facts.2) hI.body hS hrC hoC
    (apart_zero _ _) noWrap_zero hj hpc
    (by
      show st.regs.X21.toBitVec = _
      rw [hI.x21, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add])
    fun st2 hm2' hpc2 hb2' hC e2 ↦ ?_
  simp only [NativeRustcVmArm.Vm.PolyEval.b1_length, NativeRustcVmArm.Vm.PolyEval.b1Length] at hpc2
  refine call_then hpc2 hmul (hb2'.ewMulPre hS (by decide) (by decide)) fun st3 hpc3 hpost ↦ ?_
  have hb3' := hb2'.call hS (by decide) (by decide) hpost
  have hprod : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) = acc m0 t * pt m0 := by
    have hA : (⟨st2.data.regs.X0, st2.data.regs.X1⟩ : EW) = acc m0 t := by
      rw [← hI.acc]
      exact congr (congrArg EW.mk (e2 .X0 (by simp))) (e2 .X1 (by simp))
    have hP : (⟨st2.data.regs.X2, st2.data.regs.X3⟩ : EW) = pt m0 := by
      have h2 := hm2'.regs .X2 _ rfl
      have h3 := hm2'.regs .X3 _ rfl
      simp only [Sym.eval, Env.ofMachine_regs] at h2 h3
      show (⟨st2.data.regs.getXReg .X2, st2.data.regs.getXReg .X3⟩ : EW) = _
      rw [UInt64.toBitVec_inj.mp h2, UInt64.toBitVec_inj.mp h3]
      exact congr (congrArg EW.mk hI.x20) hI.x19
    rw [hpost.1, hpost.2.1, hA, hP]
    rfl
  have hc : (⟨st3.data.regs.X23, st3.data.regs.X24⟩ : EW) =
      (coefs m0)[len m0 - 1 - t]'(lt_len hlt) := by
    rw [← hC]
    exact congr (congrArg EW.mk (hpost.2.2.2.1 .X23 rfl)) (hpost.2.2.2.1 .X24 rfl)
  have e3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22], st3.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    have hcs : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl
    have hr' : r ∈ [XReg.X0, .X1, .X19, .X20, .X21, .X22] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp
    rw [hpost.2.2.2.1 r hcs, e2 r hr']
  -- `b2`: add the coefficient, advance, count
  refine exec_at (hb2 hp) run_b2 (Env.wf_nil _) hpc3 (match_nil _) fun st4 hm4 hpc4 ↦ ?_
  have hb4' := hb3'.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b2 ▸ b2_keeps)
  have h0 := hm4.regs .X0 _ rfl
  have h1' := hm4.regs .X1 _ rfl
  have h21 := hm4.regs .X21 _ rfl
  have h22 := hm4.regs .X22 _ rfl
  sym_simp at h0 h1' h21 h22
  simp only [Env.ofMachine_regs] at h0 h1' h21 h22
  have hacc : (⟨st4.data.regs.X0, st4.data.regs.X1⟩ : EW) = acc m0 (t + 1) := by
    rw [acc_succ m0 hI.lt, ← hprod, ← hc]
    show (⟨st4.data.regs.getXReg .X0, st4.data.regs.getXReg .X1⟩ : EW) = _
    rw [toBitVec_eq h0, toBitVec_eq h1']
    rfl
  have hx22 : (st3.data.regs.getXReg .X22).toBitVec = 0#64 - BitVec.ofNat 64 (16 * (len m0 - t)) := by
    rw [e3 .X22 (by simp)]; exact hI.x22
  have hx21 : (st3.data.regs.getXReg .X21).toBitVec =
      m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * (len m0 - 1 - t) + 8) := by
    rw [e3 .X21 (by simp)]; exact hI.x21
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  have hpc4' := pc_ne hpc4
  have hzero : (st3.data.regs.getXReg .X22).toBitVec + 16#64 = 0#64 ↔ t + 1 = len m0 := by
    rw [hx22]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at h'
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
  by_cases hlast : t + 1 = len m0
  · have hpc4 := hpc4'.2 (hzero.mpr hlast)
    simp only [NativeRustcVmArm.Vm.PolyEval.b2_length, NativeRustcVmArm.Vm.PolyEval.b2Length] at hpc4
    refine Eventually.mono (finish hp ⟨hS, h1, hrC, hoC⟩ hpc4 hb4' ?_) fun _ h ↦ Or.inl h
    rw [hacc, hlast]
  · have hpc4 := hpc4'.1 (fun h ↦ hlast (hzero.mp h))
    refine .done _ (Or.inr ⟨hpc4.trans (lbl_1 hp), hb4', by omega, ?_, ?_, ?_, ?_, hacc⟩)
    · have q : st4.data.regs.getXReg .X19 = st3.data.regs.getXReg .X19 :=
        Match.reg_eq (match_nil _) hm4 rfl rfl
      rw [e3 .X19 (by simp)] at q
      exact q.trans hI.x19
    · have q : st4.data.regs.getXReg .X20 = st3.data.regs.getXReg .X20 :=
        Match.reg_eq (match_nil _) hm4 rfl rfl
      rw [e3 .X20 (by simp)] at q
      exact q.trans hI.x20
    · show (st4.data.regs.getXReg .X21).toBitVec = _
      rw [h21, hx21]
      show m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * (len m0 - 1 - t) + 8) - BitVec.ofNat 64 16 =
        m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * (len m0 - 1 - (t + 1)) + 8)
      bv_omega
    · show (st4.data.regs.getXReg .X22).toBitVec = _
      rw [h22, hx22]
      show 0#64 - BitVec.ofNat 64 (16 * (len m0 - t)) + BitVec.ofNat 64 16 =
        0#64 - BitVec.ofNat 64 (16 * (len m0 - (t + 1)))
      bv_omega

/-- **`poly_eval` meets its contract.** -/
theorem polyEval_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hS, h1, hrC, hoC⟩ := hpre
  have hnw : m0.regs.X0.toBitVec.toNat + 16 * m0.regs.X1.toNat ≤ 2 ^ 64 := hrC.2
  have h64 : 64 ≤ polyEvalStack := by decide
  obtain ⟨hwf, hm⟩ := entry_match hS h64 rfl
  refine exec_then (hb0 hp) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.PolyEval.b0_length, NativeRustcVmArm.Vm.PolyEval.b0Length] at hpc1
  obtain ⟨hw, hmem, hregs⟩ := after_eq run_b0 ▸ b0_frame
  have hI : Inv m0 0 st1.data := by
    have h0 := hm1.regs .X0 _ rfl
    have h1' := hm1.regs .X1 _ rfl
    have h19 := hm1.regs .X19 _ rfl
    have h20 := hm1.regs .X20 _ rfl
    have h21 := hm1.regs .X21 _ rfl
    have h22 := hm1.regs .X22 _ rfl
    simp only [Sym.eval, lsl4] at h21 h22
    sym_simp at h0 h1' h19 h20 h21 h22
    simp only [Env.ofMachine_regs] at h19 h20 h21 h22
    refine ⟨Body.of_entry hS h64 hm1 rfl hw hregs hmem, h1, UInt64.toBitVec_inj.mp h19,
      UInt64.toBitVec_inj.mp h20, ?_, ?_, ?_⟩
    · show (st1.data.regs.getXReg .X21).toBitVec = _
      rw [h21]
      have e1 : (m0.regs.getXReg .X1).toBitVec.toNat = m0.regs.X1.toNat := rfl
      have e0 : (m0.regs.getXReg .X0).toBitVec = m0.regs.X0.toBitVec := rfl
      rw [e1, e0]
      show BitVec.ofNat 64 (16 * m0.regs.X1.toNat) + m0.regs.X0.toBitVec - BitVec.ofNat 64 8 =
        m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * (m0.regs.X1.toNat - 1 - 0) + 8)
      bv_omega
    · show (st1.data.regs.getXReg .X22).toBitVec = _
      rw [h22]
      rfl
    · show (⟨st1.data.regs.getXReg .X0, st1.data.regs.getXReg .X1⟩ : EW) = _
      rw [UInt64.toBitVec_inj.mp (h0.trans rfl), UInt64.toBitVec_inj.mp (h1'.trans rfl)]
      unfold acc
      rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp)]
      rfl
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PolyEval.b1Offset) ∧ ∃ t, len m0 - t = n ∧
    Inv m0 t st.data) (fun n st ⟨hpc, t, hn, hI⟩ ↦ ?_) ⟨hpc1, 0, rfl, hI⟩
  refine Eventually.mono (step hp hmul ⟨hS, h1, hrC, hoC⟩ hpc hI) fun st' h ↦ ?_
  rcases h with h | ⟨hpc', hI'⟩
  · exact Or.inl h
  · exact Or.inr ⟨len m0 - (t + 1), by have := hI'.lt; omega, hpc', t + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Arrays.PolyEval
