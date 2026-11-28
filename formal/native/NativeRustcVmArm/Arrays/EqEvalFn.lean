module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Arrays.EqEvalFn.Exec
public import NativeRustcVm.Arrays.Folds

/-!
# `eq_eval_fn` with `eq_above`'s closure on AArch64

**`eqEvalFn_spec`**: rustc's `eq_eval_fn(n, |k| bit_e(selector, k), right)`, placed anywhere in
the program, meets `EqEvalFnOfEqAbovePre`/`EqEvalFnOfEqAbovePost` given `EW::mul`'s contract: the
value is `eqEval (selectorPoint selector n) right`. The prologue (`b0`) saves X19-X22 and X30 in
its 48-byte frame and takes `min n |right|`; at `0` it returns `1` (`b5`); else the loop (`b2`,
`EW::mul`, `b3`) multiplies the accumulator (X0, X1) by `1 + bit_e(selector, k) + right[k]`
(`Inv`; `bit_e` is `lsr`, `and #1`, bit `k` of the selector for `k < 64`), and the epilogue (`b4`)
returns it.
-/

namespace NativeRustcVmArm.Arrays.EqEvalFn

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EqEvalFnOfEqAbove NativeVm.Model
open NativeRustcVm (ewsOf ewOf)

public section

/-- The left side: the selector's bits. -/
abbrev lft (m : MachineData) : List EW := (selectorPoint m.regs.X1.toNat m.regs.X0.toNat).toList
/-- The right slice at the entry. -/
abbrev rgt (m : MachineData) : List EW := ewsOf m.dmem m.regs.X2.toBitVec m.regs.X3.toNat
/-- The common length. -/
abbrev cnt (m : MachineData) : Nat := min m.regs.X0.toNat m.regs.X3.toNat

theorem length_lft (m : MachineData) : (lft m).length = m.regs.X0.toNat := by
  simp [lft, selectorPoint]

theorem lt_l {m : MachineData} {i : Nat} (h : i < cnt m) : i < (lft m).length := by
  rw [length_lft]; exact Nat.lt_of_lt_of_le h (Nat.min_le_left _ _)

theorem lt_r {m : MachineData} {i : Nat} (h : i < cnt m) : i < (rgt m).length := by
  simp only [rgt, NativeRustcVm.length_ewsOf]; exact Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)

theorem getElem_lft (m : MachineData) {i : Nat} (h : i < (lft m).length) :
    (lft m)[i] = EW.ofNat ((m.regs.X1.toNat >>> i) % 2) := by
  simp [lft, selectorPoint]

/-- The product of the first `i` factors. -/
def acc (m : MachineData) (i : Nat) : EW :=
  (List.zipWith (fun x z ↦ 1 + x + z) ((lft m).take i) ((rgt m).take i)).foldl (· * ·) 1

theorem eqEval_eq_acc (m : MachineData) :
    eqEval (selectorPoint m.regs.X1.toNat m.regs.X0.toNat) (slice m m.regs.X2 m.regs.X3) =
      acc m (cnt m) := by
  unfold slice acc
  rw [← @Array.toArray_toList _ (selectorPoint _ _), NativeRustcVm.eqEval_eq,
    NativeRustcVm.zipWith_take_min, length_lft]
  simp

theorem acc_succ (m : MachineData) {i : Nat} (h : i < cnt m) :
    acc m (i + 1) = acc m i * (1 + (lft m)[i]'(lt_l h) + (rgt m)[i]'(lt_r h)) :=
  NativeRustcVm.zipFold_take_succ _ _ _ _ _ _ _

/-- **The loop head** `.LEqEvalFnOfEqAbove_2`, `i` factors multiplied. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 eqEvalFnStack slots 0 0 st
  lt : i < cnt m0
  x19 : st.regs.X19 = m0.regs.X1
  x20 : st.regs.X20.toNat = cnt m0
  x22 : st.regs.X22.toNat = i
  x21 : st.regs.X21.toBitVec = m0.regs.X2.toBitVec + BitVec.ofNat 64 (16 * i + 8)
  acc : (⟨st.regs.X0, st.regs.X1⟩ : EW) = acc m0 i

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryOffset) NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2Offset) NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.label_2_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b5Offset) NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.label_4_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ EqEvalFnOfEqAbovePost m0 st.data

/-- **The epilogue** `b4`: from the loop's exit, the product returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : EqEvalFnOfEqAbovePre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b4Offset))
    (hb : Body m0 48 eqEvalFnStack slots 0 0 st.data)
    (hacc : (⟨st.data.regs.X0, st.data.regs.X1⟩ : EW) = acc m0 (cnt m0)) :
    Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hpre.1 (by decide) rfl
  refine exec_at (hb4 hp) run_b4 hwf hpc hm fun st' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩)
    (after_eq run_b4 ▸ b4_restores) rfl
  refine ⟨?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · rw [eqEval_eq_acc, ← hacc]
    show (⟨st'.data.regs.getXReg .X0, st'.data.regs.getXReg .X1⟩ : EW) =
      ⟨st.data.regs.getXReg .X0, st.data.regs.getXReg .X1⟩
    rw [Match.reg_eq hm hm' rfl rfl, Match.reg_eq (r := .X1) hm hm' rfl rfl]
  · intro p hp'
    rw [hdm]
    exact hb.same p hp'

/-- **A turn of the loop**: the accumulator multiplied by `1 + bit_e(selector, i) + right[i]`, back
at the head or out of the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : EqEvalFnOfEqAbovePre m0) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2Offset)) (hI : Inv m0 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2Offset) ∧ Inv m0 (i + 1) st'.data)) st := by
  obtain ⟨hS, h64, hrR, hoR⟩ := hpre
  have hlt := hI.lt
  have hiR : i < m0.regs.X3.toNat := Nat.lt_of_lt_of_le hI.lt (Nat.min_le_right _ _)
  have hlt' : i < min m0.regs.X0.toNat m0.regs.X3.toNat := hlt
  have hi64 : i < 64 := by omega
  obtain ⟨st, pc⟩ := st
  -- `right[i]`, the factor, the call
  refine load_step (lo := .X9) (hi' := .X3) (hb2 hp) run_b2 rfl rfl
    (after_eq run_b2 ▸ b2_facts.1) _ (after_eq run_b2 ▸ b2_facts.2) hI.body hS hrR hoR
    (apart_zero _ _) noWrap_zero hiR hpc
    (by
      show st.regs.X21.toBitVec = _
      rw [hI.x21, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add])
    fun st2 hm2' hpc2 hb2' hR e2 ↦ ?_
  simp only [NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2_length, NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2Length] at hpc2
  have hx22 : (st.regs.getXReg .X22).toBitVec.toNat = i := hI.x22
  have hfac : (⟨st2.data.regs.X2, st2.data.regs.X3⟩ : EW) =
      1 + (lft m0)[i]'(lt_l hlt) + (rgt m0)[i]'(lt_r hlt) := by
    rw [← hR, getElem_lft]
    have h2 := hm2'.regs .X2 _ rfl
    have h9 := hm2'.regs .X9 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h2
    rw [bit_eval _ _ (by rw [hx22]; exact hi64), hx22] at h2
    sym_simp at h2 h9
    rw [← h9] at h2
    show (⟨st2.data.regs.getXReg .X2, st2.data.regs.getXReg .X3⟩ : EW) = _
    rw [toBitVec_eq h2]
    show (⟨_, _⟩ : EW) = ⟨(1 ^^^ _) ^^^ _, (0 ^^^ 0) ^^^ _⟩
    congr 1
    · apply UInt64.toBitVec_inj.mp
      simp only [UInt64.toBitVec_xor]
      rw [show (st.regs.getXReg .X19).toBitVec.toNat = m0.regs.X1.toNat from
        congrArg UInt64.toNat hI.x19]
      show _ = (1#64 ^^^ BitVec.ofNat 64 _) ^^^ _
      ac_rfl
    · rw [UInt64.zero_xor, UInt64.zero_xor]
  refine call_then hpc2 hmul (hb2'.ewMulPre hS (by decide) (by decide)) fun st3 hpc3 hpost ↦ ?_
  have hb3' := hb2'.call hS (by decide) (by decide) hpost
  have hprod : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) =
      acc m0 i * (1 + (lft m0)[i]'(lt_l hlt) + (rgt m0)[i]'(lt_r hlt)) := by
    have hA : (⟨st2.data.regs.X0, st2.data.regs.X1⟩ : EW) = acc m0 i := by
      rw [← hI.acc]
      exact congr (congrArg EW.mk (e2 .X0 (by simp))) (e2 .X1 (by simp))
    rw [hpost.1, hpost.2.1, hA, hfac]
    rfl
  have h22 := hm2'.regs .X22 _ rfl
  sym_simp at h22
  simp only [Env.ofMachine_regs] at h22
  have e3 : ∀ r ∈ [XReg.X19, .X20], st3.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rfl
    have hr' : r ∈ [XReg.X0, .X1, .X19, .X20] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl <;> simp
    rw [hpost.2.2.2.1 r hc, e2 r hr']
  have e22 : (st3.data.regs.getXReg .X22).toBitVec = (st.regs.getXReg .X22).toBitVec + 1#64 := by
    rw [hpost.2.2.2.1 .X22 rfl, h22]
  have e21 : st3.data.regs.getXReg .X21 = st2.data.regs.getXReg .X21 := hpost.2.2.2.1 .X21 rfl
  have h21 := hm2'.regs .X21 _ rfl
  simp only [Sym.eval, base0] at h21
  -- `b3`: advance, count
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) hpc3 (match_nil _) fun st4 hm4 hpc4 ↦ ?_
  have hb4' := hb3'.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  have h21' := hm4.regs .X21 _ rfl
  sym_simp at h21'
  simp only [Env.ofMachine_regs] at h21'
  have hacc : (⟨st4.data.regs.X0, st4.data.regs.X1⟩ : EW) = acc m0 (i + 1) := by
    rw [acc_succ m0 hI.lt, ← hprod]
    exact congr (congrArg EW.mk (Match.reg_eq (r := .X0) (match_nil _) hm4 rfl rfl))
      (Match.reg_eq (r := .X1) (match_nil _) hm4 rfl rfl)
  have hk22 : st4.data.regs.getXReg .X22 = st3.data.regs.getXReg .X22 :=
    Match.reg_eq (match_nil _) hm4 rfl rfl
  have hx22' : (st4.data.regs.getXReg .X22).toBitVec.toNat = i + 1 := by
    rw [hk22, e22, BitVec.toNat_add, hx22]
    simp only [BitVec.toNat_ofNat]
    omega
  have hx20 : (st3.data.regs.getXReg .X20).toBitVec.toNat = cnt m0 := by
    rw [e3 .X20 (by simp)]; exact hI.x20
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  have hpc4' := pc_ne hpc4
  have hinv : ∀ r ∈ [XReg.X19, .X20], st4.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    rw [← e3 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq (match_nil _) hm4 rfl rfl
  by_cases hlast : i + 1 = cnt m0
  · have hpc4 := hpc4'.2 (by
      show (st3.data.regs.getXReg .X20).toBitVec = (st3.data.regs.getXReg .X22).toBitVec
      apply BitVec.eq_of_toNat_eq
      rw [hx20, ← hk22, hx22', hlast])
    simp only [NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b3_length, NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b3Length] at hpc4
    refine Eventually.mono (finish hp ⟨hS, h64, hrR, hoR⟩ hpc4 hb4' ?_) fun _ h ↦ Or.inl h
    rw [hacc, hlast]
  · have hpc4 := hpc4'.1 (by
      show (st3.data.regs.getXReg .X20).toBitVec ≠ (st3.data.regs.getXReg .X22).toBitVec
      intro h
      have := congrArg BitVec.toNat h
      rw [hx20, ← hk22, hx22'] at this
      omega)
    refine .done _ (Or.inr ⟨hpc4.trans (lbl_2 hp), hb4', by omega, ?_, ?_, ?_, ?_, hacc⟩)
    · exact (hinv .X19 (by simp)).trans hI.x19
    · show (st4.data.regs.getXReg .X20).toBitVec.toNat = _
      rw [hinv .X20 (by simp)]; exact hI.x20
    · exact hx22'
    · show (st4.data.regs.getXReg .X21).toBitVec = _
      rw [h21', e21, h21, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
        show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, addr_add, addr_add]
      congr 2

/-- **`eq_eval_fn` (`eq_above`'s closure) meets its contract.** -/
theorem eqEvalFn_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hS := hpre.1
  have h48 : 48 ≤ eqEvalFnStack := by decide
  obtain ⟨hwf, hm⟩ := entry_match hS h48 rfl
  have hcnt := min_toNat (m0.regs.getXReg .X0).toBitVec (m0.regs.getXReg .X3).toBitVec
  refine exec_then (hb0 hp) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b0_length, NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b0Length] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  have hc : (((if (m0.regs.getXReg .X3).toBitVec.ult (m0.regs.getXReg .X0).toBitVec then
      (m0.regs.getXReg .X3).toBitVec else (m0.regs.getXReg .X0).toBitVec) == 0#64) = true) ↔
      cnt m0 = 0 := by
    rw [beq_iff_eq]
    constructor
    · intro h
      have hc' := hcnt
      rw [h] at hc'
      show min (m0.regs.getXReg .X0).toBitVec.toNat (m0.regs.getXReg .X3).toBitVec.toNat = 0
      rw [← hc']
      rfl
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hcnt]; exact h
  by_cases hz' : cnt m0 = 0
  · -- `n = 0`: return `1`.
    have hpc1 := hpc1'.1 (hc.mpr hz')
    refine exec_at (hb5 hp) (exec_after run_b0 run_b5) hwf (hpc1.trans (lbl_4 hp)) hm1
      fun st2 hm2 hpc2 ↦ .done _ ⟨?_, ?_, ?_, ?_⟩
    · simp only [PcOk] at hpc2
      rw [hpc2]
      simp only [retOf]
      rw [show st2.data.regs.X30 = m0.regs.X30 from Match.reg_eq (r := .X30) hm hm2 rfl rfl]
    · rw [eqEval_eq_acc, hz']
      have h0 := hm2.regs .X0 _ rfl
      have h1 := hm2.regs .X1 _ rfl
      simp only [Sym.eval] at h0 h1
      show (⟨st2.data.regs.getXReg .X0, st2.data.regs.getXReg .X1⟩ : EW) = _
      rw [UInt64.toBitVec_inj.mp (h0.trans rfl), UInt64.toBitVec_inj.mp (h1.trans rfl)]
      rfl
    · exact changes_of_frame hS h48 hm2 (after_eq run_b5 ▸ b5_frame)
    · exact Match.saved hm hm2 hwf rfl (after_eq run_b5 ▸ b5_keeps)
  · -- `n > 0`: the loop.
    have hpc1 := hpc1'.2 (fun h ↦ hz' (hc.mp h))
    have hpos : 0 < cnt m0 := Nat.pos_of_ne_zero hz'
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf hpc1 hm1 fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b1_length, NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b1Length] at hpc2
    obtain ⟨hw, hmem, hregs⟩ := after_eq run_b1 ▸ b1_frame
    have hI : Inv m0 0 st2.data := by
      have h0 := hm2.regs .X0 _ rfl
      have h1 := hm2.regs .X1 _ rfl
      have h19 := hm2.regs .X19 _ rfl
      have h20 := hm2.regs .X20 _ rfl
      have h21 := hm2.regs .X21 _ rfl
      have h22 := hm2.regs .X22 _ rfl
      sym_simp at h0 h1 h19 h20 h21 h22
      simp only [Env.ofMachine_regs] at h19 h20 h21
      refine ⟨Body.of_entry hS h48 hm2 rfl hw hregs hmem, hpos, ?_, ?_, ?_, ?_, ?_⟩
      · exact UInt64.toBitVec_inj.mp h19
      · show (st2.data.regs.getXReg .X20).toBitVec.toNat = _
        rw [h20]
        exact hcnt
      · show (st2.data.regs.getXReg .X22).toBitVec.toNat = _
        rw [h22]; rfl
      · show (st2.data.regs.getXReg .X21).toBitVec = _
        rw [h21]
        rfl
      · show (⟨st2.data.regs.getXReg .X0, st2.data.regs.getXReg .X1⟩ : EW) = _
        rw [UInt64.toBitVec_inj.mp (h0.trans rfl), UInt64.toBitVec_inj.mp (h1.trans rfl)]
        rfl
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.b2Offset) ∧ ∃ i, cnt m0 - i = n ∧
      Inv m0 i st.data) (fun n st ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul hpre hpc hI) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨cnt m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Arrays.EqEvalFn
