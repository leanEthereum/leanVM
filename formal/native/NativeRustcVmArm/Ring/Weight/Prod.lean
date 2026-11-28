module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Ring.Weight.Square
public import NativeRustcVmArm.Ring.Weight.Entry

/-!
# `ring_weight`: a coefficient's product

With `r'` not empty, the product `c · Π_n (1 + P_n + r'_n)` over the first `min |r| |r'|`
factors, one per turn (`b14`: the factor formed and `EW::mul`; `b15`: the pointers stepped).
`ProdI`: the first `i` factors multiplied in X0, X1 (`prodPart`), X26, X29 at `r'_i`, `P_i`, X28
counting down; `prodLoop`: the product (`ProdDone`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight
open NativeRustcVmArm.Arrays (calleeRegs regs_eq_of keepsAll)

@[expose] public section

/-- `min |r| |r'|`. -/
abbrev mn (m0 : MachineData) : Nat := min (nR m0) (nQ m0)

/-- The callee-saved registers the coefficients' loop keeps across a product. -/
def prodKeep : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X27]

/-- The powers hold `P`. -/
def PowP (m0 : MachineData) (d : DataMem) (P : Array EW) : Prop :=
  ∀ l < nR m0, NativeRustcVm.EWAt d (slotA m0 l) (P.getD l 0)

/-- **The product, factor `i`.** -/
structure ProdI (m0 : MachineData) (P : Array EW) (c : EW) (ref : MachineData) (i : Nat)
    (m : MachineData) : Prop where
  fr : WFr m0 m
  lt : i < mn m0
  x26 : (m.regs.getXReg .X26).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i + 8)
  x29 : (m.regs.getXReg .X29).toBitVec = fb m0 + BitVec.ofNat 64 (16 + 16 * i + 8)
  x28 : (m.regs.getXReg .X28).toBitVec = BitVec.ofNat 64 (mn m0 - i)
  regs : ∀ r ∈ prodKeep, m.regs.getXReg r = ref.regs.getXReg r
  acc : (⟨m.regs.getXReg .X0, m.regs.getXReg .X1⟩ : EW) = prodPart P (qL m0) c i
  pow : PowP m0 m.dmem P

/-- **The product done.** -/
structure ProdDone (m0 : MachineData) (P : Array EW) (c : EW) (ref : MachineData)
    (m : MachineData) : Prop where
  fr : WFr m0 m
  regs : ∀ r ∈ prodKeep, m.regs.getXReg r = ref.regs.getXReg r
  acc : (⟨m.regs.getXReg .X0, m.regs.getXReg .X1⟩ : EW) = prodOf P (qL m0) c
  pow : PowP m0 m.dmem P

end

public section

variable {m0 : MachineData}

theorem getElem_getD {xs : Array EW} {i : Nat} (hi : i < xs.size) : xs[i] = xs.getD i 0 := by
  simp [Array.getD, hi]

/-- The factor as `b14` forms it. -/
theorem factor (P q : EW) : (⟨P.c0 ^^^ q.c0 ^^^ 1, q.c1 ^^^ P.c1⟩ : EW) = 1 + P + q := by
  show _ = (⟨(1 ^^^ P.c0) ^^^ q.c0, (0 ^^^ P.c1) ^^^ q.c1⟩ : EW)
  rw [UInt64.zero_xor, UInt64.xor_comm q.c1]
  congr 1
  ac_rfl

theorem prodKeep_cs : ∀ r ∈ prodKeep, calleeSaved r = true := by decide

theorem PowP.of_eq {d d' : DataMem} {P : Array EW} (h : PowP m0 d P) (e : d' = d) : PowP m0 d' P :=
  e ▸ h

variable [Host] {k : Nat}

/-- **A factor** (`b14`, `EW::mul`, `b15`). -/
theorem prodTurn (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {P : Array EW}
    (hP : P.size = nR m0) {c : EW} {ref : MachineData} {i : Nat} {m : MachineData}
    (hI : ProdI m0 P c ref i m) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b14Offset) ∧ ∃ i',
        ProdI m0 P c ref i' st.data ∧ mn m0 - i' < mn m0 - i) ∨
      (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b16Offset) ∧ ProdDone m0 P c ref st.data)) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b14Offset)⟩ := by
  have hn := n36 h
  have hi := hI.lt
  have hmn : mn m0 = min (nR m0) (nQ m0) := rfl
  have hnq : nQ m0 = m0.regs.X4.toNat := rfl
  have hiR : i < nR m0 := by omega
  have hiQ : i < nQ m0 := by omega
  have hq := h.2.2.2.1
  let rs : List (BitVec 64 × Nat) :=
    [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i), 16), (slotA m0 i, 16)]
  have hwf : (Env.ofMachine m rs).WF :=
    win_wf2 (arg_win hI.fr hq.1 (by omega) (by decide)) (frame_win h hI.fr (by omega) (by decide))
      (win_apart h hq.2 hq.1.2 (by omega) (by decide) (by omega))
  have hm : Match (Env.ofMachine m rs) prodS m :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show _ = m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 (8 : Nat)
        rw [hI.x26, ofInt_lit, addr_eq rfl],
      by
        show _ = slotA m0 i + BitVec.ofInt 64 (8 : Nat)
        rw [hI.x29, ofInt_lit, addr_eq rfl], trivial⟩
      trivial trivial trivial
  have hPi : NativeRustcVm.ewOf m.dmem (slotA m0 i) = P.getD i 0 :=
    NativeRustcVm.ewOf_of_ewAt (hI.pow i hiR)
  have hQi : NativeRustcVm.ewOf m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i)) =
      (qL m0).getD i 0 := elem_q h hI.fr hiQ
  refine mulStep h hmul (hb b14_in_code (by simp [b14]) hp) run_b14 hI.fr hm hwf rfl rfl
    fun st m2 hm1 hfr1 hfr2 hmp hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b14Offset + b14.length = k + NativeRustcVmArm.Vm.RingWeight.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b14_next]]
  have hd1 : st.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have L0 := load_c0 (m := m) (rs := rs) (r := 0) rfl 0
  have L0' := load_c1 (m := m) (rs := rs) (r := 0) rfl 0
  have L1 := load_c0 (m := m) (rs := rs) (r := 1) rfl 0
  have L1' := load_c1 (m := m) (rs := rs) (r := 1) rfl 0
  simp only [NativeRustcVm.addr_add_zero, Nat.zero_add] at L0 L0' L1 L1'
  have e2 : st.regs.getXReg .X2 = (P.getD i 0).c0 ^^^ ((qL m0).getD i 0).c0 ^^^ 1 :=
    reg_of hm1 rfl (eor_eval (eor_eval (by rw [L1, hPi]) (by rw [L0, hQi])) rfl)
  have e3 : st.regs.getXReg .X3 = ((qL m0).getD i 0).c1 ^^^ (P.getD i 0).c1 :=
    reg_of hm1 rfl (eor_eval (by rw [L0', hQi]) (by rw [L1', hPi]))
  have e01 : (⟨st.regs.getXReg .X0, st.regs.getXReg .X1⟩ : EW) = prodPart P (qL m0) c i := by
    rw [Match.reg_eq hm hm1 rfl rfl, Match.reg_eq hm hm1 (r := .X1) rfl rfl]
    exact hI.acc
  have hprod : (⟨m2.regs.X0, m2.regs.X1⟩ : EW) = prodPart P (qL m0) c (i + 1) := by
    rw [hmp.1, hmp.2.1, prodPart_succ (by omega) (by rw [size_qL]; exact hiQ),
      getElem_getD (by omega), getElem_getD (by rw [size_qL]; exact hiQ), ← factor, ← e01, ← e2, ← e3]
    rfl
  -- `b15`
  refine exec_then (hb b15_in_code (by simp [b15]) hp) run_b15 (Env.wf_nil m2) (match_nil m2)
    fun st3 hm3 hpc3 ↦ ?_
  have hfr3 := regs_fr hfr2 hm3 rfl rfl
  have hd3 : st3.data.dmem = m2.dmem := hm3.dmem_eq (Env.wf_nil m2) rfl
  have hpow : PowP m0 st3.data.dmem P := fun l hl ↦ by
    rw [hd3]
    exact ew_call h hfr1 hmp (o := 16 + 16 * l) (by omega) (by rw [hd1]; exact hI.pow l hl)
  have hk : ∀ r, calleeSaved r = true → m2.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    rw [hcs r hr]
    have := regs_eq_of hm hm1 calleeRegs (by decide) r (NativeRustcVmArm.Arrays.mem_calleeRegs hr)
    exact this
  have hregs : ∀ r ∈ prodKeep, st3.data.regs.getXReg r = ref.regs.getXReg r := fun r hr ↦ by
    rw [regs_eq_of (match_nil m2) hm3 prodKeep (by decide) r hr,
      hk r (prodKeep_cs r hr)]
    exact hI.regs r hr
  have h28 : (m2.regs.getXReg .X28).toBitVec = BitVec.ofNat 64 (mn m0 - i) := by
    rw [hk .X28 rfl]; exact hI.x28
  have hacc : (⟨st3.data.regs.getXReg .X0, st3.data.regs.getXReg .X1⟩ : EW) =
      prodPart P (qL m0) c (i + 1) := by
    rw [Match.reg_eq (match_nil m2) hm3 rfl rfl, Match.reg_eq (match_nil m2) hm3 (r := .X1) rfl rfl]
    exact hprod
  simp only [PcOk] at hpc3
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc3
  have he : (SBool.not (SBool.cmp .eq .W64 (.reg .X28) (.lit 1))).eval (Env.ofMachine m2 []) = true ↔
      i + 1 ≠ mn m0 := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, Sym.low_W64, h28,
      Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
    rw [eq_lit (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  by_cases hl : i + 1 = mn m0
  · refine .done _ (.inr ⟨hc.2 (fun e ↦ he.mp e hl), hfr3, hregs, ?_, hpow⟩)
    rw [hacc, hl, prodOf_eq, hP, size_qL]
  · refine .done _ (.inl ⟨(hc.1 (he.mpr hl)).trans (hp.label (j := NativeRustcVmArm.Vm.RingWeight.b14Offset) NativeRustcVmArm.Vm.RingWeight.label_14_at), i + 1,
      ⟨hfr3, by omega, ?_, ?_, ?_, hregs, hacc, hpow⟩, by omega⟩)
    · refine reg_bv hm3 rfl ?_
      simp only [Sym.eval, Env.ofMachine_regs, add_bv]
      rw [hk .X26 rfl, hI.x26, addr_eq (z := 16 * (i + 1) + 8) (by omega)]
    · refine reg_bv hm3 rfl ?_
      simp only [Sym.eval, Env.ofMachine_regs, add_bv]
      rw [hk .X29 rfl, hI.x29, addr_eq (z := 16 + 16 * (i + 1) + 8) (by omega)]
    · refine reg_bv hm3 rfl ?_
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [h28, sub_lit (by omega) (by omega)]
      congr 1

/-- **The product** (`b14` to `b15`). -/
theorem prodLoop (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {P : Array EW}
    (hP : P.size = nR m0) {c : EW} {ref : MachineData} {m : MachineData}
    (hI : ProdI m0 P c ref 0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b16Offset) ∧
      ProdDone m0 P c ref st.data) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b14Offset)⟩ :=
  Sym.loop (I := fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b14Offset) ∧ ∃ i, n = mn m0 - i ∧
      ProdI m0 P c ref i st.data)
    (fun _ _ ⟨hpc', _, hn, hI⟩ ↦ at_pc hpc' ((prodTurn hp h hmul hP hI).mono fun _ h' ↦
      h'.elim (fun ⟨hp', i', hI', hlt⟩ ↦ .inr ⟨_, hn ▸ hlt, hp', i', rfl, hI'⟩) .inl))
    ⟨rfl, 0, rfl, hI⟩

end

end NativeRustcVmArm.Ring.Weight
