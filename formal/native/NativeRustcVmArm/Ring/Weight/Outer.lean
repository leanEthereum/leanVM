module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Ring.Weight.Prod
public import NativeRustcVmArm.Ring.Weight.Odd
public import NativeRustcVmArm.Ring.Weight.Exit

/-!
# `ring_weight`: the coefficients' loop, `r'` not empty

`b11` clears the total and branches on `|r'| = 0`; `b12` sets up the loop. Each turn (`OutI`:
`k` coefficients done, the total and the powers `accW`'s) loads the coefficient (`b13`), forms
the product (`prodLoop`), squares the powers (`b16`, `sqLoop` over `b17`, `b18`), adds the
product to the total (`b19`), and after the last jumps to the epilogue (`b20`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight
open NativeRustcVmArm.Arrays (calleeRegs regs_eq_of)

@[expose] public section

/-- The total and the powers after `k` coefficients. -/
abbrev A (m0 : MachineData) (k : Nat) : EW × Array EW := accW (rL m0) (qL m0) (cL m0) k

/-- **The coefficients' loop, turn `k`** (`r'` not empty). -/
structure OutI (m0 : MachineData) (k : Nat) (m : MachineData) : Prop where
  fr : WFr m0 m
  lt : k < 64
  x19 : (m.regs.getXReg .X19).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 8
  x20 : m.regs.getXReg .X20 = m0.regs.X5
  x22 : (m.regs.getXReg .X22).toBitVec = slotA m0 (nR m0)
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (mn m0)
  x25 : (m.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (16 * k)
  x27 : (m.regs.getXReg .X27).toBitVec = fb m0 + BitVec.ofNat 64 24
  tot : (⟨m.regs.getXReg .X21, m.regs.getXReg .X23⟩ : EW) = (A m0 k).1
  pow : PowP m0 m.dmem (A m0 k).2

end

public section

variable {m0 : MachineData}

theorem size_A {k : Nat} : (A m0 k).2.size = nR m0 := by rw [size_accW, size_rL]

theorem A_succ {k : Nat} (hk : k < 64) : A m0 (k + 1) = wStep (qL m0) (A m0 k) ((cL m0).getD k 0) := by
  unfold A
  rw [accW_succ (by rw [size_cL]; exact hk), getElem_getD (by rw [size_cL]; exact hk)]

theorem getD_map_sq {P : Array EW} {l : Nat} (hl : l < P.size) :
    (P.map fun v ↦ v * v).getD l 0 = P.getD l 0 * P.getD l 0 := by
  simp [Array.getD, hl]

theorem tot_step (t p : EW) : (⟨p.c0 ^^^ t.c0, p.c1 ^^^ t.c1⟩ : EW) = t + p := by
  show _ = (⟨t.c0 ^^^ p.c0, t.c1 ^^^ p.c1⟩ : EW)
  rw [UInt64.xor_comm p.c0, UInt64.xor_comm p.c1]

theorem A_done : ringWeight (rL m0) (qL m0) (cL m0) = (A m0 64).1 := by
  rw [ringWeight_eq, size_cL]

/-- The coefficient, loaded from its window. -/
theorem coef_ew (h : RingWeightPre m0) [Labels] {m : MachineData} (hfr : WFr m0 m) {k : Nat}
    (hk : k < 64) :
    (Sym.load 0 0 8).eval (Env.ofMachine m [(m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * k), 16)]) =
        ((cL m0).getD k 0).c0.toBitVec ∧
      (Sym.load 0 8 8).eval (Env.ofMachine m [(m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * k), 16)]) =
        ((cL m0).getD k 0).c1.toBitVec := by
  have e0 := load_c0 (m := m) (rs := [(m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * k), 16)])
    (r := 0) rfl 0
  have e1 := load_c1 (m := m) (rs := [(m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * k), 16)])
    (r := 0) rfl 0
  rw [NativeRustcVm.addr_add_zero, elem_c h hfr hk] at e0 e1
  exact ⟨e0, e1⟩

theorem coef_wf (h : RingWeightPre m0) {m : MachineData} (hfr : WFr m0 m) {k : Nat} (hk : k < 64) :
    (Env.ofMachine m [(m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * k), 16)]).WF :=
  win_wf1 (arg_win hfr h.2.2.2.2.1.1 (by show 16 * k + 16 ≤ 16 * 64; omega) (by decide))

theorem coef_match [Labels] {m : MachineData} {r : XReg} {k : Nat}
    (hx : (m.regs.getXReg .X20).toBitVec + (m.regs.getXReg r).toBitVec =
      m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * k)) :
    Match (Env.ofMachine m [(m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * k), 16)]) (coefS r) m :=
  match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
    ⟨by
      show BinOp.apply .add .W64 _ _ = _ + BitVec.ofInt 64 (0 : Nat)
      rw [add_bv, ofInt_lit, NativeRustcVm.addr_add_zero]
      exact hx, trivial⟩

variable [Host] {k : Nat}

/-- **A turn of the coefficients' loop** (`b13` to `b20`). -/
theorem outTurn (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {m : MachineData}
    (hI : OutI m0 j m) (hQ : 0 < nQ m0) (hR : 0 < nR m0) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b13Offset) ∧ ∃ j',
        OutI m0 j' st.data ∧ 64 - j' < 64 - j) ∨
      (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset) ∧ Done m0 st.data)) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b13Offset)⟩ := by
  have hn := n36 h
  have hj := hI.lt
  have hmn : mn m0 = min (nR m0) (nQ m0) := rfl
  -- `b13`: the coefficient
  have hwf := coef_wf h hI.fr hj
  have hm := coef_match (m := m) (r := .X25) (k := j) (by rw [hI.x20, hI.x25])
  refine exec_then (hb b13_in_code (by simp [b13]) hp) run_b13 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine at_pc hpc1 ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b13Offset + b13.length = k + NativeRustcVmArm.Vm.RingWeight.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b13_next]]
  have hfr1 : WFr m0 st1.data := hI.fr.ofBlock hm hm1 hwf rfl rfl rfl fun r hr ↦ by simp at hr
  have k1 := regs_eq_of hm hm1 prodKeep (by decide)
  have hce := coef_ew h hI.fr hj
  have hpI : ProdI m0 (A m0 j).2 ((cL m0).getD j 0) st1.data 0 st1.data := by
    refine ⟨hfr1, by omega, ?_, ?_, ?_, fun _ _ ↦ rfl, ?_, ?_⟩
    · rw [reg_bv hm1 rfl rfl]; exact hI.x19
    · rw [reg_bv hm1 rfl rfl]; exact hI.x27
    · rw [reg_bv hm1 rfl rfl]; exact hI.x24
    · rw [reg_of hm1 rfl hce.1, reg_of hm1 rfl hce.2]; rfl
    · exact hI.pow.of_eq (hm1.dmem_eq hwf rfl)
  refine (prodLoop hp h hmul size_A hpI).bind fun st2 ⟨hpc2, hD⟩ ↦ at_pc hpc2 ?_
  -- `b16`: the squares set up
  refine exec_then (hb b16_in_code (by simp [b16]) hp) run_b16 (Env.wf_nil _) (match_nil _)
    fun st3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  refine at_pc hpc3 ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b16Offset + b16.length = k + NativeRustcVmArm.Vm.RingWeight.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b16_next]]
  have k3 := regs_eq_of (match_nil _) hm3 prodKeep (by decide)
  have hfr3 := regs_fr hD.fr hm3 rfl rfl
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (Env.wf_nil _) rfl
  have h22 : (st3.data.regs.getXReg .X22).toBitVec = slotA m0 (nR m0) := by
    rw [k3 .X22 (by simp [prodKeep]), hD.regs .X22 (by simp [prodKeep]), k1 .X22 (by simp [prodKeep])]; exact hI.x22
  have hsI : SqI m0 .X29 (A m0 j).2 st3.data 0 st3.data := by
    refine ⟨hfr3, hR, ?_, fun _ _ _ ↦ rfl, fun _ h ↦ absurd h (by omega), fun l _ hl ↦ ?_⟩
    · refine reg_bv hm3 rfl ?_
      simp only [Sym.eval, add_bv]
      show st2.data.regs.SP.toBitVec + _ = _
      rw [hD.fr.sp]
    · rw [hd3]; exact hD.pow l hl
  refine (sqLoop h hmul rfl h22 (by decide) (hb b17_in_code (by simp [b17]) hp) run_b17
    (by decide) (show k + NativeRustcVmArm.Vm.RingWeight.b17Offset + b17.length = k + NativeRustcVmArm.Vm.RingWeight.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b17_next]) (hb b18_in_code (by simp [b18]) hp) run_b18 (by decide)
    (hp.label (j := NativeRustcVmArm.Vm.RingWeight.b17Offset) NativeRustcVmArm.Vm.RingWeight.label_16_at) hsI).bind fun st4 ⟨hpc4, hS⟩ ↦ at_pc hpc4 ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b18Offset + b18.length = k + NativeRustcVmArm.Vm.RingWeight.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b18_next]]
  -- `b19`: the product added
  refine exec_then (hb b19_in_code (by simp [b19]) hp) run_b19 (Env.wf_nil _) (match_nil _)
    fun st5 hm5 hpc5 ↦ ?_
  have hfr5 := regs_fr hS.fr hm5 rfl rfl
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  have k5 := regs_eq_of (match_nil _) hm5 [.X19, .X20, .X22, .X24, .X26, .X27, .X28] (by decide)
  have kS : ∀ r ∈ [XReg.X19, .X20, .X22, .X24, .X27], st5.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [k5 _ (by simp), hS.regs _ (by simp [calleeRegs]) (by simp), k3 _ (by simp [prodKeep]),
        hD.regs _ (by simp [prodKeep]), k1 _ (by simp [prodKeep])]
  have hprod : (⟨st4.data.regs.getXReg .X28, st4.data.regs.getXReg .X26⟩ : EW) =
      prodOf (A m0 j).2 (qL m0) ((cL m0).getD j 0) := by
    rw [hS.regs .X28 (by simp [calleeRegs]) (by simp), hS.regs .X26 (by simp [calleeRegs]) (by simp),
      reg_of hm3 (w := st2.data.regs.getXReg .X0) rfl rfl,
      reg_of hm3 (w := st2.data.regs.getXReg .X1) rfl rfl]
    exact hD.acc
  have htot : (⟨st4.data.regs.getXReg .X21, st4.data.regs.getXReg .X23⟩ : EW) = (A m0 j).1 := by
    rw [hS.regs .X21 (by simp [calleeRegs]) (by simp), hS.regs .X23 (by simp [calleeRegs]) (by simp),
      k3 .X21 (by simp [prodKeep]), k3 .X23 (by simp [prodKeep]), hD.regs .X21 (by simp [prodKeep]),
      hD.regs .X23 (by simp [prodKeep]), k1 .X21 (by simp [prodKeep]), k1 .X23 (by simp [prodKeep])]
    exact hI.tot
  have hA := A_succ (m0 := m0) hj
  have htot' : (⟨st5.data.regs.getXReg .X21, st5.data.regs.getXReg .X23⟩ : EW) = (A m0 (j + 1)).1 := by
    have x21 : st5.data.regs.getXReg .X21 =
        st4.data.regs.getXReg .X28 ^^^ st4.data.regs.getXReg .X21 :=
      reg_of hm5 rfl (eor_eval (a := st4.data.regs.getXReg .X28)
        (b := st4.data.regs.getXReg .X21) rfl rfl)
    have x23 : st5.data.regs.getXReg .X23 =
        st4.data.regs.getXReg .X26 ^^^ st4.data.regs.getXReg .X23 :=
      reg_of hm5 rfl (eor_eval (a := st4.data.regs.getXReg .X26)
        (b := st4.data.regs.getXReg .X23) rfl rfl)
    have e1 := congrArg EW.c0 hprod
    have e2 := congrArg EW.c1 hprod
    have e3 := congrArg EW.c0 htot
    have e4 := congrArg EW.c1 htot
    simp only at e1 e2 e3 e4
    rw [hA, x21, x23, e1, e2, e3, e4, tot_step]
    rfl
  have hpow' : PowP m0 st5.data.dmem (A m0 (j + 1)).2 := fun l hl ↦ by
    rw [hd5, hA]
    show NativeRustcVm.EWAt _ _ (((A m0 j).2.map fun v ↦ v * v).getD l 0)
    rw [getD_map_sq (by rw [size_A]; exact hl)]
    exact hS.sq l hl
  have h25 : (st5.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (16 * (j + 1)) := by
    refine reg_bv hm5 rfl ?_
    simp only [Sym.eval, add_bv, Env.ofMachine_regs]
    rw [hS.regs .X25 (by simp [calleeRegs]) (by simp), k3 .X25 (by simp [prodKeep]), hD.regs .X25 (by simp [prodKeep]),
      k1 .X25 (by simp [prodKeep]), hI.x25]
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  simp only [PcOk] at hpc5
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc5
  have he : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X25) (.lit 16)) (.lit 1024))).eval
      (Env.ofMachine st4.data []) = true ↔ j + 1 ≠ 64 := by
    have : (Sym.bin .add .W64 (.reg .X25) (.lit 16)).eval (Env.ofMachine st4.data []) =
        BitVec.ofNat 64 (16 * (j + 1)) := by
      rw [← h25]; exact (reg_bv hm5 rfl rfl).symm
    simp only [SBool.eval, CmpOp.apply, Sym.low_W64, Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
    rw [this]
    simp only [Sym.eval]
    rw [eq_lit (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  by_cases hl : j + 1 = 64
  · refine at_pc (hc.2 (fun e ↦ he.mp e hl)) ?_
    rw [show k + NativeRustcVmArm.Vm.RingWeight.b19Offset + b19.length = k + NativeRustcVmArm.Vm.RingWeight.b20Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b19_next]]
    refine exec_then (hb b20_in_code (by simp [b20]) hp) run_b20 (Env.wf_nil _) (match_nil _)
      fun st6 hm6 hpc6 ↦ ?_
    simp only [PcOk] at hpc6
    refine .done _ (.inr ⟨hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.RingWeight.b26Offset) NativeRustcVmArm.Vm.RingWeight.label_22_at), regs_fr hfr5 hm6 rfl rfl, ?_⟩)
    rw [Match.reg_eq (match_nil _) hm6 (r := .X21) rfl rfl,
      Match.reg_eq (match_nil _) hm6 (r := .X23) rfl rfl, htot', A_done, hl]
  · refine .done _ (.inl ⟨(hc.1 (he.mpr hl)).trans (hp.label (j := NativeRustcVmArm.Vm.RingWeight.b13Offset) NativeRustcVmArm.Vm.RingWeight.label_13_at), j + 1,
      ⟨hfr5, by omega, ?_, by rw [kS .X20 (by simp)]; exact hI.x20, ?_, ?_, h25, ?_, htot', hpow'⟩,
      by omega⟩)
    · rw [kS .X19 (by simp)]; exact hI.x19
    · rw [kS .X22 (by simp)]; exact hI.x22
    · rw [kS .X24 (by simp)]; exact hI.x24
    · rw [kS .X27 (by simp)]; exact hI.x27

end

end NativeRustcVmArm.Ring.Weight
