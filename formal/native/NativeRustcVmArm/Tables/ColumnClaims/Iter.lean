module

public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Tables.ColumnClaims.Loop

/-!
# `table_column_claims`: a table's loop

From a table's loop head with `j` values pushed (`LoopAt`): all pushed, to the next table (`head`);
else the value's claim pushed (`push`): back to the head with `j + 1`, or a failed push (the claims
do not fit) to the block after the loop. `loop`: the whole loop, by induction on the values left.
-/

namespace NativeRustcVmArm.Tables.ColumnClaims

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm.Tables
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap)

public section

theorem le_push : 64 + pushClaimStack ≤ tableColumnClaimsStack := Nat.le_refl _
theorem evalsBytes_eq : tableEvalsBytes = 11808 := rfl

theorem base_le (i : Nat) : globalColumnBasesW.getD i 0 ≤ 66 := by
  rw [bases_eq]
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp

theorem bit_one : (low .W32 (1 : UInt64).toBitVec).getLsbD 0 = true := by decide
theorem bit_zero : (low .W32 (0 : UInt64).toBitVec).getLsbD 0 = false := by decide

theorem push_eq {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW} {i j : Nat}
    (hj : j < (claimsOf ev i).length) :
    (cs ++ (pre ev i j).toArray).push (claimsOf ev i)[j] = cs ++ (pre ev i (j + 1)).toArray := by
  rw [pre_succ i j hj]
  apply Array.toList_inj.mp
  simp

section
variable [Labels] {R : Regs} {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW}
  {m0 : MachineData}

omit [Labels] in
/-- The evaluations in a state of the frame. -/
theorem evals_in (hpre : TableColumnClaimsPre ev cs m0) {m : MachineData}
    (h : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m) :
    TableEvalsAt m.dmem m0.regs.X0.toBitVec ev := by
  obtain ⟨hS, hin, hev, hcR, -, -⟩ := hpre
  have hA := hin.2.2 ⟨m0.regs.X1.toBitVec, claimsBytes⟩ (by simp)
  exact TableEvalsAt.of_same hev (same_in h hS hin.1.2 hin.2.1 fun j hj ho ↦
    Bus.not_inRange_of_apart hA hin.1.2 hcR.2 hj ho)

/-- `LoopAt` in a state with the same registers and memory. -/
theorem LoopAt.of_eq {i j : Nat} {m m' : MachineData} (h : LoopAt R ev cs m0 i j m)
    (hfr : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m')
    (hr : ∀ r, m'.regs.getXReg r = m.regs.getXReg r) (hd : m'.dmem = m.dmem) :
    LoopAt R ev cs m0 i j m' where
  fr := hfr
  x19 := (hr _).trans h.x19
  x20 hi := (hr _).trans (h.x20 hi)
  a := by rw [hr]; exact h.a
  c := by rw [hr]; exact h.c
  n := by rw [hr]; exact h.n
  p := by rw [hr]; exact h.p
  l := by rw [hr]; exact h.l
  j_le := h.j_le
  claims := by rw [hd]; exact h.claims

end

section
variable [Host] {k : Nat} {R : Regs} {ev : Array (Array EW × Array EW)} {cs : Array ColumnClaimW}
  {m0 : MachineData}

/-- **The head**: all values pushed, to the next table; else to the body. -/
theorem head (L : LB k R) (hpre : TableColumnClaimsPre ev cs m0) {i j : Nat}
    {Q : MachineState → Prop}
    (hnext : j = (valsOf ev i).size → ∀ m, LoopAt R ev cs m0 i j m →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jN)⟩)
    (hbody : j < (valsOf ev i).size → ∀ m, LoopAt R ev cs m0 i j m →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jH + L.H.length)⟩)
    {m : MachineData} (h : LoopAt R ev cs m0 i j m) :
    Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jH)⟩ := by
  obtain ⟨hmem, hsp, hall⟩ := L.okH
  refine Bus.Gkr.Fr.runBlock hpre.1 F_le rfl h.fr L.inH L.runH hmem hsp
    (all_sub hall fun r _ ↦ mem_allXRegs r) (by decide) fun st hfr hd hm hpc ↦ ?_
  have hr : ∀ r, st.data.regs.getXReg r = m.regs.getXReg r := fun r ↦
    Bus.Gkr.reg_of hm (reg_all hall (mem_allXRegs r))
  have h' := h.of_eq hfr hr hd
  have hn := h.n
  have hjl := h.j_le
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs,
    cmp_eq_lit _ _ (by decide : 0 < 2 ^ 64), hn] at hpc
  split at hpc
  next hc =>
    rw [L.lblN] at hpc
    exact Bus.Gkr.at_pc hpc (hnext (by simp at hc; omega) _ h')
  next hc =>
    exact Bus.Gkr.at_pc hpc (hbody (by simp at hc; omega) _ h')

/-- **One push**: the value's claim pushed; on to the head with `j + 1`, or, where it failed (the
claims do not fit), to the block after the loop with X0 zero. -/
theorem push (hpush : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (L : LB k R) (hpre : TableColumnClaimsPre ev cs m0) {i j : Nat} (hi : i < 6)
    (hj : j < (valsOf ev i).size) {Q : MachineState → Prop}
    (hfail : ∀ m, Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m → m.regs.X0 = 0 →
      ¬cs.size + (tableColumnClaims ev).size ≤ claimCap →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jF)⟩)
    (ih : ∀ m, LoopAt R ev cs m0 i (j + 1) m →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jH)⟩)
    {m : MachineData} (h : LoopAt R ev cs m0 i j m) :
    Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jH + L.H.length)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hin, hev, hcR, hcO, -⟩ := hpre'
  have hN := hS.2.1
  have hsz := vals_le hev hi
  have hpl := pt_le hev hi
  have hev6 : ev.size = 6 := hev.1
  -- `B`: the value's words, the arguments.
  have hinA := ReadIn.sub hin (o := 1968 * i + 496 + 16 * j) (k := 16)
    (by rw [evalsBytes_eq]; omega) (by rw [evalsBytes_eq]; omega)
  have hinP := ReadIn.sub hin (o := 1968 * i + 8) (k := 16 * (ptOf ev i).size)
    (by rw [evalsBytes_eq]; omega) (by rw [evalsBytes_eq]; omega)
  have hwf := Bus.wf_frame2 hS F_le h.fr.kept (a := (m.regs.getXReg R.a).toBitVec) (n := 16)
    (by rw [h.a]; exact hinA.1) (by rw [h.a]; exact hinA.2.1)
  have hm := Bus.match_frame2 (r := R.a) (n := 16) hS F_le rfl h.fr.sp
  refine exec_then L.inB L.runB hwf hm fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨bmem, bsp, ball, b0, b1, b2, b3, b4, b5, bc, bn, bs⟩ := L.okB
  have hfr2 : Fr m0 64 tableColumnClaimsStack slots keep (outs m0) st2.data :=
    Fr.ofBlock h.fr hm hm2 hwf rfl bmem (by rw [bsp]; rfl) fun r hr ↦
      ⟨.reg r, reg_all L.kB hr, reg_all ball (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))⟩
  have hd2 : st2.data.dmem = m.dmem := hm2.dmem_eq hwf bmem
  have x0 : st2.data.regs.X0 = m0.regs.X1 := (Bus.Gkr.reg_of hm2 b0).trans h.x19
  have x2 : st2.data.regs.X2.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (1968 * i + 8) :=
    (congrArg UInt64.toBitVec (Bus.Gkr.reg_of hm2 b2)).trans h.p
  have x3 : st2.data.regs.X3.toNat = (ptOf ev i).size :=
    (congrArg UInt64.toNat (Bus.Gkr.reg_of hm2 b3)).trans h.l
  have hv := NativeRustcVm.ewAt_iff.mp (val_at (evals_in hpre h.fr) hi hj)
  have x4 : st2.data.regs.X4 = (valsOf ev i)[j].c0 := by
    apply UInt64.toBitVec_inj.mp
    show (st2.data.regs.getXReg .X4).toBitVec = _
    rw [hm2.regs .X4 _ b4, Bus.load_r1, h.a, NativeRustcVm.addr_add_zero,
      NativeRustcVm.wordOf_of_wordAt hv.1]
  have x5 : st2.data.regs.X5 = (valsOf ev i)[j].c1 := by
    apply UInt64.toBitVec_inj.mp
    show (st2.data.regs.getXReg .X5).toBitVec = _
    rw [hm2.regs .X5 _ b5, Bus.load_r1, h.a, NativeRustcVm.wordOf_of_wordAt hv.2]
  have hc := h.c
  have hbl := base_le i
  have x1 : st2.data.regs.X1.toNat = globalColumnBasesW.getD i 0 + j := by
    show (st2.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm2.regs .X1 _ b1]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [add_lit _ _ (by show (m.regs.getXReg R.c).toNat + 1 < 2 ^ 64; omega)]
    show (m.regs.getXReg R.c).toNat + 1 = _
    omega
  have hsl : slice st2.data st2.data.regs.X2 st2.data.regs.X3 = ptOf ev i := by
    have hpt := NativeRustcVm.ewsOf_of_ewsAt (pt_at (evals_in hpre hfr2) hi)
    rw [Array.length_toList] at hpt
    unfold slice
    rw [x2, x3, hpt]
  -- The call.
  have hap : Apart m0.regs.X1.toBitVec claimsBytes (base m0 64) 64 := apart_frame hN F_le hcO
  have hfrO : ∀ q, outs m0 q → ¬InRange (base m0 64) 64 q := fun q hq ↦
    NativeRustcVm.Apart.not_inRange hap hcR.2 (base_noWrap (by have := F_le; omega)) hq
  have hP2 := ReadIn.fr hfr2 hS le_push hinP
  have hpc2' : st2.pc = Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel ∧
      retOf st2.data = Host.addrOf (k + L.jH + L.H.length + L.B.length) := hpc2
  refine Bus.Gkr.Fr.callSpec hfr2 hN le_push keep_callee slots_le hfrO
    (hpush (cs ++ (pre ev i j).toArray)) hpc2' ⟨hfr2.stackOk hS rfl le_push, ?_, ?_, ?_, ?_, ?_⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ hq'.elim
      (fun h' ↦ .inr (by rw [x0] at h'; exact h')) .inl, hq.2.2⟩) fun m3 hfr3 hq3 hcs3 ↦ ?_
  · rw [x0, hd2]; exact h.claims
  · rw [x0]; exact Bus.Fr.readable hfr2 hcR
  · rw [x0]; exact Bus.Fr.offStack hfr2 hS hcO le_push
  · unfold SliceOk; rw [x2, x3]; exact ⟨hP2.1, hP2.2.1⟩
  · rw [x0, x2, x3]
    exact NativeRustcVm.Apart.symm (hinP.2.2 ⟨m0.regs.X1.toBitVec, claimsBytes⟩ (by simp))
  -- `A`: the next value's address, the result.
  obtain ⟨amem, asp, aall, aa, ax0⟩ := L.okA
  refine Bus.Gkr.Fr.runBlock hS F_le rfl hfr3 L.inA L.runA amem asp
    (all_sub aall fun r hr ↦ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))))
    (by decide)
    fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_
  simp only [PcOk, L.evalA, Env.ofMachine_regs, L.fA] at hpc4
  have hm3 : ∀ r ∈ [XReg.X19, .X20, R.c, R.n, R.p, R.l, .X26, .X27, .X28, .X29],
      st4.data.regs.getXReg r = m3.regs.getXReg r := fun r hr ↦ Bus.Gkr.reg_of hm4 (reg_all aall hr)
  obtain ⟨hif, -, -⟩ := hq3
  split at hif
  next hok =>
    rw [show m3.regs.getXReg .X0 = 1 from hif.1, bit_one] at hpc4
    simp only [ite_true] at hpc4
    rw [L.lblH] at hpc4
    refine Bus.Gkr.at_pc hpc4 (ih _ ⟨hfr4, ?_, fun hi5 ↦ ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩)
    · rw [hm3 _ (by simp), hcs3 _ (saved_of L.saved (by simp)),
        Bus.Gkr.reg_of hm2 (reg_all ball (by simp))]
      exact h.x19
    · rw [hm3 _ (by simp), hcs3 _ (saved_of L.saved (by simp)),
        Bus.Gkr.reg_of hm2 (reg_all ball (by simp))]
      exact h.x20 hi5
    · rw [Bus.Gkr.reg_of hm4 aa, hcs3 _ (saved_of L.saved (by simp)), hm2.regs _ _ bs]
      show (m.regs.getXReg R.a).toBitVec + BitVec.ofInt 64 16 = _
      rw [h.a, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add,
        show 1968 * i + 496 + 16 * j + 16 = 1968 * i + 496 + 16 * (j + 1) by omega]
    · rw [hm3 _ (by simp), hcs3 _ (saved_of L.saved (by simp))]
      show (st2.data.regs.getXReg R.c).toBitVec.toNat + 1 = _
      rw [hm2.regs _ _ bc]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [add_lit _ _ (by show (m.regs.getXReg R.c).toNat + 1 < 2 ^ 64; omega)]
      show (m.regs.getXReg R.c).toNat + 1 + 1 = _
      omega
    · rw [hm3 _ (by simp), hcs3 _ (saved_of L.saved (by simp))]
      show (st2.data.regs.getXReg R.n).toBitVec.toNat = _
      rw [hm2.regs _ _ bn]
      simp only [Sym.eval, Env.ofMachine_regs]
      have hn := h.n
      rw [sub_lit _ _ (by show 16 ≤ (m.regs.getXReg R.n).toNat; omega)]
      show (m.regs.getXReg R.n).toNat - 16 = _
      omega
    · rw [hm3 _ (by simp), hcs3 _ (saved_of L.saved (by simp)),
        Bus.Gkr.reg_of hm2 (reg_all ball (by simp))]
      exact h.p
    · rw [hm3 _ (by simp), hcs3 _ (saved_of L.saved (by simp)),
        Bus.Gkr.reg_of hm2 (reg_all ball (by simp))]
      exact h.l
    · have hjc : j < (claimsOf ev i).length := by rw [length_claimsOf]; exact hj
      have hcl := getElem_claimsOf (ev := ev) i j hjc
      have h2 := hif.2
      rw [x0, x1, hsl, show ewArg st2.data.regs.X4 st2.data.regs.X5 = (valsOf ev i)[j] by
        rw [x4, x5]; rfl] at h2
      rw [hd4, ← push_eq hjc, hcl]
      exact h2
  next hfl =>
    have hx0 : st4.data.regs.X0 = 0 := by
      rcases ax0 with ax0 | ax0
      · exact (Bus.Gkr.reg_of hm4 ax0).trans hif
      · exact UInt64.toBitVec_inj.mp (Bus.Gkr.reg_lit hm4 ax0)
    rw [show m3.regs.getXReg .X0 = 0 from hif, bit_zero] at hpc4
    simp only [Bool.false_eq_true, ite_false] at hpc4
    refine Bus.Gkr.at_pc hpc4 (hfail _ hfr4 hx0 fun hfit ↦ hfl ⟨?_, ?_⟩)
    · have hlt := length_pre_lt (ev := ev) hi (j := j) (by rw [length_claimsOf]; exact hj) hev6
      simp only [Array.size_append, List.size_toArray]
      unfold claimCap at hfit ⊢
      omega
    · rw [x3]; unfold pointCap; omega

/-- **A table's loop**, from the head with `j` values pushed. -/
theorem loop (hpush : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (L : LB k R) (hpre : TableColumnClaimsPre ev cs m0) {i : Nat} (hi : i < 6)
    {Q : MachineState → Prop}
    (hnext : ∀ m, LoopAt R ev cs m0 i (valsOf ev i).size m →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jN)⟩)
    (hfail : ∀ m, Fr m0 64 tableColumnClaimsStack slots keep (outs m0) m → m.regs.X0 = 0 →
      ¬cs.size + (tableColumnClaims ev).size ≤ claimCap →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jF)⟩) :
    ∀ n j m, (valsOf ev i).size - j = n → LoopAt R ev cs m0 i j m →
      Eventually (step1 Host.exe) Q ⟨m, Host.addrOf (k + L.jH)⟩ := by
  intro n
  induction n with
  | zero =>
    intro j m hn h
    have := h.j_le
    exact head L hpre (fun hj m' h' ↦ by subst hj; exact hnext m' h') (fun hj ↦ by omega) h
  | succ n ih =>
    intro j m hn h
    exact head L hpre (fun hj ↦ by omega) (fun hj m' h' ↦
      push hpush L hpre hi hj hfail (fun m'' h'' ↦ ih (j + 1) m'' (by omega) h'') h') h

end

end

end NativeRustcVmArm.Tables.ColumnClaims
