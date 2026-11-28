module

public import NativeRustcVmX64.Sumcheck.OpenPhase.Frame

/-!
# `open_phase`: the shape, the count, the positions (x86-64)

`b0` saves the registers and loads the phase's count, height and width (`PhaseHW`); `b1` to `b5`
check the shape and the count (`check_spec`), `b6`, `b7` the positions one by one (`PInv`,
`pos_loop`); at `NativeRustcVmX64.Vm.OpenPhase.label_4` (`b10`) the phase passed them (`Checked`), else the exit with
`None` (`b8`).
-/

namespace NativeRustcVmX64.Sumcheck.OpenPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.OpenPhase NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Sumcheck LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- `open_phase`'s end: returned with its postcondition. -/
abbrev Done [Labels] (P : Array OpeningW) (R : Digest) (Q : Array UInt64) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ OpenPhasePost P R Q m0 st.data

/-- The registers the checks keep. -/
structure CRegs (m0 : MachineData) (P : Array OpeningW) (h w : Nat) (m : MachineData) : Prop where
  rdi : reg m .rdi = outO m0
  rsi : reg m .rsi = rootO m0
  r10 : reg m .r10 = h.toUInt64.toBitVec
  r13 : reg m .r13 = P.size.toUInt64.toBitVec
  r14 : reg m .r14 = w.toUInt64.toBitVec
  r15 : reg m .r15 = phO m0

/-- **The positions loop's invariant** at `NativeRustcVmX64.Vm.OpenPhase.label_3` (`b6`), `j` positions checked. -/
structure PInv (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (h w j : Nat)
    (m : MachineData) : Prop where
  fr : FrO m0 8 m
  regs : CRegs m0 P h w m
  shape : ShapeOk P Q h w (reg m0 .rdx).toNat (reg m0 .rcx).toNat
  le : j ≤ Q.size
  rax : (reg m .rax).toNat = 1544 * Q.size
  rcx : (reg m .rcx).toNat = 1544 * j
  r8 : reg m .r8 = off (posO m0) (8 * j)
  rbp : reg m .rbp = off (phO m0) 24
  pos : PositionsOk P Q j

/-- At `NativeRustcVmX64.Vm.OpenPhase.label_4` (`b10`): the checks passed. -/
structure Checked (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (h w : Nat)
    (m : MachineData) : Prop where
  fr : FrO m0 8 m
  regs : CRegs m0 P h w m
  shape : ShapeOk P Q h w (reg m0 .rdx).toNat (reg m0 .rcx).toNat
  rbp : reg m .rbp = off (phO m0) 24
  pos : PositionsOk P Q P.size

end

public section

variable {m0 m m' : MachineData} {P : Array OpeningW} {h w : Nat}

theorem CRegs.keep (hc : CRegs m0 P h w m) {rs : List Reg64}
    (hk : ∀ r, r ≠ .rsp → rs.contains r = false → reg m' r = reg m r)
    (h1 : rs.contains .rdi = false) (h2 : rs.contains .rsi = false)
    (h3 : rs.contains .r10 = false) (h4 : rs.contains .r13 = false)
    (h5 : rs.contains .r14 = false) (h6 : rs.contains .r15 = false) : CRegs m0 P h w m' :=
  ⟨(hk _ (by decide) h1).trans hc.rdi, (hk _ (by decide) h2).trans hc.rsi,
    (hk _ (by decide) h3).trans hc.r10, (hk _ (by decide) h4).trans hc.r13,
    (hk _ (by decide) h5).trans hc.r14, (hk _ (by decide) h6).trans hc.r15⟩

theorem isZero_eval [Labels] (env : Env) (s : Sym) :
    (isZero s).eval env = (s.eval env == 0#64) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]

theorem beq_zero_toUInt64 {x : Nat} (hx : x < 2 ^ 64) :
    (x.toUInt64.toBitVec == 0#64) = decide (x = 0) :=
  toUInt64_beq hx 0#64

variable [Host] {R : Digest} {Q : Array UInt64} {k : Nat}

/-- **A step of the positions loop**: from `b6`, the exit with `None`, `b10` after the last
position, or `b6` one position on. -/
theorem pos_step (hp : Placed code k) (hpre : OpenPhasePre P R Q m0)
    (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat} (hi : PInv m0 P Q h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Done P R Q m0 st ∨ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b6Offset) ∧ j < Q.size ∧ PInv m0 P Q h w (j + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b6Offset)⟩ := by
  have hst := hpre.1
  obtain ⟨-, -, -, -, -, hQn, hQw, hmp, hnwp, -, hnwq, -, -, haps, -, haqs, -, -, -, -, -, haqp, -⟩ :=
    id hpre
  have hsize := hi.shape.2
  have hPq : P.size ≤ 256 := hph.2.2.1
  have hpw : phaseWords = 49411 := rfl
  have how : openingWords = 193 := rfl
  refine frTest hst hi.fr (infix_of b6_in_code (by simp [b6]) hp) exit_b6 nofun ok_b6.1 ok_b6.2.1
    ok_b6.2.2 fun st hf hd hk hm hpc ↦ ?_
  have hc : (CmpOp.apply .eq .W64 (m.regs.get64 .rax) (m.regs.get64 .rcx)) =
      decide (j = Q.size) := by
    simp only [CmpOp.apply, low_W64]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
    show (reg m .rax).toNat = (reg m .rcx).toNat ↔ _
    rw [hi.rax, hi.rcx]
    omega
  simp only [PcOk, c6, SBool.eval, Sym.eval, Env.ofMachine_regs, hc] at hpc
  have hregs : CRegs m0 P h w st.data :=
    hi.regs.keep hk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrbp : reg st.data .rbp = off (phO m0) 24 := (hk _ (by decide) (by decide)).trans hi.rbp
  by_cases hj : j = Q.size
  · simp only [hj, decide_true, ↓reduceIte] at hpc
    refine .done _ (.inr (.inl ⟨hpc.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_4_at), hf, hregs, hi.shape, hrbp, ?_⟩))
    rw [hsize, ← hj]; exact hi.pos
  simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc
  have hjl : j < Q.size := Nat.lt_of_le_of_ne hi.le hj
  have hjP : j < P.size := by omega
  -- `b7`: position `j` against opening `j`'s leaf index.
  have hS := stk_toNat hst
  have hfa : (stackBelow m0 176).toNat = (rspOf m0).toNat - 176 := fa_toNat hst
  have h8 := hst.2.1
  have hN := hst.1
  rw [openPhaseStack_eq] at hN
  have hnwp' : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hnwp
  have hnwq' : (posO m0).toNat + 8 * (reg m0 .r9).toNat ≤ 2 ^ 64 := hnwq
  have haps' : (phO m0).toNat + 8 * phaseWords ≤ (stackBelow m0 openPhaseStack).toNat ∨
      (stackBelow m0 openPhaseStack).toNat + (openPhaseStack + 8) ≤ (phO m0).toNat := haps
  have haqs' : (posO m0).toNat + 8 * (reg m0 .r9).toNat ≤
      (stackBelow m0 openPhaseStack).toNat ∨
      (stackBelow m0 openPhaseStack).toNat + (openPhaseStack + 8) ≤ (posO m0).toNat := haqs
  have haqp' : (posO m0).toNat + 8 * (reg m0 .r9).toNat ≤ (phO m0).toNat ∨
      (phO m0).toNat + 8 * phaseWords ≤ (posO m0).toNat := haqp
  rw [hS, openPhaseStack_eq] at haps' haqs'
  rw [← hQn] at hnwq' haqs' haqp'
  have hqoff : (off (posO m0) (8 * j)).toNat = (posO m0).toNat + 8 * j := toNat_off (by omega)
  have hpoff : (off (phO m0) (24 + 1544 * j)).toNat = (phO m0).toNat + (24 + 1544 * j) :=
    toNat_off (by omega)
  have hq : NativeRustcVm.WordAt st.data.dmem (off (posO m0) (8 * j)) Q[j] := by
    have := hQw.getElem (i := j) (by simpa using hjl)
    simp only [Array.getElem_toList] at this
    exact keepB hst hf.same (n := 8) (by unfold NativeRustcVm.NoWrap; rw [hqoff]; omega)
      (by unfold NativeRustcVm.Apart; rw [hqoff, hS, openPhaseStack_eq]; omega)
      (by rw [NativeRustcVm.length_wordBytes]) this
  have hidx : NativeRustcVm.WordAt st.data.dmem (off (phO m0) (24 + 1544 * j))
      P[j].leafIndex := by
    have := (hph.2.2.2.2.2.2 j hjP).2.2.2.1
    rw [show 8 * (3 + j * openingWords) = 24 + 1544 * j by rw [how]; omega] at this
    exact ph_word hpre hf.same (by omega) this
  have hwf7 := frame_wf (m0 := m0) (d := st.data) (F := 176)
    (rest := [(off (posO m0) (8 * j), 8), (off (phO m0) (24 + 1544 * j), 8)])
    (vars := fun _ ↦ 0) (ret := 0)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hf.frame.kept, fa_noWrap hst⟩
    (rest2_ok ⟨mapped_off (Mapped.keeps hQw.mapped hf.frame.kept) (by
        rw [Array.length_toList]; omega), by unfold NativeRustcVm.NoWrap; rw [hqoff]; omega⟩
      ⟨mapped_off (Mapped.keeps hmp hf.frame.kept) (by omega),
        by unfold NativeRustcVm.NoWrap; rw [hpoff]; omega⟩ fun _ h ↦ h)
    (pairwise3 (by unfold NativeRustcVm.Apart; dsimp only; rw [hfa, hqoff]; omega)
      (by unfold NativeRustcVm.Apart; dsimp only; rw [hfa, hpoff]; omega)
      (by unfold NativeRustcVm.Apart; dsimp only; rw [hqoff, hpoff]; omega))
  have hr8 : reg st.data .r8 = off (posO m0) (8 * j) := (hk _ (by decide) (by decide)).trans hi.r8
  have hrcx : (reg st.data .rcx).toNat = 1544 * j := by
    rw [hk _ (by decide) (by decide)]; exact hi.rcx
  have hm7 : Match (frameEnv m0 st.data 176 [(off (posO m0) (8 * j), 8),
      (off (phO m0) (24 + 1544 * j), 8)] (fun _ ↦ 0) 0) posS st.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, known_ptr rfl hr8, trivial⟩
      trivial trivial ⟨?_, trivial⟩
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [ofInt_zero64, BitVec.add_zero]
    show reg st.data .rbp + reg st.data .rcx = off (phO m0) (24 + 1544 * j)
    rw [hrbp]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, toNat_off (by omega), hrcx, hpoff]
    omega
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf7 nofun
    (hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b6_next)) hm7 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hrcx1, hr81, hkb1⟩ := ok_b7
  have hf1 : FrO m0 8 st1.data := FrO.block hst hf hwf7 hm1 hmid1 (memNil hmem1)
  have hk1 : ∀ r, r ≠ .rsp → [Reg64.rcx, .rdx, .r8].contains r = false →
      reg st1.data r = reg st.data r := fun r h1 h2 ↦ KeepBut.regs hkb1 hm1 h1 h2
  have hl1 : (frameEnv m0 st.data 176 [(off (posO m0) (8 * j), 8),
      (off (phO m0) (24 + 1544 * j), 8)] (fun _ ↦ 0) 0).load 1 0 8 = Q[j].toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hq)
  have hl2 : (frameEnv m0 st.data 176 [(off (posO m0) (8 * j), 8),
      (off (phO m0) (24 + 1544 * j), 8)] (fun _ ↦ 0) 0).load 2 0 8 = P[j].leafIndex.toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hidx)
  simp only [PcOk, c7, SBool.eval, CmpOp.apply, Sym.eval, low_W64, hl1, hl2] at hpc1
  have hregs1 : CRegs m0 P h w st1.data :=
    hregs.keep hk1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  by_cases heq : P[j].leafIndex = Q[j]
  · have e : (P[j].leafIndex.toBitVec == Q[j].toBitVec) = true := by simp [heq]
    simp only [e, ↓reduceIte] at hpc1
    refine .done _ (.inr (.inr ⟨hpc1.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_3_at), hjl, hf1, hregs1, hi.shape,
      by omega, ?_, ?_, ?_, ?_, (positionsOk_succ hjP (by omega)).2 ⟨hi.pos, heq⟩⟩))
    · rw [hk1 _ (by decide) (by decide), hk _ (by decide) (by decide)]; exact hi.rax
    · rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx1]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [BitVec.toNat_add, show (st.data.regs.get64 .rcx).toNat = 1544 * j from hrcx]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [show reg st1.data .r8 = _ from hm1.regs .r8 _ hr81]
      show off (posO m0) (8 * j) + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, off_add]
      congr 1
    · rw [hk1 _ (by decide) (by decide)]; exact hrbp
  · have e : (P[j].leafIndex.toBitVec == Q[j].toBitVec) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h' ↦ heq (UInt64.toBitVec_inj.mp h')
    simp only [e, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    have hpc1' : pc1 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b8Offset) := hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b7_next)
    subst hpc1'
    refine Eventually.mono (exit_fail8 hp hpre hf1 hregs1.rdi (openPhase_none hph ?_))
      fun st h ↦ .inl h
    rintro ⟨-, -, hpos⟩
    exact heq (hpos j hjP (by omega) (by omega))

/-- **The positions loop**: from `b6`, the exit with `None` or `b10`. -/
theorem pos_loop (hp : Placed code k) (hpre : OpenPhasePre P R Q m0)
    (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat} (hi : PInv m0 P Q h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Done P R Q m0 st ∨ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b6Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b6Offset) ∧
      ∃ j, Q.size - j = n ∧ PInv m0 P Q h w j st.data) (fun n st ⟨hpc, j, hn, hi⟩ ↦ ?_)
    ⟨rfl, j, rfl, hi⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hn
  refine Eventually.mono (pos_step hp hpre hph hi) fun st h ↦ ?_
  rcases h with h | h | ⟨hpc, hlt, hinv⟩
  · exact .inl (.inl h)
  · exact .inl (.inr h)
  · exact .inr ⟨Q.size - (j + 1), by omega, hpc, j + 1, rfl, hinv⟩

/-- **`b5`**: from `NativeRustcVmX64.Vm.OpenPhase.label_2`, the positions loop's start. -/
theorem b5_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0)
    (hph : PhaseHW m0.dmem (phO m0) P h w) (hf : FrO m0 8 m) (hr : CRegs m0 P h w m)
    (hsh : ShapeOk P Q h w (reg m0 .rdx).toNat (reg m0 .rcx).toNat)
    (hr8 : reg m .r8 = posO m0) (hr9 : reg m .r9 = reg m0 .r9) :
    Eventually (step1 Host.exe)
      (fun st ↦ Done P R Q m0 st ∨ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b5Offset)⟩ := by
  have hst := hpre.1
  obtain ⟨hmid, hmem, hbp, hax, hcx, hkb⟩ := ok_b5
  refine frTest hst hf (infix_of b5_in_code (by simp [b5]) hp) exit_b5 nofun hmid hmem hkb
    fun st hf1 hd hk hm hpc ↦ ?_
  have hQn : Q.size = (reg m0 .r9).toNat := hpre.2.2.2.2.2.1
  have hPq : P.size ≤ 256 := hph.2.2.1
  have hsz := hsh.2
  obtain ⟨d, pc⟩ := st
  have hpc' : pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b6Offset) := hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b5_next)
  subst hpc'
  refine pos_loop hp hpre hph (j := 0) ⟨hf1, hr.keep hk (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide), hsh, Nat.zero_le _, ?_, ?_, ?_, ?_, positionsOk_zero P Q⟩
  · rw [show reg d .rax = _ from hm.regs .rax _ hax]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    show (reg m .r9 * BitVec.ofNat 64 1544).toNat = _
    rw [BitVec.toNat_mul, hr9, ← hQn, BitVec.toNat_ofNat]
    omega
  · rw [show reg d .rcx = _ from hm.regs .rcx _ hcx]; rfl
  · rw [hk _ (by decide) (by decide), hr8, Nat.mul_zero, off_zero]
  · rw [show reg d .rbp = _ from hm.regs .rbp _ hbp]
    show reg m .r15 + _ = _
    rw [hr.r15]
    rfl

/-- **The entry**: the exit with `None`, or `b10` with the checks passed. -/
theorem check_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0)
    (hph : PhaseHW m0.dmem (phO m0) P h w) :
    Eventually (step1 Host.exe)
      (fun st ↦ Done P R Q m0 st ∨ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b0Offset)⟩ := by
  have hst := hpre.1
  obtain ⟨-, -, hargs, -, -, hQn, -, hmp, hnwp, -, -, -, -, haps, -⟩ := id hpre
  have hpw : phaseWords = 49411 := rfl
  have hmq : wireMaxQueries = 256 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  have hmh : wireMaxHeight = 32 := rfl
  obtain ⟨hh, hw, hsz, hc0, hc8, hc16, -⟩ := id hph
  have hN := hst.1
  have h8 := hst.2.1
  rw [openPhaseStack_eq] at hN
  have hfa : (stackBelow m0 176).toNat = (rspOf m0).toNat - 176 := fa_toNat hst
  have hS0 := stk_toNat hst
  have ha2 : (rspOf m0).toNat + 8 + 8 * 1 ≤ 2 ^ 64 := hargs.2
  have hsa : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 :=
    toNat_off (b := rspOf m0) (j := 8) (by omega)
  have hnwp' : (phO m0).toNat + 8 * phaseWords ≤ 2 ^ 64 := hnwp
  have haps' : (phO m0).toNat + 8 * phaseWords ≤ (stackBelow m0 openPhaseStack).toNat ∨
      (stackBelow m0 openPhaseStack).toNat + (openPhaseStack + 8) ≤ (phO m0).toNat := haps
  rw [hS0, openPhaseStack_eq] at haps'
  have hQn' : Q.size = (reg m0 .r9).toNat := hQn
  -- The exits.
  have fail8 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b8Offset) → FrO m0 8 st.data →
      reg st.data .rdi = outO m0 → openPhase R (reg m0 .rdx).toNat (reg m0 .rcx).toNat Q P = none →
      Eventually (step1 Host.exe) (fun st ↦ Done P R Q m0 st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data)) st := by
    intro st hpc hf hdi hr
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact Eventually.mono (exit_fail8 hp hpre hf hdi hr) fun st h ↦ .inl h
  have toB5 : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b5Offset) → FrO m0 8 st.data →
      CRegs m0 P h w st.data → ShapeOk P Q h w (reg m0 .rdx).toNat (reg m0 .rcx).toNat →
      reg st.data .r8 = posO m0 → reg st.data .r9 = reg m0 .r9 →
      Eventually (step1 Host.exe) (fun st ↦ Done P R Q m0 st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data)) st := by
    intro st hpc hf hr hsh h8' h9'
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact b5_spec hp hpre hph hf hr hsh h8' h9'
  -- `b0a`: the prologue, the phase's address.
  have hwfA := frame_wf (m0 := m0) (d := m0) (F := 176) (rest := [(rspOf m0 + 8#64, 8)])
    (vars := fun _ ↦ 0) (ret := 0) ⟨frame_mapped hst (by decide), fa_noWrap hst⟩
    (fun z hz ↦ by
      rw [List.mem_singleton] at hz; subst hz
      exact ⟨hargs.1, by show (rspOf m0 + 8#64).toNat + 8 ≤ 2 ^ 64; omega⟩)
    (List.pairwise_pair.mpr (by
      show (stackBelow m0 176).toNat + (176 + 8) ≤ (rspOf m0 + 8#64).toNat ∨
        (rspOf m0 + 8#64).toNat + 8 ≤ (stackBelow m0 176).toNat
      omega))
  have hal : (Sym.ptr 0 184).eval (frameEnv m0 m0 176 [(rspOf m0 + 8#64, 8)] (fun _ ↦ 0) 0) =
      (frameEnv m0 m0 176 [(rspOf m0 + 8#64, 8)] (fun _ ↦ 0) 0).base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero]
    exact (eval_ptr0 (F := 176) 184).trans (frame_add 176 8)
  refine exec_then (infix_of b0a_in_code b0a_ne hp) exit_b0a hwfA nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial ⟨hal, trivial⟩)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hws, hr15a, hkba⟩ := ok_b0a
  have hf1 : FrO m0 8 st1.data :=
    ⟨Frame.of_prologue Frame.entry hwfA hm1 hpro slots_le slots_cs,
      NativeRustcVm.SameOutside.mono (sameOutside_low hwfA hm1 (r := 0) rfl (hi := 176)
        (by omega) hws) fun q hq ↦ fa_stk hst hq⟩
  have hk1 : ∀ r, r ≠ .rsp → [Reg64.r15].contains r = false → reg st1.data r = reg m0 r :=
    fun r h1 h2 ↦ KeepBut.regs hkba hm1 h1 h2
  have hr15 : reg st1.data .r15 = phO m0 := by
    rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ hr15a]
    show Env.load _ 1 0 8 = _
    rw [load_ofMachine (o := 0) (w := NativeRustcVm.wordOf m0.dmem (rspOf m0 + 8#64)) rfl
      (by rw [off_zero]; exact NativeRustcVm.wordAt_of_mapped hargs.1)]
    rfl
  -- `b0b`: the phase's counts.
  have hwfB := wf1 (o := 8) (ret := 0) hst hf1 (x := phO m0) (n := 24)
    (Mapped.keeps (fun i hi ↦ hmp i (by omega)) hf1.frame.kept)
    (by show (phO m0).toNat + 24 ≤ 2 ^ 64; omega)
    (by show (phO m0).toNat + 24 ≤ _ ∨ _; rw [hS0, openPhaseStack_eq]; omega)
  have l0 : (frameEnv m0 st1.data 176 [(phO m0, 24)] (fun _ ↦ 0) 0).load 1 0 8 =
      P.size.toUInt64.toBitVec := load_ofMachine (o := 0) rfl
    (ph_word hpre hf1.same (by omega) (by rw [off_zero]; exact hc0))
  have l8 : (frameEnv m0 st1.data 176 [(phO m0, 24)] (fun _ ↦ 0) 0).load 1 8 8 =
      h.toUInt64.toBitVec := load_ofMachine (o := 8) rfl (ph_word hpre hf1.same (by omega) hc8)
  have l16 : (frameEnv m0 st1.data 176 [(phO m0, 24)] (fun _ ↦ 0) 0).load 1 16 8 =
      w.toUInt64.toBitVec := load_ofMachine (o := 16) rfl (ph_word hpre hf1.same (by omega) hc16)
  refine exec_at (infix_of b0b_in_code b0b_ne hp) exit_b0b hwfB nofun
    (hpc1.trans (by rw [Nat.add_assoc]))
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf1.frame.rsp_eval, known_ptr rfl hr15, trivial⟩
      trivial trivial trivial) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmidB, hmemB, h13B, h10B, h14B, h15B, hkbB⟩ := ok_b0b
  have hf2 : FrO m0 8 st2.data := FrO.block hst hf1 hwfB hm2 hmidB (memNil hmemB)
  have hk2 : ∀ r, r ≠ .rsp → [Reg64.r10, .r13, .r14, .r15].contains r = false →
      reg st2.data r = reg m0 r := fun r h1 h2 ↦
    (KeepBut.regs hkbB hm2 h1 h2).trans (hk1 r h1 (by revert h2; cases r <;> decide))
  have hregs : CRegs m0 P h w st2.data :=
    ⟨hk2 _ (by decide) (by decide), hk2 _ (by decide) (by decide),
      (hm2.regs .r10 _ h10B).trans l8, (hm2.regs .r13 _ h13B).trans l0,
      (hm2.regs .r14 _ h14B).trans l16, (hm2.regs .r15 _ h15B).trans (eval_ptr rfl)⟩
  have hc2 : (isZero (.load 1 0 8)).eval (frameEnv m0 st1.data 176 [(phO m0, 24)] (fun _ ↦ 0) 0) =
      decide (P.size = 0) := by
    rw [isZero_eval]
    show (Env.load _ 1 0 8 == 0#64) = _
    rw [l0, beq_zero_toUInt64 (by omega)]
  simp only [PcOk, hc2] at hpc2
  obtain ⟨d2, pc2⟩ := st2
  simp only at hf2 hk2 hregs hpc2
  by_cases h0 : P.size = 0
  · -- No opening: `b4`, the positions must be none too.
    simp only [h0, decide_true, ↓reduceIte] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.OpenPhase.label_1_at] at hpc2
    subst hpc2
    obtain ⟨hmid4, hmem4, hk4⟩ := ok_b4
    refine frTest hst hf2 (infix_of b4_in_code (by simp [b4]) hp) exit_b4 nofun hmid4 hmem4 hk4
      fun st hf hd hk hm hpc ↦ ?_
    have hr9 : reg d2 .r9 = reg m0 .r9 := hk2 _ (by decide) (by decide)
    have hc : (isZero (.reg .r9)).not.eval (frameEnv m0 d2 176 [] (fun _ ↦ 0) 0) =
        !decide (Q.size = 0) := by
      rw [SBool.eval, isZero_eval]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [show d2.regs.get64 .r9 = reg m0 .r9 from hr9, bv_beq_zero, ← hQn']
    simp only [PcOk, hc] at hpc
    have hrg := hregs.keep hk (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    by_cases hq0 : Q.size = 0
    · simp only [hq0, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
      exact toB5 st (hpc.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b4_next)) hf hrg
        ⟨.inl h0, by omega⟩ ((hk _ (by decide) (by decide)).trans (hk2 _ (by decide) (by decide)))
        ((hk _ (by decide) (by decide)).trans hr9)
    · simp only [hq0, decide_false, Bool.not_false, ↓reduceIte] at hpc
      exact fail8 st (hpc.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_16_at)) hf hrg.rdi
        (openPhase_none hph fun ⟨_, hs, _⟩ ↦ hq0 (by omega))
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
    have hpc2' : pc2 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b1Offset) := hpc2.trans (by change Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b0Offset + b0.length) = _; rw [Nat.add_assoc, NativeRustcVmX64.Vm.OpenPhase.b0_next])
    subst hpc2'
    -- `b1`: the width.
    obtain ⟨hmid1, hmem1, hk1'⟩ := ok_b1
    refine frTest hst hf2 (infix_of b1_in_code (by simp [b1]) hp) exit_b1 nofun hmid1 hmem1 hk1'
      fun st3 hf3 hd3 hk3 hm3 hpc3 ↦ ?_
    have hrg3 := hregs.keep hk3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have hk3' : ∀ r, r ≠ .rsp → [Reg64.r10, .r13, .r14, .r15].contains r = false →
        reg st3.data r = reg m0 r := fun r h1 h2 ↦ (hk3 r h1 rfl).trans (hk2 r h1 h2)
    have hc : c1.eval (frameEnv m0 d2 176 [] (fun _ ↦ 0) 0) =
        !decide (w = (reg m0 .rcx).toNat) := by
      simp only [c1, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
      rw [show d2.regs.get64 .r14 = w.toUInt64.toBitVec from hregs.r14,
        show d2.regs.get64 .rcx = reg m0 .rcx from hk2 _ (by decide) (by decide),
        toUInt64_beq (by omega)]
    simp only [PcOk, hc] at hpc3
    by_cases hwW : w = (reg m0 .rcx).toNat
    swap
    · simp only [hwW, decide_false, Bool.not_false, ↓reduceIte] at hpc3
      exact fail8 st3 (hpc3.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_16_at)) hf3 hrg3.rdi
        (openPhase_none hph fun ⟨hs, _, _⟩ ↦ hs.elim h0 fun ⟨e, _⟩ ↦ hwW e)
    simp only [hwW, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    have hpc3' : pc3 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b2Offset) := hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b1_next)
    subst hpc3'
    -- `b2`: the count and the height.
    obtain ⟨hmid2, hmem2, hk2'⟩ := ok_b2
    refine frTest hst hf3 (infix_of b2_in_code (by simp [b2]) hp) exit_b2 nofun hmid2 hmem2 hk2'
      fun st4 hf4 hd4 hk4 hm4 hpc4 ↦ ?_
    have hrg4 := hrg3.keep hk4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have hc : c2.eval (frameEnv m0 d3 176 [] (fun _ ↦ 0) 0) =
        (decide (P.size = Q.size) && decide (h = (reg m0 .rdx).toNat)) := by
      simp only [c2, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
        Env.ofMachine_regs]
      rw [show d3.regs.get64 .r13 = P.size.toUInt64.toBitVec from hrg3.r13,
        show d3.regs.get64 .r10 = h.toUInt64.toBitVec from hrg3.r10,
        show d3.regs.get64 .r9 = reg m0 .r9 from hk3' _ (by decide) (by decide),
        show d3.regs.get64 .rdx = reg m0 .rdx from hk3' _ (by decide) (by decide),
        xor_or_beq, toUInt64_beq (by omega), beq_toUInt64 (by omega), ← hQn']
    simp only [PcOk, hc] at hpc4
    by_cases hc4 : P.size = Q.size ∧ h = (reg m0 .rdx).toNat
    · simp only [hc4, decide_true, Bool.and_self, ↓reduceIte] at hpc4
      exact toB5 st4 (hpc4.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_2_at)) hf4 hrg4 ⟨.inr ⟨hwW, hc4.2⟩, hc4.1⟩
        ((hk4 _ (by decide) (by decide)).trans (hk3' _ (by decide) (by decide)))
        ((hk4 _ (by decide) (by decide)).trans (hk3' _ (by decide) (by decide)))
    · have hf' : (decide (P.size = Q.size) && decide (h = (reg m0 .rdx).toNat)) = false := by
        simpa [Bool.and_eq_true] using hc4
      simp only [hf', Bool.false_eq_true, ↓reduceIte] at hpc4
      obtain ⟨d4, pc4⟩ := st4
      have hpc4' : pc4 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b3Offset) := hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b2_next)
      subst hpc4'
      obtain ⟨hmid3, hmem3, hk3''⟩ := ok_b3
      refine frTest hst hf4 (infix_of b3_in_code (by simp [b3]) hp) exit_b3 nofun hmid3 hmem3
        hk3'' fun st5 hf5 hd5 hk5 hm5 hpc5 ↦ ?_
      simp only [PcOk] at hpc5
      exact fail8 st5 (hpc5.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_16_at)) hf5
        ((hk5 _ (by decide) (by decide)).trans hrg4.rdi)
        (openPhase_none hph fun ⟨hs, hPQ, _⟩ ↦ hc4 ⟨hPQ, (hs.resolve_left h0).2⟩)

end

end NativeRustcVmX64.Sumcheck.OpenPhase
