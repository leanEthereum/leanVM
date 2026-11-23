module

public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Sumcheck.OpenPhase.Frame

/-!
# `open_phase`: the shape, the count, the positions

`b0` saves the registers and loads the phase's count, height and width (`PhaseHW`); `b1` to `b5`
check the shape and the count, `b6` to `b9` the positions one by one (`PInv`, `pos_loop`); at
`.L8` the phase passed them (`Checked`, `check_spec`), else the exit with `None`.
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

@[expose] public section

/-- `PhaseAt` with its height `h` and width `w`. -/
def PhaseHW (d : Mem 64) (b : BitVec 64) (P : Array OpeningW) (h w : Nat) : Prop :=
  h ≤ wireMaxHeight ∧ w ≤ wireMaxLeafWords ∧ P.size ≤ wireMaxQueries ∧
    NativeRustcVm.WordAt d b P.size.toUInt64 ∧ NativeRustcVm.WordAt d (off b 8) h.toUInt64 ∧
    NativeRustcVm.WordAt d (off b 16) w.toUInt64 ∧
    ∀ j (hj : j < P.size), OpeningAt d (off b (8 * (3 + j * openingWords))) h w P[j]

/-- What the shape check asks, the count's, and the positions' up to `j`. -/
def ShapeOk (P : Array OpeningW) (Q : Array UInt64) (h w height width : Nat) : Prop :=
  (P.size = 0 ∨ (w = width ∧ h = height)) ∧ P.size = Q.size

/-- The registers the checks keep. -/
structure Regs (m0 : MachineData) (P : Array OpeningW) (h w : Nat) (m : MachineData) : Prop where
  x1 : m.regs.getXReg .X1 = m0.regs.X1
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : m.regs.getXReg .X20 = m0.regs.X6
  x21 : m.regs.getXReg .X21 = w.toUInt64
  x22 : m.regs.getXReg .X22 = h.toUInt64
  x23 : m.regs.getXReg .X23 = P.size.toUInt64

/-- **The positions loop's invariant** at `.L6`, `j` positions checked. -/
structure PInv [Labels] (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (h w j : Nat)
    (m : MachineData) : Prop where
  fr : FrO m0 m
  regs : Regs m0 P h w m
  shape : ShapeOk P Q h w m0.regs.X2.toNat m0.regs.X3.toNat
  le : j ≤ Q.size
  x8 : (m.regs.getXReg .X8).toNat = 8 * (Q.size - j)
  x4 : (m.regs.getXReg .X4).toBitVec = posO m0 + BitVec.ofNat 64 (8 * j)
  x9 : (m.regs.getXReg .X9).toBitVec = phO m0 + BitVec.ofNat 64 (24 + 1544 * j)
  pos : PositionsOk P Q j

/-- At `.L8`: the checks passed. -/
structure Checked [Labels] (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (h w : Nat)
    (m : MachineData) : Prop where
  fr : FrO m0 m
  regs : Regs m0 P h w m
  shape : ShapeOk P Q h w m0.regs.X2.toNat m0.regs.X3.toNat
  pos : PositionsOk P Q P.size

end

public section

/-- The openings' shape, from `PhaseHW`. -/
theorem PhaseHW.shape {d : Mem 64} {b : BitVec 64} {P : Array OpeningW} {h w : Nat}
    (hph : PhaseHW d b P h w) : ∀ j (hj : j < P.size), P[j].leaf.size = w ∧ P[j].path.size = h :=
  fun j hj ↦ ⟨(hph.2.2.2.2.2.2 j hj).1, (hph.2.2.2.2.2.2 j hj).2.1⟩

/-- **The model rejects** where the checks fail. -/
theorem openPhase_none {R : Digest} {height width : Nat} {Q : Array UInt64} {P : Array OpeningW}
    {d : Mem 64} {b : BitVec 64} {h w : Nat} (hph : PhaseHW d b P h w)
    (hn : ¬ ((P.size = 0 ∨ (w = width ∧ h = height)) ∧ P.size = Q.size ∧
      PositionsOk P Q P.size)) :
    openPhase R height width Q P = none := by
  rw [openPhase_eq hph.shape, ite_eq_right hn]

theorem toUInt64_eq_iff {x : Nat} (hx : x < 2 ^ 64) (y : UInt64) :
    (x.toUInt64.toBitVec == y.toBitVec) = (x == y.toNat) := by
  have hy := y.toNat_lt
  by_cases h : x = y.toNat
  · subst h; simp
  · have : x.toUInt64.toBitVec ≠ y.toBitVec := fun e ↦ h (by
      have := congrArg BitVec.toNat e
      simp only [UInt64.toNat_toBitVec] at this
      rw [← this]; simp [Nat.toUInt64]; omega)
    simp [this, h]

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}

/-- A word of an input apart from the stack, kept in a state of the frame. -/
theorem keepWord (hpre : OpenPhasePre P R Q m0) {m : MachineData} (hf : FrO m0 m)
    {x : BitVec 64} {n o : Nat} (hnw : NoWrap x n)
    (hap : Apart x n (stackBelow m0 openPhaseStack) openPhaseStack) (hon : o + 8 ≤ n) {v : UInt64}
    (h : NativeRustcVm.WordAt m0.dmem (x + BitVec.ofNat 64 o) v) :
    NativeRustcVm.WordAt m.dmem (x + BitVec.ofNat 64 o) v := by
  have hoff : (x + BitVec.ofNat 64 o).toNat = x.toNat + o := by
    unfold NoWrap at hnw; exact NativeRustcVm.toNat_add_ofNat (by omega)
  exact keep hpre hf (n := 8) (by unfold NoWrap at hnw ⊢; rw [hoff]; omega)
    (NativeRustcVm.Apart.mono hap (by rw [hoff]; omega) (by rw [hoff]; omega) (Nat.le_refl _)
      (Nat.le_refl _)) (le_of_eq (NativeRustcVm.length_wordBytes v)) h

/-- **A step of the positions loop**: from `.L6`, the exit with `None`, `.L8` after the last
position, or `.L6` one position on. -/
theorem pos_step (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {h w : Nat}
    (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat} {m : MachineData} (hi : PInv m0 P Q h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b7Offset) ∧ j < Q.size ∧ PInv m0 P Q h w (j + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b7Offset)⟩ := by
  have hS := hpre.1
  have hN' := hN hpre
  rw [openPhaseStack_eq] at hN'
  obtain ⟨-, -, -, -, hqn, hposw, hmp, hnwp, -, hnwq, -, -, haps, -, hapq, -, -, -, -, -,
    hqp⟩ := id hpre
  have hpw : phaseWords = 49411 := rfl
  have how : openingWords = 193 := rfl
  have hmq : wireMaxQueries = 256 := rfl
  have hsize := hi.shape.2
  have hPq : P.size ≤ 256 := hph.2.2.1
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b7Offset) := b7_in_code.trans hp.1 (by simp [b7])
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b8Offset) := b8_in_code.trans hp.1 (by simp [b8])
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b9Offset) := b9_in_code.trans hp.1 (by simp [b9])
  have hl8 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b10Offset) NativeRustcVmArm.Vm.OpenPhase.label_8_at
  have hl6 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b7Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b7Offset) NativeRustcVmArm.Vm.OpenPhase.label_6_at
  have hl18 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_18 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b22Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b22Offset) NativeRustcVmArm.Vm.OpenPhase.label_18_at
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hi.fr.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hi.fr.sp
  refine exec_then hk7 run_b7 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hfr, hd⟩ := frBlock hi.fr hS (by decide) (by decide) hm' rfl rfl (by decide) (by decide)
  have hsame : ∀ r, st.data.regs.getXReg r = m.regs.getXReg r := fun r ↦
    UInt64.toBitVec_inj.mp ((hm'.regs r _ (by cases r <;> rfl)).trans rfl)
  have hregs : Regs m0 P h w st.data := by
    obtain ⟨a1, a19, a20, a21, a22, a23⟩ := hi.regs
    exact ⟨(hsame _).trans a1, (hsame _).trans a19, (hsame _).trans a20, (hsame _).trans a21,
      (hsame _).trans a22, (hsame _).trans a23⟩
  have hc : (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X8) (.lit 0)).eval
      (Env.ofMachine m [(base m0 176, 176)]) = (j == Q.size) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    show ((m.regs.getXReg .X8).toBitVec == 0#64) = _
    have h8 : (m.regs.getXReg .X8).toBitVec.toNat = 8 * (Q.size - j) := hi.x8
    by_cases hj : j = Q.size
    · subst hj
      have e : (m.regs.getXReg .X8).toBitVec = 0#64 := BitVec.eq_of_toNat_eq (by
        simpa using h8)
      simp [e]
    · have e : (m.regs.getXReg .X8).toBitVec ≠ 0#64 := fun e ↦ by
        have := congrArg BitVec.toNat e
        rw [h8] at this
        have := hi.le
        have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
        omega
      simp [e, hj]
  simp only [PcOk] at hpc
  rw [hc] at hpc
  by_cases hj : j = Q.size
  · simp only [hj, beq_self_eq_true, ↓reduceIte] at hpc
    refine Eventually.done _ (.inr (.inl ⟨hpc.trans hl8, hfr, hregs, hi.shape, ?_⟩))
    rw [hsize, ← hj]; exact hi.pos
  have hb : (j == Q.size) = false := by simpa using hj
  simp only [hb, Bool.false_eq_true, ↓reduceIte] at hpc
  have hjl : j < Q.size := Nat.lt_of_le_of_ne hi.le hj
  -- `b8`: position `j` against opening `j`'s leaf index.
  unfold NoWrap at hnwp hnwq
  rw [hpw] at hnwp hmp
  rw [← hqn] at hnwq hapq hqp
  have hbt := base_toNat (m0 := m0) (F := 176) (by omega)
  have hstk : (stackBelow m0 openPhaseStack).toNat = m0.regs.SP.toNat - 1088 := by
    rw [openPhaseStack_eq]; exact base_toNat (by omega)
  have hl := m0.regs.SP.toNat_lt
  unfold Apart at haps hapq hqp
  rw [hstk, openPhaseStack_eq] at haps hapq
  have hnwp' : (phO m0).toNat + 8 * 49411 ≤ 2 ^ 64 := hnwp
  have hnwq' : (posO m0).toNat + 8 * Q.size ≤ 2 ^ 64 := hnwq
  have haps' : (phO m0).toNat + 8 * 49411 ≤ m0.regs.SP.toNat - 1088 ∨
      m0.regs.SP.toNat - 1088 + 1088 ≤ (phO m0).toNat := haps
  have hapq' : (posO m0).toNat + 8 * Q.size ≤ m0.regs.SP.toNat - 1088 ∨
      m0.regs.SP.toNat - 1088 + 1088 ≤ (posO m0).toNat := hapq
  have hqp' : (posO m0).toNat + 8 * Q.size ≤ (phO m0).toNat ∨
      (phO m0).toNat + 8 * 49411 ≤ (posO m0).toNat := hqp
  have hqoff : (posO m0 + BitVec.ofNat 64 (8 * j)).toNat = (posO m0).toNat + 8 * j :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hpoff : (phO m0 + BitVec.ofNat 64 (24 + 1544 * j)).toNat =
      (phO m0).toNat + (24 + 1544 * j) := NativeRustcVm.toNat_add_ofNat (by omega)
  have hwf8 : (Env.ofMachine st.data [(base m0 176, 176), (posO m0 + BitVec.ofNat 64 (8 * j), 8),
      (phO m0 + BitVec.ofNat 64 (24 + 1544 * j), 8)]).WF := by
    refine Env.wf_of ⟨⟨fun i hi' ↦ hfr.kept _ ((Bus.frame_mapped hS (by decide)).1 i hi'),
        (Bus.frame_mapped hS (by decide)).2⟩,
      ⟨fun i hi' ↦ hfr.kept _ ?_, by unfold NoWrap; rw [hqoff]; omega⟩,
      ⟨fun i hi' ↦ hfr.kept _ ?_, by unfold NoWrap; rw [hpoff]; omega⟩, trivial⟩ ?_
    · have := NativeRustcVm.WordsAt.mapped hposw
      simp only [Array.length_toList] at this
      rw [NativeRustcVm.addr_add_add]; exact this _ (by omega)
    · rw [NativeRustcVm.addr_add_add]; exact hmp _ (by omega)
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq]
        unfold Apart
        rw [hbt, hqoff, hpoff]
        omega
      · simp only [List.mem_singleton, forall_eq]
        unfold Apart
        rw [hqoff, hpoff]
        omega
  have hm8 : Match (Env.ofMachine st.data [(base m0 176, 176),
      (posO m0 + BitVec.ofNat 64 (8 * j), 8), (phO m0 + BitVec.ofNat 64 (24 + 1544 * j), 8)])
      posS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Bus.base_aligned hS (by decide) (by decide), rfl, nofun, rfl,
        nofun, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]; rw [hfr.sp]; simp)
      ⟨by
        show (st.data.regs.getXReg .X4).toBitVec = _
        rw [hsame, hi.x4]; simp [Sym.eval, Env.base, Env.ofMachine],
       by
        show (st.data.regs.getXReg .X9).toBitVec = _
        rw [hsame, hi.x9]; simp [Sym.eval, Env.base, Env.ofMachine], trivial⟩
      trivial trivial trivial
  refine exec_at hk8 run_b8 hwf8 hpc hm8 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hfr1, hd1⟩ : FrO m0 st1.data ∧ st1.data.dmem = st.data.dmem := by
    have hwf2 := Bus.wf_frame (F := 176) hS (by decide) hfr.kept
    refine ⟨Fr.ofBlock hfr hm8 hm1 hwf8 rfl rfl rfl (fun r hr ↦ nomatch hr), ?_⟩
    exact hm1.dmem_eq hwf8 rfl
  have hq : NativeRustcVm.WordAt st.data.dmem (posO m0 + BitVec.ofNat 64 (8 * j)) Q[j] := by
    have := (NativeRustcVm.wordsAt_iff.1 hposw) j (by simpa using hjl)
    simp only [Array.getElem_toList] at this
    exact keepWord hpre hfr (n := 8 * Q.size) (by unfold NoWrap; omega)
      (by unfold Apart; rw [hstk, openPhaseStack_eq]; omega) (by omega) this
  have hjP : j < P.size := by omega
  have hidx : NativeRustcVm.WordAt st.data.dmem (phO m0 + BitVec.ofNat 64 (24 + 1544 * j))
      P[j].leafIndex := by
    have := (hph.2.2.2.2.2.2 j hjP).2.2.2.1
    rw [off, show 8 * (3 + j * openingWords) = 24 + 1544 * j by rw [how]; ring] at this
    exact keepWord hpre hfr (n := 8 * 49411) (by unfold NoWrap; omega)
      (by unfold Apart; rw [hstk, openPhaseStack_eq]; omega) (by omega) this
  have hl1 : (Env.ofMachine st.data [(base m0 176, 176), (posO m0 + BitVec.ofNat 64 (8 * j), 8),
      (phO m0 + BitVec.ofNat 64 (24 + 1544 * j), 8)]).load 1 0 8 = Q[j].toBitVec :=
    load_word (by rw [NativeRustcVm.addr_add_zero]; exact hq)
  have hl2 : (Env.ofMachine st.data [(base m0 176, 176), (posO m0 + BitVec.ofNat 64 (8 * j), 8),
      (phO m0 + BitVec.ofNat 64 (24 + 1544 * j), 8)]).load 2 0 8 = P[j].leafIndex.toBitVec :=
    load_word (by rw [NativeRustcVm.addr_add_zero]; exact hidx)
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64, hl1, hl2] at hpc1
  have hregs1 : Regs m0 P h w st1.data := by
    obtain ⟨a1, a19, a20, a21, a22, a23⟩ := hregs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | exact (UInt64.toBitVec_inj.mp ((hm1.regs _ _ rfl).trans rfl)).trans ‹_›
  by_cases heq : P[j].leafIndex = Q[j]
  · have e : (P[j].leafIndex.toBitVec == Q[j].toBitVec) = true := by simp [heq]
    simp only [e, ↓reduceIte] at hpc1
    refine Eventually.done _ (.inr (.inr ⟨hpc1.trans hl6, hjl, hfr1, hregs1, hi.shape, by omega,
      ?_, ?_, ?_, ?_⟩))
    · rw [UInt64.toNat, hm1.regs .X8 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      show ((st.data.regs.getXReg .X8).toBitVec - 8#64).toNat = _
      rw [hsame]
      have h8 : (m.regs.getXReg .X8).toBitVec.toNat = 8 * (Q.size - j) := hi.x8
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h8]; simp; omega), h8]
      simp; omega
    · rw [hm1.regs .X4 _ rfl]
      simp only [Sym.eval, Env.base, Env.ofMachine, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
      congr 2
    · rw [hm1.regs .X9 _ rfl]
      simp only [Sym.eval, Env.base, Env.ofMachine, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some]
      rw [show BitVec.ofInt 64 1544 = BitVec.ofNat 64 1544 from rfl, NativeRustcVm.addr_add_add,
        show 24 + 1544 * j + 1544 = 24 + 1544 * (j + 1) by ring]
    · exact (positionsOk_succ hjP (by omega)).2 ⟨hi.pos, heq⟩
  · have e : (P[j].leafIndex.toBitVec == Q[j].toBitVec) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h' ↦ heq (UInt64.toBitVec_inj.mp h')
    simp only [e, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hwf9 := Bus.wf_frame (F := 176) hS (by decide) hfr1.kept
    have hm9 := Bus.match_frame hS (F := 176) (by decide) (by decide) hfr1.sp
    refine exec_at hk9 run_b9 hwf9 hpc1 hm9 fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨hfr2, -⟩ := frBlock hfr1 hS (by decide) (by decide) hm2 rfl rfl (by decide)
      (by decide)
    have hx19 : st2.data.regs.getXReg .X19 = m0.regs.X0 :=
      (UInt64.toBitVec_inj.mp ((hm2.regs .X19 _ rfl).trans rfl)).trans hregs1.x19
    obtain ⟨d2, pc2⟩ := st2
    simp only [PcOk] at hpc2
    rw [hl18] at hpc2
    subst hpc2
    refine Eventually.mono (exit_fail hp hpre hfr2 hx19 (openPhase_none hph ?_)) fun st h ↦ .inl h
    rintro ⟨-, -, hpos⟩
    exact heq (hpos j hjP (by omega) (by omega))

/-- **The positions loop**: from `.L6`, the exit with `None` or `.L8`. -/
theorem pos_loop (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {h w : Nat}
    (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat} {m : MachineData} (hi : PInv m0 P Q h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b7Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b7Offset) ∧
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

omit [Host] in
theorem lsl3 (x : BitVec 64) : UnOp.apply (.ubfm 61 60) .W64 x = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- **`b6`**: from `.L5`, the positions loop's start. -/
theorem b6_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {h w : Nat}
    (hph : PhaseHW m0.dmem (phO m0) P h w) {m : MachineData} (hf : FrO m0 m)
    (hr : Regs m0 P h w m) (hsh : ShapeOk P Q h w m0.regs.X2.toNat m0.regs.X3.toNat)
    (hx4 : m.regs.getXReg .X4 = m0.regs.X4) (hx5 : m.regs.getXReg .X5 = m0.regs.X5) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) ∧ Checked m0 P Q h w st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b6Offset)⟩ := by
  have hS := hpre.1
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b6Offset) := b6_in_code.trans hp.1 (by simp [b6])
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hf.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hf.sp
  refine exec_then hk6 run_b6 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hfr, -⟩ := frBlock hf hS (by decide) (by decide) hm' rfl rfl (by decide) (by decide)
  have hqn : Q.size = m0.regs.X5.toNat := hpre.2.2.2.2.1
  have hnwq : (m0.regs.X4.toBitVec).toNat + 8 * m0.regs.X5.toNat ≤ 2 ^ 64 :=
    hpre.2.2.2.2.2.2.2.2.2.1
  have hl4 := m0.regs.X4.toBitVec.isLt
  have hsame : ∀ r, r = .X1 ∨ r = .X4 ∨ r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st.data.regs.getXReg r = m.regs.getXReg r := by
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact UInt64.toBitVec_inj.mp ((hm'.regs _ _ rfl).trans rfl)
  obtain ⟨a1, a19, a20, a21, a22, a23⟩ := hr
  have hpc' : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b7Offset) := hpc
  obtain ⟨d, pc⟩ := st
  simp only at hpc'
  subst hpc'
  refine pos_loop hp hpre hph (j := 0) ⟨hfr, ⟨(hsame _ (by simp)).trans a1,
    (hsame _ (by simp)).trans a19, (hsame _ (by simp)).trans a20,
    (hsame _ (by simp)).trans a21, (hsame _ (by simp)).trans a22,
    (hsame _ (by simp)).trans a23⟩, hsh, Nat.zero_le _, ?_, ?_, ?_,
    positionsOk_zero P Q⟩
  · rw [UInt64.toNat, hm'.regs .X8 _ rfl]
    simp only [Sym.eval, lsl3]
    show (BitVec.ofNat 64 (8 * (m.regs.getXReg .X5).toBitVec.toNat)).toNat = _
    rw [hx5, hqn]
    simp only [BitVec.toNat_ofNat, Nat.sub_zero]
    have h1 := hsh.2
    have h2 : P.size ≤ 256 := hph.2.2.1
    have h3 : Q.size = m0.regs.X5.toBitVec.toNat := hqn
    exact Nat.mod_eq_of_lt (by omega)
  · rw [hsame _ (by simp), hx4]; simp
  · rw [hm'.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
    show (m.regs.getXReg .X20).toBitVec + BitVec.ofInt 64 24 = _
    rw [a20]; rfl

end

end NativeRustcVmArm.Sumcheck.OpenPhase
