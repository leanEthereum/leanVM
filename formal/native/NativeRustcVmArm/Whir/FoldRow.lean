module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Whir.FoldRow.Entry
public import NativeRustcVmArm.Whir.FoldRow.Round1
public import NativeRustcVmArm.Whir.FoldRow.Round2
public import NativeRustcVmArm.Whir.FoldRow.Round3
public import NativeRustcVmArm.Whir.FoldRow.Round4
public import NativeRustcVmArm.Whir.FoldRow.Round5
public import NativeRustcVmArm.Whir.FoldRow.Round6

/-!
# `fold_row`

rustc unrolled the rounds (at most six, `FoldRowPre`): the entry and round 1's head (`entry`),
per round its turns (`turn<r>`, by `Sym.loop`: `run_loop`) and its end (`chk<r>`), the next round's
head (`head<r>`), round 6 (`Round6`); `b55` returns lane `0`, or `0` once no lane is left (`exit`).
The lanes in memory are `foldMem` (`NativeRustcVm.Whir.MathFold`), so the result is `foldRow`
(`foldRow_eq`).
-/

namespace NativeRustcVmArm.Whir.FoldRow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRow NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf)

public section

variable [Host] {k : Nat}

/-- **A round's turns**: from turn `0` at `pc` until the round's end `Q`. -/
theorem run_loop {L : Nat → MachineData → Prop} {Q : MachineState → Prop} {pc : Int64}
    (B : Nat) (hB : ∀ i st, L i st → i < B)
    (ht : ∀ i st, L i st →
      Eventually (step1 Host.exe) (fun s ↦ Q s ∨ (L (i + 1) s.data ∧ s.pc = pc)) ⟨st, pc⟩)
    {st : MachineData} (h0 : L 0 st) : Eventually (step1 Host.exe) Q ⟨st, pc⟩ :=
  Sym.loop (tr := step1 Host.exe) (Q := Q)
    (fun n s ↦ ∃ i, n = B - i ∧ s.pc = pc ∧ L i s.data)
    (fun n s ⟨i, hn, hpc, hL⟩ ↦ by
      obtain ⟨d, pc'⟩ := s
      simp only at hpc
      subst hpc
      have := hB i d hL
      refine (ht i d hL).mono fun s' h ↦ ?_
      rcases h with h | ⟨hL', hpc'⟩
      · exact .inl h
      · exact .inr ⟨B - (i + 1), by omega, i + 1, rfl, hpc', hL'⟩)
    (n := B) ⟨0, by omega, rfl, h0⟩

/-- Continue from a state at `pc` (a disjunct's). -/
theorem at_pc {P : MachineData → Prop} {R : MachineState → Prop} {pc : Int64}
    (h : ∀ st, P st → Eventually (step1 Host.exe) R ⟨st, pc⟩) {s : MachineState}
    (hs : P s.data ∧ s.pc = pc) : Eventually (step1 Host.exe) R s := by
  obtain ⟨d, pc'⟩ := s
  obtain ⟨hP, hpc⟩ := hs
  simp only at hpc
  subst hpc
  exact h d hP

/-- The end, `Fin`'s. -/
abbrev FinQ (m0 : MachineData) (k : Nat) : MachineState → Prop :=
  fun s ↦ Fin m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset)

section
variable (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
  (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {m0 : MachineData} (hpre : FoldRowPre m0)
include hp hkmul hmul hpre

theorem from5 : ∀ st, Head m0 5 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b46Offset)⟩ :=
  fun _ h ↦ (head6 hp hkmul hpre h).bind fun _ h ↦ h.elim (fun h ↦ .done _ h)
    (at_pc fun _ h ↦ run_loop (L := Loop6 m0) _ (fun _ _ h ↦ h.hi)
      (fun _ _ h ↦ turn6 hp hmul hpre h) h)

theorem fromChk5 : ∀ st, Chk m0 5 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b45Offset)⟩ :=
  fun _ h ↦ (chk5 hp hpre h).bind fun _ h ↦ h.elim (fun h ↦ .done _ h)
    (at_pc (from5 hp hkmul hmul hpre))

theorem from4 : ∀ st, Head m0 4 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b37Offset)⟩ :=
  fun _ h ↦ (head5 hp hkmul hpre h).bind fun _ h ↦ h.elim (at_pc (fromChk5 hp hkmul hmul hpre))
    (at_pc fun _ h ↦ (run_loop (L := Loop m0 5) _ (fun _ _ h ↦ h.hi)
      (fun _ _ h ↦ turn5 hp hmul hpre h) h).bind fun _ h ↦ at_pc (fromChk5 hp hkmul hmul hpre) h)

theorem fromChk4 : ∀ st, Chk m0 4 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b36Offset)⟩ :=
  fun _ h ↦ (chk4 hp hpre h).bind fun _ h ↦ h.elim (fun h ↦ .done _ h)
    (at_pc (from4 hp hkmul hmul hpre))

theorem from3 : ∀ st, Head m0 3 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b28Offset)⟩ :=
  fun _ h ↦ (head4 hp hkmul hpre h).bind fun _ h ↦ h.elim (at_pc (fromChk4 hp hkmul hmul hpre))
    (at_pc fun _ h ↦ (run_loop (L := Loop m0 4) _ (fun _ _ h ↦ h.hi)
      (fun _ _ h ↦ turn4 hp hmul hpre h) h).bind fun _ h ↦ at_pc (fromChk4 hp hkmul hmul hpre) h)

theorem fromChk3 : ∀ st, Chk m0 3 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b27Offset)⟩ :=
  fun _ h ↦ (chk3 hp hpre h).bind fun _ h ↦ h.elim (fun h ↦ .done _ h)
    (at_pc (from3 hp hkmul hmul hpre))

theorem from2 : ∀ st, Head m0 2 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b19Offset)⟩ :=
  fun _ h ↦ (head3 hp hkmul hpre h).bind fun _ h ↦ h.elim (at_pc (fromChk3 hp hkmul hmul hpre))
    (at_pc fun _ h ↦ (run_loop (L := Loop m0 3) _ (fun _ _ h ↦ h.hi)
      (fun _ _ h ↦ turn3 hp hmul hpre h) h).bind fun _ h ↦ at_pc (fromChk3 hp hkmul hmul hpre) h)

theorem fromChk2 : ∀ st, Chk m0 2 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b18Offset)⟩ :=
  fun _ h ↦ (chk2 hp hpre h).bind fun _ h ↦ h.elim (fun h ↦ .done _ h)
    (at_pc (from2 hp hkmul hmul hpre))

theorem from1 : ∀ st, Head m0 1 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b10Offset)⟩ :=
  fun _ h ↦ (head2 hp hkmul hpre h).bind fun _ h ↦ h.elim (at_pc (fromChk2 hp hkmul hmul hpre))
    (at_pc fun _ h ↦ (run_loop (L := Loop m0 2) _ (fun _ _ h ↦ h.hi)
      (fun _ _ h ↦ turn2 hp hmul hpre h) h).bind fun _ h ↦ at_pc (fromChk2 hp hkmul hmul hpre) h)

theorem fromChk1 : ∀ st, Chk m0 1 st → Eventually (step1 Host.exe) (FinQ m0 k) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b9Offset)⟩ :=
  fun _ h ↦ (chk1 hp hpre h).bind fun _ h ↦ h.elim (fun h ↦ .done _ h)
    (at_pc (from1 hp hkmul hmul hpre))

/-- **To the end block.** -/
theorem to_fin : Eventually (step1 Host.exe) (FinQ m0 k) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b0Offset)⟩ :=
  (entry hp hkmul hpre).bind fun _ h ↦ h.elim (fun h ↦ .done _ h) fun h ↦
    h.elim (at_pc (fromChk1 hp hkmul hmul hpre))
      (at_pc fun _ h ↦ (run_loop (L := Loop m0 1) _ (fun _ _ h ↦ h.hi)
        (fun _ _ h ↦ turn1 hp hmul hpre h) h).bind fun _ h ↦
          at_pc (fromChk1 hp hkmul hmul hpre) h)

end

omit [Host] in
/-- The model's lanes are the entry's. -/
theorem foldRow_fin {m0 : MachineData} (hpre : FoldRowPre m0) :
    foldRow (ewSlice m0 m0.regs.X0.toBitVec (min m0.regs.X1.toNat laneCap)) m0.regs.X2
        (roundsOf m0.dmem m0.regs.X3.toBitVec m0.regs.X4.toNat).toArray =
      if nOf m0 >>> rnOf m0 = 0 then 0 else memOf m0 (rnOf m0) 0 := by
  have h := foldRow_eq m0.regs.X2 (rdsOf m0) (nOf m0) (v0Of m0)
    (ewSlice m0 m0.regs.X0.toBitVec (min m0.regs.X1.toNat laneCap))
    (by simp [ewSlice, nOf, laneCap]) (fun j hj ↦ by simp [ewSlice, v0Of, vOf])
    (by simpa [rdsOf, roundsOf] using (pre_parts hpre).2.2.2.2)
  rw [show (rdsOf m0).size = rnOf m0 by simp [rdsOf, roundsOf]] at h
  exact h

/-- **The end** (`b55`): lane `0` or `0`, the epilogue. -/
theorem exit (hp : Placed code k) {m0 : MachineData} (hpre : FoldRowPre m0) {st : MachineData}
    (hF : Fin m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ FoldRowPost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset)⟩ := by
  obtain ⟨hS, hvin, -, -, -⟩ := pre_parts hpre
  have hF128 : 128 ≤ foldRowStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF128
  have hfr := hF.fr
  let fb := fbOf m0
  have hl0 : Readable st (vOf m0) 16 := hfr.readable (Readable.mono hvin.1 (by omega))
  have hap0 : Apart fb 128 (vOf m0) 16 := by
    have := apart_frame hvin.2 hF128 hS.2.1
    have hfb : fb.toNat = m0.regs.SP.toBitVec.toNat - 128 := hfe
    unfold Apart at this ⊢
    rw [hfe] at this
    omega
  let env := Env.ofMachine st [(fb, 128), (vOf m0, 16)]
  have hwf : env.WF := Env.wf_of ⟨⟨(hfr.readable ⟨hfmap, hfnw⟩).1, hfnw⟩, ⟨hl0.1, hl0.2⟩, trivial⟩
    (List.pairwise_pair.mpr hap0)
  have lv : env.load 0 24 8 = m0.regs.X0.toBitVec := load_word hF.v
  have hm : Match env exitS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF128 rfl, rfl, fun h ↦ absurd h (by decide),
        trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial
      ⟨by
        show env.load 0 24 8 = vOf m0 + BitVec.ofInt 64 0
        rw [lv]; simp [vOf], trivial⟩
  have hk : b55.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b55Offset) := b55_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk run_b55 hwf hm fun s1 hm1 hpc1 ↦ .done _ ?_
  have hb := after_eq run_b55 ▸ b55_restores
  obtain ⟨hsaved, hx30⟩ := hfr.ret hm1 hwf x30_mem hb.1
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq hwf hb.2
  refine ⟨hpc1.trans (by simp only [retOf, hx30]), ?_, fun p hp' ↦ ?_, hsaved⟩
  · -- the result
    rw [foldRow_fin hpre]
    have l0 := hF.lanes 0 (by decide)
    rw [show 16 * 0 = 0 from rfl, NativeRustcVm.addr_add_zero] at l0
    have lw0 : env.load 1 0 8 = (ewOf st.dmem (vOf m0)).c0.toBitVec := by
      rw [load8_eq, show env.base 1 = vOf m0 from rfl, NativeRustcVm.addr_add_zero]
      rfl
    have lw1 : env.load 1 8 8 = (ewOf st.dmem (vOf m0)).c1.toBitVec := by
      rw [load8_eq]
      rfl
    have h26 : ((st.regs.getXReg .X26).toBitVec == BitVec.ofNat 64 0) =
        decide (nOf m0 >>> rnOf m0 = 0) := by
      rw [bv_beq_toNat]
      refine decide_eq_decide.mpr ?_
      rw [← hF.x26]
      exact ⟨fun h ↦ UInt64.toNat.inj h, fun h ↦ by
        show st.regs.X26.toNat = 0
        rw [h]; rfl⟩
    have r0 := hm1.regs .X0 _ rfl
    have r1 := hm1.regs .X1 _ rfl
    sym_simp at r0 r1
    rw [Env.ofMachine_regs, h26] at r0 r1
    by_cases hz : nOf m0 >>> rnOf m0 = 0
    · simp only [hz, decide_true, ↓reduceIte] at r0 r1 ⊢
      show (⟨s1.data.regs.X0, s1.data.regs.X1⟩ : EW) = ⟨0, 0⟩
      rw [show s1.data.regs.X0 = 0 from UInt64.toBitVec_inj.mp r0,
        show s1.data.regs.X1 = 0 from UInt64.toBitVec_inj.mp r1]
    · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at r0 r1 ⊢
      show (⟨s1.data.regs.X0, s1.data.regs.X1⟩ : EW) = _
      rw [show s1.data.regs.X0 = _ from UInt64.toBitVec_inj.mp (r0.trans lw0),
        show s1.data.regs.X1 = _ from UInt64.toBitVec_inj.mp (r1.trans lw1), ← l0]
  · rw [hd1]
    exact hfr.same p hp'

/-- **`fold_row`'s contract.** -/
theorem foldRow_spec (hp : Placed code k)
    (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (label NativeRustcVmArm.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.FoldRow.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b0Offset) from hp.label NativeRustcVmArm.Vm.FoldRow.entry_at]
  exact (to_fin hp hkmul hmul hpre).bind fun _ h ↦ at_pc (fun _ h ↦ exit hp hpre h) h

end

end NativeRustcVmArm.Whir.FoldRow
