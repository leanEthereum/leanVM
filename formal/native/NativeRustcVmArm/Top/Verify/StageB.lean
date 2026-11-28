module

public import NativeRustcVmArm.Code.Vm.VerifyExecution.Names
public import NativeRustcVmArm.Top.Verify.PreB

/-!
# `verify`: the walk

From `SA` (after `seed`), `b1` writes `TState::new`'s fields (`tstateAt_start`) and calls
`verify_execution` on the frame's `TState`, the bytecode, the public input and the working area,
whose contract gives the walk's success and last state: `stageB`, to `SB`.
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify NativeVm.Model
open NativeRustcVm.Transcript
open NativeRustcVm (WordAt WordsAt Region wordsOf wordOf)
open NativeRustcVm.Top (workAreaBytes)

public section

variable [Host] {k : Nat}

theorem stageB (hp : Placed code k)
    (hve : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s))
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)} {m0 : MachineData}
    (hpre : VerifyPre a stream openings m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b1Offset)) (hSA : SA m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b2Offset) ∧
      SB a stream openings m0 st'.data) st := by
  have g := geo_of hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, hmap⟩, -, -, hdecF, hD0, ⟨hbcM, -⟩, ⟨hpubM, -⟩, ⟨hdecM, -⟩, ⟨haM, -⟩,
    -, -, -, -⟩ := hpre
  have hs := g.s
  have hF := g.F
  have hT := g.T
  have hsb0 := g.sb
  have hS := verifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hVE : verifyExecutionStack = 18384 := rfl
  have e1 : m0.regs.X1.toNat = m0.regs.X1.toBitVec.toNat := rfl
  obtain ⟨hB, hx19, hx20, hx21, hx22, hx23, hseed⟩ := hSA
  set F := frameOf m0 with hFdef
  set dec := m0.regs.X3.toBitVec
  have gdec : dec.toNat + 24 ≤ m0.regs.SP.toBitVec.toNat - 19216 ∨
      m0.regs.SP.toBitVec.toNat ≤ dec.toNat := g.dec
  have gdecN : dec.toNat + 24 ≤ 2 ^ 64 := g.decN
  have hsp : st.data.regs.SP.toBitVec = F := hB.sp
  have hFm : Mapped m0.dmem F 832 :=
    Mapped.within hmap (by rw [hsb0]; omega) (by rw [hsb0, hF]; omega) (by rw [hsb0, hF]; omega)
  have hdF : F.toNat + 832 ≤ dec.toNat ∨ dec.toNat + 24 ≤ F.toNat := by omega
  have hwf : (Env.ofMachine st.data [(F, 832), (dec, 24)]).WF :=
    Env.wf_of ⟨⟨Mapped.kept hFm hB.kept, show F.toNat + 832 ≤ 2 ^ 64 by omega⟩,
      ⟨Mapped.kept hdecM hB.kept, gdecN⟩, trivial⟩ (List.pairwise_pair.mpr hdF)
  have hm0 : Match (Env.ofMachine st.data [(F, 832), (dec, 24)]) initS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ show F.toNat % 16 = 0 by have := g.al; omega, rfl,
      fun h ↦ absurd h (by decide), trivial⟩
      (show st.data.regs.SP.toBitVec = F + BitVec.ofInt 64 0 by rw [hsp]; simp)
      ⟨show (st.data.regs.getXReg .X19).toBitVec = dec + BitVec.ofInt 64 0 by
        show st.data.regs.X19.toBitVec = _
        rw [hx19]; simp [dec], trivial⟩
      trivial trivial trivial
  have hdecF : DecFieldsAt st.data.dmem dec a := by
    obtain ⟨h0, h1, h2⟩ := hdecF
    have keep : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 24 →
        WordAt m0.dmem (dec + BitVec.ofNat 64 o) w → WordAt st.data.dmem (dec + BitVec.ofNat 64 o) w :=
      fun {o w} ho h ↦ bytesAt_keep h hB.same (by
        rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]
        omega) fun q hq ↦ by
          rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]
          unfold InStack at hq; omega
    refine ⟨?_, keep (by omega) h1, keep (by omega) h2⟩
    have := keep (o := 0) (by omega) (by rw [NativeRustcVm.addr_add_zero]; exact h0)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hD : DecodedAt st.data.dmem a stream openings := by
    refine hD0.agree fun j hj _ ↦ hB.same _ fun hq ↦ ?_
    unfold InStack at hq
    rw [toNat_addr (by have := g.areaN; omega)] at hq
    have := g.area; omega
  have hld : ∀ {o : Nat} {w : UInt64}, WordAt st.data.dmem (dec + BitVec.ofNat 64 o) w →
      (Env.ofMachine st.data [(F, 832), (dec, 24)]).load 1 o 8 = w.toBitVec :=
    fun h ↦ load_wordAt (r := 1) h
  have hl0 := hld (o := 0) (by rw [NativeRustcVm.addr_add_zero]; exact hdecF.1)
  have hl1 := hld (o := 8) hdecF.2.1
  have hl2 := hld (o := 16) hdecF.2.2
  refine exec_at (hb1 hp) run_b1 hwf hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have hb1m := b1_mem
  rw [after_eq run_b1] at hb1m
  have hk1 := b1_keeps
  rw [after_eq run_b1] at hk1
  have hW1 : ∀ q, Written (Env.ofMachine st.data [(F, 832), (dec, 24)]) (after b1 initS) q →
      F.toNat + 208 ≤ q.toNat ∧ q.toNat < F.toNat + 768 := fun q hq ↦ by
    rw [after_eq run_b1] at hq
    exact written_sub (r := 0) rfl hb1m hq
  have hB1 : Body m0 832 slots (InStack m0 verifyStack) st1.data :=
    hB.block slotsIn (by show 832 ≤ m0.regs.SP.toBitVec.toNat; omega) hm0 hm1 hwf rfl hk1
      fun q hq ↦ by
        have := hW1 q (by rw [after_eq run_b1]; exact hq)
        unfold InStack; omega
  have hsame1 : SameOutside st.data.dmem st1.data.dmem
      (fun q ↦ F.toNat + 208 ≤ q.toNat ∧ q.toNat < F.toNat + 768) := fun q hq ↦
    hm1.get?_mem0 hwf fun hw ↦ hq (hW1 q (by rw [after_eq run_b1]; exact hw))
  have hm1' : Match (Env.ofMachine st.data [(F, 832), (dec, 24)]) (after b1 initS) st1.data := by
    rw [after_eq run_b1]; exact hm1
  have hsp1 : st1.data.regs.SP.toBitVec = F := hB1.sp
  have hX0 : st1.data.regs.X0.toBitVec = tOf m0 := hm1.regs .X0 _ rfl
  have hX1 : st1.data.regs.X1 = m0.regs.X0 :=
    (UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)).trans hx23
  have hX2 : st1.data.regs.X2 = m0.regs.X1 :=
    (UInt64.toBitVec_inj.mp (hm1.regs .X2 _ rfl)).trans hx22
  have hX3 : st1.data.regs.X3 = m0.regs.X2 :=
    (UInt64.toBitVec_inj.mp (hm1.regs .X3 _ rfl)).trans hx21
  have hX4 : st1.data.regs.X4 = m0.regs.X4 :=
    (UInt64.toBitVec_inj.mp (hm1.regs .X4 _ rfl)).trans hx20
  have hX19 : st1.data.regs.X19 = m0.regs.X3 := by
    apply UInt64.toBitVec_inj.mp
    show (st1.data.regs.getXReg .X19).toBitVec = _
    rw [hm1.regs .X19 _ rfl]
    show m0.regs.X3.toBitVec + BitVec.ofInt 64 0 = _
    simp
  -- The first state.
  have hseed1 : WordsAt st1.data.dmem (tOf m0) (seed (bcOf m0).toArray (pubOf m0)).toList :=
    wordsAt_keep hseed hsame1 (by simp; omega) fun q hq ↦ by simp; omega
  have hD1 : DecodedAt st1.data.dmem a stream openings :=
    hD.agree fun j hj _ ↦ hsame1 _ fun ⟨h1, h2⟩ ↦ by
      rw [toNat_addr (by have := g.areaN; omega)] at h1 h2
      have := g.area; omega
  have hTm : Mapped st1.data.dmem (tOf m0) 760 :=
    Mapped.kept (Mapped.within hFm (by omega) (by omega) (by omega)) (hB1.kept)
  have hts : TStateAt st1.data.dmem (tOf m0) a (start (bcOf m0) (pubOf m0) stream openings) :=
    tstateAt_start hm1' rfl hseed1 hl0 hl1 hl2 hD1
      ⟨⟨hTm, show (tOf m0).toNat + 760 ≤ 2 ^ 64 by omega⟩,
        ⟨Mapped.kept haM hB1.kept, g.areaN⟩, by
          show _ ∨ _
          unfold tstateBytes
          have := g.area; omega⟩
  -- The inputs, kept.
  have hbc : WordsAt st1.data.dmem m0.regs.X0.toBitVec (bcOf m0) := by
    by_cases hn0 : m0.regs.X1.toBitVec.toNat = 0
    · rw [show bcOf m0 = [] from List.eq_nil_of_length_eq_zero ((length_bcOf m0).trans hn0)]
      exact NativeRustcVm.wordsAt_nil _ _
    · have hap := g.bc (by omega)
      exact wordsAt_keep (wordsAt_bcOf hbcM) hB1.same (by rw [length_bcOf]; exact g.bcN)
        fun q hq ↦ by unfold InStack at hq; rw [length_bcOf]; omega
  have hpub : WordsAt st1.data.dmem m0.regs.X2.toBitVec (pubOf m0).toList := by
    have hap := g.pub
    have := g.pubN
    exact wordsAt_keep (wordsAt_pubOf hpubM) hB1.same (by rw [Vector.length_toList]; omega)
      fun q hq ↦ by unfold InStack at hq; rw [Vector.length_toList]; omega
  -- `verify_execution`.
  have hsbV : (stackBelow st1.data verifyExecutionStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19216 := by
    show (st1.data.regs.SP.toBitVec - BitVec.ofNat 64 verifyExecutionStack).toNat = _
    rw [hsp1, hVE, toNat_subAddr (by rw [hF]; omega), hF]; omega
  refine call_then hpc1 (hve a _) (vePre hpre' hB1 hX0 hX1 hX2 hX3 hX4 hts rfl)
    fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hres, hsame2, hsaved2⟩ := hpost
  have hr := hres (bcOf m0) (by rw [length_bcOf, hX2])
    (by show WordsAt st1.data.dmem st1.data.regs.X1.toBitVec _; rw [hX1]; exact hbc)
    (pubOf m0) (by show WordsAt st1.data.dmem st1.data.regs.X3.toBitVec _; rw [hX3]; exact hpub)
  rw [hX0] at hr
  rw [show k + NativeRustcVmArm.Vm.Verify.b1Offset + b1.length = k + NativeRustcVmArm.Vm.Verify.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b1_next]] at hpc2
  refine Eventually.done _ ⟨hpc2, ?_, (hsaved2.1 .X19 rfl).trans hX19, hr.1, hr.2⟩
  refine (hB1.mono fun q h ↦ Or.inl h).call slotsIn
    (by show 832 ≤ m0.regs.SP.toBitVec.toNat; omega) hsame2 hsaved2 fun q hq ↦ ?_
  simp only [NativeRustcVm.InAny, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
    exists_eq_left, NativeRustcVm.Region.Holds, stackR] at hq
  rcases hq with hq | hq | hq
  · rw [hX0] at hq
    change InRange (tOf m0) 760 q at hq
    rw [inRange_nat (by omega)] at hq
    refine ⟨Or.inl ?_, ?_⟩ <;> (try unfold InStack) <;> omega
  · rw [hX4] at hq
    change InRange m0.regs.X4.toBitVec workAreaBytes q at hq
    have hq' := hq
    rw [inRange_nat g.workN] at hq'
    have := g.work
    exact ⟨Or.inr hq, by omega⟩
  · change InRange (stackBelow st1.data verifyExecutionStack) verifyExecutionStack q at hq
    rw [inRange_nat (by rw [hsbV]; omega), hsbV, hVE] at hq
    refine ⟨Or.inl ?_, ?_⟩ <;> (try unfold InStack) <;> omega

end

end NativeRustcVmArm.Top.Verify
