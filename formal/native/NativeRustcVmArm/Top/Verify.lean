module

public import NativeRustcVmArm.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmArm.Code.Vm.Seed.Names
public import NativeRustcVmArm.Code.Vm.Verify.Names
public import NativeRustcVmArm.Code.Vm.VerifyExecution.Names
public import NativeRustcVmArm.Top.Verify.StageA
public import NativeRustcVmArm.Top.Verify.StageB
public import NativeRustcVmArm.Top.Verify.Check

/-!
# `verify` on AArch64

**`verify_spec`**: rustc's `verify`, placed anywhere in the program, meets its contract
(`VerifyPre`, `VerifyPost`) given the contracts of `seed`, `verify_execution` and
`Decoded::phase_count`. The prologue and `seed` (`stageA`), `TState::new` and the walk
(`stageB`), then `b2` returns `0` when the walk failed (`stageC`), else the end check (`check`):
X0 is `Model.verify`'s verdict.
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify NativeVm.Model
open NativeRustcVm.Transcript
open NativeRustcVm (WordAt WordsAt Region wordsOf wordOf)
open NativeRustcVm.Top (workAreaBytes)

public section

variable [Host] {k : Nat}

omit [Host] in
/-- The verdict on the walk's run. -/
theorem verify_eq (bcw : List UInt64) (P : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    NativeVm.Model.verify bcw.toArray P stream openings =
      match (verifyExecution bcw.toArray P).run (start bcw P stream openings) with
      | some ((), s) => s.cursor == s.stream.size && s.phase == s.openings.size
      | none => false := rfl

/-- **After the walk**: from `SB`, `0` when it failed, else the end check. -/
theorem stageC (hp : Placed code k)
    (hpcnt : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)} {m0 : MachineData}
    (hpre : VerifyPre a stream openings m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b2Offset)) (hSB : SB a stream openings m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = (if NativeVm.Model.verify (bcOf m0).toArray (pubOf m0) stream openings
        then 1 else 0) ∧
      SameOutside m0.dmem st'.data.dmem
        (fun q ↦ InStack m0 verifyStack q ∨ InRange m0.regs.X4.toBitVec workAreaBytes q) ∧
      Saved m0 st'.data) st := by
  have g := geo_of hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, hmap⟩, -, -, hdecF, -, -, -, ⟨hdecM, -⟩, -, -, -, -, -⟩ := hpre
  have hs := g.s
  have hS := verifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs832 : 832 ≤ m0.regs.SP.toBitVec.toNat := by omega
  have hF := g.F
  have hsb0 := g.sb
  have gdec := g.dec
  have gdecN := g.decN
  have hFm0 : Mapped m0.dmem (frameOf m0) 832 :=
    Mapped.within hmap (by rw [hsb0]; omega) (by rw [hsb0, hF]; omega) (by rw [hsb0, hF]; omega)
  obtain ⟨hB, hx19, hx0, hnext⟩ := hSB
  refine exec_at (hb2 hp) run_b2 (Env.wf_nil _) hpc (match_nil _) fun st1 hm1 hpc1 ↦ ?_
  have hk1 := b2_keeps
  rw [after_eq run_b2] at hk1
  have hB1 := body_nomem hB hs832 (match_nil _) hm1 (Env.wf_nil _) rfl hk1.1 hk1.2
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq (Env.wf_nil _) hk1.2
  have hX0 : st1.data.regs.X0 = st.data.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X0 _ rfl)
  have hX19 : st1.data.regs.X19 = m0.regs.X3 :=
    (UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)).trans hx19
  have hFm : Mapped st1.data.dmem (frameOf m0) 832 := Mapped.kept hFm0 hB1.kept
  have hdecM' : Mapped st1.data.dmem m0.regs.X3.toBitVec 24 := Mapped.kept hdecM hB1.kept
  have hdec' : DecFieldsAt st1.data.dmem m0.regs.X3.toBitVec a := by
    obtain ⟨h0, h1, h2⟩ := hdecF
    have keep : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 24 →
        WordAt m0.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) w →
        WordAt st1.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) w :=
      fun {o w} ho h ↦ bytesAt_keep h hB1.same (by
        rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]
        omega) fun q hq ↦ by
          rw [NativeRustcVm.length_wordBytes, toNat_addr (by omega)]
          rcases hq with hq | hq
          · unfold InStack at hq; omega
          · rw [inRange_nat g.workN] at hq
            have := g.decWork; omega
    refine ⟨?_, keep (by omega) h1, keep (by omega) h2⟩
    have := keep (o := 0) (by omega) (by rw [NativeRustcVm.addr_add_zero]; exact h0)
    rwa [NativeRustcVm.addr_add_zero] at this
  rw [verify_eq]
  generalize hr : (verifyExecution (bcOf m0).toArray (pubOf m0)).run
    (start (bcOf m0) (pubOf m0) stream openings) = r at hx0 hnext
  cases r with
  | none =>
    have hc : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (Env.ofMachine st.data []) = true := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show st.data.regs.getXReg .X0 = okWord false from hx0]
      rfl
    simp only [PcOk, hc, ite_true] at hpc1
    rw [lbl_5 hp] at hpc1
    refine Eventually.mono (exit8 hp hs832 g.al hpc1 hB1 hFm) fun st' h ↦ ⟨h.1, ?_, h.2.2⟩
    rw [h.2.1, hX0, hx0]
    rfl
  | some p =>
    obtain ⟨⟨⟩, s⟩ := p
    have hc : (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval (Env.ofMachine st.data []) = false := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show st.data.regs.getXReg .X0 = okWord true from hx0]
      rfl
    simp only [PcOk, hc, Bool.false_eq_true, ite_false,
      show k + NativeRustcVmArm.Vm.Verify.b2Offset + b2.length = k + NativeRustcVmArm.Vm.Verify.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b2_next]] at hpc1
    exact check hp hpcnt g hpc1 hB1 hX19 (by rw [hd1]; exact hnext () s rfl) hdec' hdecM' hFm

/-- **`verify` meets its contract.** -/
theorem verify_spec (hp : Placed code k)
    (hseed : Spec (Labels.label NativeRustcVmArm.Vm.Seed.entryLabel) SeedPre SeedPost)
    (hve : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.VerifyExecution.entryLabel) (VerifyExecutionPre a s)
      (VerifyExecutionPost a s))
    (hpcnt : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel)
      (PhaseCountPre a stream openings) (PhaseCountPost openings))
    (a : DecArea) (stream : Array EW) (openings : Array (Array OpeningW)) :
    Spec (Labels.label NativeRustcVmArm.Vm.Verify.entryLabel) (VerifyPre a stream openings) (VerifyPost stream openings) := by
  intro m0 hpre
  rw [lbl_entry hp]
  have g := geo_of hpre
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, ⟨hbcM, -⟩, ⟨hpubM, -⟩, -⟩ := hpre'
  refine Eventually.bind (stageA hp hseed hpre) fun st1 ⟨hpc1, hSA⟩ ↦ ?_
  refine Eventually.bind (stageB hp hve hpre hpc1 hSA) fun st2 ⟨hpc2, hSB⟩ ↦ ?_
  refine Eventually.mono (stageC hp hpcnt hpre hpc2 hSB) fun st ⟨h1, h2, h3, h4⟩ ↦
    ⟨h1, fun bcw hl hbc P hP ↦ ?_, fun q hq ↦ h3 q fun h ↦ hq ?_, h4⟩
  · rw [bcOf_eq hl hbc, pubOf_eq hP]
    exact h2
  · have hs := g.s
    have hS := verifyStack_eq
    have hsl := m0.regs.SP.toBitVec.isLt
    rcases h with h | h
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      show InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 verifyStack) verifyStack q
      rw [inRange_below (by omega)]
      exact h
    · exact ⟨_, List.mem_cons_self, h⟩

end

end NativeRustcVmArm.Top.Verify
