module

public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Whir.NextLevel.Core

/-!
# `next_level`: the out-of-domain sample

From `b7` (`H7`): `μ` loaded and checked (`b7`, `μ ≤ 30`), the out-of-domain point's buffer
(`μ` at `192`) filled by `sample_challenges` (`b8`, items from `200`): `mid1`, to `b9`. Then
`read_scalar` into the `Option<EW>` at `680` (`b9`), its tag tested (`b10`), the value into X24,
X25 and `grind(t, 17)` (`b11`), tested (`b12`): `mid2`, to `b13` with `H13`.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

@[expose] public section

/-- At `b13`: the frame, the registers, the high part `xs`, the out-of-domain point `ood` and
value `v` (X24, X25), the `TState`. -/
structure H13 [Labels] (a : DecArea) (level : Whir.Level) (m0 : MachineData) (xs ood : Array EW)
    (v : EW) (s6 : TState) (st : MachineData) : Prop where
  fr : NFr m0 st
  regs : Regs level m0 st
  x21 : st.regs.X21 = level.fold.toUInt64
  x23 : st.regs.X23.toBitVec = loc m0 200
  x24 : st.regs.X24 = v.c0
  x25 : st.regs.X25 = v.c1
  x26 : st.regs.X26 = m0.regs.X5
  facts : Facts m0 st.dmem [(200, ood.toList.flatMap NativeRustcVm.ewBytes),
    (88, NativeRustcVm.wordBytes m0.regs.X5), (96, xs.toList.flatMap NativeRustcVm.ewBytes),
    (192, NativeRustcVm.wordBytes m0.regs.X5)]
  size : xs.size = level.fold
  osize : ood.size = m0.regs.X5.toNat
  ts : TStateAt st.dmem (tA m0) a s6

end

public section

theorem reg_bv [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : XReg} {v : Sym} (h : S.reg r = some v) {w : BitVec 64} (hv : v.eval env = w) :
    (m.regs.getXReg r).toBitVec = w :=
  (hm.regs r v h).trans hv

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **`μ` checked, `sample_challenges`**, to `b9`. -/
theorem mid1 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    {st : MachineState} {xs : Array EW} {s3 : TState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b7Offset))
    (h7 : H7 a level m0 xs s3 st.data)
    (cont : ∀ (m2 : MachineData) (ood : Array EW) (s4 : TState), NFr m0 m2 → Regs level m0 m2 →
      m2.regs.X21 = level.fold.toUInt64 → m2.regs.X23.toBitVec = loc m0 200 →
      m2.regs.X26 = m0.regs.X5 →
      Facts m0 m2.dmem [(200, ood.toList.flatMap NativeRustcVm.ewBytes),
        (88, NativeRustcVm.wordBytes m0.regs.X5), (96, xs.toList.flatMap NativeRustcVm.ewBytes),
        (192, NativeRustcVm.wordBytes m0.regs.X5)] →
      ood.size = m0.regs.X5.toNat → TStateAt m2.dmem (tA m0) a s4 →
      (sampleChallenges m0.regs.X5.toNat).run s3 = some (ood, s4) →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b9Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  have c := ctx h
  have hf := h7.fr
  have hmu30 : m0.regs.X5.toNat ≤ 30 := h.2.2.2.2.2.2.2.2.2.2.1
  have hf6 : level.fold ≤ 6 := h.2.2.2.2.2.1
  have hsz := h7.size
  -- `b7`: `μ` loaded and checked, the point's buffer zeroed.
  have hld : (envF m0 st.data).load 0 88 8 = m0.regs.X5.toBitVec := load_word (by simpa using h7.mu)
  have hle30 : m0.regs.X5.toBitVec.toNat ≤ (BitVec.ofNat 64 30).toNat := by
    rw [show (BitVec.ofNat 64 30).toNat = 30 from rfl, UInt64.toNat_toBitVec]; exact hmu30
  have hc : (SBool.and (.not (.cmp .ult .W64 (.load 0 88 8) (.lit 30)))
      (.not (.cmp .eq .W64 (.load 0 88 8) (.lit 30)))).eval (envF m0 st.data) = false := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hld]
    exact not_hi hle30
  have hF0 : Facts m0 st.data.dmem [(88, NativeRustcVm.wordBytes m0.regs.X5),
      (96, xs.toList.flatMap NativeRustcVm.ewBytes)] := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h7.mu
    · exact h7.high
  have hW0 : Within [(88, NativeRustcVm.wordBytes m0.regs.X5),
      (96, xs.toList.flatMap NativeRustcVm.ewBytes)] 88 104 :=
    within_word (by omega) (by omega) (within_ews (by omega) (by omega) within_nil)
  refine blk hp h b7_in_code (by simp [b7]) run_b7 (wfF h hf) (mF h hf) (by decide) rfl hf hpc
    fun st1 hm1 hpc1 hf1 hs1 ↦ ?_
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc1
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b7Offset + b7.length = k + NativeRustcVmArm.Vm.NextLevel.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b7_next]] at hpc1
  have e1 := sameRegs_ok (mF h hf) hm1
    (rs := [.X19, .X20, .X21, .X22, .X27, .X28, .X29]) (by decide)
  have hR1 : Regs level m0 st1.data :=
    ⟨(e1 .X19 (by simp)).trans h7.regs.x19, (e1 .X20 (by simp)).trans h7.regs.x20,
      (e1 .X22 (by simp)).trans h7.regs.x22, (e1 .X27 (by simp)).trans h7.regs.x27,
      (e1 .X28 (by simp)).trans h7.regs.x28, (e1 .X29 (by simp)).trans h7.regs.x29⟩
  have h21 : st1.data.regs.X21 = level.fold.toUInt64 := (e1 .X21 (by simp)).trans h7.x21
  have h26 : st1.data.regs.X26 = m0.regs.X5 := reg_of hm1 (r := .X26) rfl hld
  have hF1 := Facts.block hm1 (wfF h hf) (by decide) (by decide) hW0 hF0
  have hts1 := tsB h (hm1.kept (wfF h hf)) hs1 h7.ts
  -- `b8`: `sample_challenges(t, sp + 200, μ)`, `μ` at `192`.
  refine blk hp h b8_in_code (by simp [b8]) run_b8 (wfF h hf1) (mF h hf1) (by decide) rfl hf1
    hpc1 fun st2 hm2 hpc2 hf2 hs2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b8Offset + b8.length = k + NativeRustcVmArm.Vm.NextLevel.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b8_next]] at hpc2
  have e2 := sameRegs_ok (mF h hf1) hm2
    (rs := [.X19, .X20, .X21, .X22, .X26, .X27, .X28, .X29]) (by decide)
  have hR2 : Regs level m0 st2.data :=
    ⟨(e2 .X19 (by simp)).trans hR1.x19, (e2 .X20 (by simp)).trans hR1.x20,
      (e2 .X22 (by simp)).trans hR1.x22, (e2 .X27 (by simp)).trans hR1.x27,
      (e2 .X28 (by simp)).trans hR1.x28, (e2 .X29 (by simp)).trans hR1.x29⟩
  have h21' : st2.data.regs.X21 = level.fold.toUInt64 := (e2 .X21 (by simp)).trans h21
  have h26' : st2.data.regs.X26 = m0.regs.X5 := (e2 .X26 (by simp)).trans h26
  have hx0 : st2.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm2 (r := .X0) (v := .reg .X22) rfl rfl).trans hR1.x22
  have hx1 : st2.data.regs.X1.toBitVec = loc m0 200 := by
    show (st2.data.regs.getXReg .X1).toBitVec = _
    rw [reg_val hm2 (r := .X1) rfl]
    simp [Sym.eval]
  have hx23 : st2.data.regs.X23.toBitVec = loc m0 200 := by
    show (st2.data.regs.getXReg .X23).toBitVec = _
    rw [reg_val hm2 (r := .X23) rfl]
    simp [Sym.eval]
  have hx2 : st2.data.regs.X2 = m0.regs.X5 :=
    (reg_of hm2 (r := .X2) (v := .reg .X26) (w := st1.data.regs.X26) rfl rfl).trans h26
  have h192 : NativeRustcVm.WordAt st2.data.dmem (loc m0 192) m0.regs.X5 :=
    word_of hm2 (r := 0) (o := 192) (sz := 8192) rfl (by decide) (s := .reg .X26)
      (congrArg UInt64.toBitVec h26) (by decide)
  have hF2 := Facts.block hm2 (wfF h hf1) (by decide) (by decide) hW0 hF1
  have hF2' : Facts m0 st2.data.dmem [(88, NativeRustcVm.wordBytes m0.regs.X5),
      (96, xs.toList.flatMap NativeRustcVm.ewBytes), (192, NativeRustcVm.wordBytes m0.regs.X5)] :=
    fun p hp ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact hF2.get (by simp)
      · exact hF2.get (by simp)
      · exact h192
  have hW2 : Within [(88, NativeRustcVm.wordBytes m0.regs.X5),
      (96, xs.toList.flatMap NativeRustcVm.ewBytes), (192, NativeRustcVm.wordBytes m0.regs.X5)]
      88 112 :=
    within_word (by omega) (by omega) (within_ews (by omega) (by omega)
      (within_word (by omega) (by omega) within_nil))
  have hts2 := tsB h (hm2.kept (wfF h hf1)) hs2 hts1
  have hle : 8192 + sampleChallengesStack ≤ nextLevelStack := by decide
  have hx2' : st2.data.regs.X2.toNat = m0.regs.X5.toNat := by rw [hx2]
  refine ncall c hf2 (N' := sampleChallengesStack) (o := 200) (n := 16 * m0.regs.X5.toNat) hle
    (by omega) (hsc a s3) hpc2 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m3 hf3 hq hs3 hcs ↦ ?_
  · refine ⟨c.stackOk hf2 hle, c.rcAt hf2 hle, ?_, ?_, ?_⟩
    · show TStateAt st2.data.dmem st2.data.regs.X0.toBitVec a s3
      rw [hx0]; exact hts2
    · show TStateOk st2.data st2.data.regs.X0.toBitVec a sampleChallengesStack
      rw [hx0]; exact c.tstateOk hf2 hle
    · show OutOk st2.data st2.data.regs.X0.toBitVec a st2.data.regs.X1.toBitVec
        (16 * st2.data.regs.X2.toNat) sampleChallengesStack
      rw [hx0, hx1, hx2']; exact c.localOk hf2 hle (by omega)
  · rw [hx1, hx2'] at hq'
    rw [show st2.data.regs.X0.toBitVec = tA m0 by rw [hx0]] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr (.inl hq'))
    · exact .inl hq'
  obtain ⟨⟨ood, s4, hr4, hood, hts4⟩, -, -⟩ := hq
  rw [hx2'] at hr4
  rw [hx1] at hood
  rw [hx0] at hts4
  have hos := Bus.Gkr.sampleChallenges_size hr4
  have hF3 := Facts.call c hf2 hle (by omega) hs3 hW2 (by decide) (by omega) hF2'
  refine cont m3 ood s4 hf3 (hR2.of_cs hcs) ((hcs .X21 rfl).trans h21')
    (by rw [show m3.regs.X23 = st2.data.regs.X23 from hcs .X23 rfl]; exact hx23)
    ((hcs .X26 rfl).trans h26') (hF3.cons hood) hos hts4 hr4

omit [Host] in
theorem tail3_eq {index mu : Nat} {level : Whir.Level} {w : WhirStateW}
    {rounds : Array FoldRoundW} {xs ood : Array EW} {s3 s4 : TState}
    (h : (sampleChallenges mu).run s3 = some (ood, s4)) :
    tail3 index mu level w rounds xs s3 = tail4 index mu level w rounds xs ood s4 := by
  unfold tail3; rw [h]; rfl

/-- **`read_scalar`, `grind(t, 17)`, their tests**, to `b13`. -/
theorem mid2 (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {xs ood : Array EW} {s4 : TState}
    (hrun : runN level w rounds m0 s =
      tail4 m0.regs.X1.toNat m0.regs.X5.toNat level w rounds xs ood s4)
    {m2 : MachineData} (hf : NFr m0 m2) (hR : Regs level m0 m2)
    (h21 : m2.regs.X21 = level.fold.toUInt64) (h23 : m2.regs.X23.toBitVec = loc m0 200)
    (h26 : m2.regs.X26 = m0.regs.X5)
    (hF : Facts m0 m2.dmem [(200, ood.toList.flatMap NativeRustcVm.ewBytes),
        (88, NativeRustcVm.wordBytes m0.regs.X5), (96, xs.toList.flatMap NativeRustcVm.ewBytes),
        (192, NativeRustcVm.wordBytes m0.regs.X5)])
    (hsz : xs.size = level.fold) (hos : ood.size = m0.regs.X5.toNat)
    (hts : TStateAt m2.dmem (tA m0) a s4)
    (cont : ∀ (st : MachineState) (v : EW) (s6 : TState), st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b13Offset) →
      H13 a level m0 xs ood v s6 st.data →
      runN level w rounds m0 s =
        tail6 m0.regs.X1.toNat m0.regs.X5.toNat level w rounds xs ood v s6 →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b9Offset)⟩ := by
  have c := ctx h
  have hmu30 : m0.regs.X5.toNat ≤ 30 := h.2.2.2.2.2.2.2.2.2.2.1
  have hf6 : level.fold ≤ 6 := h.2.2.2.2.2.1
  have hW : Within [(200, ood.toList.flatMap NativeRustcVm.ewBytes),
      (88, NativeRustcVm.wordBytes m0.regs.X5), (96, xs.toList.flatMap NativeRustcVm.ewBytes),
      (192, NativeRustcVm.wordBytes m0.regs.X5)] 88 592 :=
    within_ews (by omega) (by omega) (within_word (by omega) (by omega)
      (within_ews (by omega) (by omega) (within_word (by omega) (by omega) within_nil)))
  -- `b9`: `read_scalar(sp + 680, t)`.
  refine blk hp h b9_in_code (by simp [b9]) run_b9 (wfF h hf) (mF h hf) (by decide) rfl hf rfl
    fun st1 hm1 hpc1 hf1 hs1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b9Offset + b9.length = k + NativeRustcVmArm.Vm.NextLevel.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b9_next]] at hpc1
  have e1 := sameRegs_ok (mF h hf) hm1
    (rs := [.X19, .X20, .X21, .X22, .X23, .X26, .X27, .X28, .X29]) (by decide)
  have hR1 : Regs level m0 st1.data :=
    ⟨(e1 .X19 (by simp)).trans hR.x19, (e1 .X20 (by simp)).trans hR.x20,
      (e1 .X22 (by simp)).trans hR.x22, (e1 .X27 (by simp)).trans hR.x27,
      (e1 .X28 (by simp)).trans hR.x28, (e1 .X29 (by simp)).trans hR.x29⟩
  have hx0 : st1.data.regs.X0.toBitVec = loc m0 680 := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [reg_val hm1 (r := .X0) rfl]
    simp [Sym.eval]
  have hx1 : st1.data.regs.X1 = m0.regs.X0 :=
    (reg_of hm1 (r := .X1) (v := .reg .X22) rfl rfl).trans hR.x22
  have hd1 : st1.data.dmem = m2.dmem := hm1.dmem_eq (wfF h hf) rfl
  have hle : 8192 + readScalarStack ≤ nextLevelStack := by decide
  refine ncall c hf1 (N' := readScalarStack) (o := 680) (n := 24) hle (by decide) (hrs a s4) hpc1
    ?_ (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m3 hf3 hq hs3 hcs ↦ ?_
  · refine ⟨c.stackOk hf1 hle, c.rcAt hf1 hle, ?_, ?_, ?_⟩
    · show TStateAt st1.data.dmem st1.data.regs.X1.toBitVec a s4
      rw [hx1, hd1]; exact hts
    · show TStateOk st1.data st1.data.regs.X1.toBitVec a readScalarStack
      rw [hx1]; exact c.tstateOk hf1 hle
    · show OutOk st1.data st1.data.regs.X1.toBitVec a st1.data.regs.X0.toBitVec 24
        readScalarStack
      rw [hx1, hx0]; exact c.localOk hf1 hle (by decide)
  · rw [hx0, show st1.data.regs.X1.toBitVec = tA m0 by rw [hx1]] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr (.inl hq'))
    · exact .inl hq'
  obtain ⟨hopt, hnext, -, -⟩ := hq
  rw [hx0] at hopt
  rw [show st1.data.regs.X1.toBitVec = tA m0 by rw [hx1]] at hnext
  have hF3 := Facts.call c hf1 hle (by decide) hs3 hW (by decide) (by omega)
    (by rw [hd1]; exact hF)
  have hR3 := hR1.of_cs hcs
  -- `b10`: the tag.
  refine blk hp h b10_in_code (by simp [b10]) run_b10 (wfF h hf3) (mF h hf3) (by decide) rfl hf3
    rfl fun st4 hm4 hpc4 hf4 hs4 ↦ ?_
  simp only [PcOk] at hpc4
  have hd4 : st4.data.dmem = m3.dmem := hm4.dmem_eq (wfF h hf3) rfl
  cases hr5 : readScalar.run s4 with
  | none =>
    rw [hr5] at hopt
    have h0 : NativeRustcVm.WordAt m3.dmem (loc m0 680) 0 := hopt
    have l0 : (envF m0 m3).load 0 680 8 = (0 : UInt64).toBitVec := load_word (by simpa using h0)
    rw [cbz_load l0] at hpc4
    simp only [beq_self_eq_true, ↓reduceIte] at hpc4
    refine none13 hp h ?_ hf4 (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.NextLevel.b26Offset) NativeRustcVmArm.Vm.NextLevel.label_13_at))
    rw [hrun]; unfold tail4; rw [hr5]; rfl
  | some p5 =>
  obtain ⟨v, s5⟩ := p5
  rw [hr5] at hopt hnext
  obtain ⟨h1, hv⟩ : NativeRustcVm.WordAt m3.dmem (loc m0 680) 1 ∧
      NativeRustcVm.EWAt m3.dmem (off (loc m0 680) 8) v := hopt
  have l1 : (envF m0 m3).load 0 680 8 = (1 : UInt64).toBitVec := load_word (by simpa using h1)
  rw [cbz_load l1] at hpc4
  simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hpc4
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b10Offset + b10.length = k + NativeRustcVmArm.Vm.NextLevel.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b10_next]] at hpc4
  obtain ⟨hv0, hv1⟩ := NativeRustcVm.ewAt_iff.mp hv
  have e688 : off (loc m0 680) 8 = loc m0 688 := NativeRustcVm.addr_add_add _ _ _
  have e696 : loc m0 688 + BitVec.ofNat 64 8 = loc m0 696 := NativeRustcVm.addr_add_add _ _ _
  rw [e688] at hv0 hv1
  rw [e696] at hv1
  have hl0 : (envF m0 st4.data).load 0 688 8 = v.c0.toBitVec :=
    load_word (show NativeRustcVm.WordAt st4.data.dmem (loc m0 688) v.c0 by rw [hd4]; exact hv0)
  have hl1 : (envF m0 st4.data).load 0 696 8 = v.c1.toBitVec :=
    load_word (show NativeRustcVm.WordAt st4.data.dmem (loc m0 696) v.c1 by rw [hd4]; exact hv1)
  have hts5 : TStateAt st4.data.dmem (tA m0) a s5 := by rw [hd4]; exact hnext _ _ rfl
  have e4 := sameRegs_ok (mF h hf3) hm4
    (rs := [.X19, .X20, .X21, .X22, .X23, .X26, .X27, .X28, .X29]) (by decide)
  -- `b11`: the value into X24, X25, `grind(t, 17)`.
  refine blk hp h b11_in_code (by simp [b11]) run_b11 (wfF h hf4) (mF h hf4) (by decide) rfl hf4
    hpc4 fun st6 hm6 hpc6 hf6' hs6 ↦ ?_
  simp only [PcOk] at hpc6
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b11Offset + b11.length = k + NativeRustcVmArm.Vm.NextLevel.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b11_next]] at hpc6
  have e6 := sameRegs_ok (mF h hf4) hm6
    (rs := [.X19, .X20, .X21, .X22, .X23, .X26, .X27, .X28, .X29]) (by decide)
  have hd6 : st6.data.dmem = st4.data.dmem := hm6.dmem_eq (wfF h hf4) rfl
  have h24 : st6.data.regs.X24 = v.c0 := reg_of hm6 (r := .X24) rfl hl0
  have h25 : st6.data.regs.X25 = v.c1 := reg_of hm6 (r := .X25) rfl hl1
  have gx0 : st6.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm6 (r := .X0) (v := .reg .X22) rfl rfl).trans
      ((e4 .X22 (by simp)).trans ((hcs .X22 rfl).trans ((e1 .X22 (by simp)).trans hR.x22)))
  have gx1 : st6.data.regs.X1 = 17 := reg_of hm6 (r := .X1) (v := .lit 17) rfl rfl
  have hbits : grindBits st6.data = Whir.queryGrindingBits := by
    unfold grindBits; rw [gx1]; rfl
  have hleg : 8192 + grindStack ≤ nextLevelStack := by decide
  refine ncall c hf6' (N' := grindStack) (o := 0) (n := 0) hleg (by decide) (hgr a s5) hpc6 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m7 hf7 hq hs7 hcs7 ↦ ?_
  · refine ⟨c.stackOk hf6' hleg, c.rcAt hf6' hleg, ?_, ?_, ?_⟩
    · show TStateAt st6.data.dmem st6.data.regs.X0.toBitVec a s5
      rw [gx0, hd6]; exact hts5
    · show TStateOk st6.data st6.data.regs.X0.toBitVec a grindStack
      rw [gx0]; exact c.tstateOk hf6' hleg
    · rw [hbits]; decide
  · rw [show st6.data.regs.X0.toBitVec = tA m0 by rw [gx0]] at hq'
    rcases hq' with hq' | hq'
    · exact .inr (.inr (.inl hq'))
    · exact .inl hq'
  obtain ⟨h07, hnext7, -, -⟩ := hq
  rw [hbits] at h07 hnext7
  rw [show st6.data.regs.X0.toBitVec = tA m0 by rw [gx0]] at hnext7
  -- `b12`: the grind's result.
  refine chk13 hp h b12_in_code (st := ⟨m7, _⟩) hf7 rfl h07 (fun hn ↦ by
      rw [hrun]; unfold tail4; rw [hr5]
      show ((grind Whir.queryGrindingBits).run s5).bind _ = none
      exact bind_none_of hn)
    (fun _ h ↦ h) fun hok st8 hpc8 hf8 hd8 hr8 ↦ ?_
  obtain ⟨⟨⟨⟩, s6⟩, hr6⟩ := Option.isSome_iff_exists.mp hok
  have hF6 : Facts m0 st6.data.dmem [(200, ood.toList.flatMap NativeRustcVm.ewBytes),
      (88, NativeRustcVm.wordBytes m0.regs.X5), (96, xs.toList.flatMap NativeRustcVm.ewBytes),
      (192, NativeRustcVm.wordBytes m0.regs.X5)] := by rw [hd6, hd4]; exact hF3
  have hF7 := Facts.call c hf6' hleg (by decide) hs7 hW (by decide) (by omega) hF6
  have cs : ∀ r, calleeSaved r = true →
      r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X26, .X27, .X28, .X29] →
      st8.data.regs.getXReg r = m2.regs.getXReg r := by
    intro r hc hr
    rw [hr8 r, hcs7 r hc, e6 r hr, e4 r hr, hcs r hc, e1 r hr]
  refine cont st8 v s6 (by rw [hpc8, ← b12_next]; simp only [b12_length, b12Length, Nat.add_assoc]) ⟨hf8, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hsz,
    hos, ?_⟩ ?_
  · exact (cs .X19 rfl (by simp)).trans hR.x19
  · exact (cs .X20 rfl (by simp)).trans hR.x20
  · exact (cs .X22 rfl (by simp)).trans hR.x22
  · exact (cs .X27 rfl (by simp)).trans hR.x27
  · exact (cs .X28 rfl (by simp)).trans hR.x28
  · exact (cs .X29 rfl (by simp)).trans hR.x29
  · exact (cs .X21 rfl (by simp)).trans h21
  · rw [show st8.data.regs.X23 = m2.regs.X23 from cs .X23 rfl (by simp)]; exact h23
  · rw [show st8.data.regs.X24 = st6.data.regs.X24 from (hr8 .X24).trans (hcs7 .X24 rfl)]
    exact h24
  · rw [show st8.data.regs.X25 = st6.data.regs.X25 from (hr8 .X25).trans (hcs7 .X25 rfl)]
    exact h25
  · exact (cs .X26 rfl (by simp)).trans h26
  · rw [hd8]; exact hF7
  · rw [hd8]; exact hnext7 _ _ hr6
  · rw [hrun]; unfold tail4; rw [hr5]
    show ((grind Whir.queryGrindingBits).run s5).bind _ = _
    rw [hr6]; rfl

end

end

end NativeRustcVmArm.Whir.NextLevel
