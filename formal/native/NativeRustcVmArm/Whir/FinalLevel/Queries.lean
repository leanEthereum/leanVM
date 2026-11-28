module

public import NativeRustcVmArm.Code.Vm.SampleQueries.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Whir.FinalLevel.State
public import NativeRustcVmArm.Whir.WhirLevels.Calls

/-!
# `final_level`: the grind and the queries

`queries`: from `b6`, the grind (`b6`, `b7`: `None` to the epilogue), the queries sampled into
the `WhirW`'s buffer (`b8`, `b9`; `sample_queries` always succeeds), to `b10`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr)

public section

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem three_iff {x y z q : BitVec 64} {n m l : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩, ⟨y, m⟩, ⟨z, l⟩] q ↔ InRange x n q ∨ InRange y m q ∨
      InRange z l q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]
  exact Iff.rfl

omit [Host] in
theorem two_iff {x y q : BitVec 64} {n m : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩, ⟨y, m⟩] q ↔ InRange x n q ∨ InRange y m q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]
  exact Iff.rfl

/-- **The grind and the queries.** -/
theorem queries (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s))
    {st : MachineState} {folded : Array EW} {s1 : TState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b6Offset))
    (hl : Live level m0 st.data folded) (hx26 : st.data.regs.X26 = m0.regs.X2)
    (hx25 : st.data.regs.X25.toNat = level.logInvRate)
    (hts : TStateAt st.data.dmem (tA m0) a s1)
    (hrun : runF s0 level b w rounds m0 =
      (C1 m0.regs.X1.toNat level (mu m0) m0.regs.X4.toNat b w rounds folded).run s1)
    (cont : ∀ (st' : MachineState) (qs : Array UInt64) (s3 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b10Offset) → Live level m0 st'.data folded →
      (st'.data.regs.X26).toBitVec = qA m0 →
      (st'.data.regs.X29).toBitVec = pA m0 + BitVec.ofNat 64 57344 →
      NativeRustcVm.BufWordsAt st'.data.dmem (qA m0) queryCap qs.toList →
      TStateAt st'.data.dmem (tA m0) a s3 →
      runF s0 level b w rounds m0 =
        (C3 m0.regs.X1.toNat (mu m0) m0.regs.X4.toNat b w rounds folded qs).run s3 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hfo := c.two_mu_le
  have hmu : m0.regs.X3.toNat < 64 := c.mu64
  -- `b6`: `grind(t, 17)`.
  refine c.fblock hp b6_in_code (by simp [b6]) run_b6 rfl rfl hpc hl.fr
    fun st6 hm6 hpc6 hf6 hd6 hk6 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b6Offset + b6.length = k + NativeRustcVmArm.Vm.FinalLevel.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b6_next]] at hpc6
  have x0 : st6.data.regs.X0.toBitVec = tA m0 := by
    have := reg_val hm6 (r := .X0) (v := .reg .X22) rfl
    rw [show st6.data.regs.X0.toBitVec = _ from this]
    exact congrArg UInt64.toBitVec hl.x22
  have x1 : st6.data.regs.X1.toNat = 17 := by
    have := reg_val hm6 (r := .X1) (v := .lit 17) rfl
    rw [← UInt64.toNat_toBitVec, show st6.data.regs.X1.toBitVec = _ from this]; rfl
  have hle : 2672 + grindStack ≤ finalLevelStack := by decide
  have hl6 : Live level m0 st6.data folded :=
    hl.saved hf6 (fun r hr ↦ hk6 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd6]) hfo
  refine c.call hf6 (lo := 0) (n := 0) hle (by decide) (hgr a s1) hpc6 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q h ↦ ?_, hq.2.2.2⟩)
    fun m2 hf2 hq hcs ↦ ?_
  · refine ⟨c.stackOk' hf6 hle, c.rcAt' hf6 hle, ?_, ?_, ?_⟩
    · show TStateAt st6.data.dmem st6.data.regs.X0.toBitVec a s1
      rw [x0, hd6]; exact hts
    · show TStateOk st6.data st6.data.regs.X0.toBitVec a grindStack
      rw [x0]; exact c.tstateOk' hf6 hle
    · show st6.data.regs.X1.toNat % 2 ^ 32 < 64
      rw [x1]; decide
  · rcases h with h | h
    · rw [x0] at h; exact .inr (.inr (.inr h))
    · exact .inl h
  -- `b7`: the grind's verdict.
  obtain ⟨h0, hnext, hs2, -⟩ := hq
  have hg : grindBits st6.data = Whir.queryGrindingBits := by
    show st6.data.regs.X1.toNat % 2 ^ 32 = 17; rw [x1]; decide
  rw [hg] at h0 hnext
  rw [x0] at hnext hs2
  have hl2 : Live level m0 m2 folded :=
    hl6.saved hf2 (live_cs hcs) (c.same_call hf6 hle (lo := 0) (n := 0)
      (NativeRustcVm.SameOutside.mono hs2 fun q h ↦ by
        rcases h with h | h
        · exact .inr (.inr (.inr h))
        · exact .inl h) (by decide) (by omega) (by decide)) hfo
  refine c.fblock hp b7_in_code (by simp [b7]) run_b7 rfl rfl rfl hf2
    fun st7 hm7 hpc7 hf7 hd7 hk7 ↦ ?_
  simp only [PcOk] at hpc7
  rw [cbz_ok (show (fenv m0 m2 []).regs .X0 = _ from congrArg UInt64.toBitVec h0)] at hpc7
  have hl7 : Live level m0 st7.data folded :=
    hl2.saved hf7 (fun r hr ↦ hk7 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd7]) hfo
  cases hr : (grind Whir.queryGrindingBits).run s1 with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte,
      hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b3Offset) NativeRustcVmArm.Vm.FinalLevel.label_3_at] at hpc7
    have hnone : runF s0 level b w rounds m0 = none := by
      rw [hrun, C1]; exact run_bind_none hr
    refine exit3 hp c hpc7 hf7 ?_ ?_
    · rw [hnone, show st7.data.regs.X0 = m2.regs.X0 from hk7 .X0 rfl]; rw [hr] at h0; exact h0
    · rw [hnone]; intro _ _ h; cases h
  | some p =>
  obtain ⟨⟨⟩, s2⟩ := p
  simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.FinalLevel.b7Offset + b7.length = k + NativeRustcVmArm.Vm.FinalLevel.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b7_next]] at hpc7
  have hts2 : TStateAt st7.data.dmem (tA m0) a s2 := by rw [hd7]; exact hnext () s2 hr
  have hrun2 : runF s0 level b w rounds m0 =
      (C2 m0.regs.X1.toNat level (mu m0) m0.regs.X4.toNat b w rounds folded).run s2 := by
    rw [hrun, C1]; exact run_bind_some hr
  -- `b8`: `sample_queries(t, μ + rate, queries, &w.queries)`.
  have hf7 := hl7.fr
  have x26 : (st7.data.regs.getXReg .X26).toBitVec = lvA m0 :=
    congrArg UInt64.toBitVec
      (((hk7 .X26 rfl).trans ((hcs .X26 rfl).trans (hk6 .X26 rfl))).trans hx26)
  have hwf8 := c.wf1 hf7 c.lin
  refine exec_at (inf hp b8_in_code (by simp [b8])) run_b8 hwf8 hpc7 (c.match1 hf7 x26)
    fun st8 hm8 hpc8 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b8Offset + b8.length = k + NativeRustcVmArm.Vm.FinalLevel.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b8_next]] at hpc8
  have hf8 : FFr m0 st8.data :=
    Fr.ofBlock hf7 (c.match1 hf7 x26) hm8 hwf8 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd8 : st8.data.dmem = st7.data.dmem := hm8.dmem_eq hwf8 rfl
  have hk8 : ∀ r, (after b8 lev26S).reg r = some (.reg r) →
      st8.data.regs.getXReg r = st7.data.regs.getXReg r := fun r h ↦
    reg_of hm8 (by rw [← after_eq run_b8]; exact h) rfl
  have hl8 : Live level m0 st8.data folded :=
    hl7.saved hf8 (fun r hr ↦ hk8 r (kept_of (by rw [after_eq run_b8]; decide) r hr))
      (fun j _ ↦ by rw [hd8]) hfo
  have k25 : st7.data.regs.X25 = st.data.regs.X25 :=
    (hk7 .X25 rfl).trans ((hcs .X25 rfl).trans (hk6 .X25 rfl))
  have hr64 := c.rate
  have x0 : st8.data.regs.X0.toBitVec = tA m0 := by
    have := reg_val hm8 (r := .X0) (v := .reg .X22) rfl
    rw [show st8.data.regs.X0.toBitVec = _ from this]
    exact congrArg UInt64.toBitVec hl7.x22
  have x1 : st8.data.regs.X1.toNat = mu m0 + level.logInvRate := by
    have := (reg_val hm8 (r := .X1) (v := .bin .add .W64 (.reg .X25) (.reg .X20)) rfl).trans
      (ev_add2 _ _ _ _)
    rw [← UInt64.toNat_toBitVec, show st8.data.regs.X1.toBitVec = _ from this, BitVec.toNat_add]
    have e25 : (st7.data.regs.getXReg .X25).toBitVec.toNat = level.logInvRate := by
      rw [UInt64.toNat_toBitVec]; exact (congrArg UInt64.toNat k25).trans hx25
    have e20 : (st7.data.regs.getXReg .X20).toBitVec.toNat = mu m0 := by
      rw [UInt64.toNat_toBitVec]; exact congrArg UInt64.toNat hl7.base.x20
    rw [e25, e20]
    have : mu m0 < 64 := c.mu64
    omega
  have x2 : st8.data.regs.X2.toNat = level.queries := by
    obtain ⟨-, -, hq64, hw⟩ := c.level_at hf7
    have hl : (fenv m0 st7.data [(lvA m0, 24)]).load 1 16 8 = level.queries.toUInt64.toBitVec :=
      load_ofMachine (r := 1) (o := 16) rfl
        (by simpa [off] using NativeRustcVm.wordsAt_getElem hw (i := 2) (by simp))
    have := (reg_val hm8 (r := .X2) (v := .load 1 16 8) rfl).trans hl
    rw [← UInt64.toNat_toBitVec, show st8.data.regs.X2.toBitVec = _ from this]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hq64
  have x3 : st8.data.regs.X3.toBitVec = qA m0 := by
    have := (reg_val hm8 (r := .X3) (v := .bin .add .W64 (.reg .X27) (.lit 61352)) rfl).trans
      (ev_add _ _ _ _)
    rw [show st8.data.regs.X3.toBitVec = _ from this]
    rw [show st7.data.regs.getXReg .X27 = m0.regs.X6 from hl7.base.x27]
    rfl
  have x26 : st8.data.regs.X26.toBitVec = qA m0 := by
    have := (reg_val hm8 (r := .X26) (v := .bin .add .W64 (.reg .X27) (.lit 61352)) rfl).trans
      (ev_add _ _ _ _)
    rw [show st8.data.regs.X26.toBitVec = _ from this]
    rw [show st7.data.regs.getXReg .X27 = m0.regs.X6 from hl7.base.x27]
    rfl
  have x29 : st8.data.regs.X29.toBitVec = pA m0 + BitVec.ofNat 64 57344 := by
    have := (reg_val hm8 (r := .X29) (v := .bin .add .W64 (.reg .X27) (.lit 57344)) rfl).trans
      (ev_add _ _ _ _)
    rw [show st8.data.regs.X29.toBitVec = _ from this]
    rw [show st7.data.regs.getXReg .X27 = m0.regs.X6 from hl7.base.x27]
  have hle8 : 2672 + sampleQueriesStack ≤ finalLevelStack := by decide
  have hwo := WhirLevels.whirOut_sub c.pout (o := queriesOff) (k := queryBufBytes) (by decide)
  have hso : ∀ m' : MachineData, SampleQueriesPost a s2 st8.data m' →
      SameOutside st8.data.dmem m'.dmem (fun q ↦ InRange (stackBelow st8.data sampleQueriesStack)
        sampleQueriesStack q ∨ InRange (loc m0 0) 0 q ∨ outs m0 q) := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.2.1 fun q h ↦ by
      rcases h with h | h
      · rcases two_iff.mp h with h | h
        · rw [x3] at h; exact .inr (.inr (.inl h))
        · rw [x0] at h; exact .inr (.inr (.inr h))
      · exact .inl h
  refine c.call hf8 (lo := 0) (n := 0) hle8 (by decide) (hsq a s2) hpc8 ?_
    (fun m' hq ↦ ⟨hso m' hq, hq.2.2.2⟩) fun m2 hf2 hq hcs2 ↦ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show WhirT st8.data st8.data.regs.X0.toBitVec a sampleQueriesStack
      rw [x0]; exact c.whirT hf8 hle8
    · show TStateAt st8.data.dmem st8.data.regs.X0.toBitVec a s2
      rw [x0, hd8]; exact hts2
    · show st8.data.regs.X2.toNat ≤ queryCap
      rw [x2]; exact c.queries
    · show WhirOut st8.data st8.data.regs.X0.toBitVec a st8.data.regs.X3.toBitVec queryBufBytes
        sampleQueriesStack
      rw [x0, x3]
      exact ⟨c.tctx.outOk hf8 hle8 hwo.1, hwo.2⟩
  -- `b9`: `sample_queries` succeeds.
  have hs2 := hso m2 hq
  obtain ⟨h0, ⟨qs, s3, hq3, hbuf, hts3⟩, -, -⟩ := hq
  rw [x1, x2] at hq3
  rw [x3] at hbuf
  rw [x0] at hts3
  have hl2 : Live level m0 m2 folded :=
    hl8.saved hf2 (live_cs hcs2) (c.same_call hf8 hle8 (lo := 0) (n := 0) hs2 (by decide)
      (by omega) (by decide)) hfo
  refine c.fblock hp b9_in_code (by simp [b9]) run_b9 rfl rfl rfl hf2
    fun st9 hm9 hpc9 hf9 hd9 hk9 ↦ ?_
  simp only [PcOk] at hpc9
  rw [cbz_ok (b := true) (show (fenv m0 m2 []).regs .X0 = _ from congrArg UInt64.toBitVec h0)]
    at hpc9
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.FinalLevel.b9Offset + b9.length = k + NativeRustcVmArm.Vm.FinalLevel.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b9_next]] at hpc9
  have hl9 : Live level m0 st9.data folded :=
    hl2.saved hf9 (fun r hr ↦ hk9 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd9]) hfo
  refine cont st9 qs s3 hpc9 hl9 ?_ ?_ (by rw [hd9]; exact hbuf) (by rw [hd9]; exact hts3) ?_
  · exact (congrArg UInt64.toBitVec ((hk9 .X26 rfl).trans (hcs2 .X26 rfl))).trans x26
  · exact (congrArg UInt64.toBitVec ((hk9 .X29 rfl).trans (hcs2 .X29 rfl))).trans x29
  · rw [hrun2, C2]; exact run_bind_some hq3

end

end NativeRustcVmArm.Whir.FinalLevel
