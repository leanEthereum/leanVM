module

public import NativeRustcVmArm.Code.Vm.SampleQueries.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Whir.NextLevel.Regions

/-!
# `next_level`: the queries and `λ`

From `b13` (`H13`): the out-of-domain value's `c0` stored at `80`, `sample_queries(t, μ + rate,
queries, &w.queries)` (`b13`, always `Some`; `b14`), `squeeze` for `λ` (`b15`), `λ` stored at
`64`, `72` and the zeroing loop set up (`b16`): `qry`, to the loop's head `b17` with `H17`.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

@[expose] public section

/-- The frame's facts at `b13`. -/
abbrev F13 (m0 : MachineData) (xs ood : Array EW) : List (Nat × List UInt8) :=
  [(200, ood.toList.flatMap NativeRustcVm.ewBytes), (88, NativeRustcVm.wordBytes m0.regs.X5),
    (96, xs.toList.flatMap NativeRustcVm.ewBytes), (192, NativeRustcVm.wordBytes m0.regs.X5)]

/-- The frame's facts from `b17` on: `λ` (`c1`, `c0`) at `64`, `72`, the out-of-domain value's
`c0` at `80`. -/
abbrev F17 (m0 : MachineData) (xs ood : Array EW) (v lam : EW) : List (Nat × List UInt8) :=
  (64, NativeRustcVm.wordBytes lam.c1) :: (72, NativeRustcVm.wordBytes lam.c0) ::
    (80, NativeRustcVm.wordBytes v.c0) :: F13 m0 xs ood

/-- At the zeroing loop's head (`b17`), turn `i`. -/
structure H17 [Labels] (a : DecArea) (level : Whir.Level) (m0 : MachineData) (xs ood : Array EW)
    (v lam : EW) (qs : Array UInt64) (s8 : TState) (i : Nat) (st : MachineData) : Prop where
  fr : NFr m0 st
  x19 : st.regs.X19 = m0.regs.X6
  x20 : st.regs.X20 = m0.regs.X1
  x21 : st.regs.X21 = level.fold.toUInt64
  x22 : st.regs.X22 = m0.regs.X0
  x23 : st.regs.X23.toBitVec = loc m0 200
  x24 : st.regs.X24.toBitVec = pA m0 + BitVec.ofNat 64 57344
  x25 : st.regs.X25 = v.c1
  x26 : st.regs.X26 = m0.regs.X5
  x8 : st.regs.X8 = qs.size.toUInt64
  x9 : st.regs.X9.toNat = 64 * i
  x10 : st.regs.X10.toBitVec = loc m0 4368
  facts : Facts m0 st.dmem (F17 m0 xs ood v lam)
  size : xs.size = level.fold
  osize : ood.size = m0.regs.X5.toNat
  qbuf : NativeRustcVm.BufWordsAt st.dmem (qA m0) queryCap qs.toList
  ts : TStateAt st.dmem (tA m0) a s8
  i57 : i ≤ 57

end

public section

theorem within13 {m0 : MachineData} {xs ood : Array EW} (h1 : xs.size ≤ 6) (h2 : ood.size ≤ 30) :
    Within (F13 m0 xs ood) 88 592 :=
  within_ews (by omega) (by omega) (within_word (by omega) (by omega)
    (within_ews (by omega) (by omega) (within_word (by omega) (by omega) within_nil)))

theorem within17 {m0 : MachineData} {xs ood : Array EW} {v lam : EW} (h1 : xs.size ≤ 6)
    (h2 : ood.size ≤ 30) : Within (F17 m0 xs ood v lam) 64 616 :=
  within_word (by omega) (by omega) (within_word (by omega) (by omega)
    (within_word (by omega) (by omega) ((within13 h1 h2).mono (by omega) (by omega))))

theorem two_iff {x y q : BitVec 64} {n m : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩, ⟨y, m⟩] q ↔ InRange x n q ∨ InRange y m q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]
  exact Iff.rfl

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The queries and `λ`**, to the zeroing loop. -/
theorem qry (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hsq : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s))
    (hsqz : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} {xs ood : Array EW} {v : EW} {s6 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b13Offset)) (h13 : H13 a level m0 xs ood v s6 st.data)
    (hrun : runN level w rounds m0 s =
      tail6 m0.regs.X1.toNat m0.regs.X5.toNat level w rounds xs ood v s6)
    (cont : ∀ (st' : MachineState) (qs : Array UInt64) (lam : EW) (s8 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b17Offset) → H17 a level m0 xs ood v lam qs s8 0 st'.data →
      runN level w rounds m0 s =
        tail8 m0.regs.X1.toNat m0.regs.X5.toNat w rounds xs ood v qs lam s8 →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  have c := ctx h
  have g := geo h
  have hf := h13.fr
  have hmu30 : m0.regs.X5.toNat ≤ 30 := h.2.2.2.2.2.2.2.2.2.2.1
  have hf6 : level.fold ≤ 6 := h.2.2.2.2.2.1
  have hrate : level.logInvRate < 64 := h.2.2.2.2.2.2.1
  have hqc : level.queries ≤ queryCap := h.2.2.2.2.2.2.2.1
  have hW13 := within13 (m0 := m0) (xs := xs) (ood := ood) (by rw [h13.size]; exact hf6)
    (by rw [h13.osize]; exact hmu30)
  -- `b13`: `sample_queries(t, μ + rate, queries, &w.queries)`.
  have hlv := level_words (level_keep h hf)
  have hq16 := hlv.2.2
  rw [NativeRustcVm.addr_add_add] at hq16
  have hld : (envL m0 st.data).load 1 16 8 = level.queries.toUInt64.toBitVec :=
    load_word (by simpa using hq16)
  refine blk hp h b13_in_code (by simp [b13]) run_b13 (wfL h hf) (mL h hf h13.regs.x28)
    (by decide) rfl hf hpc fun st1 hm1 hpc1 hf1 hs1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b13Offset + b13.length = k + NativeRustcVmArm.Vm.NextLevel.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b13_next]] at hpc1
  have e1 := sameRegs_ok (mL h hf h13.regs.x28) hm1
    (rs := [.X19, .X20, .X21, .X22, .X23, .X25, .X26, .X27, .X29]) (by decide)
  have hx0 : st1.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm1 (r := .X0) (v := .reg .X22) rfl rfl).trans h13.regs.x22
  have hx1 : st1.data.regs.X1.toNat = m0.regs.X5.toNat + level.logInvRate := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X1) rfl, ev_add2, BitVec.toNat_add,
      show st.data.regs.getXReg .X29 = _ from h13.regs.x29,
      show st.data.regs.getXReg .X27 = _ from h13.regs.x27, toNat_toUInt64' (by omega),
      UInt64.toNat_toBitVec]
    omega
  have hx2 : st1.data.regs.X2.toNat = level.queries := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X2) rfl]
    show ((envL m0 st.data).load 1 16 8).toNat = _
    rw [hld, toNat_toUInt64' (level_keep h hf).2.2.1]
  have hx3 : st1.data.regs.X3.toBitVec = qA m0 := by
    show (st1.data.regs.getXReg .X3).toBitVec = _
    rw [reg_val hm1 (r := .X3) rfl]
    sym_simp
    simp only [Env.ofMachine_regs, show st.data.regs.getXReg .X19 = m0.regs.X6 from h13.regs.x19]
    rfl
  have hx28 : st1.data.regs.X28.toBitVec = qA m0 := by
    show (st1.data.regs.getXReg .X28).toBitVec = _
    rw [reg_val hm1 (r := .X28) rfl]
    sym_simp
    simp only [Env.ofMachine_regs, show st.data.regs.getXReg .X19 = m0.regs.X6 from h13.regs.x19]
    rfl
  have hx24 : st1.data.regs.X24.toBitVec = pA m0 + BitVec.ofNat 64 57344 := by
    show (st1.data.regs.getXReg .X24).toBitVec = _
    rw [reg_val hm1 (r := .X24) rfl, ev_add,
      show st.data.regs.getXReg .X19 = m0.regs.X6 from h13.regs.x19]
  have h80 : NativeRustcVm.WordAt st1.data.dmem (loc m0 80) v.c0 :=
    word_of hm1 (r := 0) (o := 80) (sz := 8192) rfl (by decide) (s := .reg .X24)
      (congrArg UInt64.toBitVec h13.x24) (by decide)
  have hF1 := Facts.block hm1 (wfL h hf) (by decide) (by decide) hW13 h13.facts
  have hts1 := tsB h (hm1.kept (wfL h hf)) hs1 h13.ts
  have hle : 8192 + sampleQueriesStack ≤ nextLevelStack := by decide
  have hqo := whirOut_sub (whirOut h) (o := queriesOff) (k := queryBufBytes) (by decide)
  have hso : ∀ m' : MachineData, SampleQueriesPost a s6 st1.data m' →
      SameOutside st1.data.dmem m'.dmem (fun q ↦
        InRange (stackBelow st1.data sampleQueriesStack) sampleQueriesStack q ∨
          InRange (loc m0 0) 0 q ∨ outs m0 q) := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rcases hq' with hq' | hq'
      · rcases two_iff.mp hq' with hq' | hq'
        · rw [hx3] at hq'; exact .inr (.inr (.inr hq'))
        · rw [show st1.data.regs.X0.toBitVec = tA m0 by rw [hx0]] at hq'
          exact .inr (.inr (.inl hq'))
      · exact .inl hq'
  refine ncall c hf1 (N' := sampleQueriesStack) (o := 0) (n := 0) hle (by decide) (hsq a s6) hpc1
    ?_ (fun m' hq ↦ ⟨hso m' hq, hq.2.2.2⟩) fun m2 hf2 hq hs2 hcs2 ↦ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · show WhirT st1.data st1.data.regs.X0.toBitVec a sampleQueriesStack
      rw [hx0]; exact whirT' h hf1 hle
    · show TStateAt st1.data.dmem st1.data.regs.X0.toBitVec a s6
      rw [hx0]; exact hts1
    · show st1.data.regs.X2.toNat ≤ queryCap
      rw [hx2]; exact hqc
    · show WhirOut st1.data st1.data.regs.X0.toBitVec a st1.data.regs.X3.toBitVec queryBufBytes
        sampleQueriesStack
      rw [hx0, hx3]; exact whirOut' h hf1 hle hqo
  obtain ⟨h02, ⟨qs, s7, hr7, hbuf, hts7⟩, -, -⟩ := hq
  rw [hx1, hx2] at hr7
  rw [hx3] at hbuf
  rw [show st1.data.regs.X0.toBitVec = tA m0 by rw [hx0]] at hts7
  have hW80 : Within ((80, NativeRustcVm.wordBytes v.c0) :: F13 m0 xs ood) 80 600 :=
    within_word (by omega) (by omega) (hW13.mono (by omega) (by omega))
  have hF2 := Facts.call c hf1 hle (o' := 0) (n' := 0) (by decide) hs2
    hW80 (by decide) (by omega) (hF1.cons h80)
  -- `b14`: `sample_queries`' result.
  refine chk14 hp h b14_in (st := ⟨m2, _⟩) hf2 rfl (ok := true) h02 (fun e ↦ by cases e)
    (fun _ h ↦ h) fun _ st3 hpc3 hf3 hd3 hr3 ↦ ?_
  -- `b15`: `squeeze(t)`.
  refine blk hp h b15_in_code (by simp [b15]) run_b15 (wfF h hf3) (mF h hf3) (by decide) rfl hf3
    hpc3 fun st4 hm4 hpc4 hf4 hs4 ↦ ?_
  simp only [PcOk] at hpc4
  rw [Nat.add_assoc, b15_next] at hpc4
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (wfF h hf3) rfl
  have e4 := sameRegs_ok (mF h hf3) hm4
    (rs := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X28]) (by decide)
  have cs3 : ∀ r, calleeSaved r = true →
      r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X28] →
      st4.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hc hr ↦ by
    rw [e4 r hr, hr3 r, hcs2 r hc]
  have g0 : st4.data.regs.X0.toBitVec = tA m0 := by
    rw [show st4.data.regs.X0 = st3.data.regs.X22 from reg_of hm4 (r := .X0) (v := .reg .X22)
      rfl rfl, show st3.data.regs.X22 = st1.data.regs.X22 from (hr3 .X22).trans (hcs2 .X22 rfl),
      show st1.data.regs.X22 = st.data.regs.X22 from e1 .X22 (by simp), h13.regs.x22]
  have hts4 : TStateAt st4.data.dmem (tA m0) a s7 := by rw [hd4, hd3]; exact hts7
  have hle' : 8192 + squeezeStack ≤ nextLevelStack := by decide
  refine tsqueeze c hsqz hf4 hle' (fun _ h ↦ by cases h) slots_le' hpc4 g0 hts4
    fun m5 hf5 hts5 h0 h1 hcs5 hs5 ↦ ?_
  have hs5' : SameOutside st4.data.dmem m5.dmem (fun q ↦
      InRange (stackBelow st4.data squeezeStack) squeezeStack q ∨ InRange (loc m0 0) 0 q ∨
        outs m0 q) :=
    NativeRustcVm.SameOutside.mono hs5 fun q hq ↦ by
      rcases hq with hq | hq
      · exact .inr (.inr (.inl (sponge_t h hq)))
      · exact .inl hq
  have hF5 := Facts.call c hf4 hle' (o' := 0) (n' := 0) (by decide) hs5'
    hW80 (by decide) (by omega) (by rw [hd4, hd3]; exact hF2)
  have hqb5 : NativeRustcVm.BufWordsAt m5.dmem (qA m0) queryCap qs.toList := by
    refine qbuf_keep h hs5 (fun q hq ↦ ?_) (by rw [hd4, hd3]; exact hbuf)
    rcases hq with hq | hq
    · have := t_nat h (sponge_t h hq); have := g.pT; omega
    · have := stack_nat h hf4 hle' hq; have := g.pS; omega
  -- `b16`: `λ` stored, the loop set up.
  have cs5 : ∀ r, calleeSaved r = true →
      r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X28] →
      m5.regs.getXReg r = st1.data.regs.getXReg r := fun r hc hr ↦ by
    rw [hcs5 r hc, cs3 r hc hr]
  have r19 : m5.regs.X19 = m0.regs.X6 :=
    (cs5 .X19 rfl (by simp)).trans ((e1 .X19 (by simp)).trans h13.regs.x19)
  have r28 : m5.regs.X28.toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 61352 := by
    rw [show m5.regs.X28 = st1.data.regs.X28 from cs5 .X28 rfl (by simp), hx28]; rfl
  have hl8 : (envW m0 m5).load 1 61352 8 = qs.size.toUInt64.toBitVec := by
    have := hqb5.2.1
    rw [Array.length_toList] at this
    exact load_word (show NativeRustcVm.WordAt m5.dmem (qA m0) _ from this)
  refine blk hp h b16_in_code (by simp [b16]) run_b16 (wfW h hf5) (mB h hf5 r19 r28) (by decide)
    rfl hf5 rfl fun st6 hm6 hpc6 hf6' hs6 ↦ ?_
  simp only [PcOk] at hpc6
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b16Offset + b16.length = k + NativeRustcVmArm.Vm.NextLevel.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b16_next]] at hpc6
  have e6 := sameRegs_ok (mB h hf5 r19 r28) hm6
    (rs := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26]) (by decide)
  have r6 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26],
      st6.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦ by
    rw [e6 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact cs5 _ rfl (by simp)
  have r1 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X25, .X26],
      st6.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [r6 _ (by simp), e1 _ (by simp)]
  have w64 : NativeRustcVm.WordAt st6.data.dmem (loc m0 64) (NativeRustcVm.Whir.sq s7).1.c1 :=
    word_of hm6 (r := 0) (o := 64) (sz := 8192) rfl (by decide) (s := .reg .X1)
      (congrArg UInt64.toBitVec h1) (by decide)
  have w72 : NativeRustcVm.WordAt st6.data.dmem (loc m0 72) (NativeRustcVm.Whir.sq s7).1.c0 :=
    word_of hm6 (r := 0) (o := 72) (sz := 8192) rfl (by decide) (s := .reg .X0)
      (congrArg UInt64.toBitVec h0) (by decide)
  have hF6 := Facts.block hm6 (wfW h hf5) (by decide) (by decide) hW80 hF5
  refine cont st6 qs (NativeRustcVm.Whir.sq s7).1 (NativeRustcVm.Whir.sq s7).2 hpc6
    ⟨hf6', (r1 .X19 (by simp)).trans h13.regs.x19, (r1 .X20 (by simp)).trans h13.regs.x20,
      (r1 .X21 (by simp)).trans h13.x21, (r1 .X22 (by simp)).trans h13.regs.x22, ?_, ?_,
      (r1 .X25 (by simp)).trans h13.x25, (r1 .X26 (by simp)).trans h13.x26,
      reg_of hm6 (r := .X8) rfl hl8, ?_, ?_, (hF6.cons w72).cons w64, h13.size, h13.osize,
      qbuf_keep h hs6 (fun q hq ↦ by have := frame_nat h hq; have := g.pS; omega) hqb5,
      tsB h (hm6.kept (wfW h hf5)) hs6 hts5, by decide⟩ ?_
  · rw [show st6.data.regs.X23 = st.data.regs.X23 from r1 .X23 (by simp)]; exact h13.x23
  · rw [show st6.data.regs.X24 = st1.data.regs.X24 from r6 .X24 (by simp)]; exact hx24
  · rw [← UInt64.toNat_toBitVec]
    show (st6.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [reg_val hm6 (r := .X9) rfl]
    rfl
  · show (st6.data.regs.getXReg .X10).toBitVec = _
    rw [reg_val hm6 (r := .X10) rfl]
    simp [Sym.eval]
  · rw [hrun]; unfold tail6; rw [hr7]; rfl

end

end

end NativeRustcVmArm.Whir.NextLevel
