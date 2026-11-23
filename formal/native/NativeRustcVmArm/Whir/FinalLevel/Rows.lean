module

public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmArm.Whir.FinalLevel.Check
public import NativeVm.Math.QueryRows

/-!
# `final_level`: the openings and the rows' check

`rows`: from `b10`, the openings (`b10`, `query_openings`; `b11`, `None` to `.LFinalLevel_2`),
the rows checked against the folded scalars (`b12`, `each_row`; `b13`, a rejection to
`.LFinalLevel_2`), to `b14`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr wordAt_write load_of_wordAt)
open NativeRustcVm.Sumcheck (RowsAt OptRowsAt openingsWords)
open NativeVm (phaseBase phaseWords)

public section

/-- `queryOpenings` that returned: the phase's leaves, the phase advanced. -/
theorem qo_some {i : Nat} {qs : Array UInt64} {s s' : TState} {rows : Array (Array UInt64)}
    (h : (queryOpenings i qs).run s = some (rows, s')) :
    ∃ hlt : s.phase < s.openings.size, rows = s.openings[s.phase].map (·.leaf) ∧
      s' = { s with phase := s.phase + 1 } := by
  rw [NativeVm.Equiv.queryOpenings_run] at h
  split at h
  · rename_i r ph _ hph
    cases ho : openPhase r.digest r.height r.width qs ph with
    | none => rw [ho] at h; cases h
    | some rows' =>
      rw [ho] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hph
      exact ⟨hlt, by rw [(NativeVm.Math.openPhase_some ho).1, heq], rfl⟩
  · cases h

theorem ite_ult_pos [Labels] {env : Env} {x y z : Sym} {n : Nat} (hx : (x.eval env).toNat < n)
    (hn : n < 2 ^ 64) : (Sym.ite (.cmp .ult .W64 x (.lit n)) y z).eval env = y.eval env := by
  sym_simp
  have hc : (x.eval env).ult (BitVec.ofNat 64 n) = true := by
    rw [bv_ult_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    exact decide_eq_true hx
  simp only [hc, ↓reduceIte]

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The openings and the rows' check.** -/
theorem rows (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hqo : ∀ a s Q, Spec (Labels.label NativeRustcVmArm.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    (hrow : ∀ rows op, Spec (Labels.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.entryLabel) (EachRowFinalPre rows op)
      (EachRowFinalPost rows))
    {st : MachineState} {folded : Array EW} {qs : Array UInt64} {s3 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b10Offset)) (hl : Live level m0 st.data folded)
    (hx26 : (st.data.regs.getXReg .X26).toBitVec = qA m0)
    (hx29 : (st.data.regs.getXReg .X29).toBitVec = pA m0 + BitVec.ofNat 64 57344)
    (hq : NativeRustcVm.BufWordsAt st.data.dmem (qA m0) queryCap qs.toList)
    (hts : TStateAt st.data.dmem (tA m0) a s3)
    (hrun : runF s0 level b w rounds m0 =
      (C3 m0.regs.X1.toNat (mu m0) m0.regs.X4.toNat b w rounds folded qs).run s3)
    (cont : ∀ (st' : MachineState) (s4 : TState), st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b14Offset) →
      Live level m0 st'.data folded → TStateAt st'.data.dmem (tA m0) a s4 →
      runF s0 level b w rounds m0 = (C5 (mu m0) m0.regs.X4.toNat b w folded).run s4 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hfo := c.two_mu_le
  have hf := hl.fr
  have hqn : qs.size ≤ queryCap := by have := hq.1; rwa [Array.length_toList] at this
  -- `b10`: `query_openings(&rows, t, index, queries)`.
  have hqin : WhirIn m0 (qA m0) 8 finalLevelStack :=
    WhirLevels.whirIn_sub c.pIn (o := queriesOff) (k := 8) (by decide)
  have hwf10 := c.wf1 hf hqin
  have hm := c.match1 (n := 8) hf hx26
  refine exec_at (inf hp b10_in_code (by simp [b10])) run_b10 hwf10 hpc hm
    fun st10 hm10 hpc10 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b10Offset + b10.length = k + NativeRustcVmArm.Vm.FinalLevel.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b10_next]] at hpc10
  have hf10 : FFr m0 st10.data :=
    Fr.ofBlock hf hm hm10 hwf10 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd10 : st10.data.dmem = st.data.dmem := hm10.dmem_eq hwf10 rfl
  have hl10 : Live level m0 st10.data folded :=
    hl.saved hf10 (fun r hr ↦ reg_of hm10 (kept_of (by decide) r hr) rfl)
      (fun j _ ↦ by rw [hd10]) hfo
  have l0 : (fenv m0 st.data [(qA m0, 8)]).load 1 0 8 = qs.size.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero, ← Array.length_toList]; exact hq.2.1)
  have hlt : ((Sym.load 1 0 8).eval (fenv m0 st.data [(qA m0, 8)])).toNat < 231 := by
    show ((fenv m0 st.data [(qA m0, 8)]).load 1 0 8).toNat < 231
    rw [l0]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    unfold queryCap at hqn
    omega
  have x0 : st10.data.regs.X0.toBitVec = loc m0 2064 :=
    reg_val hm10 (r := .X0) (v := .ptr 0 2064) rfl
  have x1 : st10.data.regs.X1.toBitVec = tA m0 := by
    rw [show st10.data.regs.X1.toBitVec = _ from reg_val hm10 (r := .X1) (v := .reg .X22) rfl]
    exact congrArg UInt64.toBitVec hl.x22
  have x2 : st10.data.regs.X2 = m0.regs.X1 :=
    (reg_of hm10 (r := .X2) (v := .reg .X24) rfl rfl).trans hl.x24
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have vq : ((Sym.ite (.cmp .ult .W64 (.load 1 0 8) (.lit 231))
      (.bin .add .W64 (.reg .X27) (.lit 61360)) (.lit 8)).eval
        (fenv m0 st.data [(qA m0, 8)])) = pA m0 + BitVec.ofNat 64 61360 := by
    rw [ite_ult_pos hlt (by decide), ev_add]
    rw [show st.data.regs.getXReg .X27 = m0.regs.X6 from hl.base.x27]
  have vn : ((Sym.ite (.cmp .ult .W64 (.load 1 0 8) (.lit 231)) (.load 1 0 8) (.lit 0)).eval
      (fenv m0 st.data [(qA m0, 8)])).toNat = qs.size := by
    rw [ite_ult_pos hlt (by decide)]
    show ((fenv m0 st.data [(qA m0, 8)]).load 1 0 8).toNat = _
    rw [l0]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    unfold queryCap at hqn
    omega
  have x3 : st10.data.regs.X3.toBitVec = pA m0 + BitVec.ofNat 64 61360 :=
    (reg_val hm10 (r := .X3) rfl).trans vq
  have x26 : st10.data.regs.X26.toBitVec = pA m0 + BitVec.ofNat 64 61360 :=
    (reg_val hm10 (r := .X26) rfl).trans vq
  have x4 : st10.data.regs.X4.toNat = qs.size := by
    rw [← UInt64.toNat_toBitVec]; show (st10.data.regs.getXReg .X4).toBitVec.toNat = _
    rw [reg_val hm10 (r := .X4) rfl]; exact vn
  have x25 : st10.data.regs.X25.toNat = qs.size := by
    rw [← UInt64.toNat_toBitVec]; show (st10.data.regs.getXReg .X25).toBitVec.toNat = _
    rw [reg_val hm10 (r := .X25) rfl]; exact vn
  have hqb : 61360 + 8 * qs.size ≤ whirBytes := by unfold whirBytes; unfold queryCap at hqn; omega
  have hqs10 : NativeRustcVm.WordsAt st10.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList := by
    rw [hd10, ← e8]; exact hq.2.2
  have hpos := WhirLevels.whirIn_sub c.pIn (o := 61360) (k := 8 * qs.size) hqb
  have hle : 2672 + queryOpeningsStack ≤ finalLevelStack := by decide
  have hso : ∀ m' : MachineData, QueryOpeningsPost a s3 qs st10.data m' →
      SameOutside st10.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st10.data queryOpeningsStack) queryOpeningsStack q ∨
          InRange (loc m0 2064) 32 q ∨ InRange (tA m0) tstateBytes q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.2.1 fun q h ↦ by
      rcases h with h | h | h
      · rw [x0] at h; exact .inr (.inl h)
      · rw [x1] at h; exact .inr (.inr h)
      · exact .inl h
  refine c.call hf10 (lo := 2064) (n := 32) hle (by decide) (hqo a s3 qs) hpc10 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hso m' hq) fun q h ↦ by
      rcases h with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr h)), hq.2.2.2⟩) fun m2 hf2 hq hcs2 ↦ ?_
  · have hpin := c.whirIn' hf10 hle hpos
    refine ⟨c.stackOk' hf10 hle, c.rcAt' hf10 hle, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show TStateAt st10.data.dmem st10.data.regs.X1.toBitVec a s3
      rw [x1, hd10]; exact hts
    · show TStateOk st10.data st10.data.regs.X1.toBitVec a queryOpeningsStack
      rw [x1]; exact c.tstateOk' hf10 hle
    · exact x4.symm
    · show NativeRustcVm.WordsAt st10.data.dmem st10.data.regs.X3.toBitVec qs.toList
      rw [x3]; exact hqs10
    · show NoWrap st10.data.regs.X3.toBitVec (8 * st10.data.regs.X4.toNat)
      rw [x3, x4]; exact hpos.1.2
    · show Apart st10.data.regs.X3.toBitVec (8 * st10.data.regs.X4.toNat)
        (stackBelow st10.data queryOpeningsStack) queryOpeningsStack
      rw [x3, x4]; exact hpin.2
    · show Apart st10.data.regs.X3.toBitVec (8 * st10.data.regs.X4.toNat) a.words (8 * a.len)
      rw [x3, x4]; exact WhirLevels.apart_sub c.pout.1.2.2.2.1 c.pnw hqb
    · show OutOk st10.data st10.data.regs.X1.toBitVec a st10.data.regs.X0.toBitVec 32
        queryOpeningsStack
      rw [x0, x1]; exact c.localOk' hf10 hle (by decide)
    · show Apart st10.data.regs.X0.toBitVec 32 st10.data.regs.X3.toBitVec
        (8 * st10.data.regs.X4.toNat)
      rw [x0, x3, x4]; exact NativeRustcVm.Apart.symm (c.apart_loc hpos (by decide))
  -- `b11`: the openings' verdict.
  have hs2 := hso m2 hq
  obtain ⟨hrows, hnext, -, -⟩ := hq
  rw [x0, x2] at hrows
  rw [x1, x2] at hnext
  have hl2 : Live level m0 m2 folded :=
    hl10.saved hf2 (live_cs hcs2) (c.same_call hf10 hle (lo := 2064) (n := 32)
      (NativeRustcVm.SameOutside.mono hs2 fun q h ↦ by
        rcases h with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inr h))) (by decide) (by omega) (by decide)) hfo
  have hqs2 : NativeRustcVm.WordsAt m2.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList :=
    NativeRustcVm.Layout.BytesAt.of_same hqs10 (c.w_same hf10 hle (by decide) hs2 hqb)
      (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList])
  refine c.fblock hp b11_in_code (by simp [b11]) run_b11 rfl rfl rfl hf2
    fun st11 hm11 hpc11 hf11 hd11 hk11 ↦ ?_
  simp only [PcOk] at hpc11
  cases hr : (queryOpenings m0.regs.X1.toNat qs).run s3 with
  | none =>
    rw [hr] at hrows
    have h0 : (fenv m0 m2 []).load 0 2064 8 = (0 : UInt64).toBitVec :=
      load_of_wordAt (hrows : NativeRustcVm.WordAt _ _ 0)
    rw [cbz_load h0] at hpc11
    simp only [beq_self_eq_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b2Offset) NativeRustcVmArm.Vm.FinalLevel.label_2_at] at hpc11
    exact exit2 hp c hpc11 hf11 (by rw [hrun, C3]; exact run_bind_none hr)
  | some p =>
  obtain ⟨rws, s4⟩ := p
  rw [hr] at hrows
  have hrw : RowsAt m2.dmem (loc m0 2064) (off (a.word (phaseBase a.l s3.phase)) 24) rws := hrows
  obtain ⟨hlt, -, -⟩ := qo_some hr
  have hne : (UInt64.ofBitVec (off (a.word (phaseBase a.l s3.phase)) 24) == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    exact hrw.1 (congrArg UInt64.toBitVec h)
  obtain ⟨-, -, ww, -, hhdr, -⟩ := hrw
  rw [cbz_load (load_of_wordAt (wordsAt_cons.mp hhdr).1), hne] at hpc11
  simp only [Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmArm.Vm.FinalLevel.b11Offset + b11.length = k + NativeRustcVmArm.Vm.FinalLevel.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b11_next]]
    at hpc11
  -- The openings' area.
  have hpb : phaseBase a.l s3.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts.decoded.phases_le))
      hts.decoded.len
  have hpw : phaseWords = 3 + openingsWords := rfl
  have hop := WhirLevels.whirIn_sub c.decIn (o := 8 * phaseBase a.l s3.phase + 24)
    (k := 8 * openingsWords) (by omega)
  rw [← show off (a.word (phaseBase a.l s3.phase)) 24 =
    a.words + BitVec.ofNat 64 (8 * phaseBase a.l s3.phase + 24) from off_off _ _ _] at hop
  exact check hp c hrow hpc11
    (hl2.saved hf11 (fun r hr ↦ hk11 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd11]) hfo)
    ((congrArg UInt64.toBitVec ((hk11 .X26 rfl).trans (hcs2 .X26 rfl))).trans x26)
    ((congrArg UInt64.toNat ((hk11 .X25 rfl).trans (hcs2 .X25 rfl))).trans x25)
    ((congrArg UInt64.toBitVec ((hk11 .X29 rfl).trans ((hcs2 .X29 rfl).trans
      (reg_of hm10 (r := .X29) (v := .reg .X29) rfl rfl)))).trans hx29)
    hqn (by rw [hd11]; exact hqs2) (by rw [hd11]; exact hrows) hop
    (by rw [hd11]; exact hnext rws s4 hr) (by rw [hrun, C3]; exact run_bind_some hr)
    fun st' h1 h2 h3 h4 ↦ cont st' s4 h1 h2 h3 h4

end

end NativeRustcVmArm.Whir.FinalLevel
