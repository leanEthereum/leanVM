module

public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Whir.FinalLevel.Keep
public import NativeRustcVmArm.Whir.FinalLevel.Queries

/-!
# `final_level`: the rows' check

`check`: from `b12`, the rows (at the frame's byte `2064`) copied to `1064`, `each_row` with
`final_level`'s closure (`finalOk`), its verdict (`b13`, a rejection to `.LFinalLevel_2`), to
`b14`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr wordAt_write)
open NativeRustcVm.Sumcheck (RowsAt openingsWords)

public section

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The rows' check.** -/
theorem check (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hrow : ∀ rows op, Spec (Labels.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.entryLabel) (EachRowFinalPre rows op)
      (EachRowFinalPost rows))
    {st : MachineState} {folded : Array EW} {qs : Array UInt64} {rws : Array (Array UInt64)}
    {op : BitVec 64} {s4 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b12Offset)) (hl : Live level m0 st.data folded)
    (hx26 : st.data.regs.X26.toBitVec = pA m0 + BitVec.ofNat 64 61360)
    (hx25 : st.data.regs.X25.toNat = qs.size)
    (hx29 : st.data.regs.X29.toBitVec = pA m0 + BitVec.ofNat 64 57344)
    (hqn : qs.size ≤ queryCap)
    (hq : NativeRustcVm.WordsAt st.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList)
    (hrows : RowsAt st.data.dmem (loc m0 2064) op rws)
    (hop : WhirIn m0 op (8 * openingsWords) finalLevelStack)
    (hts : TStateAt st.data.dmem (tA m0) a s4)
    (hrun : runF s0 level b w rounds m0 =
      (C4 m0.regs.X1.toNat (mu m0) m0.regs.X4.toNat b w rounds folded qs rws).run s4)
    (cont : ∀ (st' : MachineState), st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b14Offset) →
      Live level m0 st'.data folded → TStateAt st'.data.dmem (tA m0) a s4 →
      runF s0 level b w rounds m0 = (C5 (mu m0) m0.regs.X4.toNat b w folded).run s4 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hfo := c.two_mu_le
  have hf := hl.fr
  have hmu := mu_le hfo
  have x27 : (st.data.regs.getXReg .X27).toBitVec = pA m0 := congrArg UInt64.toBitVec hl.base.x27
  have hwf := c.wf1 hf c.pIn
  have hm : Match (fenv m0 st.data [(pA m0, whirBytes)]) rS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ c.aligned, rfl, fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) ⟨known_ptr (i := 1) rfl x27, trivial⟩ trivial trivial
      ⟨by show st.data.regs.X29.toBitVec = _; rw [hx29]; rfl, trivial⟩
  -- `b12`: the rows copied, `each_row(index, queries, &rows, μ, rounds, folded)`.
  refine exec_at (inf hp b12_in_code (by simp [b12])) run_b12 hwf hpc hm
    fun st12 hm12 hpc12 ↦ ?_
  have hf12 : FFr m0 st12.data := c.fr_block hf hm hm12 hwf rfl (by decide +kernel)
  have hS : ∀ w ∈ (after b12 rS).mem, w.r = 0 ∧ w.off + w.n ≤ 2672 := by
    rw [after_eq run_b12]; decide +kernel
  have hs12 := c.blk_stk hm12 hwf (by rw [← after_eq run_b12]; exact hS)
  have hk12 : ∀ r ∈ liveRegs, st12.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [liveRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact reg_of hm12 rfl rfl
      | exact UInt64.toBitVec_inj.mp ((reg_val hm12 (r := .X27) (v := .ptr 1 0) rfl).trans
          ((eval_ptr rfl).trans x27.symm))
  have hl12 : Live level m0 st12.data folded :=
    hl.saved hf12 hk12 (Ctx.same_block hm12 hwf (by decide +kernel) (by decide)) hfo
  have hts12 : TStateAt st12.data.dmem (tA m0) a s4 :=
    c.ts_block hm12 hwf (by rw [← after_eq run_b12]; exact hS) hts
  -- The arguments.
  have hro := c.rounds_at hf
  have l61152 : (fenv m0 st.data [(pA m0, whirBytes)]).load 1 61152 8 =
      rounds.toList.length.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 61152) rfl hro.2.1
  have hrl : rounds.size ≤ 6 := by have := hro.1; rwa [Array.length_toList] at this
  have hlt7 : ((Sym.load 1 61152 8).eval (fenv m0 st.data [(pA m0, whirBytes)])).toNat < 7 := by
    show ((fenv m0 st.data [(pA m0, whirBytes)]).load 1 61152 8).toNat < 7
    rw [l61152]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat', Array.length_toList]
    omega
  have x0 : st12.data.regs.X0 = m0.regs.X1 :=
    (reg_of hm12 (r := .X0) (v := .reg .X24) rfl rfl).trans hl.x24
  have x1 : st12.data.regs.X1.toBitVec = pA m0 + BitVec.ofNat 64 61360 :=
    (reg_val hm12 (r := .X1) (v := .reg .X26) rfl).trans hx26
  have x2 : st12.data.regs.X2.toNat = qs.size := by
    rw [← UInt64.toNat_toBitVec]
    show (st12.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_val hm12 (r := .X2) (v := .reg .X25) rfl]
    exact hx25
  have x3 : st12.data.regs.X3.toBitVec = loc m0 1064 :=
    reg_val hm12 (r := .X3) (v := .ptr 0 1064) rfl
  have x4 : st12.data.regs.X4 = m0.regs.X3 :=
    (reg_of hm12 (r := .X4) (v := .reg .X20) rfl rfl).trans hl.base.x20
  have e61160 : pA m0 + BitVec.ofNat 64 61160 = off (off (pA m0) roundsOff) 8 := by
    show _ = pA m0 + BitVec.ofNat 64 61152 + BitVec.ofNat 64 8
    rw [BitVec.add_assoc]
    rfl
  have x5 : st12.data.regs.X5.toBitVec = pA m0 + BitVec.ofNat 64 61160 := by
    show (st12.data.regs.getXReg .X5).toBitVec = _
    rw [reg_val hm12 (r := .X5) rfl, ite_ult hlt7 (by decide)]
    rfl
  have x6 : st12.data.regs.X6.toNat = rounds.size := by
    rw [← UInt64.toNat_toBitVec]
    show (st12.data.regs.getXReg .X6).toBitVec.toNat = _
    rw [reg_val hm12 (r := .X6) rfl, ite_ult hlt7 (by decide)]
    show ((fenv m0 st.data [(pA m0, whirBytes)]).load 1 61152 8).toNat = _
    rw [l61152]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat', Array.length_toList]
    omega
  have x7 : st12.data.regs.X7 = UInt64.ofBitVec (loc m0 40) :=
    reg_of hm12 (r := .X7) (v := .ptr 0 40) rfl rfl
  have x7' : st12.data.regs.X7.toBitVec = loc m0 40 :=
    reg_val hm12 (r := .X7) (v := .ptr 0 40) rfl
  have hw0 := wordAt_write hm12 (r := 0) (o := 0) (b := base m0 2672) (sz := 2672) rfl
    (by decide) (v := .reg .X23) (by decide +kernel)
  have hsa : whirStackArg st12.data 0 = st.data.regs.X23 := by
    unfold whirStackArg
    rw [hf12.sp]
    exact NativeRustcVm.wordOf_of_wordAt hw0
  have hsaN : (whirStackArg st12.data 0).toNat = 2 ^ mu m0 + level.fold := by
    rw [hsa]; exact hl.x23
  have hqb : 61360 + 8 * qs.size ≤ whirBytes := by
    unfold whirBytes; unfold queryCap at hqn; omega
  have hpos := WhirLevels.whirIn_sub c.pIn (o := 61360) (k := 8 * qs.size) hqb
  have hq12 : NativeRustcVm.WordsAt st12.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList :=
    NativeRustcVm.Layout.BytesAt.of_same hq (c.same_in hs12 hpos)
      (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList])
  have hrb : 61160 + roundBytes * rounds.size ≤ whirBytes := by
    unfold whirBytes roundBytes; omega
  have hle : 2672 + eachRowFinalStack ≤ finalLevelStack := by decide
  -- The rows' header, copied.
  have hcopy : ∀ w0 w1 w2 w3 : UInt64,
      NativeRustcVm.WordsAt st.data.dmem (loc m0 2064) [w0, w1, w2, w3] →
      NativeRustcVm.WordsAt st12.data.dmem (loc m0 1064) [w0, w1, w2, w3] := by
    intro w0 w1 w2 w3 h
    obtain ⟨h0, h⟩ := wordsAt_cons.mp h
    obtain ⟨h1, h⟩ := wordsAt_cons.mp h
    obtain ⟨h2, h⟩ := wordsAt_cons.mp h
    obtain ⟨h3, -⟩ := wordsAt_cons.mp h
    rw [loc_off] at h1
    rw [loc_off, loc_off] at h2
    rw [loc_off, loc_off, loc_off] at h3
    have v0 := wordAt_write hm12 (r := 0) (o := 1064) (b := base m0 2672) (sz := 2672) rfl
      (by decide) (v := .load 0 2064 8) (by decide +kernel)
    have v1 := wordAt_write hm12 (r := 0) (o := 1072) (b := base m0 2672) (sz := 2672) rfl
      (by decide) (v := .load 0 2072 8) (by decide +kernel)
    have v2 := wordAt_write hm12 (r := 0) (o := 1080) (b := base m0 2672) (sz := 2672) rfl
      (by decide) (v := .load 0 2080 8) (by decide +kernel)
    have v3 := wordAt_write hm12 (r := 0) (o := 1088) (b := base m0 2672) (sz := 2672) rfl
      (by decide) (v := .load 0 2088 8) (by decide +kernel)
    rw [show (Sym.load 0 2064 8).eval (fenv m0 st.data [(pA m0, whirBytes)]) = w0.toBitVec from
      load_ofMachine (o := 2064) rfl h0] at v0
    rw [show (Sym.load 0 2072 8).eval (fenv m0 st.data [(pA m0, whirBytes)]) = w1.toBitVec from
      load_ofMachine (o := 2072) rfl h1] at v1
    rw [show (Sym.load 0 2080 8).eval (fenv m0 st.data [(pA m0, whirBytes)]) = w2.toBitVec from
      load_ofMachine (o := 2080) rfl h2] at v2
    rw [show (Sym.load 0 2088 8).eval (fenv m0 st.data [(pA m0, whirBytes)]) = w3.toBitVec from
      load_ofMachine (o := 2088) rfl h3] at v3
    refine wordsAt_cons.mpr ⟨v0, ?_⟩
    rw [loc_off]
    refine wordsAt_cons.mpr ⟨v1, ?_⟩
    rw [loc_off]
    refine wordsAt_cons.mpr ⟨v2, ?_⟩
    rw [loc_off]
    exact wordsAt_cons.mpr ⟨v3, wordsAt_nil _ _⟩
  have hfr : ∀ m' : MachineData, EachRowFinalPost rws st12.data m' →
      SameOutside st12.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st12.data eachRowFinalStack) eachRowFinalStack q ∨
          InRange (loc m0 0) 0 q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      rcases h with h | h
      · exact absurd h (NativeRustcVm.inAny_nil _)
      · exact .inl h
  refine c.call hf12 (lo := 0) (n := 0) hle (by decide) (hrow rws op) hpc12 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hfr m' hq) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), hq.2.2⟩) fun m3 hf3 hq hcs3 ↦ ?_
  · refine ⟨⟨c.stackOk' hf12 hle, ?_, ?_, c.whirIn' hf12 hle hop, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show RowsAt st12.data.dmem st12.data.regs.X3.toBitVec op rws
      rw [x3]
      exact rowsAt_move hrows hcopy (c.same_in hs12 hop)
    · show WhirIn st12.data st12.data.regs.X3.toBitVec 32 eachRowFinalStack
      rw [x3]; exact c.locIn hf12 hle (by decide)
    · show WhirIn st12.data st12.data.regs.X1.toBitVec (8 * st12.data.regs.X2.toNat)
        eachRowFinalStack
      rw [x1, x2]; exact c.whirIn' hf12 hle hpos
    · show st12.data.regs.X4.toNat ≤ 30
      rw [x4]; show mu m0 ≤ 30; omega
    · show st12.data.regs.X6.toNat ≤ roundCap
      rw [x6]; exact hrl
    · show WhirIn st12.data st12.data.regs.X5.toBitVec (roundBytes * st12.data.regs.X6.toNat)
        eachRowFinalStack
      rw [x5, x6]
      exact c.whirIn' hf12 hle (WhirLevels.whirIn_sub c.pIn (o := 61160) hrb)
    · show Readable st12.data st12.data.regs.SP.toBitVec 8
      rw [hf12.sp]
      have := (c.locIn hf12 hle (o := 0) (n := 8) (by decide)).1
      rwa [show loc m0 0 = base m0 2672 from BitVec.add_zero _] at this
    · rw [hsaN]; exact c.fold
    · show SliceOk st12.data st12.data.regs.X7 (whirStackArg st12.data 0) eachRowFinalStack
      rw [x7]
      exact c.locSlice hf12 hle (by rw [hsaN]; omega)
  -- `b13`: the rows' verdict.
  have hs3 := hfr m3 hq
  obtain ⟨h0, -, hsv⟩ := hq
  have hl3 : Live level m0 m3 folded :=
    hl12.saved hf3 (live_cs hcs3) (c.same_call hf12 hle (lo := 0) (n := 0)
      (NativeRustcVm.SameOutside.mono hs3 fun q h ↦ by
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)) (by decide) (by omega) (by decide)) hfo
  have hts3 : TStateAt m3.dmem (tA m0) a s4 :=
    c.ts_stk hsv.2.2 (c.call_stk hf12 hle (by decide) hs3) hts12
  have eR : (eachRowArgs st12.data).2 = rounds := by
    show (roundsOf st12.data.dmem st12.data.regs.X5.toBitVec st12.data.regs.X6.toNat).toArray = _
    rw [x5, x6, e61160, ← Array.length_toList,
      roundsOf_of_roundsAt (c.rounds_at hf12).2.2, Array.toArray_toList]
  have eQ : (eachRowArgs st12.data).1 = qs := by
    show (NativeRustcVm.wordsOf st12.data.dmem st12.data.regs.X1.toBitVec
      st12.data.regs.X2.toNat).toArray = _
    rw [x1, x2, ← Array.length_toList, NativeRustcVm.wordsOf_of_wordsAt hq12,
      Array.toArray_toList]
  have eF : slice st12.data st12.data.regs.X7 (whirStackArg st12.data 0) = folded := by
    show (NativeRustcVm.ewsOf st12.data.dmem st12.data.regs.X7.toBitVec
      (whirStackArg st12.data 0).toNat).toArray = _
    rw [x7', hsaN, ← hl12.size, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hl12.fold,
      Array.toArray_toList]
  rw [eR, eQ, eF, x0, x4] at h0
  refine c.fblock hp b13_in_code (by simp [b13]) run_b13 rfl rfl rfl hf3
    fun st13 hm13 hpc13 hf13 hd13 hk13 ↦ ?_
  simp only [PcOk] at hpc13
  rw [tbz_ok (show (fenv m0 m3 []).regs .X0 = _ from congrArg UInt64.toBitVec h0)] at hpc13
  cases hb : finalOk m0.regs.X1.toNat (mu m0) rounds folded qs rws with
  | false =>
    simp only [hb, Bool.not_false, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b2Offset) NativeRustcVmArm.Vm.FinalLevel.label_2_at] at hpc13
    exact exit2 hp c hpc13 hf13 (by rw [hrun, C4, run_require_bind, hb]; rfl)
  | true =>
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      show k + NativeRustcVmArm.Vm.FinalLevel.b13Offset + b13.length = k + NativeRustcVmArm.Vm.FinalLevel.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b13_next]] at hpc13
    refine cont st13 hpc13
      (hl3.saved hf13 (fun r hr ↦ hk13 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd13])
        hfo) (by rw [hd13]; exact hts3) ?_
    rw [hrun, C4, run_require_bind, hb]
    rfl

end

end NativeRustcVmArm.Whir.FinalLevel
