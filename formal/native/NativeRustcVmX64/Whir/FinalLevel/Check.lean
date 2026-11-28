module

public import NativeRustcVmX64.Whir.FinalLevel.Open
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names

/-!
# `final_level`: the rows' check (x86-64)

From `b12` (`Live`, the rows at `144`): the rows' header copied to `112`, the rounds' count, the
folded scalars' address and count pushed, `each_row(index, queries, &rows, μ, rounds, folded)`
(`b12`), its `bool` tested (`b13`, `false` to `NativeRustcVmX64.Vm.FinalLevel.label_6` with AL `0`): `check`, to `b14`.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel
open NativeRustcVm.Sumcheck (RowsAt openingsWords)
open NativeVm (phaseBase phaseWords)

public section

theorem roundsOf_succ (d : Mem 64) (p : BitVec 64) (n : Nat) :
    roundsOf d p (n + 1) =
      ⟨NativeRustcVm.ewOf d p, NativeRustcVm.ewOf d (p + BitVec.ofNat 64 16)⟩ ::
      roundsOf d (p + BitVec.ofNat 64 32) n := by
  unfold roundsOf
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ ↦ ?_⟩
  simp only [Function.comp, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 4 <;> omega

/-- The rounds read back. -/
theorem roundsOf_of_roundsAt {d : Mem 64} {p : BitVec 64} {rs : List FoldRoundW}
    (h : RoundsAt d p rs) : roundsOf d p rs.length = rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih =>
    unfold RoundsAt at h
    rw [show roundEWs (r :: rs) = r.alpha :: r.beta :: roundEWs rs from rfl, ewsAt_cons,
      ewsAt_cons, off_off] at h
    obtain ⟨ha, hb, hr⟩ := h
    rw [List.length_cons, roundsOf_succ, NativeRustcVm.ewOf_of_ewAt ha,
      show p + BitVec.ofNat 64 16 = off p 16 from rfl, NativeRustcVm.ewOf_of_ewAt hb,
      show p + BitVec.ofNat 64 32 = off p (16 + 16) from rfl, ih hr]

section
open LeanVM.Protocol.Compile

/-- **The rows moved**: their header copied to `r'`, their openings kept. -/
theorem rowsAt_move {d d' : Mem 64} {r r' p : BitVec 64} {rows : Array (Array UInt64)}
    (h : RowsAt d r p rows)
    (hh : ∀ w0 w1 w2 w3 : UInt64, NativeRustcVm.WordsAt d r [w0, w1, w2, w3] →
      NativeRustcVm.WordsAt d' r' [w0, w1, w2, w3])
    (ho : NativeRustcVm.Layout.Same d d' p (8 * openingsWords)) : RowsAt d' r' p rows := by
  obtain ⟨hp0, hsz, w, hw, hhdr, hrow⟩ := h
  refine ⟨hp0, hsz, w, hw, hh _ _ _ _ hhdr,
    fun j hj ↦ ⟨(hrow j hj).1, bytesAt_congr (hrow j hj).2 fun i hi ↦ ?_⟩⟩
  rw [off, NativeRustcVm.addr_add_add]
  refine ho _ ?_
  rw [NativeRustcVm.length_wordsBytes, Array.length_toList, (hrow j hj).1] at hi
  have e1 : wireMaxQueries = 256 := rfl
  have e2 : wireMaxLeafWords = 64 := rfl
  have e3 : NativeVm.openingWords = 193 := rfl
  have e4 : openingsWords = 49408 := rfl
  simp only [e1, e2, e3, e4] at hsz hw hj hi ⊢
  omega

end

theorem loc_add (m0 : MachineData) (o i : Nat) :
    loc m0 o + BitVec.ofNat 64 i = loc m0 (o + i) :=
  off_add _ _ _

/-- A stack argument from a frame's word. -/
theorem stackArg_loc {m0 d : MachineData} {o : Nat} (hsp : rspOf d = loc m0 o) (i : Nat)
    {u : UInt64} (hw : NativeRustcVm.WordAt d.dmem (loc m0 (o + (8 + 8 * i))) u) :
    stackArg d i = u.toBitVec := by
  show (NativeRustcVm.wordOf d.dmem (rspOf d + BitVec.ofNat 64 (8 + 8 * i))).toBitVec = _
  rw [hsp, off_add, NativeRustcVm.wordOf_of_wordAt hw]

theorem vRc_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 61152 8 = BitVec.ofNat 64 n)
    (hn : n < 7) : vRc.eval env = BitVec.ofNat 64 n := by
  simp only [vRc, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem vRp_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 61152 8 = BitVec.ofNat 64 n)
    (hn : n < 7) {p : BitVec 64} (hl : env.load 0 2680 8 = p) :
    vRp.eval env = p + BitVec.ofNat 64 61160 := by
  simp only [vRp, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h, hl,
    ult_ofNat hn (by decide), ite_true]
  exact BitVec.add_comm _ _

theorem cCl_eval [Labels] (env : Env) :
    cCl.eval env = decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [cCl, SBool.eval, Sym.eval]
  rw [testAl_eq, al_trunc]

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

/-- The stack arguments of a callee entered at RSP offset `o`. -/
theorem Ctx.argsOk (c : Ctx a s level ba b w rounds m0) {o n : Nat} (hn : o + 8 + 8 * n ≤ 2688)
    {d : MachineData} (hf : Fr m0 o d) : ArgsOk d n := by
  have g := c.geo
  have hsp : rspOf d = loc m0 o := hf.frame.sp
  have hreg := c.region_ok hf.frame.kept
  have hlo := c.loc_toNat (j := o) (by omega)
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · have := hreg.1 (o + 8 + i) (by omega)
    rwa [show fa m0 + BitVec.ofNat 64 (o + 8 + i) = rspOf d + 8#64 + BitVec.ofNat 64 i by
      rw [hsp]
      apply BitVec.eq_of_toNat_eq
      have hfa := c.fa_toNat
      simp only [loc, off, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := g.hA; have := g.hN
      omega] at this
  · rw [hsp, hlo]; have := g.hA; have := g.hN; omega

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The rows' check**: `b12`, `each_row`, `b13`, to `b14`. -/
theorem check (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hrow : ∀ rows op, Spec (Labels.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.entryLabel) (EachRowFinalPre rows op)
      (EachRowFinalPost rows))
    {st : MachineState} {folded : Array EW} {qs : Array UInt64} {rws : Array (Array UInt64)}
    {op : BitVec 64} {s4 : TState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b12Offset))
    (hl : Live level m0 st.data folded)
    (hbp : reg st.data .rbp = pA m0 + BitVec.ofNat 64 61360)
    (hbx : reg st.data .rbx = BitVec.ofNat 64 qs.size)
    (hq : NativeRustcVm.BufWordsAt st.data.dmem (qA m0) queryCap qs.toList)
    (hrows : RowsAt st.data.dmem (loc m0 144) op rws)
    (hop : WhirIn m0 op (8 * openingsWords) finalLevelStack)
    (hopBounds : a.words.toNat ≤ op.toNat ∧
      op.toNat + 8 * openingsWords ≤ a.words.toNat + 8 * a.len)
    (hts : TStateAt st.data.dmem (tA m0) a s4)
    (hrun : runF level b w rounds m0 s = (C4 (reg m0 .rsi).toNat (mu m0) (reg m0 .r8).toNat b w
      rounds folded qs rws).run s4)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b14Offset) →
      Live level m0 st'.data folded → TStateAt st'.data.dmem (tA m0) a s4 →
      runF level b w rounds m0 s = (C5 (mu m0) (reg m0 .r8).toNat b w folded).run s4 →
      Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hmu6 : mu m0 ≤ 6 := by
    by_contra hc
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ mu m0 by omega)
    have : (2 : Nat) ^ 7 = 128 := rfl
    omega
  have hqn : qs.size ≤ 230 := by have := hq.1; rwa [Array.length_toList] at this
  have hwa := c.whir_at hl.fr.same
  have hbr := hwa.2
  have hrl : rounds.size ≤ 6 := by have := hbr.1; rwa [Array.length_toList] at this
  -- `b12`: the rows copied, the arguments pushed, `each_row`.
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b13Offset)).toBitVec
  let env := argEnv m0 st.data 2672 8 [(pA m0, 63200)] (fun _ ↦ 0) ret
  have hwf : env.WF :=
    c.wf1 hl.fr.frame.kept (show NativeRustcVm.Mapped st.data.dmem (pA m0) 63200 from
      Mapped.keeps c.pout.1.1 hl.fr.frame.kept) g.pW
      (g.pS.imp_left fun h ↦ Nat.le_trans h (Nat.sub_le_sub_left (by decide) _))
  have h2680 : env.load 0 2680 8 = pA m0 :=
    load_ofMachine (r := 0) (o := 2680) rfl (c.arg_keep hl.fr.same)
  have hm : Match env rowsS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hl.fr.frame, trivial⟩ trivial trivial
      ⟨h2680.trans (eval_ptr rfl).symm, trivial⟩
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, h8, h16, h24, h112, h120, h128, h136, hrdi1, hrsi1, hrdx1, hrcx1, hr81,
    hr91, hkr1⟩ := ok_b12
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b12 rowsS).reg r = some v →
      reg st1.data r = v.eval env := fun h ↦ hm1.regs _ _ h
  obtain ⟨hf1, hs1⟩ := c.blk hl.fr hwf hm1 hmid1 (hi := 144) (by omega) (hW1.le (by decide))
  have hsp1 : rspOf st1.data = loc m0 0 := hf1.frame.sp
  have hl61152 : env.load 1 61152 8 = BitVec.ofNat 64 rounds.size := by
    have := load_ofMachine (r := 1) (o := 61152) (rs := [(stackBelow m0 2672, 2672 + 8 + 8),
      (pA m0, 63200)]) (vs := fun _ ↦ 0) (ret := ret) (m := st.data) rfl hbr.2.1
    rw [this, Array.length_toList]
    rfl
  -- the registers
  have hdi1 : reg st1.data .rdi = reg m0 .rsi := (e1 hrdi1).trans hl.r15
  have hsi1 : reg st1.data .rsi = pA m0 + BitVec.ofNat 64 61360 := (e1 hrsi1).trans hbp
  have hdx1 : reg st1.data .rdx = BitVec.ofNat 64 qs.size := (e1 hrdx1).trans hbx
  have hdxn : (reg st1.data .rdx).toNat = qs.size := by rw [hdx1, BitVec.toNat_ofNat]; omega
  have hcx1 : reg st1.data .rcx = loc m0 112 := (e1 hrcx1).trans (eval_ptr0A 112)
  have h81 : reg st1.data .r8 = reg m0 .rcx :=
    (e1 hr81).trans (load_ofMachine (r := 0) (o := 40) rfl hl.w40)
  have h91 : reg st1.data .r9 = pA m0 + BitVec.ofNat 64 61160 :=
    (e1 hr91).trans (vRp_eval env hl61152 (by omega) h2680)
  have hk1 : ∀ r ∈ six, reg st1.data r = reg st.data r := fun r hr ↦ e1 (hkr1 r hr)
  -- the stack arguments
  have w8 : NativeRustcVm.WordAt st1.data.dmem (loc m0 8) rounds.size.toUInt64 :=
    wordAt_written hm1 (r := 0) (o := 8) rfl (by omega) h8 (vRc_eval env hl61152 (by omega))
  have w16 : NativeRustcVm.WordAt st1.data.dmem (loc m0 16) (.ofBitVec (loc m0 1600)) :=
    wordAt_written hm1 (r := 0) (o := 16) rfl (by omega) h16 (eval_ptr0A 1600)
  have w24 : NativeRustcVm.WordAt st1.data.dmem (loc m0 24) (.ofBitVec (reg st.data .r13)) :=
    wordAt_written hm1 (r := 0) (o := 24) rfl (by omega) h24 rfl
  have a0 : stackArg st1.data 0 = BitVec.ofNat 64 rounds.size := stackArg_loc hsp1 0 w8
  have a1 : stackArg st1.data 1 = loc m0 1600 := stackArg_loc hsp1 1 w16
  have a2 : stackArg st1.data 2 = reg st.data .r13 := stackArg_loc hsp1 2 w24
  have a0n : (stackArg st1.data 0).toNat = rounds.size := by rw [a0, BitVec.toNat_ofNat]; omega
  have a2n : (stackArg st1.data 2).toNat = 2 ^ mu m0 + level.fold := by rw [a2]; exact hl.r13
  -- the rows moved to `112`
  have hcopy : ∀ w0 w1 w2 w3 : UInt64,
      NativeRustcVm.WordsAt st.data.dmem (loc m0 144) [w0, w1, w2, w3] →
      NativeRustcVm.WordsAt st1.data.dmem (loc m0 112) [w0, w1, w2, w3] := by
    intro w0 w1 w2 w3 hw
    obtain ⟨h0, hw⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    obtain ⟨h1, hw⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    obtain ⟨h2, hw⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    obtain ⟨h3, -⟩ := NativeRustcVm.wordsAt_cons_iff.mp hw
    simp only [loc_add] at h1 h2 h3
    have v0 := wordAt_written hm1 (r := 0) (o := 112) rfl (by omega) h112
      (load_ofMachine (r := 0) (o := 144) rfl h0)
    have v1 := wordAt_written hm1 (r := 0) (o := 120) rfl (by omega) h120
      (load_ofMachine (r := 0) (o := 152) rfl h1)
    have v2 := wordAt_written hm1 (r := 0) (o := 128) rfl (by omega) h128
      (load_ofMachine (r := 0) (o := 160) rfl h2)
    have v3 := wordAt_written hm1 (r := 0) (o := 136) rfl (by omega) h136
      (load_ofMachine (r := 0) (o := 168) rfl h3)
    refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨v0, ?_⟩
    rw [loc_add]
    refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨v1, ?_⟩
    rw [loc_add]
    refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨v2, ?_⟩
    rw [loc_add]
    exact NativeRustcVm.wordsAt_cons_iff.mpr ⟨v3, NativeRustcVm.wordsAt_nil _ _⟩
  have hsop : NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem op (8 * openingsWords) := by
    have h2 : op.toNat + 8 * openingsWords ≤ (stackBelow m0 finalLevelStack).toNat ∨
        (stackBelow m0 finalLevelStack).toNat + (finalLevelStack + 8) ≤ op.toNat := hop.2
    rw [c.stk_toNat, stack_eq] at h2
    exact c.area_frame (hi := 144) (by omega) hs1 hop.1.2 (by omega)
  have hrw1 : RowsAt st1.data.dmem (loc m0 112) op rws := rowsAt_move hrows hcopy hsop
  -- what the block kept
  have hfold1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 1600) folded.toList :=
    bytes_blk hwf hm1 (writesIn_of_mid hmid1) hW1
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hl.size]; omega)
      (fun p hp ↦ by
        rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hl.size]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> left <;> decide) hl.fold
  have hq1 := c.q_frame (hi := 144) (by omega) hs1 hq
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hqw1 : NativeRustcVm.WordsAt st1.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList := by
    rw [← e8]; exact hq1.2.2
  have hwa1 := c.whir_at hf1.same
  have hts1 := c.ts_frame (hi := 144) (by omega) (hm1.kept hwf) hs1 hts
  -- the call
  have hat := c.at_call (o := 0) (by omega) hf1
  have hle : 2672 - 0 + eachRowFinalStack ≤ finalLevelStack := by decide
  have hrb : 61160 + roundBytes * rounds.size ≤ whirBytes := by
    unfold whirBytes roundBytes; omega
  have hpre : EachRowFinalPre rws op st1.data := by
    refine ⟨⟨(c.sctx (by decide)).stackOk hat hle, c.argsOk (by omega) hf1, ?_, ?_,
      c.whirIn hat hle hop, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · show RowsAt st1.data.dmem (reg st1.data .rcx) op rws
      rw [hcx1]; exact hrw1
    · show WhirIn st1.data (reg st1.data .rcx) 32 eachRowFinalStack
      rw [hcx1]; exact c.inLoc (o := 0) (by omega) hf1 hle (by omega) (by omega)
    · show WhirIn st1.data (reg st1.data .rsi) (8 * (reg st1.data .rdx).toNat) eachRowFinalStack
      rw [hsi1, hdxn]
      exact c.whirIn hat hle (WL.whirIn_sub c.pIn (by unfold whirBytes; omega))
    · show (reg st1.data .r8).toNat ≤ stackCap
      rw [h81]; show mu m0 ≤ 30; omega
    · rw [a0n]; exact hrl
    · show WhirIn st1.data (reg st1.data .r9) (roundBytes * (stackArg st1.data 0).toNat)
        eachRowFinalStack
      rw [h91, a0n]
      exact c.whirIn hat hle (WL.whirIn_sub c.pIn hrb)
    · rw [a2n]; exact hfo
    · rw [a1]
      exact c.sliceLoc (o := 0) (by omega) hf1 hle (by omega) (by rw [a2n]; omega)
    · have hargs : rspOf st1.data + 8#64 = loc m0 8 := by
        rw [hsp1, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, loc_add]
      rw [hcx1, hsi1, hdxn, h91, a0n, a1, a2n, hargs]
      apply c.got_call hf1 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl | rfl | rfl
      · exact c.got_loc (by omega) (by omega)
      · exact ⟨(a.words, 8 * a.len), by simp, hopBounds⟩
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ (pA m0 + BitVec.ofNat 64 61360).toNat
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
        · change (pA m0 + BitVec.ofNat 64 61360).toNat + 8 * qs.size ≤ (pA m0).toNat + 63200
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ (pA m0 + BitVec.ofNat 64 61160).toNat
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
        · change (pA m0 + BitVec.ofNat 64 61160).toNat + 32 * rounds.size ≤ (pA m0).toNat + 63200
          rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
          omega
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_loc (by omega) (by omega)
  refine call_then hpc1 (hrow rws op) hpre fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hok, hch, hsv⟩ := hq2
  have hch' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InAny [] q ∨
        NativeRustcVm.InRange (stackBelow st1.data eachRowFinalStack) eachRowFinalStack q) :=
    NativeRustcVm.SameOutside.mono hch fun q hq ↦ hq
  obtain ⟨hf2, hkeep2⟩ := c.call (o := 0) (by omega) hf1 hle hsv hrsp2
    (R := NativeRustcVm.InAny []) (lo := 2624) (n := 0) (by omega) (by omega)
    (fun q hq ↦ absurd hq (NativeRustcVm.inAny_nil q)) hch'
  have hts2 := c.ts_call (o := 0) (by omega) hf1 hle hsv
    (fun q hq ↦ absurd hq (NativeRustcVm.inAny_nil q)) hch' hts1
  have hcs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := hsv.1
  -- the verdict's value
  have eR : (eachRowArgs st1.data).2 = rounds := by
    show (roundsOf st1.data.dmem (reg st1.data .r9) (stackArg st1.data 0).toNat).toArray = _
    rw [h91, a0n, show pA m0 + BitVec.ofNat 64 61160 = off (off (pA m0) roundsOff) 8 by
        rw [off_off]; rfl, ← Array.length_toList, roundsOf_of_roundsAt hwa1.2.2.2,
      Array.toArray_toList]
  have eQ : (eachRowArgs st1.data).1 = qs := by
    show (NativeRustcVm.wordsOf st1.data.dmem (reg st1.data .rsi)
      (reg st1.data .rdx).toNat).toArray = _
    rw [hsi1, hdxn, ← Array.length_toList, NativeRustcVm.wordsOf_of_wordsAt hqw1,
      Array.toArray_toList]
  have eF : slice st1.data (stackArg st1.data 1) (stackArg st1.data 2) = folded := by
    show (NativeRustcVm.ewsOf st1.data.dmem (stackArg st1.data 1)
      (stackArg st1.data 2).toNat).toArray = _
    rw [a1, a2n, ← hl.size, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hfold1,
      Array.toArray_toList]
  rw [eR, eQ, eF, hdi1, h81] at hok
  -- `b13`: the verdict.
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b13Offset) := hpc2
  have hwf2 := c.wf0 hf2.frame.kept (ret := 0)
  have hm2 : Match (argEnv m0 st2.data 2672 8 []) s8S st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf2.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf2 nofun hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hrax3, hkr3⟩ := ok_b13
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hf3 : Fr m0 40 st3.data :=
    ⟨Frame.of_blockA hf2.frame hwf2 hm3 hmid3 slots_le, by rw [Sm, hd3]; exact hf2.same⟩
  have hk3 : ∀ r ∈ six, reg st3.data r = reg st.data r := fun r hr ↦
    ((hm3.regs r _ (hkr3 r hr)).trans (hcs2 r (six_cs hr))).trans (hk1 r hr)
  simp only [PcOk, cCl_eval] at hpc3
  have hal : ((argEnv m0 st2.data 2672 8 [] (fun _ ↦ 0) 0).regs .rax).toNat % 256 =
      (okWord (finalOk (reg m0 .rsi).toNat (reg m0 .rcx).toNat rounds folded qs rws)).toNat := hok
  rw [hal] at hpc3
  have hl3 : Live level m0 st3.data folded :=
    hl.step hwf hm1 (writesIn_of_mid hmid1) hW1 (by decide)
      (fun j h1 h2 h3 ↦ by rw [hd3]; exact hkeep2 j h1 h2 h3) (by omega) (by omega) hf3
      (fun r hr ↦ hk3 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp [six])) hfo
  have hts3 : TStateAt st3.data.dmem (tA m0) a s4 := by rw [hd3]; exact hts2
  cases hb : finalOk (reg m0 .rsi).toNat (reg m0 .rcx).toNat rounds folded qs rws with
  | false =>
    rw [hb] at hpc3
    simp only [okWord_toNat, Bool.false_eq_true, ite_false, decide_true, ite_true] at hpc3
    refine none37 hp c hf3 (hpc3.trans (l6 hp)) ?_ ?_
    · rw [show reg st3.data .rax = _ from hm3.regs .rax _ hrax3]; rfl
    · rw [hrun, C4, run_require_bind]
      show (if finalOk (reg m0 .rsi).toNat (mu m0) rounds folded qs rws then _ else none) = none
      rw [show mu m0 = (reg m0 .rcx).toNat from rfl, hb]; rfl
  | true =>
    rw [hb] at hpc3
    simp only [okWord_toNat, ite_true] at hpc3
    refine cont st3 (hpc3.trans (by rfl)) hl3 hts3 ?_
    rw [hrun, C4, run_require_bind]
    show (if finalOk (reg m0 .rsi).toNat (mu m0) rounds folded qs rws then _ else none) = _
    rw [show mu m0 = (reg m0 .rcx).toNat from rfl, hb]
    rfl

end

end NativeRustcVmX64.Whir.Levels.FL
