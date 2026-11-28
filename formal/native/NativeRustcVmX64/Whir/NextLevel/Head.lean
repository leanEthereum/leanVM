module

public import NativeRustcVmX64.Whir.NextLevel.Test
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `next_level`: the prologue, the commitment, the high part, the first grind (x86-64)

`b0` saves the callee-saved registers, keeps the index (RBX), the level (RBP), the query depth
`μ + level.logInvRate` (R13), the `TState` (R14), `μ` (the frame's word `80`) and calls
`read_commitment(t, μ - next.fold + next.logInvRate, 2 << next.fold)`; `b1` tests it (`head1`, to
`H2`). `b2` zeroes the high part's buffer at `176`, reads the level's fold (R15, at most `6`),
`b3` calls `read_scalars(t, sp + 104, fold)`, `b4` tests it (`head2`, to `H5`). `b5` calls
`grind(t, 15)`, `b6` tests it (`head3`, to `H7`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

@[expose] public section

/-- The query depth `μ + level.logInvRate`. -/
abbrev depth (m0 : MachineData) (level : Whir.Level) : BitVec 64 :=
  reg m0 .r9 + level.logInvRate.toUInt64.toBitVec

/-- The registers of the body's first part. -/
structure R0 (level : Whir.Level) (m0 d : MachineData) : Prop where
  rbx : reg d .rbx = reg m0 .rsi
  rbp : reg d .rbp = lA m0
  r13 : reg d .r13 = depth m0 level
  r14 : reg d .r14 = tA m0

/-- From `read_scalars` on. -/
abbrev rest2 (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW) (m0 : MachineData)
    (s1 : TState) : Option (WhirStateW × TState) :=
  ((readScalars level.fold).run s1).bind fun p2 ↦ ((grind Whir.oodGrindingBits).run p2.2).bind
    fun p3 ↦ tail3 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds p2.1 p3.2

/-- At `b2`: the commitment read. -/
structure H2 [Labels] (a : DecArea) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (s1 : TState) (d : MachineData) : Prop where
  K : K level w rounds m0 72 d
  regs : R0 level m0 d
  ts : TStateAt d.dmem (tA m0) a s1

/-- At `b5`: the high part `xs` at `176`. -/
structure H5 [Labels] (a : DecArea) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (xs : Array EW) (s2 : TState)
    (d : MachineData) : Prop where
  K : K level w rounds m0 72 d
  regs : R0 level m0 d
  r15 : (reg d .r15).toNat = level.fold
  high : NativeRustcVm.EWsAt d.dmem (loc m0 176) xs.toList
  size : xs.size = level.fold
  ts : TStateAt d.dmem (tA m0) a s2

/-- At `b7`: the first grind done. -/
structure H7 [Labels] (a : DecArea) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (xs : Array EW) (s3 : TState)
    (d : MachineData) : Prop where
  K : K level w rounds m0 72 d
  regs : R0 level m0 d
  r15 : (reg d .r15).toNat = level.fold
  high : NativeRustcVm.EWsAt d.dmem (loc m0 176) xs.toList
  size : xs.size = level.fold
  ts : TStateAt d.dmem (tA m0) a s3

end

public section

theorem R0.saved {level : Whir.Level} {m0 d d' : MachineData} (h : R0 level m0 d)
    (hs : ∀ r, calleeSaved r = true → reg d' r = reg d r) : R0 level m0 d' :=
  ⟨(hs .rbx rfl).trans h.rbx, (hs .rbp rfl).trans h.rbp, (hs .r13 rfl).trans h.r13,
    (hs .r14 rfl).trans h.r14⟩

theorem R0.congr {level : Whir.Level} {m0 d d' : MachineData} (h : R0 level m0 d)
    (hs : ∀ r, reg d' r = reg d r) : R0 level m0 d' := h.saved fun r _ ↦ hs r

theorem level_words {d : Mem 64} {p : BitVec 64} {l : Whir.Level} (h : LevelAt d p l) :
    NativeRustcVm.WordAt d (off p 0) l.fold.toUInt64 ∧
      NativeRustcVm.WordAt d (off p 8) l.logInvRate.toUInt64 ∧
      NativeRustcVm.WordAt d (off p 16) l.queries.toUInt64 := by
  obtain ⟨-, -, -, hw⟩ := h
  rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_cons_iff,
    NativeRustcVm.wordsAt_singleton_iff] at hw
  refine ⟨by rw [off_zero]; exact hw.1, hw.2.1, ?_⟩
  have := hw.2.2
  rwa [NativeRustcVm.addr_add_add] at this

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  show (BitVec.ofNat 64 n).toNat = n
  rw [BitVec.toNat_ofNat]; omega

theorem vHeight_toNat [Labels] (env : Env) (h9 : (env.regs .r9).toNat ≤ 30)
    (h8 : (env.regs .r8).toNat < 64) :
    (vHeight.eval env).toNat =
      (env.regs .r9).toNat - (env.regs .rcx).toNat + (env.regs .r8).toNat := by
  simp only [vHeight, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  split
  · rename_i hc
    simp only [Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at hc
    rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hc)]
    omega
  · rename_i hc
    simp only [Bool.not_eq_true, Bool.not_eq_false', BitVec.ult, decide_eq_true_eq] at hc
    rw [BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega

theorem width_toNat [Labels] (env : Env) (h : (env.regs .rcx).toNat < 63) :
    ((Sym.bin .shl .W64 (.lit 2) (.reg .rcx)).eval env).toNat =
      2 * 2 ^ (env.regs .rcx).toNat := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have hs : shiftCount .W64 (env.regs .rcx) = (env.regs .rcx).toNat := by
    unfold shiftCount shiftMask low
    rw [BitVec.toNat_setWidth, show (Width.W8).bits = 8 from rfl,
      show (0x3f : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hs, Nat.shiftLeft_eq]
  have : 2 * 2 ^ (env.regs .rcx).toNat < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) (show (env.regs .rcx).toNat + 1 < 64 by omega)
    rw [Nat.pow_succ] at this
    omega
  rw [show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  omega

theorem not_hi {x c : BitVec 64} (h : x.toNat ≤ c.toNat) : (!x.ult c && !(x == c)) = false := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · have : x.ult c = true := by simp [BitVec.ult, hlt]
    simp [this]
  · simp [BitVec.eq_of_toNat_eq heq]

theorem cs_six {r : Reg64} (h : calleeSaved r = true) : r ∈ six := by
  cases r <;> simp_all [six, calleeSaved]

theorem six_cs {r : Reg64} (h : r ∈ six) : calleeSaved r = true := by
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ood_bits : Whir.oodGrindingBits = 15 := rfl
theorem query_bits : Whir.queryGrindingBits = 17 := rfl

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The prologue and `read_commitment`**, to `b2` with `H2`. -/
theorem head1 (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (hrc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s)) :
    Eventually (step1 Host.exe) (fun st ↦ Goal a s level w rounds m0 st ∨
      (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b2Offset) ∧ ∃ s1, runN level w rounds m0 s = rest2 level w rounds m0 s1 ∧
        H2 a level w rounds m0 s1 st.data)) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b0Offset)⟩ := by
  have g := c.geo
  let env0 := frameEnv m0 m0 8176 [(lA m0, 24)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b1Offset)).toBitVec
  have hwf0 : env0.WF := c.wfL (fun _ h ↦ h)
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw, h80, hrbx, hrbp, hr13, hr14, hr15, hrdi, hrsi, hrdx⟩ := ok_b0
  have hfr : Frame m0 8176 slots 64 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (fa m0) 8176) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by omega) hw
  have hf1 : Fr m0 64 st1.data := ⟨hfr, NativeRustcVm.SameOutside.mono hs1 fun q hq ↦ by
    obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact Or.inl (c.loc_stk (j := j) hj)⟩
  have hK1 : K level w rounds m0 64 st1.data :=
    ⟨hf1, wordAt_written hm1 (r := 0) (o := 80) rfl (by omega) h80 rfl,
      LevelAt.of_same c.lv (c.l_frame le_rfl hs1), WhirAt.of_same c.wa (c.p_frame le_rfl hs1)⟩
  have e : ∀ {r : Reg64} {v : Sym}, (after b0 entryS).reg r = some v →
      reg st1.data r = v.eval env0 := fun h ↦ hm1.regs _ _ h
  have hlw := level_words c.lv
  have hrate : (env0.load 1 8 8) = level.logInvRate.toUInt64.toBitVec :=
    load_ofMachine (o := 8) (r := 1) rfl hlw.2.1
  have h13 : reg st1.data .r13 = depth m0 level := by
    rw [e hr13]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [hrate]
    rfl
  have hR0 : R0 level m0 st1.data := ⟨e hrbx, (e hrbp).trans (eval_ptr rfl), h13, e hr14⟩
  have h15 : reg st1.data .r15 = 0 := e hr15
  have ht1 : reg st1.data .rdi = tA m0 := e hrdi
  have hsi : (reg st1.data .rsi).toNat =
      (reg m0 .r9).toNat - (reg m0 .rcx).toNat + (reg m0 .r8).toNat := by
    rw [e hrsi]; exact vHeight_toNat env0 c.mu c.nr
  have hdx : (reg st1.data .rdx).toNat = 2 * 2 ^ (reg m0 .rcx).toNat := by
    rw [e hrdx]; exact width_toNat env0 c.nf
  have hat := c.at_call (o := 64) (by omega) hf1
  have hle : 8176 - 64 + readCommitmentStack ≤ nextLevelStack := by decide
  have hts1 : TStateAt st1.data.dmem (tA m0) a s := c.ts_frame le_rfl (hm1.kept hwf0) hs1 c.ts
  have hwt := c.whirT hat hf1.same hle
  have hpre : ReadCommitmentPre a s st1.data := by
    refine ⟨hwt.1, hwt.2.1, ?_, ?_, c.roots, ?_⟩
    · show TStateAt st1.data.dmem (reg st1.data .rdi) a s
      rw [ht1]; exact hts1
    · show TStateOk st1.data (reg st1.data .rdi) a readCommitmentStack
      rw [ht1]; exact hwt.2.2.2.1
    · rw [ht1]
      apply c.got_call hf1 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_rc
  refine call_then hpc1 (hrc a s) hpre fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hok, hnext, hch, hsv⟩ := hq
  rw [hsi, hdx] at hok hnext
  rw [ht1] at hnext hch
  obtain ⟨hK2, -⟩ := c.K_call hK1 hle hsv hrsp2 (R := NativeRustcVm.InRange (tA m0) tstateBytes)
    (lo := 8128) (n := 0) (by omega) (by omega) (fun q hq ↦ Or.inl hq) hch
  have hcs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := hsv.1
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b0Offset + b0.length = k + NativeRustcVmX64.Vm.NextLevel.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b0_next]] at hpc2
  have hrun : runN level w rounds m0 s =
      ((readCommitment ((reg m0 .r9).toNat - (reg m0 .rcx).toNat + (reg m0 .r8).toNat)
        (2 * 2 ^ (reg m0 .rcx).toNat)).run s).bind fun p1 ↦ rest2 level w rounds m0 p1.2 :=
    run_eq (reg m0 .rsi).toNat level ⟨(reg m0 .rcx).toNat, (reg m0 .r8).toNat, 0⟩
      (reg m0 .r9).toNat w rounds s
  refine Eventually.bind (test_spec hp c b1_in_code rfl exit_b1 ok_b1 hK2 hpc2 hok)
    fun st3 ⟨hr3, hd3, hpc3⟩ ↦ ?_
  have hK3 := hK2.congr hr3 hd3
  rcases hres : (readCommitment ((reg m0 .r9).toNat - (reg m0 .rcx).toNat + (reg m0 .r8).toNat)
      (2 * 2 ^ (reg m0 .rcx).toNat)).run s with _ | ⟨⟨⟩, s1⟩
  · rw [hres] at hpc3
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hpc3
    exact Eventually.mono (none14 hp c hK3.fr (hpc3.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_14_at))
      (by rw [hr3, hcs2 .r15 rfl, h15]) (by rw [hrun, hres]; rfl)) fun _ h ↦ Or.inl h
  · rw [hres] at hpc3
    simp only [Option.isSome_some, ite_true] at hpc3
    refine .done _ (Or.inr ⟨hpc3, s1, by rw [hrun, hres]; rfl, hK3,
      (hR0.saved hcs2).congr hr3, ?_⟩)
    rw [hd3]
    exact hnext () s1 hres

/-- **The high part**: `b2`, `read_scalars`, `b4`, to `b5` with `H5`. -/
theorem head2 (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {s1 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b2Offset))
    (hH : H2 a level w rounds m0 s1 st.data)
    (hrun : runN level w rounds m0 s = rest2 level w rounds m0 s1) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s level w rounds m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b5Offset) ∧ ∃ xs s2, runN level w rounds m0 s =
        (((grind Whir.oodGrindingBits).run s2).bind fun p3 ↦
          tail3 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds xs p3.2) ∧
        H5 a level w rounds m0 xs s2 st'.data)) st := by
  have g := c.geo
  have hK := hH.K
  let env := frameEnv m0 st.data 8176 [(lA m0, 24)] (fun _ ↦ 0) 0
  have hwf : env.WF := c.wfL hK.fr.frame.kept
  have hm : Match env levelS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hK.fr.frame.rsp_eval, known_ptr rfl hH.regs.rbp, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hW, hr15, hrbp, hkr⟩ := ok_b2
  obtain ⟨hf1, hs1⟩ := c.blkF hK.fr hwf hm1 hmid (hi := 272) (by omega)
    (fun w hw ↦ ⟨(hW w hw).1, by obtain ⟨-, p, hp, -, h2⟩ := hW w hw; simp at hp; subst hp; exact h2⟩)
  have hlw := level_words hK.lv
  have hfold : env.load 1 0 8 = level.fold.toUInt64.toBitVec :=
    load_ofMachine (o := 0) (r := 1) rfl hlw.1
  have hf6 : level.fold ≤ 6 := c.fold
  have hft : level.fold.toUInt64.toBitVec.toNat = level.fold := toNat_toUInt64 (by omega)
  simp only [PcOk, cFold, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hfold] at hpc1
  rw [not_hi (by rw [hft]; simp; omega)] at hpc1
  simp only [Bool.false_eq_true, ite_false] at hpc1
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b2Offset + b2.length = k + NativeRustcVmX64.Vm.NextLevel.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b2_next]] at hpc1
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b2 levelS).reg r = some v →
      reg st1.data r = v.eval env := fun h ↦ hm1.regs _ _ h
  have hK1 : K level w rounds m0 72 st1.data :=
    c.K_frame hK hf1 (by omega) hs1 (bytes_blkF hwf hm1 (writesIn_of_mid hmid) hW
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) hK.w80)
  have hR1 : R0 level m0 st1.data :=
    ⟨(e1 (hkr .rbx (by simp))).trans hH.regs.rbx, (e1 hrbp).trans (eval_ptr rfl),
      (e1 (hkr .r13 (by simp))).trans hH.regs.r13, (e1 (hkr .r14 (by simp))).trans hH.regs.r14⟩
  have h15 : (reg st1.data .r15).toNat = level.fold := by rw [e1 hr15, Sym.eval, hfold]; exact hft
  have hts1 := c.ts_frame (by omega) (hm1.kept hwf) hs1 hH.ts
  -- `b3`: `read_scalars`
  let env2 := argEnv m0 st1.data 8176 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b4Offset)).toBitVec
  have hwf2 : env2.WF := c.wf0 hK1.fr.frame.kept
  have hm2 : Match env2 retS st1.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK1.fr.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf2 (fun _ _ ↦ rfl) hpc1 hm2
    fun st2 hm3 hpc2 ↦ ?_
  obtain ⟨hmid2, hW2, hrsi, hrdi, hrdx, hkr2⟩ := ok_b3
  obtain ⟨hf2, hs2⟩ := c.blk hK1.fr hwf2 hm3 hmid2 (hi := 72) (by omega)
    (fun w hw ↦ ⟨(hW2 w hw).1, by obtain ⟨-, p, hp, -, h2⟩ := hW2 w hw; simp at hp; subst hp; exact h2⟩)
  have hK2 : K level w rounds m0 64 st2.data :=
    c.K_frame hK1 hf2 (by omega) hs2 (Ctx.bytes_blk hwf2 hm3 (writesIn_of_mid hmid2) hW2
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) hK1.w80)
  have e2 : ∀ {r : Reg64} {v : Sym}, (after b3 retS).reg r = some v →
      reg st2.data r = v.eval env2 := fun h ↦ hm3.regs _ _ h
  have hk2 : ∀ r ∈ six, reg st2.data r = reg st1.data r := fun r hr ↦ e2 (hkr2 r hr)
  have ht2 : reg st2.data .rdi = tA m0 := (e2 hrdi).trans hR1.r14
  have hsi2 : reg st2.data .rsi = loc m0 176 := (e2 hrsi).trans (eval_ptr0A 176)
  have hdx2 : (reg st2.data .rdx).toNat = level.fold := by
    rw [e2 hrdx]; exact h15
  have hts2 := c.ts_frame (by omega) (hm3.kept hwf2) hs2 hts1
  have hat := c.at_call (o := 64) (by omega) hf2
  have hle : 8176 - 64 + readScalarsStack ≤ nextLevelStack := by decide
  have hwt := c.whirT hat hf2.same hle
  have hpre : ReadScalarsPre a s1 st2.data := by
    refine ⟨hwt.1, hwt.2.1, ?_, ?_, ?_, ?_⟩
    · show TStateAt st2.data.dmem (reg st2.data .rdi) a s1
      rw [ht2]; exact hts2
    · show TStateOk st2.data (reg st2.data .rdi) a readScalarsStack
      rw [ht2]; exact hwt.2.2.2.1
    · show OutOk st2.data (reg st2.data .rdi) a (reg st2.data .rsi)
        (16 * (reg st2.data .rdx).toNat) readScalarsStack
      rw [ht2, hsi2, hdx2]
      exact c.outLoc (by omega) hf2 hle (by omega) (by omega)
    · rw [ht2, hsi2, hdx2]
      apply c.got_call hf2 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_loc (by omega) (by have := c.fold; unfold roundCap at this; omega)
      · exact c.got_rc
  refine call_then hpc2 (hrs a s1) hpre fun st3 hpc3 hrsp3 hq ↦ ?_
  obtain ⟨hok, hxs, hnext, hch, hsv⟩ := hq
  rw [hdx2] at hok hxs hnext hch
  rw [ht2] at hnext
  rw [ht2, hsi2] at hch
  rw [hsi2] at hxs
  obtain ⟨hK3, -⟩ := c.K_call hK2 hle hsv hrsp3
    (R := fun q ↦ NativeRustcVm.InRange (loc m0 176) (16 * level.fold) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) (lo := 176) (n := 16 * level.fold)
    (by omega) (by omega) (fun q hq ↦ hq.elim (fun h ↦ Or.inr (Or.inl h)) Or.inl)
    (NativeRustcVm.SameOutside.mono hch fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq)
  have hcs3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st2.data r := hsv.1
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b3Offset + b3.length = k + NativeRustcVmX64.Vm.NextLevel.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b3_next]] at hpc3
  refine Eventually.bind (test_spec hp c b4_in_code rfl exit_b4 ok_b4 hK3 hpc3 hok)
    fun st4 ⟨hr4, hd4, hpc4⟩ ↦ ?_
  have hK4 := hK3.congr hr4 hd4
  rcases hres : (readScalars level.fold).run s1 with _ | ⟨xs, s2⟩
  · rw [hres] at hpc4
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hpc4
    exact Eventually.mono (none13 hp c hK4.fr (hpc4.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_13_at))
      (by rw [hrun, rest2, hres]; rfl)) fun _ h ↦ Or.inl h
  · rw [hres] at hpc4
    simp only [Option.isSome_some, ite_true] at hpc4
    have hr15' : (reg st4.data .r15).toNat = level.fold := by
      rw [hr4, hcs3 .r15 rfl, hk2 .r15 (by simp [six])]; exact h15
    refine .done _ (Or.inr ⟨hpc4, xs, s2, by rw [hrun, rest2, hres]; rfl, hK4,
      ((hR1.saved fun r hr ↦ hk2 r (cs_six hr)).saved hcs3).congr hr4, hr15',
      by rw [hd4]; exact hxs xs s2 hres,
      NativeRustcVm.Sumcheck.readScalars_size hres, by rw [hd4]; exact hnext xs s2 hres⟩)

/-- **The first grind**: `grind(t, 15)`, `b6`, to `b7` with `H7`. -/
theorem head3 (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {xs : Array EW} {s2 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b5Offset))
    (hH : H5 a level w rounds m0 xs s2 st.data)
    (hrun : runN level w rounds m0 s = (((grind Whir.oodGrindingBits).run s2).bind fun p3 ↦
      tail3 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds xs p3.2)) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s level w rounds m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b7Offset) ∧ ∃ s3, runN level w rounds m0 s =
        tail3 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds xs s3 ∧
        H7 a level w rounds m0 xs s3 st'.data)) st := by
  have g := c.geo
  have hK := hH.K
  let env := argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b6Offset)).toBitVec
  have hwf : env.WF := c.wf0 hK.fr.frame.kept
  have hm : Match env retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK.fr.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hW, hrdi, hrsi, hkr⟩ := ok_b5
  obtain ⟨hf1, hs1⟩ := c.blk hK.fr hwf hm1 hmid (hi := 72) (by omega)
    (fun w hw ↦ ⟨(hW w hw).1, by obtain ⟨-, p, hp, -, h2⟩ := hW w hw; simp at hp; subst hp; exact h2⟩)
  have hK1 : K level w rounds m0 64 st1.data :=
    c.K_frame hK hf1 (by omega) hs1 (Ctx.bytes_blk hwf hm1 (writesIn_of_mid hmid) hW
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) hK.w80)
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b5 retS).reg r = some v →
      reg st1.data r = v.eval env := fun h ↦ hm1.regs _ _ h
  have hk1 : ∀ r ∈ six, reg st1.data r = reg st.data r := fun r hr ↦ e1 (hkr r hr)
  have ht1 : reg st1.data .rdi = tA m0 := (e1 hrdi).trans hH.regs.r14
  have hbits : grindBits st1.data = Whir.oodGrindingBits := by
    unfold grindBits; rw [e1 hrsi]; rfl
  have hts1 := c.ts_frame (by omega) (hm1.kept hwf) hs1 hH.ts
  have hhigh1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 176) xs.toList :=
    Ctx.bytes_blk hwf hm1 (writesIn_of_mid hmid) hW (by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hH.size]; have := c.fold
      unfold roundCap at this; omega) (by simp) hH.high
  have hat := c.at_call (o := 64) (by omega) hf1
  have hle : 8176 - 64 + grindStack ≤ nextLevelStack := by decide
  have hwt := c.whirT hat hf1.same hle
  have hpre : GrindPre a s2 st1.data := by
    refine ⟨hwt.1, hwt.2.1, ?_, ?_, ?_, ?_⟩
    · show TStateAt st1.data.dmem (reg st1.data .rdi) a s2
      rw [ht1]; exact hts1
    · show TStateOk st1.data (reg st1.data .rdi) a grindStack
      rw [ht1]; exact hwt.2.2.2.1
    · rw [hbits]; decide
    · rw [ht1]
      apply c.got_call hf1 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_rc
  refine call_then hpc1 (hgr a s2) hpre fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hok, hnext, hch, hsv⟩ := hq
  rw [hbits] at hok hnext
  rw [ht1] at hnext hch
  obtain ⟨hK2, hkeep2⟩ := c.K_call hK1 hle hsv hrsp2
    (R := NativeRustcVm.InRange (tA m0) tstateBytes) (lo := 8128) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inl hq) hch
  have hcs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := hsv.1
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b5Offset + b5.length = k + NativeRustcVmX64.Vm.NextLevel.b6Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b5_next]] at hpc2
  refine Eventually.bind (test_spec hp c b6_in_code rfl (b_eq.1 ▸ exit_b4) (b_eq.1 ▸ ok_b4) hK2
    hpc2 hok) fun st3 ⟨hr3, hd3, hpc3⟩ ↦ ?_
  have hK3 := hK2.congr hr3 hd3
  rcases hres : (grind Whir.oodGrindingBits).run s2 with _ | ⟨⟨⟩, s3⟩
  · rw [hres] at hpc3
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hpc3
    exact Eventually.mono (none13 hp c hK3.fr (hpc3.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_13_at))
      (by rw [hrun, hres]; rfl)) fun _ h ↦ Or.inl h
  · rw [hres] at hpc3
    simp only [Option.isSome_some, ite_true] at hpc3
    have hcs : ∀ r ∈ six, reg st3.data r = reg st.data r := fun r hr ↦ by
      rw [hr3, hcs2 r (six_cs hr), hk1 r hr]
    refine .done _ (Or.inr ⟨hpc3, s3, by rw [hrun, hres]; rfl, hK3,
      ⟨(hcs .rbx (by simp [six])).trans hH.regs.rbx, (hcs .rbp (by simp [six])).trans hH.regs.rbp,
        (hcs .r13 (by simp [six])).trans hH.regs.r13, (hcs .r14 (by simp [six])).trans hH.regs.r14⟩,
      by rw [hcs .r15 (by simp [six])]; exact hH.r15, ?_, hH.size, by rw [hd3]; exact hnext () s3 hres⟩)
    rw [hd3]
    exact bytes_call hkeep2 (j := 176) (by omega) (by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hH.size]; have := c.fold
      unfold roundCap at this; omega) (Or.inl (by
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hH.size]; have := c.fold
      unfold roundCap at this; omega)) hhigh1

end

end NativeRustcVmX64.Whir.Levels.NL
