module

public import NativeRustcVmX64.Whir.NextLevel.Rows
public import NativeRustcVmX64.Code.Vm.GlueLevel.Names

/-!
# `next_level`: the level glued, the return (x86-64)

From `b24` (`H24`): `glue_level(w, λ, μ, ood, v, queries, weights, batched)` (`b24`, the last four
pairs as eight pushed argument words), RSP back and AL into R15 (`b25`), the epilogue (`b27`):
`glue`, the postcondition.
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

public section

theorem vOp_eval [Labels] (env : Env) {n : Nat} (h : env.load 0 272 8 = BitVec.ofNat 64 n)
    (hn : n < 31) : vOp.eval env = (Sym.ptr 0 280).eval env := by
  simp only [vOp, SBool.eval, CmpOp.apply, low_W64, ult_ofNat hn (by decide), ite_true,
    Sym.eval, h]

theorem vOn_eval [Labels] (env : Env) {n : Nat} (h : env.load 0 272 8 = BitVec.ofNat 64 n)
    (hn : n < 31) : vOn.eval env = BitVec.ofNat 64 n := by
  simp only [vOn, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

/-- Bytes of the state apart from a frame range. -/
theorem Ctx.apart_pl (c : Ctx a s level w rounds m0) {n o k : Nat} (hn : n ≤ 63200)
    (ho : o < 8192) (hk : o + k ≤ 8192) : NativeRustcVm.Apart (pA m0) n (loc m0 o) k := by
  have g := c.geo
  unfold NativeRustcVm.Apart
  rw [c.loc_toNat ho]
  have := g.pS; have := g.hN
  omega

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The level glued**, to the return. -/
theorem glue (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (hgl : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.GlueLevel.entryLabel) (GlueLevelPre s) (GlueLevelPost s))
    {xs ood : Array EW} {v lam bt : EW} {qs : Array UInt64} {s9 : TState} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b24Offset))
    (hH : H24 a level w rounds m0 xs ood v lam qs bt s9 st.data)
    (hrun : runN level w rounds m0 s = some (glueLevel w lam (reg m0 .r9).toNat ood v qs
      (powers lam qs.size) bt, s9)) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  have g := c.geo
  have hK := hH.K
  have hmu := c.mu
  have hqn : qs.size ≤ 230 := hH.qsz
  have hgl2 := c.glued
  have hfv := hH.ff.fv
  -- `b24`: the arguments, `glue_level`
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b25Offset)).toBitVec
  let env := argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) ret
  have hwf : env.WF := c.wf0 hK.fr.frame.kept
  have hm : Match env retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK.fr.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b24_in_code (by simp [b24]) hp) exit_b24 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, h8, h16, h24, h32, h40, h48, h56, h64, hrdi1, hrsi1, hrdx1, hrcx1, hr81,
    hr91, -⟩ := ok_b24
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b24 retS).reg r = some v →
      reg st1.data r = v.eval env := fun h ↦ hm1.regs _ _ h
  obtain ⟨hf1, hs1⟩ := c.blk hK.fr hwf hm1 hmid1 (hi := 72) (by omega)
    (fun w hw ↦ ⟨(hW1 w hw).1, by
      obtain ⟨-, p, hp, -, h2⟩ := hW1 w hw; simp at hp; subst hp; exact h2⟩)
  have hsp1 : rspOf st1.data = loc m0 0 := hf1.frame.sp
  have hmu' : (reg m0 .r9).toNat < 31 := by unfold stackCap at hmu; omega
  have hmuB : BitVec.ofNat 64 (reg m0 .r9).toNat = reg m0 .r9 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (BitVec.isLt _)
  have l272 : env.load 0 272 8 = BitVec.ofNat 64 (reg m0 .r9).toNat :=
    (load_ofMachine (r := 0) (o := 272) rfl hfv.oodN).trans hmuB.symm
  have hb0 : NativeRustcVm.WordAt st.data.dmem (loc m0 104) bt.c0 := (ewAt_iff.mp hH.bt).1
  have hb1 : NativeRustcVm.WordAt st.data.dmem (loc m0 112) bt.c1 := by
    have := (ewAt_iff.mp hH.bt).2
    rwa [off_off] at this
  -- the registers
  have hdi1 : reg st1.data .rdi = pA m0 :=
    (e1 hrdi1).trans (load_ofMachine (r := 0) (o := 8184) rfl (c.arg_keep hK.fr.same))
  have hsi1 : reg st1.data .rsi = lam.c0.toBitVec :=
    (e1 hrsi1).trans (load_ofMachine (r := 0) (o := 96) rfl hH.ff.l0)
  have hdx1 : reg st1.data .rdx = lam.c1.toBitVec :=
    (e1 hrdx1).trans (load_ofMachine (r := 0) (o := 88) rfl hH.ff.l1)
  have hcx1 : reg st1.data .rcx = reg m0 .r9 :=
    (e1 hrcx1).trans (load_ofMachine (r := 0) (o := 80) rfl hK.w80)
  have h81 : reg st1.data .r8 = loc m0 280 :=
    (e1 hr81).trans ((vOp_eval env l272 hmu').trans (eval_ptr0A 280))
  have h91 : reg st1.data .r9 = reg m0 .r9 := (e1 hr91).trans ((vOn_eval env l272 hmu').trans hmuB)
  -- the stack arguments
  have a0 : stackArg st1.data 0 = v.c0.toBitVec := stackArg_loc hsp1 0
    (wordAt_written hm1 (r := 0) (o := 8) rfl (by omega) h8
      (load_ofMachine (r := 0) (o := 136) rfl hfv.v0))
  have a1 : stackArg st1.data 1 = v.c1.toBitVec := stackArg_loc hsp1 1
    (wordAt_written hm1 (r := 0) (o := 16) rfl (by omega) h16
      (load_ofMachine (r := 0) (o := 128) rfl hfv.v1))
  have a2 : stackArg st1.data 2 = pA m0 + BitVec.ofNat 64 61360 := stackArg_loc hsp1 2
    (wordAt_written hm1 (r := 0) (o := 24) rfl (by omega) h24 (w := .ofBitVec _) hH.rbx)
  have a3 : stackArg st1.data 3 = BitVec.ofNat 64 qs.size := stackArg_loc hsp1 3
    (wordAt_written hm1 (r := 0) (o := 32) rfl (by omega) h32 (w := .ofBitVec _) hH.rbp)
  have a4 : stackArg st1.data 4 = loc m0 4448 := stackArg_loc hsp1 4
    (wordAt_written hm1 (r := 0) (o := 40) rfl (by omega) h40 (w := .ofBitVec _) hH.r13)
  have a5 : stackArg st1.data 5 = BitVec.ofNat 64 qs.size := stackArg_loc hsp1 5
    (wordAt_written hm1 (r := 0) (o := 48) rfl (by omega) h48 (w := .ofBitVec _) hH.r14)
  have a6 : stackArg st1.data 6 = bt.c0.toBitVec := stackArg_loc hsp1 6
    (wordAt_written hm1 (r := 0) (o := 56) rfl (by omega) h56
      (load_ofMachine (r := 0) (o := 104) rfl hb0))
  have a7 : stackArg st1.data 7 = bt.c1.toBitVec := stackArg_loc hsp1 7
    (wordAt_written hm1 (r := 0) (o := 64) rfl (by omega) h64
      (load_ofMachine (r := 0) (o := 112) rfl hb1))
  have hqsn : (BitVec.ofNat 64 qs.size).toNat = qs.size := by rw [BitVec.toNat_ofNat]; omega
  -- what the block kept
  have hts1 := c.ts_frame (hi := 72) (by omega) (hm1.kept hwf) hs1 hH.ts
  have hqb1 := c.qbuf_frame (hi := 72) (by omega) hs1 hH.qbuf
  have hK1 : K level w rounds m0 0 st1.data :=
    c.K_frame hK hf1 (by omega) hs1 (Ctx.bytes_blk hwf hm1 (writesIn_of_mid hmid1) hW1
      (by simp [NativeRustcVm.length_wordBytes]) (by simp) hK.w80)
  have hpwL : ((powers lam qs.size).toList.flatMap NativeRustcVm.ewBytes).length =
      16 * qs.size := by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']
  have hpw1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 4448) (powers lam qs.size).toList :=
    Ctx.bytes_blk hwf hm1 (writesIn_of_mid hmid1) hW1 (by rw [hpwL]; omega) (by simp) hH.pw
  have hood1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 280) ood.toList :=
    Ctx.bytes_blk hwf hm1 (writesIn_of_mid hmid1) hW1
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hH.osize]; omega) (by simp)
      hfv.oodp
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hqs1 : NativeRustcVm.WordsAt st1.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList := by
    rw [← e8]; exact hqb1.2.2
  -- `glue_level`'s precondition
  have hat1 := c.at_call (o := 0) (by omega) hf1
  have hle : 8176 - 0 + glueLevelStack ≤ nextLevelStack := by decide
  have hst := WL.whirIn_sub c.pIn (o := 0) (k := stateBytes) (by decide)
  rw [show pA m0 + BitVec.ofNat 64 0 = pA m0 from BitVec.add_zero _] at hst
  have hpos := WL.whirIn_sub c.pIn (o := 61360) (k := 8 * qs.size) (by unfold whirBytes; omega)
  have hpre : GlueLevelPre w st1.data := by
    refine ⟨(c.sctx (F := 8176 - 0) (by decide)).stackOk hat1 hle, ⟨fun i hi ↦ ?_, ?_⟩, ?_,
      hgl2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsp1, show loc m0 0 + 8#64 + BitVec.ofNat 64 i = loc m0 (8 + i) by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, loc_add, loc_add]]
      exact (c.region_ok hf1.frame.kept).1 _ (by omega)
    · rw [hsp1, c.loc_toNat (by omega)]; have := g.hA; omega
    · show WhirStateAt st1.data.dmem (reg st1.data .rdi) w
      rw [hdi1]; exact hK1.wa.1
    · show (reg st1.data .rcx).toNat ≤ stackCap
      rw [hcx1]; exact hmu
    · show (reg st1.data .r9).toNat ≤ stackCap
      rw [h91]; exact hmu
    · show (stackArg st1.data 3).toNat ≤ queryCap
      rw [a3, hqsn]; exact hqn
    · show (stackArg st1.data 5).toNat ≤ queryCap
      rw [a5, hqsn]; exact hqn
    · show WhirIn st1.data (reg st1.data .rdi) stateBytes glueLevelStack
      rw [hdi1]; exact c.whirIn hat1 hle hst
    · show SliceOk st1.data (reg st1.data .r8) (reg st1.data .r9) glueLevelStack
      rw [h81, h91]
      exact c.sliceLoc (o := 0) (by omega) hf1 hle (by omega) (by omega)
    · show WhirIn st1.data (stackArg st1.data 2) (8 * (stackArg st1.data 3).toNat) glueLevelStack
      rw [a2, a3, hqsn]; exact c.whirIn hat1 hle hpos
    · show WhirIn st1.data (stackArg st1.data 4) (16 * (stackArg st1.data 5).toNat) glueLevelStack
      rw [a4, a5, hqsn]; exact c.inLoc (o := 0) (by omega) hf1 hle (by omega) (by omega)
    · show NativeRustcVm.Apart (reg st1.data .rdi) stateBytes (rspOf st1.data + 8#64) 64
      rw [hdi1, hsp1, show loc m0 0 + 8#64 = loc m0 8 by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, loc_add]]
      exact c.apart_pl (by decide) (by omega) (by omega)
    · show NativeRustcVm.Apart (reg st1.data .rdi) stateBytes (reg st1.data .r8)
        (16 * (reg st1.data .r9).toNat)
      rw [hdi1, h81, h91]; exact c.apart_pl (by decide) (by omega) (by omega)
    · show NativeRustcVm.Apart (reg st1.data .rdi) stateBytes (stackArg st1.data 2)
        (8 * (stackArg st1.data 3).toNat)
      rw [hdi1, a2]
      unfold NativeRustcVm.Apart stateBytes
      rw [NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
      omega
    · show NativeRustcVm.Apart (reg st1.data .rdi) stateBytes (stackArg st1.data 4)
        (16 * (stackArg st1.data 5).toNat)
      rw [hdi1, a4, a5, hqsn]; exact c.apart_pl (by decide) (by omega) (by omega)
  refine call_then hpc1 (hgl w) hpre fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hok, hws2, hch2, hsv2⟩ := hq
  have eG : glueArgs st1.data = (qs, powers lam qs.size, bt) := by
    unfold glueArgs
    rw [a2, a3, a4, a5, a6, a7, hqsn]
    have hw : wordSlice st1.data (pA m0 + BitVec.ofNat 64 61360) qs.size = qs := by
      show (NativeRustcVm.wordsOf st1.data.dmem _ qs.size).toArray = _
      rw [← Array.length_toList, NativeRustcVm.wordsOf_of_wordsAt hqs1, Array.toArray_toList]
    have hs : slice st1.data (loc m0 4448) (BitVec.ofNat 64 qs.size) = powers lam qs.size := by
      show (NativeRustcVm.ewsOf st1.data.dmem (loc m0 4448) (BitVec.ofNat 64 qs.size).toNat).toArray
        = _
      have := NativeRustcVm.ewsOf_of_ewsAt hpw1
      rw [Array.length_toList, powers_size'] at this
      rw [hqsn, this, Array.toArray_toList]
    rw [hw, hs]
    rfl
  have eO : slice st1.data (reg st1.data .r8) (reg st1.data .r9) = ood := by
    show (NativeRustcVm.ewsOf st1.data.dmem (reg st1.data .r8) (reg st1.data .r9).toNat).toArray
      = _
    have := NativeRustcVm.ewsOf_of_ewsAt hood1
    rw [Array.length_toList, hH.osize] at this
    rw [h81, h91, this, Array.toArray_toList]
  have eL : ewArg (reg st1.data .rsi) (reg st1.data .rdx) = lam := by rw [hsi1, hdx1]; rfl
  have eV : ewArg (stackArg st1.data 0) (stackArg st1.data 1) = v := by rw [a0, a1]; rfl
  rw [hdi1, eL, hcx1, eO, eV, eG] at hws2
  have hch2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (pA m0) stateBytes q ∨
        NativeRustcVm.InRange (stackBelow st1.data glueLevelStack) glueLevelStack q) :=
    NativeRustcVm.SameOutside.mono hch2 fun q hq ↦ by
      rcases hq with hq | hq
      · left; rw [one_iff, hdi1] at hq; exact hq
      · exact Or.inr hq
  have hsub : ∀ q, NativeRustcVm.InRange (pA m0) stateBytes q →
      NativeRustcVm.InRange (pA m0) whirBytes q :=
    fun q hq ↦ inRange_mono hq (by decide)
  obtain ⟨hf2, -⟩ := c.call (o := 0) (by omega) hf1 hle hsv2 hrsp2 (lo := 8128) (n := 0)
    (by omega) (by omega) (fun q hq ↦ Or.inl (Or.inl (hsub q hq))) hch2'
  have hts2 := c.ts_call (o := 0) (by omega) hf1 hle hsv2 (fun q hq ↦ c.p_not_t (hsub q hq))
    hch2' hts1
  have hbr2 : BufRoundsAt st2.data.dmem (off (pA m0) roundsOff) rounds.toList := by
    have hro : (off (pA m0) roundsOff).toNat = (pA m0).toNat + 61152 :=
      NativeRustcVm.toNat_add_ofNat (i := 61152) (by have := g.pW; omega)
    refine bufRoundsAt_of_same hK1.wa.2 (c.same_call (o := 0) (by omega) hf1 hle hch2'
      (by rw [hro]; have := g.pW; unfold roundBytes roundCap; omega) (fun q hq hx ↦ ?_)
      (by rw [hro]; have := g.pS; have := g.hN; unfold roundBytes roundCap; omega))
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap stateBytes; have := g.pW; omega)] at hq
    have hnw : NativeRustcVm.NoWrap (off (pA m0) roundsOff) (8 + roundBytes * roundCap) := by
      unfold NativeRustcVm.NoWrap roundBytes roundCap; rw [hro]; have := g.pW; omega
    rw [inRange_iff' hnw, hro] at hx
    unfold stateBytes at hq
    omega
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b25Offset) := hpc2
  -- `b25`: RSP back, AL into R15
  have hwf2 := c.wf0 hf2.frame.kept (ret := 0)
  have hm2 : Match (argEnv m0 st2.data 8176 8 []) s8S st2.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf2.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b25_in_code (by simp [b25]) hp) exit_b25 hwf2 nofun hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hr153⟩ := ok_b25
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hf3 : Fr m0 72 st3.data :=
    ⟨Frame.of_blockA hf2.frame hwf2 hm3 hmid3 slots_le, by rw [Sm, hd3]; exact hf2.same⟩
  have h15 : reg st3.data .r15 = UnOp.apply .trunc .W32 (reg st2.data .rax) :=
    hm3.regs .r15 _ hr153
  simp only [PcOk] at hpc3
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b27Offset) := hpc3.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_14_at)
  -- `b27`: the epilogue
  simp only [runN] at hrun
  refine Eventually.mono (exit_spec hp c hf3 hpc3') fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, ?_, ?_, ?_, ?_, h5⟩
  · show boolRet st'.data = _
    rw [h3, hrun, h15, al_trunc]
    exact hok
  · intro x s' h
    rw [hrun] at h
    cases h
    rw [h4, hd3]
    exact hts2
  · intro x s' h
    rw [hrun] at h
    cases h
    rw [h4, hd3]
    exact ⟨hws2, hbr2⟩
  · unfold ChangesIn; rw [h4, hd3]; exact changes_of hf2.same

end

end NativeRustcVmX64.Whir.Levels.NL
