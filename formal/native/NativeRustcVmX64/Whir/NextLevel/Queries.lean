module

public import NativeRustcVmX64.Whir.NextLevel.Facts
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `next_level`: the queries and `λ` (x86-64)

From `H13` at `b13`: the state's address (the stack argument) loaded, `sample_queries(t, μ + rate,
level.queries, &w.queries)` (`b13`, always `Some`; `b14` tests it), `squeeze(t)` for `λ` (`b15`),
`λ` stored at `96`, `88`, the query count loaded and the zeroing loop's counter set (`b16`): `qry`,
to the loop's head `b17` with `H17` and RCX `72`. The query buffer across blocks (`qbuf_frame`)
and calls (`qbuf_call`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

@[expose] public section

/-- At the zeroing loop's head (`b17`): the frame's facts (`λ` at `96`, `88`), the queries `qs` in
the query buffer, their count in RAX, the `TState` at its state `s8`. -/
structure H17 [Labels] (a : DecArea) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (xs ood : Array EW) (v lam : EW)
    (qs : Array UInt64) (s8 : TState) (d : MachineData) : Prop where
  K : K level w rounds m0 72 d
  rbx : reg d .rbx = reg m0 .rsi
  r12 : reg d .r12 = reg m0 .r9
  r14 : reg d .r14 = tA m0
  r15 : (reg d .r15).toNat = level.fold
  rax : reg d .rax = BitVec.ofNat 64 qs.size
  ff : FF m0 xs ood v lam d.dmem
  size : xs.size = level.fold
  osize : ood.size = (reg m0 .r9).toNat
  qbuf : NativeRustcVm.BufWordsAt d.dmem (qA m0) queryCap qs.toList
  ts : TStateAt d.dmem (tA m0) a s8

end

public section

theorem sub_six {r : Reg64} (h : r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15]) : r ∈ six := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [six]

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level w rounds m0)
include c

theorem depth_toNat : (depth m0 level).toNat = (reg m0 .r9).toNat + level.logInvRate := by
  have h1 := c.mu
  have h2 := c.rate
  unfold stackCap at h1
  unfold depth
  rw [BitVec.toNat_add, toNat_toUInt64 (by omega)]
  omega

theorem qA_toNat : (qA m0).toNat = (pA m0).toNat + 61352 :=
  NativeRustcVm.toNat_add_ofNat (by have := c.geo.pW; omega)

/-- The query buffer across a change of the frame. -/
theorem qbuf_frame {d d' : Mem 64} {hi : Nat} (hhi : hi ≤ 8176)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (fa m0) hi)) {qs : List UInt64}
    (h : NativeRustcVm.BufWordsAt d (qA m0) queryCap qs) :
    NativeRustcVm.BufWordsAt d' (qA m0) queryCap qs :=
  bufWordsAt_of_same h ((c.p_frame hhi hs).sub (o := 61352) (k := 1848) (by decide)) (by decide)

/-- The query buffer across a call changing its stack, the `TState`, a frame range, the state. -/
theorem qbuf_call {o : Nat} (ho : o ≤ 8176) {d d' : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 8176 - o + N' ≤ nextLevelStack) {R : BitVec 64 → Prop}
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q))
    {lo n : Nat} (hn : lo + n ≤ 8192)
    (hR : ∀ q, R q → NativeRustcVm.InRange (tA m0) tstateBytes q ∨
      NativeRustcVm.InRange (loc m0 lo) n q ∨ NativeRustcVm.InRange (pA m0) stateBytes q)
    {qs : List UInt64} (h : NativeRustcVm.BufWordsAt d.dmem (qA m0) queryCap qs) :
    NativeRustcVm.BufWordsAt d'.dmem (qA m0) queryCap qs := by
  have g := c.geo
  have hqa := c.qA_toNat
  refine bufWordsAt_of_same h (c.same_call (mm := 1848) ho hf hle hch (by rw [hqa]; have := g.pW; omega)
    (fun q hq hx ↦ ?_) (by rw [hqa]; have := g.pS; have := g.hN; omega)) (by decide)
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hqa]; have := g.pW; omega), hqa] at hx
  have := g.hN
  rcases hR q hq with h' | h' | h'
  · rw [c.inT] at h'; have := g.pT; omega
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact absurd h' (by unfold NativeRustcVm.InRange; omega)
    rw [c.inLc (by omega) hn] at h'; have := g.pS; omega
  · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap stateBytes; have := g.pW; omega)] at h'
    unfold stateBytes at h'; omega

end Ctx

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- `blk_step` with `Zone` kept by the block (its writes in `Gap` ranges). -/
theorem blk_stepZ (c : Ctx a s level w rounds m0) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) (hp : Placed code k) {S : SState} {x : Exit}
    (hx : exec b retS = some (S, x)) {o' : Nat} (hmid : MidOk 8176 o' slots S = true)
    {rs : List (Nat × Nat)} (hW : Wr rs S) (hg : ∀ p ∈ rs, Gap p)
    (hrs : ∀ p ∈ rs, 88 ≤ p.1 ∧ p.2 ≤ 8128 ∨ p.2 ≤ 80)
    {st : MachineState} (hK : K level w rounds m0 72 st.data) (hpc : st.pc = Host.addrOf (k + j))
    {ret : BitVec 64} (hret : ∀ l, x = .call l → ret = (Host.addrOf (k + j + b.length)).toBitVec)
    {R : MachineState → Prop}
    (cont : ∀ st', Match (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) ret) S st'.data →
      PcOk (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) ret) x (Host.addrOf (k + j + b.length)) st' →
      K level w rounds m0 o' st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange (fa m0) 8128) →
      KeepZ m0 st.data.dmem st'.data.dmem →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  blk_step c hb hne hp hx hmid hW hrs hK hpc hret fun st' hm' hpc' hK' hs _ ↦
    cont st' hm' hpc' hK' hs (keepZ_blk (c.wf0 hK.fr.frame.kept) hm' (writesIn_of_mid hmid) hW hg)

/-- **The queries and `λ`**: `b13` to `b16`, to the zeroing loop's head with `H17`. -/
theorem qry (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (hsq : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s))
    (hsqz : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {xs ood : Array EW} {v : EW} {s6 : TState} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b13Offset)) (hH : H13 a level w rounds m0 xs ood v s6 st.data)
    (hrun : runN level w rounds m0 s =
      tail6 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds xs ood v s6) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s level w rounds m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b17Offset) ∧ reg st'.data .rcx = BitVec.ofNat 64 72 ∧
        ∃ qs lam s8, runN level w rounds m0 s =
          tail8 (reg m0 .rsi).toNat (reg m0 .r9).toNat w rounds xs ood v qs lam s8 ∧
          H17 a level w rounds m0 xs ood v lam qs s8 st'.data)) st := by
  have g := c.geo
  have hK := hH.K
  have hxs : xs.size ≤ 6 := by rw [hH.size]; exact c.fold
  have hos : ood.size ≤ 30 := by rw [hH.osize]; exact c.mu
  have hfv : FV m0 xs ood v st.data.dmem := ⟨hH.v1, hH.v0, hH.high, hH.oodN, hH.oodp⟩
  -- `b13`, its first instruction: the state's address
  have hwf0 := c.wf0 hK.fr.frame.kept (ret := 0)
  have hm0 : Match (argEnv m0 st.data 8176 8 []) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK.fr.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of ((infix_take b13 1).trans b13_in_code (by simp [b13])) (by simp [b13])
    hp) exit_b13a hwf0 nofun hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmem1, hrax1, hmid1, hkr1⟩ := ok_b13a
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf0 hmem1
  have hK1 : K level w rounds m0 72 st1.data :=
    ⟨⟨Frame.of_blockA hK.fr.frame hwf0 hm1 hmid1 slots_le, by rw [Sm, hd1]; exact hK.fr.same⟩,
      by rw [hd1]; exact hK.w80, by rw [hd1]; exact hK.lv, by rw [hd1]; exact hK.wa⟩
  have hrax : reg st1.data .rax = pA m0 :=
    (hm1.regs .rax _ hrax1).trans
      (load_ofMachine (r := 0) (o := 8184) rfl (c.arg_keep hK.fr.same))
  have hk1r : ∀ r ∈ six, reg st1.data r = reg st.data r := fun r hr ↦ hm1.regs r _ (hkr1 r hr)
  have hR1 : R0 level m0 st1.data := hH.regs.saved fun r hr ↦ hk1r r (cs_six hr)
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b13Offset + (b13.take 1).length) := hpc1
  -- `b13`, the rest: `sample_queries(t, μ + rate, level.queries, &w.queries)`
  let env2 := frameEnv m0 st1.data 8176 [(lA m0, 24)] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b14Offset)).toBitVec
  have hwf2 : env2.WF := c.wfL hK1.fr.frame.kept
  have hm2 : Match env2 levelS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hK1.fr.frame.rsp_eval, known_ptr rfl hR1.rbp, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of ((infix_drop b13 1).trans b13_in_code (by simp [b13])) (by simp [b13])
    hp) exit_b13b hwf2 (fun _ _ ↦ rfl) hpc1' hm2 fun st2 hm3 hpc2 ↦ ?_
  obtain ⟨hmid2, hW2, hrdi2, hrsi2, hrdx2, hrcx2, hrbp2, hkr2⟩ := ok_b13b
  obtain ⟨hf2, hs2⟩ := c.blkF hK1.fr hwf2 hm3 hmid2 (hi := 72) (by omega)
    (fun w hw ↦ ⟨(hW2 w hw).1, by
      obtain ⟨-, p, hp, -, h2⟩ := hW2 w hw; simp at hp; subst hp; exact h2⟩)
  have hK2 : K level w rounds m0 64 st2.data :=
    c.K_frame hK1 hf2 (by omega) hs2 (bytes_blkF hwf2 hm3 (writesIn_of_mid hmid2) hW2
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes])
      hK1.w80)
  have hz2 : KeepZ m0 st1.data.dmem st2.data.dmem :=
    keepZ_blkF hwf2 hm3 (writesIn_of_mid hmid2) hW2 (by decide)
  have e2 : ∀ {r : Reg64} {v : Sym}, (after (b13.drop 1) levelS).reg r = some v →
      reg st2.data r = v.eval env2 := fun h ↦ hm3.regs _ _ h
  have hk2r : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st2.data r = reg st1.data r :=
    fun r hr ↦ e2 (hkr2 r hr)
  have ht2 : reg st2.data .rdi = tA m0 := (e2 hrdi2).trans hR1.r14
  have hsi2 : reg st2.data .rsi = depth m0 level := (e2 hrsi2).trans hR1.r13
  have hlw := level_words hK1.lv
  have hdx2 : (reg st2.data .rdx).toNat = level.queries := by
    rw [e2 hrdx2, Sym.eval, load_ofMachine (r := 1) (o := 16) rfl hlw.2.2]
    exact toNat_toUInt64 (by have := c.qs; unfold queryCap at this; omega)
  have hcx2 : reg st2.data .rcx = qA m0 := by
    rw [e2 hrcx2]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show env2.regs .rax = reg st1.data .rax from rfl, hrax]
  have hbp2 : reg st2.data .rbp = qA m0 := by
    rw [e2 hrbp2]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show env2.regs .rax = reg st1.data .rax from rfl, hrax]
  have hts2 : TStateAt st2.data.dmem (tA m0) a s6 :=
    c.ts_frame (by omega) (hm3.kept hwf2) hs2
      (show TStateAt st1.data.dmem (tA m0) a s6 by rw [hd1]; exact hH.ts)
  have hat := c.at_call (o := 64) (by omega) hK2.fr
  have hle : 8176 - 64 + sampleQueriesStack ≤ nextLevelStack := by decide
  have hwt := c.whirT hat hK2.fr.same hle
  have hqo : WhirOut m0 (tA m0) a (qA m0) queryBufBytes nextLevelStack :=
    WL.whirOut_sub c.pout (o := 61352) (k := queryBufBytes) (by decide)
  have hpre : SampleQueriesPre a s6 st2.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show WhirT st2.data (reg st2.data .rdi) a sampleQueriesStack
      rw [ht2]; exact hwt
    · show TStateAt st2.data.dmem (reg st2.data .rdi) a s6
      rw [ht2]; exact hts2
    · show (reg st2.data .rdx).toNat ≤ queryCap
      rw [hdx2]; exact c.qs
    · show WhirOut st2.data (reg st2.data .rdi) a (reg st2.data .rcx) queryBufBytes
        sampleQueriesStack
      rw [ht2, hcx2]; exact c.whirOut hat hle hqo
    · rw [ht2, hcx2]
      apply c.got_call hK2.fr (by omega) hle (by decide)
      intro ar har
      rcases List.mem_append.mp har with har | har
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at har
        rcases har with rfl | rfl | rfl
        · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
        · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
        · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
          · change (pA m0).toNat ≤ (qA m0).toNat
            rw [c.qA_toNat]
            omega
          · change (qA m0).toNat + 1848 ≤ (pA m0).toNat + 63200
            rw [c.qA_toNat]
      · exact ⟨ar, by simp [har], le_rfl, le_rfl⟩
  refine call_then hpc2 (hsq a s6) hpre fun st3 hpc3 hrsp3 hq ↦ ?_
  obtain ⟨hok, ⟨qs, s7, hres7, hbuf, hts7⟩, hch, hsv⟩ := hq
  rw [hsi2, c.depth_toNat, hdx2] at hres7
  rw [hcx2] at hbuf
  rw [ht2] at hts7
  have hch' : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem (fun q ↦
      (NativeRustcVm.InRange (qA m0) 1848 q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st2.data sampleQueriesStack) sampleQueriesStack q) :=
    NativeRustcVm.SameOutside.mono hch fun q hq ↦ by
      rcases hq with hq | hq
      · left; rw [ht2, hcx2] at hq; exact two_iff.mp hq
      · exact Or.inr hq
  obtain ⟨hK3, hkeep3⟩ := c.K_call hK2 hle hsv hrsp3
    (R := fun q ↦ NativeRustcVm.InRange (qA m0) 1848 q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) (lo := 8128) (n := 0) (by omega) (by omega)
    (fun q hq ↦ hq.elim (fun h ↦ Or.inr (Or.inr h)) Or.inl) hch'
  have hz3 : KeepZ m0 st2.data.dmem st3.data.dmem :=
    keepZ_call (o := 64) hkeep3 (by omega) (by decide)
  have hcs3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st2.data r := hsv.1
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b14Offset) := hpc3
  -- `b14`: `sample_queries`' `Some`
  refine Eventually.bind (test_spec hp c b14_in_code rfl (b_eq.2.2 ▸ exit_b4) (b_eq.2.2 ▸ ok_b4)
    hK3 hpc3' hok) fun st4 ⟨hr4, hd4, hpc4⟩ ↦ ?_
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b15Offset) := hpc4
  have hK4 := hK3.congr hr4 hd4
  -- `b15`: `squeeze(t)`
  refine blk_stepZ c b15_in_code (by simp [b15]) hp exit_b15 ok_b15.1 ok_b15.2.1 (by decide)
    (fun p hp ↦ by simp at hp; subst hp; right; omega) hK4 hpc4'
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b16Offset)).toBitVec) (fun _ _ ↦ rfl) fun st5 hm5 hpc5 hK5 hs5 hz5 ↦ ?_
  obtain ⟨-, -, hrdi5, hkr5⟩ := ok_b15
  have hk5r : ∀ r ∈ six, reg st5.data r = reg st4.data r := fun r hr ↦ hm5.regs r _ (hkr5 r hr)
  have hc41 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st5.data r = reg st1.data r :=
    fun r hr ↦ by
      have hcs : calleeSaved r = true := six_cs (sub_six hr)
      rw [hk5r r (sub_six hr), hr4 r, hcs3 r hcs, hk2r r hr]
  have ht5 : reg st5.data .rdi = tA m0 :=
    (hm5.regs _ _ hrdi5).trans ((hr4 .r14).trans ((hcs3 .r14 rfl).trans
      ((hk2r .r14 (by simp)).trans hR1.r14)))
  have hts5 : TStateAt st5.data.dmem (tA m0) a s7 :=
    c.ts_frame (hi := 8128) (by omega) (hm5.kept (c.wf0 hK4.fr.frame.kept)) hs5
      (show TStateAt st4.data.dmem (tA m0) a s7 by rw [hd4]; exact hts7)
  have hqb5 : NativeRustcVm.BufWordsAt st5.data.dmem (qA m0) queryCap qs.toList :=
    c.qbuf_frame (hi := 8128) (by omega) hs5
      (show NativeRustcVm.BufWordsAt st4.data.dmem (qA m0) queryCap qs.toList by
        rw [hd4]; exact hbuf)
  have hat5 := c.at_call (o := 64) (by omega) hK5.fr
  have hle5 : 8176 - 64 + squeezeStack ≤ nextLevelStack := by decide
  have hwt5 := c.whirT hat5 hK5.fr.same hle5
  have htok := hwt5.2.2.2.1
  have hTn : (tA m0).toNat + 760 ≤ 2 ^ 64 := g.tW
  have h1' : (tA m0).toNat + 760 ≤ (stackBelow st5.data squeezeStack).toNat ∨
      (stackBelow st5.data squeezeStack).toNat + (squeezeStack + 8) ≤ (tA m0).toNat := htok.1
  have h2' : (tA m0).toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat := htok.2.2
  have hpre5 : SqueezePre s7.sponge st5.data := by
    unfold SqueezePre
    rw [ht5]
    refine ⟨hwt5.1, hwt5.2.1, ⟨fun j hj ↦ hts5.footprint.1.1 j (by
      simp only [spongeBytes] at hj; show j < 760; omega), ?_, ?_, ?_⟩, hts5.sponge, ?_⟩
    · show (tA m0).toNat + 328 ≤ 2 ^ 64; omega
    · show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat; omega
    · show (tA m0).toNat + 328 ≤ _ ∨ _ ≤ (tA m0).toNat; omega
    · apply c.got_call hK5.fr (by omega) hle5 (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, by
          change (tA m0).toNat + 328 ≤ (tA m0).toNat + 760; omega⟩
      · exact c.got_rc
  refine call_then hpc5 (hsqz s7.sponge) hpre5 fun st6 hpc6 hrsp6 hq ↦ ?_
  obtain ⟨hc0, hc1, hsp6, hs6, hsv6⟩ := hq
  have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b16Offset) := hpc6
  rw [ht5] at hsp6 hs6
  have hcal5 : ∀ q, NativeRustcVm.InRange (stackBelow st5.data squeezeStack) squeezeStack q →
      ¬NativeRustcVm.InRange (tA m0) tstateBytes q ∧
        ¬NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ (c.sctx (F := 8176 - 64) (by decide)).stack_not_t
      ((c.sctx (F := 8176 - 64) (by decide)).inRange_callee hat5 hle5 hq).1
  have hts6 : TStateAt st6.data.dmem (tA m0) a (sq s7).2 := by
    refine hts5.with_sponge hsv6.2 hcal5 (fun q hq ↦ hs6 q ?_) hsp6
    rintro (hq' | hq')
    · obtain ⟨j, hj, hw', rfl⟩ := touch_of_inRange (o := 0) (n := 328)
        (hTn : NativeRustcVm.NoWrap (tA m0) 760) (by decide) (by rwa [off_zero])
      exact hq (Or.inl ⟨j, hj, hw'.2, rfl⟩)
    · exact hq (Or.inr hq')
  obtain ⟨hK6, hkeep6⟩ := c.K_call hK5 hle5 hsv6 hrsp6
    (R := NativeRustcVm.InRange (tA m0) spongeBytes) (lo := 8128) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inl (inRange_mono hq (by decide))) hs6
  have hz6 : KeepZ m0 st5.data.dmem st6.data.dmem :=
    keepZ_call (o := 64) hkeep6 (by omega) (by decide)
  have hqb6 : NativeRustcVm.BufWordsAt st6.data.dmem (qA m0) queryCap qs.toList :=
    c.qbuf_call (o := 64) (by omega) hK5.fr hle5 hs6 (lo := 0) (n := 0) (by omega)
      (fun q hq ↦ Or.inl (inRange_mono hq (by decide))) hqb5
  have hcs6 : ∀ r, calleeSaved r = true → reg st6.data r = reg st5.data r := hsv6.1
  have hbp6 : reg st6.data .rbp = qA m0 := by
    rw [hcs6 .rbp rfl, hk5r .rbp (by simp [six]), hr4 .rbp, hcs3 .rbp rfl, hbp2]
  -- `b16`: `λ` stored, the query count, the loop's counter
  have hqa := c.qA_toNat
  have hqm : NativeRustcVm.Mapped st6.data.dmem (qA m0) 8 :=
    Mapped.keeps (show NativeRustcVm.Mapped m0.dmem (qA m0) 8 from
      fun i hi ↦ hqo.1.1 i (by unfold queryBufBytes queryCap; omega)) hK6.fr.frame.kept
  have hwf6 : (argEnv m0 st6.data 8176 8 [(qA m0, 8)] (fun _ ↦ 0) 0).WF :=
    c.wf1 hK6.fr.frame.kept hqm (by rw [hqa]; have := g.pW; omega)
      (by rw [hqa]; have := g.pS; have := g.hN; omega)
  have hm6 : Match (argEnv m0 st6.data 8176 8 [(qA m0, 8)]) qS st6.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hK6.fr.frame, known_ptr rfl hbp6, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) exit_b16 hwf6 nofun hpc6' hm6
    fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hW7, hw88, hw96, hrax7, hrcx7, -, hkr7⟩ := ok_b16
  obtain ⟨hf7, hs7⟩ := c.blk hK6.fr hwf6 hm7 hmid7 (hi := 104) (by omega)
    (fun w hw ↦ ⟨(hW7 w hw).1, by
      obtain ⟨-, p, hp, -, h2⟩ := hW7 w hw; simp at hp; subst hp; exact h2⟩)
  have hK7 : K level w rounds m0 72 st7.data :=
    c.K_frame hK6 hf7 (by omega) hs7 (Ctx.bytes_blk hwf6 hm7 (writesIn_of_mid hmid7) hW7
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes])
      hK6.w80)
  have hz7 : KeepV m0 st6.data.dmem st7.data.dmem :=
    keepV_blk hwf6 hm7 (writesIn_of_mid hmid7) hW7 (by decide)
  have hl1 : NativeRustcVm.WordAt st7.data.dmem (loc m0 88) (sq s7).1.c1 :=
    wordAt_written hm7 (r := 0) (o := 88) rfl (by omega) hw88 hc1
  have hl0 : NativeRustcVm.WordAt st7.data.dmem (loc m0 96) (sq s7).1.c0 :=
    wordAt_written hm7 (r := 0) (o := 96) rfl (by omega) hw96 hc0
  have hcnt : NativeRustcVm.WordAt st6.data.dmem (off (qA m0) 0) qs.size.toUInt64 := by
    rw [off_zero]; have := hqb6.2.1; rwa [Array.length_toList] at this
  have hrax7' : reg st7.data .rax = BitVec.ofNat 64 qs.size :=
    (hm7.regs _ _ hrax7).trans (load_ofMachine (r := 1) (o := 0) rfl hcnt)
  have hk7r : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st7.data r = reg st6.data r :=
    fun r hr ↦ hm7.regs r _ (hkr7 r hr)
  have hc71 : ∀ r ∈ [Reg64.rbx, .r12, .r13, .r14, .r15], reg st7.data r = reg st.data r :=
    fun r hr ↦ by
      rw [hk7r r hr, hcs6 r (six_cs (sub_six hr)), hc41 r hr, hk1r r (sub_six hr)]
  have hfv7 : FV m0 xs ood v st7.data.dmem :=
    hfv.keep ((KeepV.of_eq hd1).trans (hz2.v.trans (hz3.v.trans ((KeepV.of_eq hd4).trans
      (hz5.v.trans (hz6.v.trans hz7)))))) hxs hos
  have hpc7' : st7.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b17Offset) := hpc7
  refine .done _ (Or.inr ⟨hpc7', hm7.regs _ _ hrcx7, qs, (sq s7).1, (sq s7).2,
    by rw [hrun, tail6, hres7]; rfl,
    ⟨hK7, (hc71 .rbx (by simp)).trans hH.regs.rbx, (hc71 .r12 (by simp)).trans hH.r12,
      (hc71 .r14 (by simp)).trans hH.regs.r14, by rw [hc71 .r15 (by simp)]; exact hH.r15,
      hrax7', ⟨hfv7, hl1, hl0⟩, hH.size, hH.osize,
      c.qbuf_frame (hi := 104) (by omega) hs7 hqb6,
      c.ts_frame (hi := 104) (by omega) (hm7.kept hwf6) hs7 hts6⟩⟩)

end

end NativeRustcVmX64.Whir.Levels.NL
