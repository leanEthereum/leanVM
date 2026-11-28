module

public import NativeRustcVmX64.Whir.FinalLevel.Entry
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names

/-!
# `final_level`: the grind and the queries (x86-64)

From `Live` at `b6`: `grind(t, 17)` (`b6`), its verdict (`b7`, `None` to `NativeRustcVmX64.Vm.FinalLevel.label_5`); the
depth `μ + rate` (RBX) and the query count (RDX) from the level (`b8`, its first part, the level's
region), `sample_queries(t, depth, count, &w.queries)` (`b8`'s rest, RBP the `WhirW`), its verdict
(`b9`, always `Some`), to `b10` (`queries`). `Live.step`: `Live` across a block then a call.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

theorem two_iff {x y q : BitVec 64} {n m : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩, ⟨y, m⟩] q ↔ NativeRustcVm.InRange x n q ∨
      NativeRustcVm.InRange y m q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]

theorem six_cs {r : Reg64} (h : r ∈ six) : calleeSaved r = true := by
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **`Live` across a block and a call**: the block writes the frame's ranges `rs` off `Live`'s
words, the call from RSP offset `o` changes its stack, the outputs and the frame's bytes
`[lo, lo + n)` off them; the registers `Live` reads kept. -/
theorem Live.step [Labels] {level : Whir.Level} {m0 d d1 d' : MachineData} {folded : Array EW}
    (h : Live level m0 d folded) {rest : List (BitVec 64 × Nat)} {S : SState} {ret : BitVec 64}
    (hwf : (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret) S d1)
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S)
    (hrs : ∀ p ∈ rs, p.2 ≤ 40 ∨ (64 ≤ p.1 ∧ p.2 ≤ 1600) ∨ 2624 ≤ p.1)
    {o lo n : Nat} (hkeep : ∀ j, o + 8 ≤ j → j < 2688 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d1.dmem.get? (loc m0 j)) (ho : o ≤ 32)
    (hlo : 64 ≤ lo ∧ lo + n ≤ 1600 ∨ 2624 ≤ lo) (hf : Fr m0 40 d')
    (hr : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15], reg d' r = reg d r)
    (h64 : 2 ^ mu m0 + level.fold ≤ 64) : Live level m0 d' folded :=
  h.keep hf hr (fun j hj ↦ by
    rw [hkeep j (by omega) (by omega) (by omega)]
    refine get_blk hwf hm hin hW (by omega) fun p hp ↦ ?_
    rcases hrs p hp with h' | h' | h' <;> omega) h64

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The grind and the queries.** -/
theorem queries (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s))
    {st : MachineState} {folded : Array EW} {s1 : TState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b6Offset))
    (hl : Live level m0 st.data folded)
    (hbx : reg st.data .rbx = level.logInvRate.toUInt64.toBitVec) (hbp : reg st.data .rbp = lA m0)
    (hts : TStateAt st.data.dmem (tA m0) a s1)
    (hrun : runF level b w rounds m0 s = (C1 (reg m0 .rsi).toNat level (mu m0) (reg m0 .r8).toNat
      b w rounds folded).run s1)
    (cont : ∀ (st' : MachineState) (qs : Array UInt64) (s3 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b10Offset) → Live level m0 st'.data folded → reg st'.data .rbp = pA m0 →
      NativeRustcVm.BufWordsAt st'.data.dmem (qA m0) queryCap qs.toList →
      TStateAt st'.data.dmem (tA m0) a s3 →
      runF level b w rounds m0 s = (C3 (reg m0 .rsi).toNat (mu m0) (reg m0 .r8).toNat b w rounds
        folded qs).run s3 →
      Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hmu : mu m0 < 64 := c.mu64
  -- `b6`: `grind(t, 17)`.
  let env1 := argEnv m0 st.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b7Offset)).toBitVec
  have hwf1 : env1.WF := c.wf0 hl.fr.frame.kept
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf1 (fun _ _ ↦ rfl) hpc
    (match_retS hl.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, hrdi1, hrsi1, hkr1⟩ := ok_b6
  obtain ⟨hf1, hs1⟩ := c.blk hl.fr hwf1 hm1 hmid1 (hi := 40) (by omega) (hW1.le (by decide))
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b6 retS).reg r = some v →
      reg st1.data r = v.eval env1 := fun h ↦ hm1.regs _ _ h
  have hk1 : ∀ r ∈ six, reg st1.data r = reg st.data r := fun r hr ↦ e1 (hkr1 r hr)
  have ht1 : reg st1.data .rdi = tA m0 := (e1 hrdi1).trans hl.r12
  have hbits : grindBits st1.data = Whir.queryGrindingBits := by
    unfold grindBits; rw [e1 hrsi1]; rfl
  have hts1 := c.ts_frame (hi := 40) (by omega) (hm1.kept hwf1) hs1 hts
  have hat1 := c.at_call (o := 32) (by omega) hf1
  have hle1 : 2672 - 32 + grindStack ≤ finalLevelStack := by decide
  have hwt1 := c.whirT hat1 hf1.same hle1
  have hpre1 : GrindPre a s1 st1.data := by
    refine ⟨hwt1.1, hwt1.2.1, ?_, ?_, ?_, ?_⟩
    · show TStateAt st1.data.dmem (reg st1.data .rdi) a s1
      rw [ht1]; exact hts1
    · show TStateOk st1.data (reg st1.data .rdi) a grindStack
      rw [ht1]; exact hwt1.2.2.2.1
    · rw [hbits]; decide
    · rw [ht1]
      apply c.got_call hf1 (by omega) hle1 (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_rc
  refine call_then hpc1 (hgr a s1) hpre1 fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hok, hnext, hch, hsv⟩ := hq
  rw [hbits] at hok hnext
  rw [ht1] at hnext hch
  obtain ⟨hf2, hkeep2⟩ := c.call (o := 32) (by omega) hf1 hle1 hsv hrsp2
    (R := NativeRustcVm.InRange (tA m0) tstateBytes) (lo := 2624) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inl (Or.inr hq)) hch
  have hcs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := hsv.1
  have hr2 : ∀ r ∈ six, reg st2.data r = reg st.data r := fun r hr ↦
    (hcs2 r (six_cs hr)).trans (hk1 r hr)
  have hl2 : Live level m0 st2.data folded :=
    hl.step hwf1 hm1 (writesIn_of_mid hmid1) hW1 (by decide) hkeep2 (by omega) (by omega) hf2
      (fun r hr ↦ hr2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp [six])) hfo
  rw [show k + NativeRustcVmX64.Vm.FinalLevel.b6Offset + b6.length = k + NativeRustcVmX64.Vm.FinalLevel.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.FinalLevel.b6_next]] at hpc2
  -- `b7`: the grind's verdict.
  refine Eventually.bind (test_spec hp c b7_in_code rfl (b_eq.1 ▸ exit_b5) (b_eq.1 ▸ ok_b5) hf2
    hpc2 hok) fun st3 ⟨hr3, hd3, hpc3⟩ ↦ ?_
  have hf3 := hf2.congr hr3 hd3
  rcases hres : (grind Whir.queryGrindingBits).run s1 with _ | ⟨⟨⟩, s2⟩
  · rw [hres] at hpc3
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hpc3
    exact none36 hp c hf3 (hpc3.trans (l5 hp)) (by rw [hrun, C1]; exact run_bind_none hres)
  rw [hres] at hpc3
  simp only [Option.isSome_some, ite_true] at hpc3
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b8Offset) := hpc3
  have hl3 : Live level m0 st3.data folded :=
    hl2.keep hf3 (fun r _ ↦ hr3 r) (fun j _ ↦ by rw [hd3]) hfo
  have hts3 : TStateAt st3.data.dmem (tA m0) a s2 := by rw [hd3]; exact hnext () s2 hres
  have hrun3 : runF level b w rounds m0 s = (C2 (reg m0 .rsi).toNat level (mu m0)
      (reg m0 .r8).toNat b w rounds folded).run s2 := by
    rw [hrun, C1]; exact run_bind_some hres
  have hbx3 : reg st3.data .rbx = level.logInvRate.toUInt64.toBitVec := by
    rw [hr3 .rbx, hr2 .rbx (by simp [six])]; exact hbx
  have hbp3 : reg st3.data .rbp = lA m0 := by rw [hr3 .rbp, hr2 .rbp (by simp [six])]; exact hbp
  -- `b8`, its first part: the depth and the count, from the level.
  let env4 := frameEnv m0 st3.data 2672 [(lA m0, 24)] (fun _ ↦ 0) 0
  have hwf4 : env4.WF := c.wfL hf3.frame.kept
  have hm4 : Match env4 levelS st3.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf3.frame.rsp_eval, known_ptr rfl hbp3, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of ((infix_take b8 2).trans b8_in_code (by simp [b8])) (by simp [b8])
    hp) exit_b8a hwf4 nofun hpc3' hm4 fun st4 hm4' hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hrbx4, hrdx4, hkr4⟩ := ok_b8a
  have hd4 : st4.data.dmem = st3.data.dmem := hm4'.dmem_eq hwf4 hmem4
  have hf4 : Fr m0 40 st4.data :=
    ⟨Frame.of_block hf3.frame hwf4 hm4' hmid4 slots_le, by rw [Sm, hd4]; exact hf3.same⟩
  have e4 : ∀ {r : Reg64} {v : Sym}, (after (b8.take 2) levelS).reg r = some v →
      reg st4.data r = v.eval env4 := fun h ↦ hm4'.regs _ _ h
  have hlw := level_words (c.level_at hf3.same)
  have hdx4 : (reg st4.data .rdx).toNat = level.queries := by
    rw [e4 hrdx4, Sym.eval, load_ofMachine (r := 1) (o := 16) rfl hlw.2.2]
    exact toNat_toUInt64 (by have := c.qs; unfold queryCap at this; omega)
  have hbx4 : (reg st4.data .rbx).toNat = mu m0 + level.logInvRate := by
    rw [e4 hrbx4]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [load_ofMachine (r := 0) (o := 40) rfl hl3.w40, show env4.regs .rbx = reg st3.data .rbx from rfl,
      hbx3, BitVec.toNat_add, toNat_toUInt64 (by have := c.rate; omega)]
    have := c.rate
    have h1 : (reg m0 .rcx).toNat < 64 := hmu
    show ((reg m0 .rcx).toNat + level.logInvRate) % 2 ^ 64 = (reg m0 .rcx).toNat + level.logInvRate
    omega
  have hk4 : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15], reg st4.data r = reg st3.data r :=
    fun r hr ↦ e4 (hkr4 r hr)
  have hl4 : Live level m0 st4.data folded :=
    hl3.keep hf4 hk4 (fun j _ ↦ by rw [hd4]) hfo
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b8Offset + (b8.take 2).length) := hpc4
  -- `b8`, the rest: `sample_queries(t, depth, count, &w.queries)`.
  let env5 := argEnv m0 st4.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b9Offset)).toBitVec
  have hwf5 : env5.WF := c.wf0 hf4.frame.kept
  refine exec_at (infix_of ((infix_drop b8 2).trans b8_in_code (by simp [b8])) (by simp [b8])
    hp) exit_b8b hwf5 (fun _ _ ↦ rfl) hpc4' (match_retS hf4) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hW5, hrdi5, hrsi5, hrcx5, hrbp5, hkr5⟩ := ok_b8b
  obtain ⟨hf5, hs5⟩ := c.blk hf4 hwf5 hm5 hmid5 (hi := 40) (by omega) (hW5.le (by decide))
  have e5 : ∀ {r : Reg64} {v : Sym}, (after (b8.drop 2) retS).reg r = some v →
      reg st5.data r = v.eval env5 := fun h ↦ hm5.regs _ _ h
  have ht5 : reg st5.data .rdi = tA m0 := (e5 hrdi5).trans ((hk4 .r12 (by simp)).trans
    ((hr3 .r12).trans ((hr2 .r12 (by simp [six])).trans hl.r12)))
  have hsi5 : (reg st5.data .rsi).toNat = mu m0 + level.logInvRate := by
    rw [e5 hrsi5]; exact hbx4
  have hdx5 : (reg st5.data .rdx).toNat = level.queries := by
    rw [e5 (hkr5 .rdx (by simp))]; exact hdx4
  have harg : env5.load 0 2680 8 = pA m0 :=
    load_ofMachine (r := 0) (o := 2680) rfl (c.arg_keep hf4.same)
  have hcx5 : reg st5.data .rcx = qA m0 := by
    rw [e5 hrcx5]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [harg]
  have hbp5 : reg st5.data .rbp = pA m0 := (e5 hrbp5).trans harg
  have hts5 := c.ts_frame (hi := 40) (by omega) (hm5.kept hwf5) hs5
    (show TStateAt st4.data.dmem (tA m0) a s2 by rw [hd4]; exact hts3)
  have hat5 := c.at_call (o := 32) (by omega) hf5
  have hle5 : 2672 - 32 + sampleQueriesStack ≤ finalLevelStack := by decide
  have hwt5 := c.whirT hat5 hf5.same hle5
  have hqo : WhirOut m0 (tA m0) a (qA m0) queryBufBytes finalLevelStack :=
    WL.whirOut_sub c.pout (o := 61352) (k := queryBufBytes) (by decide)
  have hpre5 : SampleQueriesPre a s2 st5.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show WhirT st5.data (reg st5.data .rdi) a sampleQueriesStack
      rw [ht5]; exact hwt5
    · show TStateAt st5.data.dmem (reg st5.data .rdi) a s2
      rw [ht5]; exact hts5
    · show (reg st5.data .rdx).toNat ≤ queryCap
      rw [hdx5]; exact c.qs
    · show WhirOut st5.data (reg st5.data .rdi) a (reg st5.data .rcx) queryBufBytes
        sampleQueriesStack
      rw [ht5, hcx5]; exact c.whirOut hat5 hle5 hqo
    · rw [ht5, hcx5]
      apply c.got_call hf5 (by omega) hle5 (by decide)
      intro ar har
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with (rfl | rfl | rfl) | har
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ (qA m0).toNat
          rw [c.qA_toNat]
          omega
        · change (qA m0).toNat + 1848 ≤ (pA m0).toNat + 63200
          rw [c.qA_toNat]
      · exact ⟨ar, by simp [har], le_rfl, le_rfl⟩
  refine call_then hpc5 (hsq a s2) hpre5 fun st6 hpc6 hrsp6 hq ↦ ?_
  obtain ⟨hok6, ⟨qs, s3, hres6, hbuf, hts6⟩, hch6, hsv6⟩ := hq
  rw [hsi5, hdx5] at hres6
  rw [hcx5] at hbuf
  rw [ht5] at hts6
  have hch6' : NativeRustcVm.SameOutside st5.data.dmem st6.data.dmem (fun q ↦
      (NativeRustcVm.InRange (qA m0) queryBufBytes q ∨
        NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st5.data sampleQueriesStack) sampleQueriesStack q) :=
    NativeRustcVm.SameOutside.mono hch6 fun q hq ↦ by
      rcases hq with hq | hq
      · left; rw [ht5, hcx5] at hq; exact two_iff.mp hq
      · exact Or.inr hq
  obtain ⟨hf6, hkeep6⟩ := c.call (o := 32) (by omega) hf5 hle5 hsv6 hrsp6
    (R := fun q ↦ NativeRustcVm.InRange (qA m0) queryBufBytes q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) (lo := 2624) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inl hq) hch6'
  have hcs6 : ∀ r, calleeSaved r = true → reg st6.data r = reg st5.data r := hsv6.1
  have hk56 : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15], reg st6.data r = reg st4.data r := fun r hr ↦
    (hcs6 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl)).trans
      (e5 (hkr5 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp)))
  have hl6 : Live level m0 st6.data folded :=
    hl4.step hwf5 hm5 (writesIn_of_mid hmid5) hW5 (by decide) hkeep6 (by omega) (by omega) hf6
      hk56 hfo
  have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b9Offset) := hpc6
  -- `b9`: `sample_queries`' `Some`.
  refine Eventually.bind (test_spec hp c b9_in_code rfl (b_eq.2.1 ▸ exit_b5) (b_eq.2.1 ▸ ok_b5)
    hf6 hpc6' hok6) fun st7 ⟨hr7, hd7, hpc7⟩ ↦ ?_
  have hpc7' : st7.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b10Offset) := hpc7
  refine cont st7 qs s3 hpc7' (hl6.keep (hf6.congr hr7 hd7) (fun r _ ↦ hr7 r) (fun j _ ↦ by rw [hd7])
    hfo) ((hr7 .rbp).trans ((hcs6 .rbp rfl).trans hbp5)) (by rw [hd7]; exact hbuf)
    (by rw [hd7]; exact hts6) ?_
  rw [hrun3, C2]; exact run_bind_some hres6

end

end NativeRustcVmX64.Whir.Levels.FL
