module

public import NativeRustcVmX64.Whir.NextLevel.Head
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# `next_level`: the out-of-domain sample (x86-64)

From `H7`: `b7` zeroes the out-of-domain point's buffer (`272` to `760`) and tests `μ ≤ 30` (R12,
the frame's word `80`); `b8` stores `μ` at `272` and calls `sample_challenges(t, sp + 280, μ)`;
`b9` calls `read_scalar(sp + 4440, t)`, `b10` tests its tag; `b11` keeps the value at `136`, `128`
and calls `grind(t, 17)`, `b12` tests it (`mid`, to `b13` with `H13`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

@[expose] public section

/-- At `b13`: the high part, the out-of-domain point (`272`, `280`) and value (`136`, `128`). -/
structure H13 [Labels] (a : DecArea) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (xs ood : Array EW) (v : EW) (s6 : TState)
    (d : MachineData) : Prop where
  K : K level w rounds m0 72 d
  regs : R0 level m0 d
  r12 : reg d .r12 = reg m0 .r9
  r15 : (reg d .r15).toNat = level.fold
  high : NativeRustcVm.EWsAt d.dmem (loc m0 176) xs.toList
  size : xs.size = level.fold
  oodN : NativeRustcVm.WordAt d.dmem (loc m0 272) (.ofBitVec (reg m0 .r9))
  oodp : NativeRustcVm.EWsAt d.dmem (loc m0 280) ood.toList
  osize : ood.size = (reg m0 .r9).toNat
  v0 : NativeRustcVm.WordAt d.dmem (loc m0 136) v.c0
  v1 : NativeRustcVm.WordAt d.dmem (loc m0 128) v.c1
  ts : TStateAt d.dmem (tA m0) a s6

end

public section

theorem sampleChallenges_size {n : Nat} {s s' : TState} {xs : Array EW}
    (h : (sampleChallenges n).run s = some (xs, s')) : xs.size = n := by
  have key : ∀ (l : List Nat) (acc : Array EW) (s s' : TState) (xs : Array EW),
      (l.foldlM (fun acc _ ↦ do pure (acc.push (← sampleChallenge))) acc : VM (Array EW)).run s =
        some (xs, s') → xs.size = acc.size + l.length := by
    intro l
    induction l with
    | nil =>
      intro acc s s' xs h
      simp only [List.foldlM_nil, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; simp
    | cons x l ih =>
      intro acc s s' xs h
      simp only [List.foldlM_cons, StateT.run_bind] at h
      cases hr : (sampleChallenge.run s) with
      | none => simp [hr] at h
      | some p =>
        simp only [hr] at h
        have := ih _ _ _ _ h
        simp at this ⊢
        omega
  have := key _ _ _ _ _ h
  simpa using this

theorem cMu_eval [Labels] (env : Env) {x : BitVec 64} (hx : env.load 0 80 8 = x)
    (h : x.toNat ≤ 30) : cMu.eval env = false := by
  simp only [cMu, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hx]
  exact not_hi (by simp; omega)

theorem cTag_eval [Labels] (env : Env) {u : UInt64} (hu : u = 0 ∨ u = 1)
    (h : env.load 0 4440 4 = BitVec.ofNat 64 u.toNat) : cTag.eval env = (u != 1) := by
  simp only [cTag, SBool.eval, Sym.eval, CmpOp.apply, h]
  rcases hu with rfl | rfl <;> decide

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- A body block in the frame alone, from `K` at RSP offset `72`, its writes `rs` below `8128`
off the word `80`: `K` at its end, the frame's other bytes kept. -/
theorem blk_step (c : Ctx a s level w rounds m0) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) (hp : Placed code k) {S : SState} {x : Exit}
    (hx : exec b retS = some (S, x)) {o' : Nat} (hmid : MidOk 8176 o' slots S = true)
    {rs : List (Nat × Nat)} (hW : Wr rs S) (hrs : ∀ p ∈ rs, 88 ≤ p.1 ∧ p.2 ≤ 8128 ∨ p.2 ≤ 80)
    {st : MachineState} (hK : K level w rounds m0 72 st.data) (hpc : st.pc = Host.addrOf (k + j))
    {ret : BitVec 64} (hret : ∀ l, x = .call l → ret = (Host.addrOf (k + j + b.length)).toBitVec)
    {R : MachineState → Prop}
    (cont : ∀ st', Match (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) ret) S st'.data →
      PcOk (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) ret) x (Host.addrOf (k + j + b.length)) st' →
      K level w rounds m0 o' st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange (fa m0) 8128) →
      (∀ {jj : Nat} {bs : List UInt8}, jj + bs.length ≤ 8192 →
        (∀ p ∈ rs, p.2 ≤ jj ∨ jj + bs.length ≤ p.1) →
        NativeRustcVm.BytesAt st.data.dmem (loc m0 jj) bs →
        NativeRustcVm.BytesAt st'.data.dmem (loc m0 jj) bs) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hwf := c.wf0 hK.fr.frame.kept (ret := ret)
  have hm : Match (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) ret) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hK.fr.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hx hwf hret hpc hm fun st' hm' hpc' ↦ ?_
  have hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 8128 := fun w hw ↦ by
    obtain ⟨h0, p, hp, -, h2⟩ := hW w hw
    rcases hrs p hp with h | h <;> exact ⟨h0, by omega⟩
  obtain ⟨hf', hs⟩ := c.blk hK.fr hwf hm' hmid (hi := 8128) le_rfl hw
  have hkeep : ∀ {jj : Nat} {bs : List UInt8}, jj + bs.length ≤ 8192 →
      (∀ p ∈ rs, p.2 ≤ jj ∨ jj + bs.length ≤ p.1) →
      NativeRustcVm.BytesAt st.data.dmem (loc m0 jj) bs →
      NativeRustcVm.BytesAt st'.data.dmem (loc m0 jj) bs :=
    fun h1 h2 h3 ↦ Ctx.bytes_blk hwf hm' (writesIn_of_mid hmid) hW h1 h2 h3
  refine cont st' hm' hpc' (c.K_frame hK hf' (by omega) hs (hkeep (by
    simp [NativeRustcVm.length_wordBytes]) (fun p hp ↦ ?_) hK.w80)) hs hkeep
  rw [NativeRustcVm.length_wordBytes]
  rcases hrs p hp with h | h
  · right; omega
  · left; exact h


/-- **The out-of-domain sample**: `b7` to `b12`, to `b13` with `H13`. -/
theorem mid (hp : Placed code k) (c : Ctx a s level w rounds m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {xs : Array EW} {s3 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b7Offset))
    (hH : H7 a level w rounds m0 xs s3 st.data)
    (hrun : runN level w rounds m0 s =
      tail3 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds xs s3) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s level w rounds m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b13Offset) ∧ ∃ ood v s6, runN level w rounds m0 s =
        tail6 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds xs ood v s6 ∧
        H13 a level w rounds m0 xs ood v s6 st'.data)) st := by
  have g := c.geo
  have hmu : (reg m0 .r9).toNat ≤ 30 := c.mu
  have hfold : level.fold ≤ 6 := c.fold
  have hxl : xs.toList.length = level.fold := by rw [Array.length_toList, hH.size]
  -- `b7`: the buffer zeroed, `μ ≤ 30`
  refine blk_step c b7_in_code (by simp [b7]) hp exit_b7 ok_b7.1 ok_b7.2.1
    (fun p hp ↦ by simp at hp; subst hp; left; omega) hH.K hpc (ret := 0) nofun
    fun st1 hm1 hpc1 hK1 hs1 hk1 ↦ ?_
  obtain ⟨-, -, hr12, hkr⟩ := ok_b7
  have h80 : (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) 0).load 0 80 8 = reg m0 .r9 :=
    load_ofMachine (o := 80) rfl hH.K.w80
  simp only [PcOk, cMu_eval _ h80 hmu, Bool.false_eq_true, ite_false] at hpc1
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b7Offset + b7.length = k + NativeRustcVmX64.Vm.NextLevel.b8Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b7_next]] at hpc1
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b7 retS).reg r = some v →
      reg st1.data r = v.eval (argEnv m0 st.data 8176 8 [] (fun _ ↦ 0) 0) :=
    fun h ↦ hm1.regs _ _ h
  have h12 : reg st1.data .r12 = reg m0 .r9 := (e1 hr12).trans h80
  have hk1r : ∀ r ∈ [Reg64.rbx, .rbp, .r13, .r14, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ e1 (hkr r hr)
  have hR1 : R0 level m0 st1.data :=
    ⟨(hk1r .rbx (by simp)).trans hH.regs.rbx, (hk1r .rbp (by simp)).trans hH.regs.rbp,
      (hk1r .r13 (by simp)).trans hH.regs.r13, (hk1r .r14 (by simp)).trans hH.regs.r14⟩
  have h15 : (reg st1.data .r15).toNat = level.fold := by rw [hk1r .r15 (by simp)]; exact hH.r15
  have hts1 := c.ts_frame (hi := 8128) (by omega) (hm1.kept (c.wf0 hH.K.fr.frame.kept)) hs1 hH.ts
  have hxb : (xs.toList.flatMap NativeRustcVm.ewBytes).length = 16 * level.fold := by
    rw [NativeRustcVm.length_ewsBytes, hxl]
  have hhigh1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 176) xs.toList :=
    hk1 (by rw [hxb]; omega) (fun p hp ↦ by simp at hp; subst hp; rw [hxb]; right; omega) hH.high
  -- `b8`: `sample_challenges`
  refine blk_step c b8_in_code (by simp [b8]) hp exit_b8 ok_b8.1 ok_b8.2.1
    (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl <;> omega) hK1 hpc1
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b9Offset)).toBitVec) (fun _ _ ↦ rfl) fun st2 hm2 hpc2 hK2 hs2 hk2 ↦ ?_
  obtain ⟨hmid8, hW8, h272, hrsi8, hrdi8, hrdx8, hkr8⟩ := ok_b8
  have e2 : ∀ {r : Reg64} {v : Sym}, (after b8 retS).reg r = some v →
      reg st2.data r = v.eval (argEnv m0 st1.data 8176 8 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b9Offset)).toBitVec) := fun h ↦ hm2.regs _ _ h
  have hk2r : ∀ r ∈ six, reg st2.data r = reg st1.data r := fun r hr ↦ e2 (hkr8 r hr)
  have ht2 : reg st2.data .rdi = tA m0 := (e2 hrdi8).trans hR1.r14
  have hsi2 : reg st2.data .rsi = loc m0 280 := (e2 hrsi8).trans (eval_ptr0A 280)
  have hdx2 : reg st2.data .rdx = reg m0 .r9 := (e2 hrdx8).trans h12
  have hw272 : NativeRustcVm.WordAt st2.data.dmem (loc m0 272) (.ofBitVec (reg m0 .r9)) := by
    have := wordAt_written hm2 (r := 0) (o := 272) rfl (by omega) h272 (w := .ofBitVec (reg m0 .r9))
      ((show (Sym.reg .r12).eval _ = reg st1.data .r12 from rfl).trans h12)
    exact this
  have hts2 := c.ts_frame (hi := 8128) (by omega) (hm2.kept (c.wf0 hK1.fr.frame.kept)) hs2 hts1
  have hhigh2 := hk2 (by rw [hxb]; omega) (fun p hp ↦ by
    simp at hp; rcases hp with rfl | rfl <;> rw [hxb] <;> omega) hhigh1
  have hat2 := c.at_call (o := 64) (by omega) hK2.fr
  have hle2 : 8176 - 64 + sampleChallengesStack ≤ nextLevelStack := by decide
  have hwt2 := c.whirT hat2 hK2.fr.same hle2
  have hpre2 : SampleChallengesPre a s3 st2.data := by
    refine ⟨hwt2.1, hwt2.2.1, ?_, ?_, ?_, ?_⟩
    · show TStateAt st2.data.dmem (reg st2.data .rdi) a s3
      rw [ht2]; exact hts2
    · show TStateOk st2.data (reg st2.data .rdi) a sampleChallengesStack
      rw [ht2]; exact hwt2.2.2.2.1
    · show OutOk st2.data (reg st2.data .rdi) a (reg st2.data .rsi)
        (16 * (reg st2.data .rdx).toNat) sampleChallengesStack
      rw [ht2, hsi2, hdx2]
      exact c.outLoc (by omega) hK2.fr hle2 (by omega) (by omega)
    · rw [ht2, hsi2, hdx2]
      apply c.got_call hK2.fr (by omega) hle2 (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_loc (by omega) (by have := c.mu; unfold stackCap at this; omega)
      · exact c.got_rc
  refine call_then hpc2 (hsc a s3) hpre2 fun st3 hpc3 hrsp3 hq ↦ ?_
  obtain ⟨⟨ood, s4, hres4, hood, hts4⟩, hch3, hsv3⟩ := hq
  rw [hdx2] at hres4 hch3
  rw [hsi2] at hood hch3
  rw [ht2] at hts4 hch3
  obtain ⟨hK3, hkeep3⟩ := c.K_call hK2 hle2 hsv3 hrsp3
    (R := fun q ↦ NativeRustcVm.InRange (loc m0 280) (16 * (reg m0 .r9).toNat) q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) (lo := 280) (n := 16 * (reg m0 .r9).toNat)
    (by omega) (by omega) (fun q hq ↦ hq.elim (fun h ↦ Or.inr (Or.inl h)) Or.inl)
    (NativeRustcVm.SameOutside.mono hch3 fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq)
  have hcs3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st2.data r := hsv3.1
  have hosz := sampleChallenges_size hres4
  have hob : (ood.toList.flatMap NativeRustcVm.ewBytes).length = 16 * (reg m0 .r9).toNat := by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hosz]
  have hhigh3 := bytes_call hkeep3 (j := 176) (by omega) (by rw [hxb]; omega)
    (Or.inl (by rw [hxb]; omega)) hhigh2
  have h272' := bytes_call hkeep3 (j := 272) (by omega) (by simp [NativeRustcVm.length_wordBytes])
    (Or.inl (by simp [NativeRustcVm.length_wordBytes])) hw272
  have hR3 : R0 level m0 st3.data :=
    (hR1.saved fun r hr ↦ hk2r r (cs_six hr)).saved hcs3
  have h12' : reg st3.data .r12 = reg m0 .r9 := by
    rw [hcs3 .r12 rfl, hk2r .r12 (by simp [six])]; exact h12
  have h15' : (reg st3.data .r15).toNat = level.fold := by
    rw [hcs3 .r15 rfl, hk2r .r15 (by simp [six])]; exact h15
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b8Offset + b8.length = k + NativeRustcVmX64.Vm.NextLevel.b9Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b8_next]] at hpc3
  -- `b9`: `read_scalar`
  refine blk_step c b9_in_code (by simp [b9]) hp exit_b9 ok_b9.1 ok_b9.2.1
    (fun p hp ↦ by simp at hp; subst hp; right; omega) hK3 hpc3
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b10Offset)).toBitVec) (fun _ _ ↦ rfl) fun st4 hm4 hpc4 hK4 hs4 hk4 ↦ ?_
  obtain ⟨hmid9, hW9, hrdi9, hrsi9, hkr9⟩ := ok_b9
  have e4 : ∀ {r : Reg64} {v : Sym}, (after b9 retS).reg r = some v →
      reg st4.data r = v.eval (argEnv m0 st3.data 8176 8 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b10Offset)).toBitVec) := fun h ↦ hm4.regs _ _ h
  have hk4r : ∀ r ∈ six, reg st4.data r = reg st3.data r := fun r hr ↦ e4 (hkr9 r hr)
  have ht4 : reg st4.data .rsi = tA m0 := (e4 hrsi9).trans hR3.r14
  have ho4 : reg st4.data .rdi = loc m0 4440 := (e4 hrdi9).trans (eval_ptr0A 4440)
  have hts4' := c.ts_frame (hi := 8128) (by omega) (hm4.kept (c.wf0 hK3.fr.frame.kept)) hs4 hts4
  have hhigh4 := hk4 (by rw [hxb]; omega) (fun p hp ↦ by simp at hp; subst hp; left; omega) hhigh3
  have h2724 := hk4 (by simp [NativeRustcVm.length_wordBytes])
    (fun p hp ↦ by simp at hp; subst hp; left; omega) h272'
  have hood4 := hk4 (by rw [hob]; omega) (fun p hp ↦ by simp at hp; subst hp; left; omega) hood
  have hat4 := c.at_call (o := 64) (by omega) hK4.fr
  have hle4 : 8176 - 64 + readScalarStack ≤ nextLevelStack := by decide
  have hwt4 := c.whirT hat4 hK4.fr.same hle4
  have hpre4 : ReadScalarPre a s4 st4.data := by
    refine ⟨hwt4.1, hwt4.2.1, ?_, ?_, ?_, ?_⟩
    · show TStateAt st4.data.dmem (reg st4.data .rsi) a s4
      rw [ht4]; exact hts4'
    · show TStateOk st4.data (reg st4.data .rsi) a readScalarStack
      rw [ht4]; exact hwt4.2.2.2.1
    · show OutOk st4.data (reg st4.data .rsi) a (reg st4.data .rdi) 24 readScalarStack
      rw [ht4, ho4]
      exact c.outLoc (by omega) hK4.fr hle4 (by omega) (by omega)
    · rw [ht4, ho4]
      apply c.got_call hK4.fr (by omega) hle4 (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_rc
  refine call_then hpc4 (hrsc a s4) hpre4 fun st5 hpc5 hrsp5 hq ↦ ?_
  obtain ⟨hopt, hnext5, hch5, hsv5⟩ := hq
  rw [ho4] at hopt hch5
  rw [ht4] at hnext5 hch5
  obtain ⟨hK5, hkeep5⟩ := c.K_call hK4 hle4 hsv5 hrsp5
    (R := fun q ↦ NativeRustcVm.InRange (loc m0 4440) 24 q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) (lo := 4440) (n := 24)
    (by omega) (by omega) (fun q hq ↦ hq.elim (fun h ↦ Or.inr (Or.inl h)) Or.inl)
    (NativeRustcVm.SameOutside.mono hch5 fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq)
  have hcs5 : ∀ r, calleeSaved r = true → reg st5.data r = reg st4.data r := hsv5.1
  have hhigh5 := bytes_call hkeep5 (j := 176) (by omega) (by rw [hxb]; omega)
    (Or.inl (by rw [hxb]; omega)) hhigh4
  have h2725 := bytes_call hkeep5 (j := 272) (by omega) (by simp [NativeRustcVm.length_wordBytes])
    (Or.inl (by simp [NativeRustcVm.length_wordBytes])) h2724
  have hood5 := bytes_call hkeep5 (j := 280) (by omega) (by rw [hob]; omega)
    (Or.inl (by rw [hob]; omega)) hood4
  have hR5 : R0 level m0 st5.data := (hR3.saved fun r hr ↦ hk4r r (cs_six hr)).saved hcs5
  have h12'' : reg st5.data .r12 = reg m0 .r9 := by
    rw [hcs5 .r12 rfl, hk4r .r12 (by simp [six])]; exact h12'
  have h15'' : (reg st5.data .r15).toNat = level.fold := by
    rw [hcs5 .r15 rfl, hk4r .r15 (by simp [six])]; exact h15'
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b9Offset + b9.length = k + NativeRustcVmX64.Vm.NextLevel.b10Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b9_next]] at hpc5
  -- `b10`: the tag
  refine Eventually.bind (cond_spec hp c b10_in_code (by simp [b10]) exit_b10 ok_b10 hK5 hpc5)
    fun st6 ⟨hr6, hd6, hpc6⟩ ↦ ?_
  have hK6 := hK5.congr hr6 hd6
  have hrun' : runN level w rounds m0 s = tail4 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w
      rounds xs ood s4 := by rw [hrun, tail3, hres4]; rfl
  rcases hres5 : readScalar.run s4 with _ | ⟨v, s5⟩
  · rw [hres5] at hopt
    have h4 : (argEnv m0 st5.data 8176 8 [] (fun _ ↦ 0) 0).load 0 4440 4 =
        BitVec.ofNat 64 (0 : UInt64).toNat := load4_of_tag (Or.inl rfl) hopt
    simp only [cTag_eval _ (Or.inl rfl) h4] at hpc6
    exact Eventually.mono (none13 hp c hK6.fr (hpc6.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_13_at))
      (by rw [hrun', tail4, hres5]; rfl)) fun _ h ↦ Or.inl h
  rw [hres5] at hopt
  obtain ⟨hopt1, hopt2⟩ := hopt
  have h4 : (argEnv m0 st5.data 8176 8 [] (fun _ ↦ 0) 0).load 0 4440 4 =
      BitVec.ofNat 64 (1 : UInt64).toNat := load4_of_tag (Or.inr rfl) hopt1
  simp only [cTag_eval _ (Or.inr rfl) h4] at hpc6
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b10Offset + b10.length = k + NativeRustcVmX64.Vm.NextLevel.b11Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b10_next]] at hpc6
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at hpc6
  obtain ⟨hv0, hv1⟩ := ewAt_iff.mp hopt2
  rw [off_off] at hv0
  rw [off_off, off_off] at hv1
  rw [show (4440 + 8 : Nat) = 4448 from rfl] at hv0
  rw [show (4440 + 8 + 8 : Nat) = 4456 from rfl] at hv1
  have hv0' : NativeRustcVm.WordAt st6.data.dmem (loc m0 4448) v.c0 := by rw [hd6]; exact hv0
  have hv1' : NativeRustcVm.WordAt st6.data.dmem (loc m0 4456) v.c1 := by rw [hd6]; exact hv1
  have hR6 : R0 level m0 st6.data := hR5.congr hr6
  -- `b11`: the value kept, `grind(t, 17)`
  refine blk_step c b11_in_code (by simp [b11]) hp exit_b11 ok_b11.1 ok_b11.2.1
    (fun p hp ↦ by simp at hp; rcases hp with rfl | rfl <;> omega) hK6 hpc6
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b12Offset)).toBitVec) (fun _ _ ↦ rfl) fun st7 hm7 hpc7 hK7 hs7 hk7 ↦ ?_
  obtain ⟨hmid11, hW11, hw128, hw136, hrdi11, hrsi11, hkr11⟩ := ok_b11
  let env7 := argEnv m0 st6.data 8176 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b12Offset)).toBitVec
  have e7 : ∀ {r : Reg64} {v : Sym}, (after b11 retS).reg r = some v →
      reg st7.data r = v.eval env7 := fun h ↦ hm7.regs _ _ h
  have hk7r : ∀ r ∈ six, reg st7.data r = reg st6.data r := fun r hr ↦ e7 (hkr11 r hr)
  have ht7 : reg st7.data .rdi = tA m0 := (e7 hrdi11).trans hR6.r14
  have hbits7 : grindBits st7.data = Whir.queryGrindingBits := by
    unfold grindBits; rw [e7 hrsi11]; rfl
  have hc1 : NativeRustcVm.WordAt st7.data.dmem (loc m0 128) v.c1 :=
    wordAt_written hm7 (r := 0) (o := 128) rfl (by omega) hw128
      (load_ofMachine (o := 4456) rfl hv1')
  have hc0 : NativeRustcVm.WordAt st7.data.dmem (loc m0 136) v.c0 :=
    wordAt_written hm7 (r := 0) (o := 136) rfl (by omega) hw136
      (load_ofMachine (o := 4448) rfl hv0')
  have hts7 := c.ts_frame (d := st6.data.dmem) (hi := 8128) (by omega)
    (hm7.kept (c.wf0 hK6.fr.frame.kept)) hs7
    (by rw [hd6]; exact hnext5 v s5 hres5)
  have hhigh7 := hk7 (jj := 176) (by rw [hxb]; omega) (fun p hp ↦ by
    simp at hp; rcases hp with rfl | rfl <;> rw [hxb] <;> omega) (by rw [hd6]; exact hhigh5)
  have h2727 := hk7 (jj := 272) (bs := NativeRustcVm.wordBytes (.ofBitVec (reg m0 .r9)))
    (by rw [NativeRustcVm.length_wordBytes]; omega) (fun p hp ↦ by
    simp at hp; rcases hp with rfl | rfl <;> rw [NativeRustcVm.length_wordBytes] <;> omega)
    (by rw [hd6]; exact h2725)
  have hood7 := hk7 (jj := 280) (by rw [hob]; omega) (fun p hp ↦ by
    simp at hp; rcases hp with rfl | rfl <;> rw [hob] <;> omega) (by rw [hd6]; exact hood5)
  have hat7 := c.at_call (o := 64) (by omega) hK7.fr
  have hle7 : 8176 - 64 + grindStack ≤ nextLevelStack := by decide
  have hwt7 := c.whirT hat7 hK7.fr.same hle7
  have hpre7 : GrindPre a s5 st7.data := by
    refine ⟨hwt7.1, hwt7.2.1, ?_, ?_, ?_, ?_⟩
    · show TStateAt st7.data.dmem (reg st7.data .rdi) a s5
      rw [ht7]; exact hts7
    · show TStateOk st7.data (reg st7.data .rdi) a grindStack
      rw [ht7]; exact hwt7.2.2.2.1
    · rw [hbits7]; decide
    · rw [ht7]
      apply c.got_call hK7.fr (by omega) hle7 (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_rc
  refine call_then hpc7 (hgr a s5) hpre7 fun st8 hpc8 hrsp8 hq ↦ ?_
  obtain ⟨hok8, hnext8, hch8, hsv8⟩ := hq
  rw [hbits7] at hok8 hnext8
  rw [ht7] at hnext8 hch8
  obtain ⟨hK8, hkeep8⟩ := c.K_call hK7 hle7 hsv8 hrsp8
    (R := NativeRustcVm.InRange (tA m0) tstateBytes) (lo := 8128) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inl hq) hch8
  have hcs8 : ∀ r, calleeSaved r = true → reg st8.data r = reg st7.data r := hsv8.1
  rw [show k + NativeRustcVmX64.Vm.NextLevel.b11Offset + b11.length = k + NativeRustcVmX64.Vm.NextLevel.b12Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.NextLevel.b11_next]] at hpc8
  refine Eventually.bind (test_spec hp c b12_in_code rfl (b_eq.2.1 ▸ exit_b4) (b_eq.2.1 ▸ ok_b4)
    hK8 hpc8 hok8) fun st9 ⟨hr9, hd9, hpc9⟩ ↦ ?_
  have hK9 := hK8.congr hr9 hd9
  have hrun'' : runN level w rounds m0 s = (((grind Whir.queryGrindingBits).run s5).bind fun p6 ↦
      tail6 (reg m0 .rsi).toNat (reg m0 .r9).toNat level w rounds xs ood v p6.2) := by
    rw [hrun', tail4, hres5]; rfl
  rcases hres8 : (grind Whir.queryGrindingBits).run s5 with _ | ⟨⟨⟩, s6⟩
  · rw [hres8] at hpc9
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at hpc9
    exact Eventually.mono (none13 hp c hK9.fr (hpc9.trans (hp.label NativeRustcVmX64.Vm.NextLevel.label_13_at))
      (by rw [hrun'', hres8]; rfl)) fun _ h ↦ Or.inl h
  rw [hres8] at hpc9
  simp only [Option.isSome_some, ite_true] at hpc9
  have hcs : ∀ r ∈ six, reg st9.data r = reg st6.data r := fun r hr ↦ by
    rw [hr9, hcs8 r (six_cs hr), hk7r r hr]
  have kb : ∀ {jj : Nat} {bs : List UInt8}, 72 ≤ jj → jj + bs.length ≤ 8128 →
      NativeRustcVm.BytesAt st7.data.dmem (loc m0 jj) bs →
      NativeRustcVm.BytesAt st9.data.dmem (loc m0 jj) bs := fun h1 h2 h3 ↦ by
    rw [hd9]; exact bytes_call hkeep8 h1 (by omega) (Or.inl h2) h3
  refine .done _ (Or.inr ⟨hpc9, ood, v, s6, by rw [hrun'', hres8]; rfl, hK9,
    ⟨(hcs .rbx (by simp [six])).trans hR6.rbx, (hcs .rbp (by simp [six])).trans hR6.rbp,
      (hcs .r13 (by simp [six])).trans hR6.r13, (hcs .r14 (by simp [six])).trans hR6.r14⟩,
    by rw [hcs .r12 (by simp [six]), hr6]; exact h12'',
    by rw [hcs .r15 (by simp [six]), hr6]; exact h15'',
    kb (by omega) (by rw [hxb]; omega) hhigh7, hH.size,
    kb (by omega) (by simp [NativeRustcVm.length_wordBytes]) h2727,
    kb (by omega) (by rw [hob]; omega) hood7, hosz,
    kb (by omega) (by simp [NativeRustcVm.length_wordBytes]) hc0,
    kb (by omega) (by simp [NativeRustcVm.length_wordBytes]) hc1,
    by rw [hd9]; exact hnext8 () s6 hres8⟩)

end

end NativeRustcVmX64.Whir.Levels.NL
