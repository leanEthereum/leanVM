module

public import NativeRustcVmX64.Whir.FinalLevel.Check
public import NativeRustcVm.Top.Phases
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names

/-!
# `final_level`: the last sumcheck (x86-64)

From `b14` (`Live`): the tail's buffer zeroed (`1120` to `1600`), `μ ≤ 30` (RAX); the claim
loaded from the state `w` and `sumcheck_plain(&out, t, claim, 3, tail)` with the tail's length `μ`
pushed (`b15`), into the frame's `Option<EW>` at `144` and the tail at `1120`; its tag tested
(`b16`, `None` to `NativeRustcVmX64.Vm.FinalLevel.label_5`): `sum`, to `b17` with `Core`. `Core` keeps what the end reads:
the frame, `μ` at `40`, `2 ^ μ` (R14), the folded scalars.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

@[expose] public section

/-- **After the last sumcheck**: the frame, `μ` at `40`, `2 ^ μ` (R14), the folded scalars. -/
structure Core (level : Whir.Level) (m0 d : MachineData) (folded : Array EW) : Prop where
  fr : Fr m0 40 d
  w40 : NativeRustcVm.WordAt d.dmem (loc m0 40) (.ofBitVec (reg m0 .rcx))
  r14 : (reg d .r14).toNat = 2 ^ mu m0
  size : folded.size = 2 ^ mu m0 + level.fold
  fold : NativeRustcVm.EWsAt d.dmem (loc m0 1600) folded.toList

end

public section

theorem Live.core {level : Whir.Level} {m0 d : MachineData} {folded : Array EW}
    (h : Live level m0 d folded) : Core level m0 d folded :=
  ⟨h.fr, h.w40, h.r14, h.size, h.fold⟩

/-- `Core` kept: the frame, R14 and the frame's bytes `40` to `48` and `1600` to `2624`. -/
theorem Core.keep {level : Whir.Level} {m0 d d' : MachineData} {folded : Array EW}
    (h : Core level m0 d folded) (hf : Fr m0 40 d') (hr : reg d' .r14 = reg d .r14)
    (hk : ∀ j, (40 ≤ j ∧ j < 48) ∨ (1600 ≤ j ∧ j < 2624) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j)) (h64 : 2 ^ mu m0 + level.fold ≤ 64) :
    Core level m0 d' folded where
  fr := hf
  w40 := bytes_keep (fun i hi ↦ hk _ (Or.inl (by rw [NativeRustcVm.length_wordBytes] at hi; omega)))
    h.w40
  r14 := by rw [hr]; exact h.r14
  size := h.size
  fold := bytes_keep (fun i hi ↦ hk _ (Or.inr (by
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, h.size] at hi; omega))) h.fold

/-- `Core` across a block and a call (as `Live.step`). -/
theorem Core.step [Labels] {level : Whir.Level} {m0 d d1 d' : MachineData} {folded : Array EW}
    (h : Core level m0 d folded) {rest : List (BitVec 64 × Nat)} {S : SState} {ret : BitVec 64}
    (hwf : (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret) S d1)
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S)
    (hrs : ∀ p ∈ rs, p.2 ≤ 40 ∨ (48 ≤ p.1 ∧ p.2 ≤ 1600) ∨ 2624 ≤ p.1)
    {o lo n : Nat} (hkeep : ∀ j, o + 8 ≤ j → j < 2688 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d1.dmem.get? (loc m0 j)) (ho : o ≤ 32)
    (hlo : 48 ≤ lo ∧ lo + n ≤ 1600 ∨ 2624 ≤ lo) (hf : Fr m0 40 d')
    (hr : reg d' .r14 = reg d .r14) (h64 : 2 ^ mu m0 + level.fold ≤ 64) :
    Core level m0 d' folded :=
  h.keep hf hr (fun j hj ↦ by
    rw [hkeep j (by omega) (by omega) (by omega)]
    refine get_blk hwf hm hin hW (by omega) fun p hp ↦ ?_
    rcases hrs p hp with h' | h' | h' <;> omega) h64

theorem sumcheckPlain_size {claim : EW} {count n : Nat} {s s' : TState} {xs : Array EW} {c : EW}
    (h : (sumcheckPlain claim count n).run s = some ((xs, c), s')) : xs.size = n := by
  have := (NativeRustcVm.Top.sumcheck_size claim count (Array.replicate n none)).gives s _ s' h
  simpa using this

theorem cMu30_eval [Labels] (env : Env) {x : BitVec 64} (hx : env.load 0 40 8 = x)
    (h : x.toNat ≤ 30) : cMu30.eval env = false := by
  simp only [cMu30, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hx]
  exact not_hi (by simp; omega)

theorem cTag144_eval [Labels] (env : Env) {u : UInt64} (hu : u = 0 ∨ u = 1)
    (h : env.load 0 144 4 = BitVec.ofNat 64 u.toNat) : cTag144.eval env = (u != 1) := by
  simp only [cTag144, SBool.eval, Sym.eval, CmpOp.apply, h]
  rcases hu with rfl | rfl <;> decide

/-- A sumcheck's output, by cases (its type never reduces the result). -/
theorem sumcheckOut_cases [Labels] {d : Mem 64} {t : BitVec 64} {a : DecArea}
    {out slots : BitVec 64} {r : Option ((Array EW × EW) × TState)}
    (h : SumcheckOut d t a out slots r) :
    (r = none → NativeRustcVm.WordAt d out 0) ∧
      ∀ xs c s', r = some ((xs, c), s') →
        NativeRustcVm.WordAt d out 1 ∧ NativeRustcVm.EWAt d (off out 8) c ∧
          NativeRustcVm.EWsAt d slots xs.toList ∧ TStateAt d t a s' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hr ↦ ?_, fun xs c s' hr ↦ ?_⟩
  · subst hr; exact h1
  · subst hr; exact ⟨h1.1, h1.2, h2 xs c s' rfl, h3 _ s' rfl⟩

theorem ewAt_iff' {d : Mem 64} {p : BitVec 64} {x : EW} :
    NativeRustcVm.EWAt d p x ↔ NativeRustcVm.WordAt d p x.c0 ∧ NativeRustcVm.WordAt d (off p 8) x.c1 :=
  ewAt_iff

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The last sumcheck**: `b14`, `b15`, `sumcheck_plain`, `b16`, to `b17`. -/
theorem sum (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    {st : MachineState} {folded : Array EW} {s4 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b14Offset)) (hl : Live level m0 st.data folded)
    (hts : TStateAt st.data.dmem (tA m0) a s4)
    (hrun : runF level b w rounds m0 s = (C5 (mu m0) (reg m0 .r8).toNat b w folded).run s4)
    (cont : ∀ (st' : MachineState) (tail : Array EW) (claim : EW) (s5 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b17Offset) → Core level m0 st'.data folded → reg st'.data .rbx = pA m0 →
      NativeRustcVm.WordAt st'.data.dmem (loc m0 48) (.ofBitVec (reg m0 .r8)) →
      NativeRustcVm.WordAt st'.data.dmem (loc m0 56) (.ofBitVec (reg m0 .r9)) →
      tail.size = mu m0 → NativeRustcVm.EWsAt st'.data.dmem (loc m0 1120) tail.toList →
      NativeRustcVm.EWAt st'.data.dmem (loc m0 152) claim →
      TStateAt st'.data.dmem (tA m0) a s5 →
      runF level b w rounds m0 s = (C6 (mu m0) (reg m0 .r8).toNat b w folded (tail, claim)).run s5 →
      Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hmu6 : mu m0 ≤ 6 := by
    by_contra hc
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ mu m0 by omega)
    have : (2 : Nat) ^ 7 = 128 := rfl
    omega
  have hmu6' : (reg m0 .rcx).toNat ≤ 6 := hmu6
  -- `b14`: the tail zeroed, `μ ≤ 30`.
  let env1 := argEnv m0 st.data 2672 8 [] (fun _ ↦ 0) 0
  have hwf1 : env1.WF := c.wf0 hl.fr.frame.kept
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf1 nofun hpc
    (match_retS hl.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, hrax1, hkr1⟩ := ok_b14
  obtain ⟨hf1, hs1⟩ := c.blk hl.fr hwf1 hm1 hmid1 (hi := 1600) (by omega) (hW1.le (by decide))
  have h40 : env1.load 0 40 8 = reg m0 .rcx := load_ofMachine (r := 0) (o := 40) rfl hl.w40
  simp only [PcOk, cMu30_eval env1 h40 (by show mu m0 ≤ 30; omega), Bool.false_eq_true,
    ite_false] at hpc1
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b15Offset) := hpc1
  have hk1 : ∀ r ∈ six, reg st1.data r = reg st.data r := fun r hr ↦ hm1.regs r _ (hkr1 r hr)
  have hax1 : reg st1.data .rax = reg m0 .rcx := (hm1.regs .rax _ hrax1).trans h40
  have hl1 : Live level m0 st1.data folded :=
    hl.keep hf1 (fun r hr ↦ hk1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp [six]))
      (fun j hj ↦ get_blk hwf1 hm1 (writesIn_of_mid hmid1) hW1 (by omega) fun p hp ↦ by
        simp at hp; subst hp; omega) hfo
  have hts1 := c.ts_frame (hi := 1600) (by omega) (hm1.kept hwf1) hs1 hts
  -- `b15`: `sumcheck_plain(&out, t, claim, 3, tail)`.
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b16Offset)).toBitVec
  let env2 := argEnv m0 st1.data 2672 8 [(pA m0, 63200)] (fun _ ↦ 0) ret
  have hwf2 : env2.WF :=
    c.wf1 hf1.frame.kept (show NativeRustcVm.Mapped st1.data.dmem (pA m0) 63200 from
      Mapped.keeps c.pout.1.1 hf1.frame.kept) g.pW
      (g.pS.imp_left fun h ↦ Nat.le_trans h (Nat.sub_le_sub_left (by decide) _))
  have h2680 : env2.load 0 2680 8 = pA m0 :=
    load_ofMachine (r := 0) (o := 2680) rfl (c.arg_keep hf1.same)
  have hm2 : Match env2 rowsS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hf1.frame, trivial⟩ trivial trivial
      ⟨h2680.trans (eval_ptr rfl).symm, trivial⟩
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf2 (fun _ _ ↦ rfl) hpc1'
    hm2 fun st2 hm2' hpc2 ↦ ?_
  obtain ⟨hmid2, hW2, h24, hrdi2, hrsi2, hrdx2, hrcx2, hr82, hr92, hrbx2, hkr2⟩ := ok_b15
  have e2 : ∀ {r : Reg64} {v : Sym}, (after b15 rowsS).reg r = some v →
      reg st2.data r = v.eval env2 := fun h ↦ hm2'.regs _ _ h
  obtain ⟨hf2, hs2⟩ := c.blk hf1 hwf2 hm2' hmid2 (hi := 32) (by omega) (hW2.le (by decide))
  have hcl := (c.whir_at hf1.same).1.claim
  obtain ⟨hc0, hc1⟩ := ewAt_iff'.mp hcl
  have hdi2 : reg st2.data .rdi = loc m0 144 := (e2 hrdi2).trans (eval_ptr0A 144)
  have hsi2 : reg st2.data .rsi = tA m0 :=
    (e2 hrsi2).trans ((hk1 .r12 (by simp [six])).trans hl.r12)
  have hcl2 : claimArg st2.data = w.claim := by
    have e0 : reg st2.data .rdx = w.claim.c0.toBitVec :=
      (e2 hrdx2).trans (load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hc0))
    have e1 : reg st2.data .rcx = w.claim.c1.toBitVec :=
      (e2 hrcx2).trans (load_ofMachine (r := 1) (o := 8) rfl hc1)
    show (⟨.ofBitVec (reg st2.data .rdx), .ofBitVec (reg st2.data .rcx)⟩ : EW) = _
    rw [e0, e1]
  have h82 : (reg st2.data .r8).toNat = 3 := by rw [e2 hr82]; rfl
  have h92 : reg st2.data .r9 = loc m0 1120 := (e2 hr92).trans (eval_ptr0A 1120)
  have w24 : NativeRustcVm.WordAt st2.data.dmem (loc m0 24) (.ofBitVec (reg m0 .rcx)) :=
    wordAt_written hm2' (r := 0) (o := 24) rfl (by omega) h24 hax1
  have hsp2 : rspOf st2.data = loc m0 16 := hf2.frame.sp
  have a0 : stackArg st2.data 0 = reg m0 .rcx := stackArg_loc hsp2 0 w24
  have hk2 : ∀ r ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg st2.data r = reg st1.data r :=
    fun r hr ↦ e2 (hkr2 r hr)
  have hts2 := c.ts_frame (hi := 32) (by omega) (hm2'.kept hwf2) hs2 hts1
  have hat := c.at_call (o := 16) (by omega) hf2
  have hle : 2672 - 16 + sumcheckPlainStack ≤ finalLevelStack := by decide
  have hwt := c.whirT hat hf2.same hle
  have hpre : SumcheckPlainPre a s4 st2.data := by
    refine ⟨c.argsOk (by omega) hf2, hwt.1, hwt.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show TStateAt st2.data.dmem (reg st2.data .rsi) a s4
      rw [hsi2]; exact hts2
    · show TStateOk st2.data (reg st2.data .rsi) a sumcheckPlainStack
      rw [hsi2]; exact hwt.2.2.2.1
    · rw [h82]; decide
    · rw [h82]; decide
    · show OutOk st2.data (reg st2.data .rsi) a (reg st2.data .rdi) 24 sumcheckPlainStack
      rw [hsi2, hdi2]; exact c.outLoc (o := 16) (by omega) hf2 hle (by omega) (by omega)
    · show OutOk st2.data (reg st2.data .rsi) a (reg st2.data .r9)
        (16 * (stackArg st2.data 0).toNat) sumcheckPlainStack
      rw [hsi2, h92, a0]; exact c.outLoc (o := 16) (by omega) hf2 hle (by omega) (by omega)
    · show NativeRustcVm.Apart (reg st2.data .rdi) 24 (reg st2.data .r9)
        (16 * (stackArg st2.data 0).toNat)
      rw [hdi2, h92, a0]
      unfold NativeRustcVm.Apart
      rw [c.loc_toNat (by omega), c.loc_toNat (by omega)]
      omega
    · rw [hsi2, hdi2, h92, a0]
      apply c.got_call hf2 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_rc
  refine call_then hpc2 (hsc a s4) hpre fun st3 hpc3 hrsp3 hq ↦ ?_
  have hopt := sumcheckOut_cases hq.1
  have hch := hq.2.1
  have hsv := hq.2.2
  simp only [hdi2, hsi2, h92, a0, hcl2, h82] at hopt hch
  have hch' : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem (fun q ↦
      (NativeRustcVm.InRange (loc m0 144) 24 q ∨ NativeRustcVm.InRange (loc m0 1120) 480 q ∨
        NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st2.data sumcheckPlainStack) sumcheckPlainStack q) :=
    NativeRustcVm.SameOutside.mono hch fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact Or.inl (Or.inl hq)
      · refine Or.inl (Or.inr (Or.inl ?_))
        have hq' : NativeRustcVm.InRange (loc m0 1120) (16 * (reg m0 .rcx).toNat) q := hq
        rw [c.inLc (by omega) (by omega)] at hq' ⊢
        omega
      · exact Or.inl (Or.inr (Or.inr hq))
      · exact Or.inr hq
  obtain ⟨hf3, hkeep3⟩ := c.call (o := 16) (by omega) hf2 hle hsv hrsp3
    (R := fun q ↦ NativeRustcVm.InRange (loc m0 144) 24 q ∨
      NativeRustcVm.InRange (loc m0 1120) 480 q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q)
    (lo := 144) (n := 1456) (by omega) (by omega)
    (fun q hq ↦ by
      rcases hq with hq | hq | hq
      · refine Or.inr ?_
        rw [c.inLc (by omega) (by omega)] at hq ⊢
        omega
      · refine Or.inr ?_
        rw [c.inLc (by omega) (by omega)] at hq ⊢
        omega
      · exact Or.inl (Or.inr hq)) hch'
  have hcs3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st2.data r := hsv.1
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b16Offset) := hpc3
  -- `b16`: the sumcheck's tag.
  have hwf3 := c.wf0 hf3.frame.kept (ret := 0)
  have hm3 : Match (argEnv m0 st3.data 2672 8 []) s24S st3.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf3.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) exit_b16 hwf3 nofun hpc3' hm3
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hkr4⟩ := ok_b16
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hf4 : Fr m0 40 st4.data :=
    ⟨Frame.of_blockA hf3.frame hwf3 hm4 hmid4 slots_le, by rw [Sm, hd4]; exact hf3.same⟩
  have hr14 : reg st4.data .r14 = reg st.data .r14 :=
    ((hm4.regs .r14 _ (hkr4 .r14 (List.mem_filter.mpr ⟨mem_allRegs _, rfl⟩))).trans
      (hcs3 .r14 rfl)).trans ((hk2 .r14 (by simp)).trans (hk1 .r14 (by simp [six])))
  have hbx4 : reg st4.data .rbx = pA m0 :=
    ((hm4.regs .rbx _ (hkr4 .rbx (List.mem_filter.mpr ⟨mem_allRegs _, rfl⟩))).trans
      (hcs3 .rbx rfl)).trans ((e2 hrbx2).trans h2680)
  have hc4 : Core level m0 st4.data folded :=
    hl.core.keep hf4 hr14 (fun j hj ↦ by
      rw [hd4, hkeep3 j (by omega) (by omega) (by omega),
        get_blk hwf2 hm2' (writesIn_of_mid hmid2) hW2 (by omega) fun p hp ↦ by
          simp at hp; subst hp; omega,
        get_blk hwf1 hm1 (writesIn_of_mid hmid1) hW1 (by omega) fun p hp ↦ by
          simp at hp; subst hp; omega]) hfo
  have hw48 : NativeRustcVm.WordAt st4.data.dmem (loc m0 48) (.ofBitVec (reg m0 .r8)) := by
    rw [hd4]
    refine bytes_call hkeep3 (j := 48) (by omega) (by simp [NativeRustcVm.length_wordBytes])
      (Or.inl (by simp [NativeRustcVm.length_wordBytes])) ?_
    refine bytes_blk hwf2 hm2' (writesIn_of_mid hmid2) hW2
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) ?_
    exact bytes_blk hwf1 hm1 (writesIn_of_mid hmid1) hW1
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) hl.w48
  have hw56 : NativeRustcVm.WordAt st4.data.dmem (loc m0 56) (.ofBitVec (reg m0 .r9)) := by
    rw [hd4]
    refine bytes_call hkeep3 (j := 56) (by omega) (by simp [NativeRustcVm.length_wordBytes])
      (Or.inl (by simp [NativeRustcVm.length_wordBytes])) ?_
    refine bytes_blk hwf2 hm2' (writesIn_of_mid hmid2) hW2
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) ?_
    exact bytes_blk hwf1 hm1 (writesIn_of_mid hmid1) hW1
      (by simp [NativeRustcVm.length_wordBytes]) (by simp [NativeRustcVm.length_wordBytes]) hl.w56
  simp only [PcOk] at hpc4
  rcases hr : (sumcheckPlain w.claim 3 (reg m0 .rcx).toNat).run s4 with _ | ⟨⟨⟨tail, claim⟩, s5⟩⟩
  · have h0 := load4_of_tag (Or.inl rfl) (show NativeRustcVm.WordAt
      ((argEnv m0 st3.data 2672 8 [] (fun _ ↦ 0) 0).mem0)
      ((argEnv m0 st3.data 2672 8 [] (fun _ ↦ 0) 0).base 0 + BitVec.ofNat 64 144) 0 from hopt.1 hr)
    rw [cTag144_eval _ (Or.inl rfl) h0] at hpc4
    exact none36 hp c hf4 (hpc4.trans (l5 hp)) (by rw [hrun, C5]; exact run_bind_none hr)
  obtain ⟨hopt1, hopt2, hslots, hnext⟩ := hopt.2 tail claim s5 hr
  have h1 := load4_of_tag (Or.inr rfl) (show NativeRustcVm.WordAt
    ((argEnv m0 st3.data 2672 8 [] (fun _ ↦ 0) 0).mem0)
    ((argEnv m0 st3.data 2672 8 [] (fun _ ↦ 0) 0).base 0 + BitVec.ofNat 64 144) 1 from hopt1)
  rw [cTag144_eval _ (Or.inr rfl) h1] at hpc4
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at hpc4
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b17Offset) := hpc4
  refine cont st4 tail claim s5 hpc4' hc4 hbx4 hw48 hw56 (sumcheckPlain_size hr)
    (by rw [hd4]; exact hslots) (by rw [hd4]; rw [off_off] at hopt2; exact hopt2)
    (by rw [hd4]; exact hnext) ?_
  rw [hrun, C5]; exact run_bind_some hr

end

end NativeRustcVmX64.Whir.Levels.FL
