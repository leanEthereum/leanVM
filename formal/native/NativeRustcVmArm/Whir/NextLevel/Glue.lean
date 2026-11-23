module

public import NativeRustcVmArm.Code.Vm.GlueLevel.Names
public import NativeRustcVmArm.Whir.NextLevel.Rows

/-!
# `next_level`: the level glued, the return

From `b24` (`H24`): `glue_level(w, λ, μ, ood, v, queries, weights, batched)` (`b24`; the last
three on the stack), `b .LNextLevel_14` (`b25`), the epilogue (`b27`): `glue`, the postcondition.
From the call on the frame's outputs include the `WhirW` (`outsG`).
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel
open NativeRustcVmArm.Transcript (load_ofMachine)

@[expose] public section

/-- The outputs from `glue_level` on: those before, the `WhirW`. -/
def outsG (m0 : MachineData) (q : BitVec 64) : Prop :=
  outs m0 q ∨ InRange (pA m0) whirBytes q

end

public section

theorem fr_g {m0 st : MachineData} (hf : NFr m0 st) :
    Fr m0 8192 nextLevelStack slots [] (outsG m0) st :=
  ⟨hf.sp, hf.keep, hf.slots,
    NativeRustcVm.SameOutside.mono hf.same fun _ hq ↦ hq.elim .inl fun h' ↦ .inr (.inl h'),
    hf.kept⟩

/-- A stack argument the block stored. -/
theorem arg_of {m0 m : MachineData} (hsp : m.regs.SP.toBitVec = base m0 8192) {i : Nat}
    {u : UInt64} (hw : NativeRustcVm.WordAt m.dmem (loc m0 (8 * i)) u) : whirStackArg m i = u := by
  unfold whirStackArg
  rw [hsp]
  exact NativeRustcVm.wordOf_of_wordAt hw

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

theorem pA_not_frame (h : NextLevelPre a s level w rounds m0) {q : BitVec 64}
    (hq : InRange (pA m0) whirBytes q) : ¬InRange (base m0 8192) 8192 q := fun hf ↦ by
  have g := geo h
  have := p_nat h le_rfl hq
  have := frame_nat h hf
  have := g.pS; have := g.hN
  unfold whirBytes at *
  omega

theorem pin (h : NextLevelPre a s level w rounds m0) {q : BitVec 64}
    (hq : InRange (pA m0) stateBytes q) : InRange (pA m0) whirBytes q := by
  have g := geo h
  have := p_nat h (by decide) hq
  show InRange (pA m0) 63200 q
  rw [Sym.inRange_iff g.pW]
  unfold stateBytes at this
  omega

/-- The `WhirW`'s bytes apart from a frame range. -/
theorem apart_pl (h : NextLevelPre a s level w rounds m0) {n o k : Nat} (hn : n ≤ 63200)
    (hok : o + k ≤ 8192) : Apart (pA m0) n (loc m0 o) k := by
  have g := geo h
  unfold Apart
  rw [loc_toNat (hN8 h) (by omega)]
  have := g.pS; have := g.hN
  omega

/-- The state apart from the query buffer's entries. -/
theorem apart_pq (h : NextLevelPre a s level w rounds m0) {n : Nat} :
    Apart (pA m0) stateBytes (pA m0 + BitVec.ofNat 64 61360) n := by
  have g := geo h
  unfold Apart
  rw [toNat_off' (by have := g.pW; omega)]
  unfold stateBytes
  omega

/-- What `glue_level` writes, as numbers. -/
theorem glue_nat (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    (hle : 8192 + glueLevelStack ≤ nextLevelStack) (hx0 : st.regs.X0.toBitVec = pA m0)
    {q : BitVec 64}
    (hq : NativeRustcVm.InAny [⟨st.regs.X0.toBitVec, stateBytes⟩] q ∨
      InRange (stackBelow st glueLevelStack) glueLevelStack q) :
    ((pA m0).toNat ≤ q.toNat ∧ q.toNat < (pA m0).toNat + 61152) ∨
      (m0.regs.SP.toNat - 11424 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 8192) := by
  rcases hq with ⟨r, hr, hq⟩ | hq
  · rw [List.mem_singleton] at hr
    subst hr
    have hq' : InRange st.regs.X0.toBitVec stateBytes q := hq
    rw [hx0] at hq'
    exact .inl (p_nat h (by decide) hq')
  · exact .inr (stack_nat h hf hle hq)

end

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The level glued**, to the return. -/
theorem glue (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hgl : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.GlueLevel.entryLabel) (GlueLevelPre s) (GlueLevelPost s))
    {st : MachineState} {xs ood : Array EW} {v lam bt : EW} {qs : Array UInt64} {s9 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b24Offset)) (hI : H24 a level m0 xs ood v lam qs bt s9 st.data)
    (hrun : runN level w rounds m0 s = some (glueLevel w lam m0.regs.X5.toNat ood v qs
      (powers lam qs.size) bt, s9)) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  have c := ctx h
  have g := geo h
  have hf := hI.fr
  have hmu30 : m0.regs.X5.toNat ≤ 30 := h.2.2.2.2.2.2.2.2.2.2.1
  have hgl2 : w.glued.size + 2 ≤ gluedCap := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hqn : qs.size ≤ 230 := hI.qsz
  have eq : qs.size.toUInt64.toNat = qs.size := toNat_toUInt64 (by omega)
  have hW19 := within19 (m0 := m0) (xs := xs) (ood := ood) (v := v) (lam := lam) (n := qs.size)
    (by rw [hI.size]; exact h.2.2.2.2.2.1) (by rw [hI.osize]; exact hmu30)
  have f64 : NativeRustcVm.WordAt st.data.dmem (loc m0 64) lam.c1 :=
    hI.facts.get (List.mem_cons_of_mem _ List.mem_cons_self)
  have f72 : NativeRustcVm.WordAt st.data.dmem (loc m0 72) lam.c0 :=
    hI.facts.get (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ List.mem_cons_self)
  have f80 : NativeRustcVm.WordAt st.data.dmem (loc m0 80) v.c0 :=
    hI.facts.get (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ List.mem_cons_self)
  have f88 : NativeRustcVm.WordAt st.data.dmem (loc m0 88) m0.regs.X5 :=
    hI.facts.get (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ List.mem_cons_self)
  have f192 : NativeRustcVm.WordAt st.data.dmem (loc m0 192) m0.regs.X5 :=
    hI.facts.get (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ List.mem_cons_self)
  have hb0 : NativeRustcVm.WordAt st.data.dmem (loc m0 8080) bt.c0 :=
    (NativeRustcVm.ewAt_iff.mp hI.bt).1
  have hb1 : NativeRustcVm.WordAt st.data.dmem (loc m0 8088) bt.c1 := by
    have := (NativeRustcVm.ewAt_iff.mp hI.bt).2
    rwa [loc_add] at this
  have l192 : (envF m0 st.data).load 0 192 8 = m0.regs.X5.toBitVec :=
    load_ofMachine (r := 0) (o := 192) rfl f192
  have hlt31 : ((Sym.load 0 192 8).eval (envF m0 st.data)).toNat < 31 := by
    show ((envF m0 st.data).load 0 192 8).toNat < 31
    rw [l192, UInt64.toNat_toBitVec]
    omega
  -- `b24`: the arguments, `glue_level`.
  refine blk hp h b24_in_code (by simp [b24]) run_b24 (wfF h hf) (mF h hf) (by decide) rfl hf hpc
    fun st1 hm1 hpc1 hf1 hs1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b24Offset + b24.length = k + NativeRustcVmArm.Vm.NextLevel.b25Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b24_next]] at hpc1
  have x0 : st1.data.regs.X0 = m0.regs.X6 :=
    (reg_of hm1 (r := .X0) (v := .reg .X19) rfl rfl).trans hI.x19
  have x0' : st1.data.regs.X0.toBitVec = pA m0 := congrArg UInt64.toBitVec x0
  have x1 : st1.data.regs.X1 = lam.c0 :=
    reg_of hm1 (r := .X1) (v := .load 0 72 8) rfl (load_ofMachine (r := 0) (o := 72) rfl f72)
  have x2 : st1.data.regs.X2 = lam.c1 :=
    reg_of hm1 (r := .X2) (v := .load 0 64 8) rfl (load_ofMachine (r := 0) (o := 64) rfl f64)
  have x3 : st1.data.regs.X3 = m0.regs.X5 :=
    reg_of hm1 (r := .X3) (v := .load 0 88 8) rfl (load_ofMachine (r := 0) (o := 88) rfl f88)
  have x4 : st1.data.regs.X4 = UInt64.ofBitVec (loc m0 200) :=
    reg_of hm1 (r := .X4) rfl (by rw [ite_ult hlt31 (by decide)]; exact hI.x23)
  have x5 : st1.data.regs.X5 = m0.regs.X5 :=
    reg_of hm1 (r := .X5) rfl (by rw [ite_ult hlt31 (by decide)]; exact l192)
  have x6 : st1.data.regs.X6 = v.c0 :=
    reg_of hm1 (r := .X6) (v := .load 0 80 8) rfl (load_ofMachine (r := 0) (o := 80) rfl f80)
  have x7 : st1.data.regs.X7 = v.c1 :=
    (reg_of hm1 (r := .X7) (v := .reg .X25) rfl rfl).trans hI.x25
  -- The stack arguments.
  have a0 : whirStackArg st1.data 0 = UInt64.ofBitVec (pA m0 + BitVec.ofNat 64 61360) :=
    arg_of hf1.sp (word_of hm1 (r := 0) (o := 0) (sz := 8192) rfl (by decide) (s := .reg .X29)
      hI.x29 (by decide))
  have a1 : whirStackArg st1.data 1 = qs.size.toUInt64 :=
    arg_of hf1.sp (word_of hm1 (r := 0) (o := 8) (sz := 8192) rfl (by decide) (s := .reg .X27)
      (congrArg UInt64.toBitVec hI.x27) (by decide))
  have a2 : whirStackArg st1.data 2 = UInt64.ofBitVec (loc m0 688) :=
    arg_of hf1.sp (word_of hm1 (r := 0) (o := 16) (sz := 8192) rfl (by decide) (s := .reg .X22)
      hI.x22 (by decide))
  have a3 : whirStackArg st1.data 3 = qs.size.toUInt64 :=
    arg_of hf1.sp (word_of hm1 (r := 0) (o := 24) (sz := 8192) rfl (by decide) (s := .reg .X21)
      (congrArg UInt64.toBitVec hI.x21) (by decide))
  have a4 : whirStackArg st1.data 4 = bt.c0 :=
    arg_of hf1.sp (word_of hm1 (r := 0) (o := 32) (sz := 8192) rfl (by decide)
      (s := .load 0 8080 8) (load_ofMachine (r := 0) (o := 8080) rfl hb0) (by decide))
  have a5 : whirStackArg st1.data 5 = bt.c1 :=
    arg_of hf1.sp (word_of hm1 (r := 0) (o := 40) (sz := 8192) rfl (by decide)
      (s := .load 0 8088 8) (load_ofMachine (r := 0) (o := 8088) rfl hb1) (by decide))
  -- What the block kept.
  have hF1 := Facts.block hm1 (wfF h hf) (by decide) (by decide) hW19 hI.facts
  have hp1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 688) (powers lam qs.size).toList :=
    keepB hm1 (wfF h hf) (o := 688) (n := 16 * qs.size) (missAt_mono (o := 688) (n := 3680)
      (by decide) le_rfl (by omega)) (by omega)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']) hI.pw
  have hts1 := tsB h (hm1.kept (wfF h hf)) hs1 hI.ts
  have hqb1 := qbuf_keep h hs1 (fun q hq ↦ by have := frame_nat h hq; have := g.pS; omega)
    hI.qbuf
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hqs1 : NativeRustcVm.WordsAt st1.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList := by
    rw [← e8]; exact hqb1.2.2
  have hood : NativeRustcVm.EWsAt st1.data.dmem (loc m0 200) ood.toList :=
    hF1.get (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ List.mem_cons_self)
  have hle : 8192 + glueLevelStack ≤ nextLevelStack := by decide
  have hqb : 61360 + 8 * qs.size ≤ whirBytes := by unfold whirBytes; omega
  have hpos := whirIn_sub (pIn h) (o := 61360) (k := 8 * qs.size) hqb
  have hst := whirIn_sub (pIn h) (o := 0) (k := stateBytes) (by decide)
  rw [show pA m0 + BitVec.ofNat 64 0 = pA m0 from BitVec.add_zero _] at hst
  have e0 : loc m0 0 = base m0 8192 := BitVec.add_zero _
  have hpre : GlueLevelPre w st1.data := by
    simp only [GlueLevelPre, a0, a1, a2, a3, hf1.sp, x0', x3, x4, x5, tob, eq]
    refine ⟨c.stackOk hf1 hle, (whir_keep h hf1).1, hgl2, hmu30, hmu30, hqn, hqn, ?_,
      whirIn' h hf1 hle hst, locSlice h hf1 hle (by omega), whirIn' h hf1 hle hpos,
      locIn h hf1 hle (by omega), ?_, apart_pl h (by decide) (by omega), apart_pq h,
      apart_pl h (by decide) (by omega)⟩
    · have := (locIn h hf1 hle (o := 0) (n := 48) (by decide)).1
      rwa [e0] at this
    · have := apart_pl h (n := stateBytes) (o := 0) (k := 48) (by decide) (by decide)
      rwa [e0] at this
  refine Fr.callW (fr_g hf1) c.hN hle (fun _ h ↦ by cases h) slots_le'
    (fun q hq ↦ hq.elim (c.frame_outs q) (pA_not_frame h)) (o := 0) (n := 0) (by decide)
    (fun _ _ ↦ .inl (Nat.zero_le _)) (spec_with (hgl w) (· = st1.data))
    (fun m m' ⟨hq, he⟩ ↦ by
      subst he
      refine ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩
      rcases hq' with ⟨r, hr, hq'⟩ | hq'
      · rw [List.mem_singleton] at hr
        subst hr
        have hq'' : InRange st1.data.regs.X0.toBitVec stateBytes q := hq'
        rw [x0'] at hq''
        exact .inr (.inr (.inr (pin h hq'')))
      · exact .inl hq')
    hpc1 ⟨hpre, rfl⟩ fun m2 hf2 ⟨hq, _⟩ _ ↦ ?_
  obtain ⟨hx0, hws2, hso2, hsv2⟩ := hq
  -- The glued state, the rounds and the `TState` after the call.
  have eQ : wordSlice st1.data (whirStackArg st1.data 0).toBitVec
      (whirStackArg st1.data 1).toNat = qs := by
    rw [a0, a1, tob, eq]
    show (NativeRustcVm.wordsOf st1.data.dmem _ qs.size).toArray = _
    rw [← Array.length_toList, NativeRustcVm.wordsOf_of_wordsAt hqs1, Array.toArray_toList]
  have eW : slice st1.data (whirStackArg st1.data 2) (whirStackArg st1.data 3) =
      powers lam qs.size := by
    show (NativeRustcVm.ewsOf st1.data.dmem (whirStackArg st1.data 2).toBitVec
      (whirStackArg st1.data 3).toNat).toArray = _
    have := NativeRustcVm.ewsOf_of_ewsAt hp1
    rw [Array.length_toList, powers_size'] at this
    rw [a2, a3, tob, eq, this, Array.toArray_toList]
  have eB : (⟨whirStackArg st1.data 4, whirStackArg st1.data 5⟩ : EW) = bt := by rw [a4, a5]
  have eG : glueArgs st1.data = (qs, powers lam qs.size, bt) := by
    unfold glueArgs
    rw [eQ, eW, eB]
  have eO : slice st1.data st1.data.regs.X4 st1.data.regs.X5 = ood := by
    show (NativeRustcVm.ewsOf st1.data.dmem st1.data.regs.X4.toBitVec
      st1.data.regs.X5.toNat).toArray = _
    have := NativeRustcVm.ewsOf_of_ewsAt hood
    rw [Array.length_toList, hI.osize] at this
    rw [x4, x5, tob, this, Array.toArray_toList]
  rw [x0', x1, x2, x3, eO, x6, x7, eG] at hws2
  have hR2 := fun q hq ↦ glue_nat h hf1 hle x0' (q := q) hq
  have hts2 := ts_keep h hsv2.2.2 hso2 (fun q hq ↦ by
    have := hR2 q hq; have := g.pT; have := g.pA; have := g.tS; have := g.aS; have := g.hN
    omega) hts1
  have hbr2 : BufRoundsAt m2.dmem (off (pA m0) roundsOff) rounds.toList :=
    FoldRounds.bufRoundsAt_agree (whir_keep h hf1).2 fun j hj _ ↦ hso2 _ fun hq ↦ by
      have := hR2 _ hq
      have e1 : (off (pA m0) roundsOff).toNat = (pA m0).toNat + 61152 :=
        toNat_off' (j := 61152) (by have := g.pW; omega)
      have e : (off (pA m0) roundsOff + BitVec.ofNat 64 j).toNat = (pA m0).toNat + 61152 + j := by
        rw [toNat_off' (by rw [e1]; have := g.pW; omega), e1]
      rw [show off (off (pA m0) roundsOff) j = off (pA m0) roundsOff + BitVec.ofNat 64 j
        from rfl, e] at this
      have := g.pS; have := g.hN
      omega
  -- `b25`: to `.LNextLevel_14`.
  have hwf2 : (envF m0 m2).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hf2.kept _ (frame_mapped h.1.1 (by rw [stack_eq]; decide) i hi),
      frNoWrap h⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm2 : Match (envF m0 m2) fS m2 :=
    match_ofMachine ⟨rfl, fun _ ↦ frAligned h, trivial⟩ (by rw [hf2.sp]; simp [Sym.eval]) trivial
      trivial trivial trivial
  refine exec_at (st := ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b25Offset)⟩) (inf hp b25_in_code (by simp [b25])) run_b25
    hwf2 rfl hm2 fun st3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have hd3 : st3.data.dmem = m2.dmem := hm3.dmem_eq hwf2 rfl
  have hf3 : Fr m0 8192 nextLevelStack slots [] (outsG m0) st3.data :=
    Fr.ofBlock hf2 hm2 hm3 hwf2 rfl rfl rfl (fun _ h ↦ by cases h)
  have y0 : st3.data.regs.X0 = 1 := (reg_of hm3 (r := .X0) (v := .reg .X0) rfl rfl).trans hx0
  -- `b27`: the epilogue.
  refine Eventually.mono (epi hp h hf3 (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.NextLevel.b27Offset) NativeRustcVmArm.Vm.NextLevel.label_14_at)))
    fun st' ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_, fun x s' he ↦ ?_, fun w' s' he ↦ ?_, fun q hq ↦ ?_, h4⟩
  · show st'.data.regs.X0 = okWord (runN level w rounds m0 s).isSome
    rw [hrun, h2, y0]
    rfl
  · have he' : runN level w rounds m0 s = some (x, s') := he
    rw [hrun] at he'
    cases he'
    rw [h3, hd3]
    exact hts2
  · have he' : runN level w rounds m0 s = some (w', s') := he
    rw [hrun] at he'
    cases he'
    rw [h3, hd3]
    exact ⟨hws2, hbr2⟩
  · rw [h3, hd3]
    exact hf2.same q fun hq' ↦ hq (hq'.elim (fun h' ↦ .inr h') fun h' ↦
      h'.elim (fun h'' ↦ .inl (outs_changes h h'')) fun h'' ↦ .inl ⟨_, List.mem_cons_self, h''⟩)

end

end

end NativeRustcVmArm.Whir.NextLevel
