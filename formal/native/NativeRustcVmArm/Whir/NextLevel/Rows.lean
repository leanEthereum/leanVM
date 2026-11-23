module

public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmArm.Whir.NextLevel.RowsBase

/-!
# `next_level`: the rows batched

From `b22` (`H22`): the rows' header copied to `8048`, the closure at `4368` (`&μ`, the high part,
`&batched` at `8080`, zeroed, the query weights), `each_row(index, queries, &rows, μ, rounds,
&closure)` (`b22`), its `Option<()>` tested (`b23`): `rows`, to `b24` with `H24`.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel
open NativeRustcVmArm.Transcript (load_ofMachine eval_ptr)
open NativeRustcVm.Sumcheck (RowsAt openingsWords)

public section

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The rows batched**, to `b24`. -/
theorem rows (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (her : ∀ rows op, Spec (Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.entryLabel) (EachRowNextPre rows op)
      (EachRowNextPost rows))
    {st : MachineState} {xs ood : Array EW} {v lam : EW} {qs : Array UInt64}
    {rws : Array (Array UInt64)} {op : BitVec 64} {s9 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b22Offset)) (hI : H22 a level m0 xs ood v lam qs rws op s9 st.data)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b24Offset) →
      H24 a level m0 xs ood v lam qs (batchedOf m0.regs.X1.toNat m0.regs.X5.toNat rounds xs qs
        rws (powers lam qs.size)) s9 st'.data →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  have c := ctx h
  have g := geo h
  have hf := hI.fr
  have hmu30 : m0.regs.X5.toNat ≤ 30 := h.2.2.2.2.2.2.2.2.2.2.1
  have hf6 : level.fold ≤ 6 := h.2.2.2.2.2.1
  have hqn : qs.size ≤ 230 := hI.qsz
  have hW19 := within19 (m0 := m0) (xs := xs) (ood := ood) (v := v) (lam := lam) (n := qs.size)
    (by rw [hI.size]; exact hf6) (by rw [hI.osize]; exact hmu30)
  have hwf := wfW h hf
  have hm := mR h hf hI.x19 hI.x24
  have hro := (whir_keep h hf).2
  have hrl : rounds.size ≤ 6 := by have := hro.1; rwa [Array.length_toList] at this
  have l61152 : (envW m0 st.data).load 1 61152 8 = rounds.toList.length.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 61152) rfl hro.2.1
  have hlt7 : ((Sym.load 1 61152 8).eval (envW m0 st.data)).toNat < 7 := by
    show ((envW m0 st.data).load 1 61152 8).toNat < 7
    rw [l61152, Array.length_toList, toNat_toUInt64' (by omega)]
    omega
  have l680 : (envW m0 st.data).load 0 680 8 = qs.size.toUInt64.toBitVec :=
    load_ofMachine (r := 0) (o := 680) rfl (hI.facts.get List.mem_cons_self)
  have hlt231 : ((Sym.load 0 680 8).eval (envW m0 st.data)).toNat < 231 := by
    show ((envW m0 st.data).load 0 680 8).toNat < 231
    rw [l680, toNat_toUInt64' (by omega)]
    omega
  have eq : qs.size.toUInt64.toNat = qs.size := toNat_toUInt64 (by omega)
  have ef : level.fold.toUInt64.toNat = level.fold := toNat_toUInt64 (by omega)
  -- `b22`: the rows' header copied, the closure, `each_row`.
  refine blk hp h b22_in_code (by simp [b22]) run_b22 hwf hm (by decide) rfl hf hpc
    fun st1 hm1 hpc1 hf1 hs1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b22Offset + b22.length = k + NativeRustcVmArm.Vm.NextLevel.b23Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b22_next]] at hpc1
  have e1 := sameRegs_ok hm hm1 (rs := [.X20, .X23, .X25, .X26, .X27, .X29]) (by decide)
  have x0 : st1.data.regs.X0 = m0.regs.X1 :=
    (reg_of hm1 (r := .X0) (v := .reg .X20) rfl rfl).trans hI.x20
  have x1 : st1.data.regs.X1.toBitVec = pA m0 + BitVec.ofNat 64 61360 :=
    (reg_val hm1 (r := .X1) (v := .reg .X29) rfl).trans hI.x29
  have x2 : st1.data.regs.X2 = qs.size.toUInt64 :=
    (reg_of hm1 (r := .X2) (v := .reg .X27) rfl rfl).trans hI.x27
  have x3 : st1.data.regs.X3.toBitVec = loc m0 8048 :=
    reg_val hm1 (r := .X3) (v := .ptr 0 8048) rfl
  have x4 : st1.data.regs.X4 = m0.regs.X5 :=
    (reg_of hm1 (r := .X4) (v := .reg .X26) rfl rfl).trans hI.x26
  have x5 : st1.data.regs.X5.toBitVec = pA m0 + BitVec.ofNat 64 61160 := by
    show (st1.data.regs.getXReg .X5).toBitVec = _
    rw [reg_val hm1 (r := .X5) rfl, ite_ult hlt7 (by decide)]
    rfl
  have x6 : st1.data.regs.X6.toNat = rounds.size := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X6).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X6) rfl, ite_ult hlt7 (by decide)]
    show ((envW m0 st.data).load 1 61152 8).toNat = _
    rw [l61152, Array.length_toList, toNat_toUInt64' (by omega)]
  have x7 : st1.data.regs.X7.toBitVec = loc m0 4368 :=
    reg_val hm1 (r := .X7) (v := .ptr 0 4368) rfl
  have x19 : st1.data.regs.X19 = m0.regs.X6 :=
    UInt64.toBitVec_inj.mp ((reg_val hm1 (r := .X19) (v := .ptr 1 0) rfl).trans (eval_ptr rfl))
  have x21 : st1.data.regs.X21 = qs.size.toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    show (st1.data.regs.getXReg .X21).toBitVec = _
    rw [reg_val hm1 (r := .X21) rfl, ite_ult hlt231 (by decide)]
    exact l680
  have x22 : st1.data.regs.X22.toBitVec = loc m0 688 := by
    show (st1.data.regs.getXReg .X22).toBitVec = _
    rw [reg_val hm1 (r := .X22) rfl, ite_ult hlt231 (by decide)]
    exact hI.x28
  -- The frame's words the block wrote.
  have w4368 : NativeRustcVm.WordAt st1.data.dmem (loc m0 4368) (UInt64.ofBitVec (loc m0 88)) :=
    word_of hm1 (r := 0) (o := 4368) (sz := 8192) rfl (by decide) (s := .ptr 0 88) rfl
      (by decide)
  have w4376 : NativeRustcVm.WordAt st1.data.dmem (loc m0 4376) (UInt64.ofBitVec (loc m0 96)) :=
    word_of hm1 (r := 0) (o := 4376) (sz := 8192) rfl (by decide) (s := .ptr 0 96) rfl
      (by decide)
  have w4384 : NativeRustcVm.WordAt st1.data.dmem (loc m0 4384) level.fold.toUInt64 :=
    word_of hm1 (r := 0) (o := 4384) (sz := 8192) rfl (by decide) (s := .reg .X21)
      (congrArg UInt64.toBitVec hI.x21) (by decide)
  have w4392 : NativeRustcVm.WordAt st1.data.dmem (loc m0 4392) (UInt64.ofBitVec (loc m0 8080)) :=
    word_of hm1 (r := 0) (o := 4392) (sz := 8192) rfl (by decide) (s := .ptr 0 8080) rfl
      (by decide)
  have w4400 : NativeRustcVm.WordAt st1.data.dmem (loc m0 4400) (UInt64.ofBitVec (loc m0 688)) :=
    word_of hm1 (r := 0) (o := 4400) (sz := 8192) rfl (by decide)
      (s := .ite (.cmp .ult .W64 (.load 0 680 8) (.lit 231)) (.reg .X28) (.lit 8))
      (by rw [ite_ult hlt231 (by decide)]; exact hI.x28) (by decide)
  have w4408 : NativeRustcVm.WordAt st1.data.dmem (loc m0 4408) qs.size.toUInt64 :=
    word_of hm1 (r := 0) (o := 4408) (sz := 8192) rfl (by decide)
      (s := .ite (.cmp .ult .W64 (.load 0 680 8) (.lit 231)) (.load 0 680 8) (.lit 0))
      (by rw [ite_ult hlt231 (by decide)]; exact l680) (by decide)
  have w8080 : NativeRustcVm.WordAt st1.data.dmem (loc m0 8080) 0 :=
    word_of hm1 (r := 0) (o := 8080) (sz := 8192) rfl (by decide) (s := .lit 0) rfl (by decide)
  have w8088 : NativeRustcVm.WordAt st1.data.dmem (loc m0 8088) 0 :=
    word_of hm1 (r := 0) (o := 8088) (sz := 8192) rfl (by decide) (s := .lit 0) rfl (by decide)
  have n0 : nextEnv st1.data 0 = UInt64.ofBitVec (loc m0 88) := nextEnv_of x7 w4368
  have n1 : nextEnv st1.data 1 = UInt64.ofBitVec (loc m0 96) := nextEnv_of x7 w4376
  have n2 : nextEnv st1.data 2 = level.fold.toUInt64 := nextEnv_of x7 w4384
  have n3 : nextEnv st1.data 3 = UInt64.ofBitVec (loc m0 8080) := nextEnv_of x7 w4392
  have n4 : nextEnv st1.data 4 = UInt64.ofBitVec (loc m0 688) := nextEnv_of x7 w4400
  have n5 : nextEnv st1.data 5 = qs.size.toUInt64 := nextEnv_of x7 w4408
  -- The rows' header copied.
  have hcopy : ∀ w0 w1 w2 w3 : UInt64,
      NativeRustcVm.WordsAt st.data.dmem (loc m0 4368) [w0, w1, w2, w3] →
      NativeRustcVm.WordsAt st1.data.dmem (loc m0 8048) [w0, w1, w2, w3] := by
    intro w0 w1 w2 w3 hw
    obtain ⟨h0, hw⟩ := wordsAt_cons.mp hw
    obtain ⟨h1, hw⟩ := wordsAt_cons.mp hw
    obtain ⟨h2, hw⟩ := wordsAt_cons.mp hw
    obtain ⟨h3, -⟩ := wordsAt_cons.mp hw
    rw [loc_off] at h1
    rw [loc_off, loc_off] at h2
    rw [loc_off, loc_off, loc_off] at h3
    have v0 := word_of hm1 (r := 0) (o := 8048) (sz := 8192) rfl (by decide)
      (s := .load 0 4368 8) (load_ofMachine (r := 0) (o := 4368) rfl h0) (by decide)
    have v1 := word_of hm1 (r := 0) (o := 8056) (sz := 8192) rfl (by decide)
      (s := .load 0 4376 8) (load_ofMachine (r := 0) (o := 4376) rfl h1) (by decide)
    have v2 := word_of hm1 (r := 0) (o := 8064) (sz := 8192) rfl (by decide)
      (s := .load 0 4384 8) (load_ofMachine (r := 0) (o := 4384) rfl h2) (by decide)
    have v3 := word_of hm1 (r := 0) (o := 8072) (sz := 8192) rfl (by decide)
      (s := .load 0 4392 8) (load_ofMachine (r := 0) (o := 4392) rfl h3) (by decide)
    refine wordsAt_cons.mpr ⟨v0, ?_⟩
    rw [loc_off]
    refine wordsAt_cons.mpr ⟨v1, ?_⟩
    rw [loc_off]
    refine wordsAt_cons.mpr ⟨v2, ?_⟩
    rw [loc_off]
    exact wordsAt_cons.mpr ⟨v3, wordsAt_nil _ _⟩
  have hsop : NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem op (8 * openingsWords) :=
    NativeRustcVm.Layout.Same.of_sameOutside hs1 fun _ hj hq ↦
      NativeRustcVm.Apart.not_inRange_add (apart_xf h hI.opIn.2) hI.opIn.1.2 (frNoWrap h) hj hq
  have hrw1 : RowsAt st1.data.dmem (loc m0 8048) op rws := rowsAt_move hI.rows hcopy hsop
  -- What the block kept.
  have hF1 := Facts.block hm1 hwf (by decide) (by decide) hW19 hI.facts
  have hp1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 688) (powers lam qs.size).toList :=
    keepB hm1 hwf (o := 688) (n := 16 * qs.size) (missAt_mono (o := 688) (n := 3680) (by decide)
      le_rfl (by omega)) (by omega)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']) hI.pw
  have hts1 := tsB h (hm1.kept hwf) hs1 hI.ts
  have hqb1 := qbuf_keep h hs1 (fun q hq ↦ by have := frame_nat h hq; have := g.pS; omega)
    hI.qbuf
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hqs1 : NativeRustcVm.WordsAt st1.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList := by
    rw [← e8]; exact hqb1.2.2
  have hqb : 61360 + 8 * qs.size ≤ whirBytes := by unfold whirBytes; omega
  have hpos := whirIn_sub (pIn h) (o := 61360) (k := 8 * qs.size) hqb
  have hrb : 61160 + roundBytes * rounds.size ≤ whirBytes := by
    unfold whirBytes roundBytes; omega
  have hle : 8192 + eachRowNextStack ≤ nextLevelStack := by decide
  refine ncall c hf1 (N' := eachRowNextStack) (o := 8080) (n := 16) hle (by decide) (her rws op)
    hpc1 ?_ (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hf2 hq hs2 hcs2 ↦ ?_
  · show EachRowNextPre rws op st1.data
    simp only [EachRowNextPre, EachRowIn, n0, n1, n2, n3, n4, n5, x1, x2, x3, x4, x5, x6, x7, ef,
      eq, tob]
    refine ⟨⟨c.stackOk hf1 hle, hrw1, locIn h hf1 hle (by decide), whirIn' h hf1 hle hI.opIn,
      whirIn' h hf1 hle hpos, hmu30, hrl,
      whirIn' h hf1 hle (whirIn_sub (pIn h) (o := 61160) (k := roundBytes * rounds.size) hrb)⟩,
      locIn h hf1 hle (by decide), locIn h hf1 hle (by decide), ?_, by unfold laneCap; omega,
      locSlice h hf1 hle (by rw [ef]; omega), locSlice h hf1 hle (by rw [eq]; omega),
      locIn h hf1 hle (by decide),
      NativeRustcVm.ewAt_iff.mpr ⟨w8080, by rw [loc_add]; exact w8088⟩,
      apart_ll h (by decide) (by decide) (by decide),
      apart_ll h (by decide) (by decide) (by decide),
      apart_ll h (by decide) (by decide) (by decide), apart_lx h hI.opIn.2 (by decide),
      apart_lp h (by decide) (by omega) (by decide),
      apart_lp h (by decide) (by unfold roundBytes; omega) (by decide),
      apart_ll h (by decide) (by omega) (by omega), apart_ll h (by decide) (by omega) (by omega)⟩
    exact NativeRustcVm.wordOf_of_wordAt (hF1.get (List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
      List.mem_cons_of_mem _ <| List.mem_cons_self))
  · rcases hq' with ⟨r, hr, hq'⟩ | hq'
    · rw [List.mem_singleton] at hr
      subst hr
      have hq'' : InRange (nextEnv st1.data 3).toBitVec 16 q := hq'
      rw [n3] at hq''
      exact .inr (.inl hq'')
    · exact .inl hq'
  -- After `each_row`.
  obtain ⟨hx0, hbt, hso2, hsv2⟩ := hq
  have eR : (eachRowArgs st1.data).2 = rounds := by
    show (roundsOf st1.data.dmem st1.data.regs.X5.toBitVec st1.data.regs.X6.toNat).toArray = _
    have e61160 : pA m0 + BitVec.ofNat 64 61160 = off (off (pA m0) roundsOff) 8 := by
      show _ = pA m0 + BitVec.ofNat 64 61152 + BitVec.ofNat 64 8
      rw [BitVec.add_assoc]
      rfl
    rw [x5, x6, e61160, ← Array.length_toList,
      roundsOf_of_roundsAt (whir_keep h hf1).2.2.2, Array.toArray_toList]
  have eQ : (eachRowArgs st1.data).1 = qs := by
    show (NativeRustcVm.wordsOf st1.data.dmem st1.data.regs.X1.toBitVec
      st1.data.regs.X2.toNat).toArray = _
    rw [x1, x2, eq, ← Array.length_toList, NativeRustcVm.wordsOf_of_wordsAt hqs1,
      Array.toArray_toList]
  have eX : slice st1.data (nextEnv st1.data 1) (nextEnv st1.data 2) = xs := by
    show (NativeRustcVm.ewsOf st1.data.dmem (nextEnv st1.data 1).toBitVec
      (nextEnv st1.data 2).toNat).toArray = _
    have hx1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 96) xs.toList :=
      hF1.get (List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <| List.mem_cons_of_mem _ <|
        List.mem_cons_self)
    have := NativeRustcVm.ewsOf_of_ewsAt hx1
    rw [Array.length_toList, hI.size] at this
    rw [n1, n2, tob, ef, this, Array.toArray_toList]
  have eP : slice st1.data (nextEnv st1.data 4) (nextEnv st1.data 5) = powers lam qs.size := by
    show (NativeRustcVm.ewsOf st1.data.dmem (nextEnv st1.data 4).toBitVec
      (nextEnv st1.data 5).toNat).toArray = _
    have := NativeRustcVm.ewsOf_of_ewsAt hp1
    rw [Array.length_toList, powers_size'] at this
    rw [n4, n5, tob, eq, this, Array.toArray_toList]
  rw [n3, tob, x0, x4, eR, eQ, eX, eP] at hbt
  have hF2 := Facts.call c hf1 hle (by decide) hs2 hW19 (by decide) (by omega) hF1
  have hp2 := keepC c hf1 hle (o' := 8080) (n' := 16) (by decide) hs2
    (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']; omega)
    (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']; omega) hp1
  have hR2 : ∀ q, (NativeRustcVm.InAny [⟨(nextEnv st1.data 3).toBitVec, 16⟩] q ∨
      InRange (stackBelow st1.data eachRowNextStack) eachRowNextStack q) →
      (m0.regs.SP.toNat - 11424 ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat) := fun q hq ↦ by
    rcases hq with ⟨r, hr, hq⟩ | hq
    · rw [List.mem_singleton] at hr
      subst hr
      have hq' : InRange (nextEnv st1.data 3).toBitVec 16 q := hq
      rw [n3, tob] at hq'
      have := loc_nat h (by decide) hq'
      have := g.hN
      omega
    · have := stack_nat h hf1 hle hq
      have := g.hN
      omega
  have hts2 := ts_keep h hsv2.2.2 hso2 (fun q hq ↦ by
    have := hR2 q hq; have := g.tS; have := g.aS; have := g.hN; omega) hts1
  have hqb2 := qbuf_keep h hso2 (fun q hq ↦ by
    have := hR2 q hq; have := g.pS; have := g.hN; omega) hqb1
  -- `b23`: `each_row`'s `Option<()>`.
  refine chk13 hp h b23_in (st := ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b23Offset)⟩) hf2 rfl
    (ok := true) (by rw [hx0]; rfl) (fun e ↦ by cases e) (fun _ h ↦ h)
    fun _ st' hpc' hf' hd' hr' ↦ ?_
  have k2 : ∀ r, calleeSaved r = true → st'.data.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hc ↦ (hr' r).trans (hcs2 r hc)
  refine cont st' (hpc'.trans (congrArg Host.addrOf (by
    simpa only [Nat.add_assoc, b23_length, b23Length] using congrArg (k + ·) b23_next)))
    ⟨hf', (k2 .X19 rfl).trans x19, (k2 .X21 rfl).trans x21, ?_, ?_,
    (k2 .X25 rfl).trans ((e1 .X25 (by simp)).trans hI.x25),
    (k2 .X27 rfl).trans ((e1 .X27 (by simp)).trans hI.x27), ?_,
    by rw [hd']; exact hF2, by rw [hd']; exact hp2, by rw [hd']; exact hbt, hI.size, hI.osize,
    hI.qsz, by rw [hd']; exact hqb2, by rw [hd']; exact hts2⟩
  · rw [show st'.data.regs.X22 = st1.data.regs.X22 from k2 .X22 rfl]; exact x22
  · rw [show st'.data.regs.X23 = st.data.regs.X23 from (k2 .X23 rfl).trans (e1 .X23 (by simp))]
    exact hI.x23
  · rw [show st'.data.regs.X29 = st.data.regs.X29 from (k2 .X29 rfl).trans (e1 .X29 (by simp))]
    exact hI.x29

end

end

end NativeRustcVmArm.Whir.NextLevel
