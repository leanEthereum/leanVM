module

public import NativeRustcVmX64.Whir.FinalLevel.Queries
public import NativeVm.Equiv.Transcript
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names

/-!
# `final_level`: the openings (x86-64)

From `b10` (`Live`, RBP the `WhirW`, the queries in its buffer): the query count saturated (RBX,
R8), the queries' address (RBP, RCX), `query_openings(&rows, t, index, queries)` into the frame's
`Option<Rows>` at `144` (`b10`), its tag tested (`b11`, `None` to `NativeRustcVmX64.Vm.FinalLevel.label_5`): `openings`,
to `b12`. The query buffer across blocks (`Ctx.q_frame`) and calls (`Ctx.q_call`).
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel
open NativeRustcVm.Sumcheck (RowsAt OptRowsAt openingsWords)
open NativeVm (phaseBase phaseWords)

public section

/-- `queryOpenings` that returned: its phase existed. -/
theorem qo_lt {i : Nat} {qs : Array UInt64} {s s' : TState} {rows : Array (Array UInt64)}
    (h : (queryOpenings i qs).run s = some (rows, s')) : s.phase < s.openings.size := by
  rw [NativeVm.Equiv.queryOpenings_run] at h
  split at h
  · rename_i r ph _ hph
    exact (Array.getElem?_eq_some_iff.mp hph).1
  · cases h

theorem ult_ofNat {n c : Nat} (hn : n < c) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 c) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

theorem vN_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 61352 8 = BitVec.ofNat 64 n)
    (hn : n < 231) : vN.eval env = BitVec.ofNat 64 n := by
  simp only [vN, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]

theorem vQ_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 61352 8 = BitVec.ofNat 64 n)
    (hn : n < 231) : vQ.eval env = env.base 1 + BitVec.ofInt 64 61360 := by
  simp only [vQ, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem cRows_eval [Labels] (env : Env) {x : BitVec 64} (hl : env.load 0 144 8 = x) :
    cRows.eval env = (x == BitVec.ofNat 64 0) := by
  simp only [cRows, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl]

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level ba b w rounds m0)
include c

/-- The `WhirW` as an input. -/
theorem pIn : WhirIn m0 (pA m0) whirBytes finalLevelStack :=
  ⟨⟨c.pout.1.1, c.pout.1.2.1⟩, c.pout.1.2.2.2.2.1⟩

/-- The decoded area as an input. -/
theorem decIn : WhirIn m0 a.words (8 * a.len) finalLevelStack :=
  ⟨c.ts.footprint.2.1, c.wt.2.2.2.1.2.1⟩

/-- Bytes of an area off the frame region kept across a change of the frame. -/
theorem area_frame {d d' : Mem 64} {hi : Nat} (hhi : hi ≤ 2672)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (fa m0) hi)) {x : BitVec 64}
    {n : Nat} (hnw : x.toNat + n ≤ 2 ^ 64)
    (hx : x.toNat + n ≤ (rspOf m0).toNat - 5760 ∨ (rspOf m0).toNat + 8 ≤ x.toNat) :
    NativeRustcVm.Layout.Same d d' x n := by
  have h1 : 2672 ≤ (rspOf m0).toNat := Nat.le_trans (by decide) c.geo.hN
  refine c.same_frame (hi := hi) (Nat.le_trans hhi (by decide)) hs hnw ?_
  rcases hx with hx | hx
  · exact Or.inl (Nat.le_trans hx (Nat.sub_le_sub_left (by decide) _))
  · refine Or.inr (Nat.le_trans ?_ hx)
    calc (rspOf m0).toNat - 2672 + hi ≤ (rspOf m0).toNat - 2672 + 2672 := Nat.add_le_add_left hhi _
      _ = (rspOf m0).toNat := Nat.sub_add_cancel h1
      _ ≤ (rspOf m0).toNat + 8 := Nat.le_add_right _ _

/-- **Bytes of an area off the frame, the stack and the `TState`** kept across a call from RSP
offset `o` changing its stack, the `TState` and a frame range. -/
theorem area_call {o : Nat} (ho : o ≤ 2672) {d d' : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) {R : BitVec 64 → Prop}
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q))
    {lo n : Nat} (hn : lo + n ≤ 2672)
    (hR : ∀ q, R q → NativeRustcVm.InRange (loc m0 lo) n q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q)
    {x : BitVec 64} {len : Nat} (hnw : x.toNat + len ≤ 2 ^ 64)
    (hx : x.toNat + len ≤ (rspOf m0).toNat - 5760 ∨ (rspOf m0).toNat + 8 ≤ x.toNat)
    (ht : x.toNat + len ≤ (tA m0).toNat ∨ (tA m0).toNat + 760 ≤ x.toNat) :
    NativeRustcVm.Layout.Same d.dmem d'.dmem x len := by
  have g := c.geo
  refine c.same_call ho hf hle hch hnw (by have := g.hN; omega) fun j hj hq ↦ ?_
  have hxj : (x + BitVec.ofNat 64 j).toNat = x.toNat + j := NativeRustcVm.toNat_add_ofNat (by omega)
  rcases hR _ hq with h' | h'
  · rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact absurd h' (by unfold NativeRustcVm.InRange; omega)
    rw [c.inLc (by omega) (by omega), hxj] at h'
    have := g.hN
    omega
  · rw [c.inT, hxj] at h'
    omega

/-- The query buffer across a change of the frame. -/
theorem q_frame {d d' : Mem 64} {hi : Nat} (hhi : hi ≤ 2672)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (fa m0) hi)) {qs : List UInt64}
    (h : NativeRustcVm.BufWordsAt d (qA m0) queryCap qs) :
    NativeRustcVm.BufWordsAt d' (qA m0) queryCap qs := by
  have g := c.geo
  have hqa := c.qA_toNat
  exact bufWordsAt_of_same h (c.area_frame hhi hs (n := queryBufBytes)
    (by rw [hqa]; have := g.pW; unfold queryBufBytes queryCap; omega)
    (by rw [hqa]; have := g.pS; unfold queryBufBytes queryCap; omega)) (by decide)

/-- The query buffer across a call. -/
theorem q_call {o : Nat} (ho : o ≤ 2672) {d d' : MachineData} (hf : Fr m0 o d) {N' : Nat}
    (hle : 2672 - o + N' ≤ finalLevelStack) {R : BitVec 64 → Prop}
    (hch : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d N') N' q))
    {lo n : Nat} (hn : lo + n ≤ 2672)
    (hR : ∀ q, R q → NativeRustcVm.InRange (loc m0 lo) n q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q)
    {qs : List UInt64} (h : NativeRustcVm.BufWordsAt d.dmem (qA m0) queryCap qs) :
    NativeRustcVm.BufWordsAt d'.dmem (qA m0) queryCap qs := by
  have g := c.geo
  have hqa := c.qA_toNat
  exact bufWordsAt_of_same h (c.area_call ho hf hle hch hn hR (len := queryBufBytes)
    (by rw [hqa]; have := g.pW; unfold queryBufBytes queryCap; omega)
    (by rw [hqa]; have := g.pS; unfold queryBufBytes queryCap; omega)
    (by rw [hqa]; have := g.pT; unfold queryBufBytes queryCap; omega)) (by decide)

/-- A frame range apart from bytes of the `WhirW`. -/
theorem apart_lp {o k j n : Nat} (ho : o < 2688) (hok : o + k ≤ 2688) (hj : j + n ≤ 63200)
    (hj' : j < 63200) : NativeRustcVm.Apart (loc m0 o) k (pA m0 + BitVec.ofNat 64 j) n := by
  have g := c.geo
  unfold NativeRustcVm.Apart
  rw [c.loc_toNat (by omega), NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)]
  have := g.pS; have := g.hN
  omega

end Ctx

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The openings**: `b10`, `query_openings`, `b11`, to `b12`. -/
theorem openings (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hqo : ∀ a s Q, Spec (Labels.label NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    {st : MachineState} {folded : Array EW} {qs : Array UInt64} {s3 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b10Offset)) (hl : Live level m0 st.data folded)
    (hbp : reg st.data .rbp = pA m0)
    (hq : NativeRustcVm.BufWordsAt st.data.dmem (qA m0) queryCap qs.toList)
    (hts : TStateAt st.data.dmem (tA m0) a s3)
    (hrun : runF level b w rounds m0 s = (C3 (reg m0 .rsi).toNat (mu m0) (reg m0 .r8).toNat b w
      rounds folded qs).run s3)
    (cont : ∀ (st' : MachineState) (rws : Array (Array UInt64)) (s4 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b12Offset) → Live level m0 st'.data folded →
      reg st'.data .rbp = pA m0 + BitVec.ofNat 64 61360 →
      reg st'.data .rbx = BitVec.ofNat 64 qs.size →
      NativeRustcVm.BufWordsAt st'.data.dmem (qA m0) queryCap qs.toList →
      RowsAt st'.data.dmem (loc m0 144) (off (a.word (phaseBase a.l s3.phase)) 24) rws →
      WhirIn m0 (off (a.word (phaseBase a.l s3.phase)) 24) (8 * openingsWords) finalLevelStack →
      (a.words.toNat ≤ (off (a.word (phaseBase a.l s3.phase)) 24).toNat ∧
        (off (a.word (phaseBase a.l s3.phase)) 24).toNat + 8 * openingsWords ≤
          a.words.toNat + 8 * a.len) →
      TStateAt st'.data.dmem (tA m0) a s4 →
      runF level b w rounds m0 s = (C4 (reg m0 .rsi).toNat (mu m0) (reg m0 .r8).toNat b w rounds
        folded qs rws).run s4 →
      Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hqn : qs.size ≤ 230 := by have := hq.1; rwa [Array.length_toList] at this
  -- `b10`: `query_openings(&rows, t, index, queries)`.
  let ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b11Offset)).toBitVec
  let env := argEnv m0 st.data 2672 8 [(pA m0, 63200)] (fun _ ↦ 0) ret
  have hwf : env.WF :=
    c.wf1 hl.fr.frame.kept (show NativeRustcVm.Mapped st.data.dmem (pA m0) 63200 from
      Mapped.keeps c.pout.1.1 hl.fr.frame.kept) g.pW
      (g.pS.imp_left fun h ↦ Nat.le_trans h (Nat.sub_le_sub_left (by decide) _))
  have hm : Match env wS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hl.fr.frame, known_ptr rfl hbp, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf (fun _ _ ↦ rfl) hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, hrdi1, hrsi1, hrdx1, hrcx1, hr81, hrbx1, hrbp1, hkr1⟩ := ok_b10
  obtain ⟨hf1, hs1⟩ := c.blk hl.fr hwf hm1 hmid1 (hi := 40) (by omega) (hW1.le (by decide))
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b10 wS).reg r = some v →
      reg st1.data r = v.eval env := fun h ↦ hm1.regs _ _ h
  have hl0 : env.load 1 61352 8 = BitVec.ofNat 64 qs.size := by
    have := load_ofMachine (r := 1) (o := 61352) (rs := [(stackBelow m0 2672, 2672 + 8 + 8),
      (pA m0, 63200)]) (vs := fun _ ↦ 0) (ret := ret) (m := st.data) rfl hq.2.1
    rw [this, Array.length_toList]
    rfl
  have hvN : vN.eval env = BitVec.ofNat 64 qs.size := vN_eval env hl0 (by omega)
  have hvQ : vQ.eval env = pA m0 + BitVec.ofNat 64 61360 := (vQ_eval env hl0 (by omega)).trans rfl
  have hcx1 : reg st1.data .rcx = pA m0 + BitVec.ofNat 64 61360 := (e1 hrcx1).trans hvQ
  have hn1 : reg st1.data .r8 = BitVec.ofNat 64 qs.size := (e1 hr81).trans hvN
  have hbx1 : reg st1.data .rbx = BitVec.ofNat 64 qs.size := (e1 hrbx1).trans hvN
  have hbp1 : reg st1.data .rbp = pA m0 + BitVec.ofNat 64 61360 := (e1 hrbp1).trans hvQ
  have hdi1 : reg st1.data .rdi = loc m0 144 := (e1 hrdi1).trans (eval_ptr0A 144)
  have hsi1 : reg st1.data .rsi = tA m0 := (e1 hrsi1).trans hl.r12
  have hdx1 : reg st1.data .rdx = reg m0 .rsi := (e1 hrdx1).trans hl.r15
  have hk1 : ∀ r ∈ [Reg64.r12, .r13, .r14, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ e1 (hkr1 r hr)
  have hts1 := c.ts_frame (hi := 40) (by omega) (hm1.kept hwf) hs1 hts
  have hq1 := c.q_frame (hi := 40) (by omega) hs1 hq
  have hat := c.at_call (o := 32) (by omega) hf1
  have hle : 2672 - 32 + queryOpeningsStack ≤ finalLevelStack := by decide
  have hwt := c.whirT hat hf1.same hle
  have hpos := c.whirOut hat hle (WL.whirOut_sub c.pout (o := 61360) (k := 8 * qs.size)
    (by unfold whirBytes; omega))
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hnq : (reg st1.data .r8).toNat = qs.size := by
    rw [hn1, BitVec.toNat_ofNat]; omega
  have hpre : QueryOpeningsPre a s3 qs st1.data := by
    simp only [QueryOpeningsPre, hdi1, hsi1, hcx1, hnq]
    refine ⟨hwt.1, hwt.2.1, hts1, hwt.2.2.2.1, trivial, ?_, hpos.1.2.1, hpos.1.2.2.2.2.1,
      hpos.1.2.2.2.1, c.outLoc (o := 32) (by omega) hf1 hle (by omega) (by omega),
      c.apart_lp (by omega) (by omega) (by omega) (by omega), ?_⟩
    · rw [← e8]; exact hq1.2.2
    · apply c.got_call hf1 (by omega) hle (by decide)
      intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp, le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ (pA m0 + BitVec.ofNat 64 61360).toNat
          rw [NativeRustcVm.toNat_add_ofNat (by have := c.geo.pW; omega)]
          omega
        · change (pA m0 + BitVec.ofNat 64 61360).toNat + 8 * qs.size ≤ (pA m0).toNat + 63200
          rw [NativeRustcVm.toNat_add_ofNat (by have := c.geo.pW; omega)]
          omega
      · exact c.got_loc (by omega) (by omega)
      · exact c.got_rc
  refine call_then hpc1 (hqo a s3 qs) hpre fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hrw, hnext, hch2, hsv2⟩ := hq2
  rw [hdi1, hdx1] at hrw
  rw [hsi1, hdx1] at hnext
  rw [hdi1, hsi1] at hch2
  have hch2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      (NativeRustcVm.InRange (loc m0 144) 32 q ∨ NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st1.data queryOpeningsStack) queryOpeningsStack q) :=
    NativeRustcVm.SameOutside.mono hch2 fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact Or.inl (Or.inl hq)
      · exact Or.inl (Or.inr hq)
      · exact Or.inr hq
  obtain ⟨hf2, hkeep2⟩ := c.call (o := 32) (by omega) hf1 hle hsv2 hrsp2
    (R := fun q ↦ NativeRustcVm.InRange (loc m0 144) 32 q ∨
      NativeRustcVm.InRange (tA m0) tstateBytes q) (lo := 144) (n := 32) (by omega) (by omega)
    (fun q hq ↦ hq.elim Or.inr fun h ↦ Or.inl (Or.inr h)) hch2'
  have hq2 := c.q_call (o := 32) (by omega) hf1 hle hch2' (lo := 144) (n := 32) (by omega)
    (fun q hq ↦ hq) hq1
  have hcs2 : ∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r := hsv2.1
  have hl2 : Live level m0 st2.data folded :=
    hl.step hwf hm1 (writesIn_of_mid hmid1) hW1 (by decide) hkeep2 (by omega) (by omega) hf2
      (fun r hr ↦ (hcs2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl)).trans
        (hk1 r hr)) hfo
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b11Offset) := hpc2
  -- `b11`: the openings' tag.
  refine Eventually.bind (cond_spec hp c b11_in_code (by simp [b11]) exit_b11 ok_b11 hf2 hpc2')
    fun st3 ⟨hr3, hd3, hpc3⟩ ↦ ?_
  have hf3 := hf2.congr hr3 hd3
  rcases hr : (queryOpenings (reg m0 .rsi).toNat qs).run s3 with _ | ⟨rws, s4⟩
  · rw [hr] at hrw
    have h0 : NativeRustcVm.WordAt st2.data.dmem (loc m0 144) 0 := hrw
    rw [cRows_eval _ (load_ofMachine (r := 0) (o := 144) rfl h0)] at hpc3
    exact none36 hp c hf3 (hpc3.trans (l5 hp)) (by rw [hrun, C3]; exact run_bind_none hr)
  rw [hr] at hrw
  have hrows : RowsAt st2.data.dmem (loc m0 144) (off (a.word (phaseBase a.l s3.phase)) 24) rws :=
    hrw
  obtain ⟨hp0, -, ww, -, hhdr, -⟩ := hrows
  have hl1 := load_ofMachine (r := 0) (o := 144) (rs := [(stackBelow m0 2672, 2672 + 8 + 8)])
    (vs := fun _ ↦ 0) (ret := 0) rfl (NativeRustcVm.wordsAt_cons_iff.mp hhdr).1
  rw [cRows_eval _ hl1] at hpc3
  have hne : ((UInt64.ofBitVec (off (a.word (phaseBase a.l s3.phase)) 24)).toBitVec ==
      BitVec.ofNat 64 0) = false := by
    rw [beq_eq_false_iff_ne]
    exact hp0
  rw [hne] at hpc3
  simp only [Bool.false_eq_true, ite_false] at hpc3
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b12Offset) := hpc3
  have hlt := qo_lt hr
  have hpb : phaseBase a.l s3.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts1.decoded.phases_le))
      hts1.decoded.len
  have hpwd : phaseWords = 3 + openingsWords := rfl
  have hop := WL.whirIn_sub c.decIn (o := 8 * phaseBase a.l s3.phase + 24)
    (k := 8 * openingsWords) (by omega)
  rw [← show off (a.word (phaseBase a.l s3.phase)) 24 =
    a.words + BitVec.ofNat 64 (8 * phaseBase a.l s3.phase + 24) from off_off _ _ _] at hop
  have hopBounds : a.words.toNat ≤ (off (a.word (phaseBase a.l s3.phase)) 24).toNat ∧
      (off (a.word (phaseBase a.l s3.phase)) 24).toNat + 8 * openingsWords ≤
        a.words.toNat + 8 * a.len := by
    have hopenings : 0 < openingsWords := by decide
    rw [show off (a.word (phaseBase a.l s3.phase)) 24 =
      a.words + BitVec.ofNat 64 (8 * phaseBase a.l s3.phase + 24) from off_off _ _ _,
      NativeRustcVm.toNat_add_ofNat (by have := c.geo.aW; omega)]
    omega
  refine cont st3 rws s4 hpc3' (hl2.keep hf3 (fun r _ ↦ hr3 r) (fun j _ ↦ by rw [hd3]) hfo)
    ((hr3 .rbp).trans ((hcs2 .rbp rfl).trans hbp1)) ((hr3 .rbx).trans ((hcs2 .rbx rfl).trans hbx1))
    (by rw [hd3]; exact hq2) (by rw [hd3]; exact hrw) hop hopBounds
    (by rw [hd3]; exact hnext rws s4 hr) ?_
  rw [hrun, C3]; exact run_bind_some hr

end

end NativeRustcVmX64.Whir.Levels.FL
