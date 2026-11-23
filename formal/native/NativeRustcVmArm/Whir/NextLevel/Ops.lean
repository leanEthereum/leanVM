module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmArm.Whir.NextLevel.Zero
public import NativeVm.Equiv.Transcript

/-!
# `next_level`: the query weights and the openings

From the zeroing loop's end (`b18`, `H17 … 57`): the zeroed scratch copied over the query weights
(`memcpy`), the weights' count stored at `680` and `powers(λ, n)` at `688` (`b19`), the openings
read into the `Option<Rows>` at `4368` (`b20`, `query_openings`), its tag tested (`b21`, `None`
to `.LNextLevel_13`): `ops`, to `b22` with `H22`.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel
open NativeRustcVm.Sumcheck (RowsAt OptRowsAt openingsWords)
open NativeVm (phaseBase phaseWords)

@[expose] public section

/-- The frame's facts from `b19` on: the weights' count at `680` too. -/
abbrev F19 (m0 : MachineData) (xs ood : Array EW) (v lam : EW) (n : Nat) :
    List (Nat × List UInt8) :=
  (680, NativeRustcVm.wordBytes n.toUInt64) :: F17 m0 xs ood v lam

/-- At `b22`: the openings `rows` read (the `Rows` at `4368`, the openings at `op`), the query
weights at `688`, the `TState` at its next state. -/
structure H22 [Labels] (a : DecArea) (level : Whir.Level) (m0 : MachineData) (xs ood : Array EW)
    (v lam : EW) (qs : Array UInt64) (rows : Array (Array UInt64)) (op : BitVec 64)
    (s9 : TState) (st : MachineData) : Prop where
  fr : NFr m0 st
  x19 : st.regs.X19 = m0.regs.X6
  x20 : st.regs.X20 = m0.regs.X1
  x21 : st.regs.X21 = level.fold.toUInt64
  x23 : st.regs.X23.toBitVec = loc m0 200
  x24 : st.regs.X24.toBitVec = pA m0 + BitVec.ofNat 64 57344
  x25 : st.regs.X25 = v.c1
  x26 : st.regs.X26 = m0.regs.X5
  x27 : st.regs.X27 = qs.size.toUInt64
  x28 : st.regs.X28.toBitVec = loc m0 688
  x29 : st.regs.X29.toBitVec = pA m0 + BitVec.ofNat 64 61360
  facts : Facts m0 st.dmem (F19 m0 xs ood v lam qs.size)
  pw : NativeRustcVm.EWsAt st.dmem (loc m0 688) (powers lam qs.size).toList
  rows : RowsAt st.dmem (loc m0 4368) op rows
  opIn : WhirIn m0 op (8 * openingsWords) nextLevelStack
  size : xs.size = level.fold
  osize : ood.size = m0.regs.X5.toNat
  qsz : qs.size ≤ queryCap
  qbuf : NativeRustcVm.BufWordsAt st.dmem (qA m0) queryCap qs.toList
  ts : TStateAt st.dmem (tA m0) a s9

end

public section

theorem powers_size' (b : EW) (n : Nat) : (powers b n).size = n := by
  unfold powers
  suffices ∀ (l : List Nat) (acc : Array EW × EW),
      (l.foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) acc).1.size =
        acc.1.size + l.length by
    rw [this]; simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp; omega

/-- `queryOpenings` that returned: its phase existed. -/
theorem qo_lt {i : Nat} {qs : Array UInt64} {s s' : TState} {rows : Array (Array UInt64)}
    (h : (queryOpenings i qs).run s = some (rows, s')) : s.phase < s.openings.size := by
  rw [NativeVm.Equiv.queryOpenings_run] at h
  split at h
  · rename_i r ph _ hph
    exact (Array.getElem?_eq_some_iff.mp hph).1
  · cases h

theorem within19 {m0 : MachineData} {xs ood : Array EW} {v lam : EW} {n : Nat}
    (h1 : xs.size ≤ 6) (h2 : ood.size ≤ 30) : Within (F19 m0 xs ood v lam n) 64 624 :=
  within_word (by omega) (by omega) ((within17 h1 h2).mono (by omega) (by omega))

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The query weights and the openings**, to `b22`. -/
theorem ops (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hpw : Spec (Labels.label NativeRustcVmArm.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hqo : ∀ a s Q, Spec (Labels.label NativeRustcVmArm.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    {st : MachineState} {xs ood : Array EW} {v lam : EW} {qs : Array UInt64} {s8 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b18Offset)) (hI : H17 a level m0 xs ood v lam qs s8 57 st.data)
    (hrun : runN level w rounds m0 s =
      tail8 m0.regs.X1.toNat m0.regs.X5.toNat w rounds xs ood v qs lam s8)
    (cont : ∀ (st' : MachineState) (rows : Array (Array UInt64)) (op : BitVec 64) (s9 : TState),
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b22Offset) → H22 a level m0 xs ood v lam qs rows op s9 st'.data →
      runN level w rounds m0 s = some (glueLevel w lam m0.regs.X5.toNat ood v qs
        (powers lam qs.size) (batchedOf m0.regs.X1.toNat m0.regs.X5.toNat rounds xs qs rows
          (powers lam qs.size)), s9) →
      Eventually (step1 Host.exe) (Goal a s level w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  have c := ctx h
  have g := geo h
  have hf := hI.fr
  have hmu30 : m0.regs.X5.toNat ≤ 30 := h.2.2.2.2.2.2.2.2.2.2.1
  have hf6 : level.fold ≤ 6 := h.2.2.2.2.2.1
  have hqn : qs.size ≤ 230 := by have := hI.qbuf.1; rwa [Array.length_toList] at this
  have hW17 := within17 (m0 := m0) (xs := xs) (ood := ood) (v := v) (lam := lam)
    (by rw [hI.size]; exact hf6) (by rw [hI.osize]; exact hmu30)
  have hW19 := within19 (m0 := m0) (xs := xs) (ood := ood) (v := v) (lam := lam) (n := qs.size)
    (by rw [hI.size]; exact hf6) (by rw [hI.osize]; exact hmu30)
  have hx8 : (envF m0 st.data).regs .X8 = BitVec.ofNat 64 qs.size := by
    show st.data.regs.X8.toBitVec = _
    rw [hI.x8]; rfl
  have hlt : ((Sym.reg .X8).eval (envF m0 st.data)).toNat < 231 := by
    show ((envF m0 st.data).regs .X8).toNat < 231
    rw [hx8, BitVec.toNat_ofNat]; omega
  -- `b18`: the copy's arguments, `memcpy(sp + 688, sp + 4368, 3680)`.
  refine blk hp h b18_in_code (by simp [b18]) run_b18 (wfF h hf) (mF h hf) (by decide) rfl hf hpc
    fun st1 hm1 hpc1 hf1 hs1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b18Offset + b18.length = k + NativeRustcVmArm.Vm.NextLevel.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b18_next]] at hpc1
  have e1 := sameRegs_ok (mF h hf) hm1
    (rs := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26]) (by decide)
  have x0 : st1.data.regs.X0.toBitVec = loc m0 688 := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [reg_val hm1 (r := .X0) rfl]; simp [Sym.eval]
  have x28 : st1.data.regs.X28.toBitVec = loc m0 688 := by
    show (st1.data.regs.getXReg .X28).toBitVec = _
    rw [reg_val hm1 (r := .X28) rfl]; simp [Sym.eval]
  have x1 : st1.data.regs.X1.toBitVec = loc m0 4368 := by
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [reg_val hm1 (r := .X1) rfl]; simp [Sym.eval]
  have x2 : st1.data.regs.X2.toNat = 3680 := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X2) rfl]; rfl
  have x27 : st1.data.regs.X27 = qs.size.toUInt64 := by
    apply UInt64.toBitVec_inj.mp
    show (st1.data.regs.getXReg .X27).toBitVec = _
    rw [reg_val hm1 (r := .X27) rfl, ite_ult hlt (by decide)]
    exact hx8
  have x29 : st1.data.regs.X29.toBitVec = pA m0 + BitVec.ofNat 64 61360 := by
    show (st1.data.regs.getXReg .X29).toBitVec = _
    rw [reg_val hm1 (r := .X29) rfl, ite_ult hlt (by decide), ev_add]
    rw [show st.data.regs.getXReg .X19 = m0.regs.X6 from hI.x19]
  have hF1 := Facts.block hm1 (wfF h hf) (by decide) (by decide) hW17 hI.facts
  have hts1 := tsB h (hm1.kept (wfF h hf)) hs1 hI.ts
  have hqb1 := qbuf_keep h hs1 (fun q hq ↦ by have := frame_nat h hq; have := g.pS; omega)
    hI.qbuf
  have hle0 : 8192 + 0 ≤ nextLevelStack := by decide
  have l688 := locIn h hf1 hle0 (o := 688) (n := 3680) (by decide)
  have l4368 := locIn h hf1 hle0 (o := 4368) (n := 3680) (by decide)
  refine ncall c hf1 (N' := 0) (o := 688) (n := 3680) hle0 (by decide) hmc hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hf2 hq hs2 hcs2 ↦ ?_
  · show Mapped _ st1.data.regs.X0.toBitVec st1.data.regs.X2.toNat ∧
      Mapped _ st1.data.regs.X1.toBitVec st1.data.regs.X2.toNat ∧
      NoWrap st1.data.regs.X0.toBitVec st1.data.regs.X2.toNat ∧
      NoWrap st1.data.regs.X1.toBitVec st1.data.regs.X2.toNat ∧
      Apart st1.data.regs.X0.toBitVec st1.data.regs.X2.toNat st1.data.regs.X1.toBitVec
        st1.data.regs.X2.toNat
    rw [x0, x1, x2]
    refine ⟨l688.1.1, l4368.1.1, l688.1.2, l4368.1.2, ?_⟩
    unfold Apart
    rw [loc_toNat (hN8 h) (by decide), loc_toNat (hN8 h) (by decide)]
    omega
  · rw [x0, x2] at hq'; exact .inr (.inl hq')
  have hF2 := Facts.call c hf1 hle0 (by decide) hs2 hW17 (by decide) (by omega) hF1
  obtain ⟨-, -, hso2, hsv2⟩ := hq
  have hts2 := ts_keep h hsv2.2.2 hso2 (fun q hq ↦ by
    rw [x0, x2] at hq
    have := loc_nat h (by decide) hq; have := g.tS; have := g.aS; have := g.hN; omega) hts1
  have hqb2 := qbuf_keep h hso2 (fun q hq ↦ by
    rw [x0, x2] at hq
    have := loc_nat h (by decide) hq; have := g.pS; have := g.hN; omega) hqb1
  have r2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26],
      m2.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦ by
    rw [← e1 r hr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcs2 _ rfl
  -- `b19`: `λ` loaded, the count stored, `powers(λ, sp + 688, n)`.
  have f64 : NativeRustcVm.WordAt m2.dmem (loc m0 64) lam.c1 := hF2.get List.mem_cons_self
  have f72 : NativeRustcVm.WordAt m2.dmem (loc m0 72) lam.c0 :=
    hF2.get (List.mem_cons_of_mem _ List.mem_cons_self)
  refine blk hp h b19_in_code (by simp [b19]) run_b19 (wfF h hf2) (mF h hf2) (by decide) rfl hf2
    rfl fun st3 hm3 hpc3 hf3 hs3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b19Offset + b19.length = k + NativeRustcVmArm.Vm.NextLevel.b20Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b19_next]] at hpc3
  have e3 := sameRegs_ok (mF h hf2) hm3
    (rs := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]) (by decide)
  have y1 : st3.data.regs.X1 = lam.c1 := reg_of hm3 (r := .X1) rfl (load_word (by simpa using f64))
  have y0 : st3.data.regs.X0 = lam.c0 := reg_of hm3 (r := .X0) rfl (load_word (by simpa using f72))
  have m27 : m2.regs.X27 = qs.size.toUInt64 := (hcs2 .X27 rfl).trans x27
  have m28 : m2.regs.X28.toBitVec = loc m0 688 := by
    rw [show m2.regs.X28 = st1.data.regs.X28 from hcs2 .X28 rfl]; exact x28
  have m29 : m2.regs.X29.toBitVec = pA m0 + BitVec.ofNat 64 61360 := by
    rw [show m2.regs.X29 = st1.data.regs.X29 from hcs2 .X29 rfl]; exact x29
  have y2 : st3.data.regs.X2.toBitVec = loc m0 688 := by
    rw [show st3.data.regs.X2 = m2.regs.X28 from reg_of hm3 (r := .X2) (v := .reg .X28) rfl rfl]
    exact m28
  have y3 : st3.data.regs.X3 = qs.size.toUInt64 :=
    (reg_of hm3 (r := .X3) (v := .reg .X27) rfl rfl).trans m27
  have hn64 : qs.size < 2 ^ 64 := by omega
  have y3' : st3.data.regs.X3.toNat = qs.size := by rw [y3]; exact toNat_toUInt64 hn64
  have w680 : NativeRustcVm.WordAt st3.data.dmem (loc m0 680) qs.size.toUInt64 :=
    word_of hm3 (r := 0) (o := 680) (sz := 8192) rfl (by decide) (s := .reg .X27)
      (congrArg UInt64.toBitVec m27) (by decide)
  have hF3 : Facts m0 st3.data.dmem (F19 m0 xs ood v lam qs.size) :=
    (Facts.block hm3 (wfF h hf2) (by decide) (by decide) hW17 hF2).cons w680
  have hts3 := tsB h (hm3.kept (wfF h hf2)) hs3 hts2
  have hqb3 := qbuf_keep h hs3 (fun q hq ↦ by have := frame_nat h hq; have := g.pS; omega) hqb2
  have hlep : 8192 + powersStack ≤ nextLevelStack := by decide
  refine ncall c hf3 (N' := powersStack) (o := 688) (n := 16 * qs.size) hlep (by omega) hpw hpc3
    ?_ (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m4 hf4 hq hs4 hcs4 ↦ ?_
  · refine ⟨c.stackOk hf3 hlep, ?_⟩
    show WhirIn st3.data st3.data.regs.X2.toBitVec (16 * st3.data.regs.X3.toNat) powersStack
    rw [y2, y3']; exact locIn h hf3 hlep (by omega)
  · rw [y2, y3'] at hq'
    rcases hq' with hq' | hq'
    · exact .inr (.inl hq')
    · exact .inl hq'
  obtain ⟨hpow, hso4, hsv4⟩ := hq
  rw [y2, y3', y0, y1] at hpow
  rw [y2, y3'] at hso4
  have hpow' : NativeRustcVm.EWsAt m4.dmem (loc m0 688) (powers lam qs.size).toList := hpow
  have hF4 := Facts.call c hf3 hlep (by omega) hs4 hW19 (by decide) (by omega) hF3
  have hts4 := ts_keep h hsv4.2.2 hso4 (fun q hq ↦ by
    rcases hq with hq | hq
    · have := loc_nat h (by omega) hq; have := g.tS; have := g.aS; have := g.hN; omega
    · have := stack_nat h hf3 hlep hq; have := g.tS; have := g.aS; have := g.hN; omega) hts3
  have hqb4 := qbuf_keep h hso4 (fun q hq ↦ by
    rcases hq with hq | hq
    · have := loc_nat h (by omega) hq; have := g.pS; have := g.hN; omega
    · have := stack_nat h hf3 hlep hq; have := g.pS; have := g.hN; omega) hqb3
  have r4 : ∀ r, calleeSaved r = true → r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
      .X27, .X28, .X29] → m4.regs.getXReg r = m2.regs.getXReg r := fun r hc hr ↦ by
    rw [hcs4 r hc, e3 r hr]
  -- `b20`: `query_openings(sp + 4368, t, index, queries, n)`.
  refine blk hp h b20_in_code (by simp [b20]) run_b20 (wfF h hf4) (mF h hf4) (by decide) rfl hf4
    rfl fun st5 hm5 hpc5 hf5 hs5 ↦ ?_
  simp only [PcOk] at hpc5
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b20Offset + b20.length = k + NativeRustcVmArm.Vm.NextLevel.b21Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b20_next]] at hpc5
  have hd5 : st5.data.dmem = m4.dmem := hm5.dmem_eq (wfF h hf4) rfl
  have e5 := sameRegs_ok (mF h hf4) hm5
    (rs := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]) (by decide)
  have z0 : st5.data.regs.X0.toBitVec = loc m0 4368 := by
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [reg_val hm5 (r := .X0) rfl]; simp [Sym.eval]
  have z1 : st5.data.regs.X1 = m0.regs.X0 :=
    (reg_of hm5 (r := .X1) (v := .reg .X22) rfl rfl).trans
      ((r4 .X22 rfl (by simp)).trans ((r2 .X22 (by simp)).trans hI.x22))
  have z2 : st5.data.regs.X2 = m0.regs.X1 :=
    (reg_of hm5 (r := .X2) (v := .reg .X20) rfl rfl).trans
      ((r4 .X20 rfl (by simp)).trans ((r2 .X20 (by simp)).trans hI.x20))
  have z3 : st5.data.regs.X3.toBitVec = pA m0 + BitVec.ofNat 64 61360 := by
    rw [show st5.data.regs.X3 = m4.regs.X29 from reg_of hm5 (r := .X3) (v := .reg .X29) rfl rfl,
      show m4.regs.X29 = m2.regs.X29 from r4 .X29 rfl (by simp)]
    exact m29
  have z4 : st5.data.regs.X4.toNat = qs.size := by
    rw [show st5.data.regs.X4 = m4.regs.X27 from reg_of hm5 (r := .X4) (v := .reg .X27) rfl rfl,
      show m4.regs.X27 = m2.regs.X27 from r4 .X27 rfl (by simp), m27]
    exact toNat_toUInt64 hn64
  have zt : st5.data.regs.X1.toBitVec = tA m0 := by rw [z1]
  have hle : 8192 + queryOpeningsStack ≤ nextLevelStack := by decide
  have hqb : 61360 + 8 * qs.size ≤ whirBytes := by unfold whirBytes; omega
  have hpos := whirIn_sub (pIn h) (o := 61360) (k := 8 * qs.size) hqb
  have hpos5 := whirIn' h hf5 hle hpos
  have e8 : qA m0 + 8#64 = pA m0 + BitVec.ofNat 64 61360 := by
    show (pA m0 + BitVec.ofNat 64 61352) + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hqs5 : NativeRustcVm.WordsAt st5.data.dmem (pA m0 + BitVec.ofNat 64 61360) qs.toList := by
    rw [hd5, ← e8]; exact hqb4.2.2
  have hp61 : (pA m0 + BitVec.ofNat 64 61360).toNat = (pA m0).toNat + 61360 :=
    toNat_off' (by have := g.pW; omega)
  refine ncall c hf5 (N' := queryOpeningsStack) (o := 4368) (n := 32) hle (by decide)
    (hqo a s8 qs) hpc5 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m6 hf6 hq hs6 hcs6 ↦ ?_
  · refine ⟨c.stackOk hf5 hle, c.rcAt hf5 hle, ?_, ?_, z4.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show TStateAt st5.data.dmem st5.data.regs.X1.toBitVec a s8
      rw [zt, hd5]; exact hts4
    · show TStateOk st5.data st5.data.regs.X1.toBitVec a queryOpeningsStack
      rw [zt]; exact c.tstateOk hf5 hle
    · show NativeRustcVm.WordsAt st5.data.dmem st5.data.regs.X3.toBitVec qs.toList
      rw [z3]; exact hqs5
    · show NoWrap st5.data.regs.X3.toBitVec (8 * st5.data.regs.X4.toNat)
      rw [z3, z4]; exact hpos.1.2
    · show Apart st5.data.regs.X3.toBitVec (8 * st5.data.regs.X4.toNat)
        (stackBelow st5.data queryOpeningsStack) queryOpeningsStack
      rw [z3, z4]; exact hpos5.2
    · show Apart st5.data.regs.X3.toBitVec (8 * st5.data.regs.X4.toNat) a.words (8 * a.len)
      rw [z3, z4]; exact apart_sub (whirOut h).1.2.2.2.1 (whirOut h).1.2.1 hqb
    · show OutOk st5.data st5.data.regs.X1.toBitVec a st5.data.regs.X0.toBitVec 32
        queryOpeningsStack
      rw [zt, z0]; exact c.localOk hf5 hle (by decide)
    · show Apart st5.data.regs.X0.toBitVec 32 st5.data.regs.X3.toBitVec
        (8 * st5.data.regs.X4.toNat)
      rw [z0, z3, z4]
      unfold Apart
      rw [loc_toNat (hN8 h) (by decide), hp61]
      have := g.pS; have := g.hN; omega
  · rw [z0, zt] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr (.inl hq'))
    · exact .inl hq'
  obtain ⟨hrw, hnext, hso6, hsv6⟩ := hq
  rw [z0, z2] at hrw
  rw [zt, z2] at hnext
  rw [z0, zt] at hso6
  have hF6 := Facts.call c hf5 hle (by decide) hs6 hW19 (by decide) (by omega)
    (by rw [hd5]; exact hF4)
  have hpw6 : NativeRustcVm.EWsAt m6.dmem (loc m0 688) (powers lam qs.size).toList :=
    keepC c hf5 hle (o' := 4368) (n' := 32) (by decide) hs6
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']; omega)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, powers_size']; omega)
      (by rw [hd5]; exact hpow')
  have hqb6 := qbuf_keep h hso6 (fun q hq ↦ by
    rcases hq with hq | hq | hq
    · have := loc_nat h (by decide) hq; have := g.pS; have := g.hN; omega
    · have := t_nat h hq; have := g.pT; omega
    · have := stack_nat h hf5 hle hq; have := g.pS; have := g.hN; omega)
    (by rw [hd5]; exact hqb4)
  have r6 : ∀ r, calleeSaved r = true → r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
      .X27, .X28, .X29] → m6.regs.getXReg r = m2.regs.getXReg r := fun r hc hr ↦ by
    rw [hcs6 r hc, e5 r hr, r4 r hc hr]
  -- `b21`: the openings' tag.
  refine blk hp h b21_in_code (by simp [b21]) run_b21 (wfF h hf6) (mF h hf6) (by decide) rfl hf6
    rfl fun st7 hm7 hpc7 hf7 hs7 ↦ ?_
  simp only [PcOk] at hpc7
  have hd7 : st7.data.dmem = m6.dmem := hm7.dmem_eq (wfF h hf6) rfl
  cases hr : (queryOpenings m0.regs.X1.toNat qs).run s8 with
  | none =>
    rw [hr] at hrw
    have h0 : NativeRustcVm.WordAt m6.dmem (loc m0 4368) 0 := hrw
    have l0 : (envF m0 m6).load 0 4368 8 = (0 : UInt64).toBitVec :=
      load_word (by simpa using h0)
    rw [cbz_load l0] at hpc7
    simp only [beq_self_eq_true, ↓reduceIte] at hpc7
    refine none13 hp h ?_ hf7 (hpc7.trans (hp.label (j := NativeRustcVmArm.Vm.NextLevel.b26Offset) NativeRustcVmArm.Vm.NextLevel.label_13_at))
    rw [hrun]; unfold tail8; rw [hr]; rfl
  | some p9 =>
  obtain ⟨rows, s9⟩ := p9
  rw [hr] at hrw
  have hrows : RowsAt m6.dmem (loc m0 4368)
      (off (a.word (phaseBase a.l s8.phase)) 24) rows := hrw
  have hne : (UInt64.ofBitVec (off (a.word (phaseBase a.l s8.phase)) 24) == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    exact hrows.1 (congrArg UInt64.toBitVec e)
  obtain ⟨-, -, ww, -, hhdr, -⟩ := hrows
  have l0 : (envF m0 m6).load 0 4368 8 =
      (UInt64.ofBitVec (off (a.word (phaseBase a.l s8.phase)) 24)).toBitVec :=
    load_word (by simpa using (NativeRustcVm.wordsAt_cons_iff.mp hhdr).1)
  rw [cbz_load l0, hne] at hpc7
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc7
  rw [show k + NativeRustcVmArm.Vm.NextLevel.b21Offset + b21.length = k + NativeRustcVmArm.Vm.NextLevel.b22Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b21_next]] at hpc7
  have hlt := qo_lt hr
  have hts5 : TStateAt st5.data.dmem (tA m0) a s8 := by rw [hd5]; exact hts4
  have hpb : phaseBase a.l s8.phase + phaseWords ≤ a.len :=
    Nat.le_trans (phaseBase_add_le (Nat.lt_of_lt_of_le hlt hts5.decoded.phases_le))
      hts5.decoded.len
  have hpw : phaseWords = 3 + openingsWords := rfl
  have hop := whirIn_sub (decIn h) (o := 8 * phaseBase a.l s8.phase + 24)
    (k := 8 * openingsWords) (by omega)
  rw [← show off (a.word (phaseBase a.l s8.phase)) 24 =
    a.words + BitVec.ofNat 64 (8 * phaseBase a.l s8.phase + 24) from off_off _ _ _] at hop
  have e7 := sameRegs_ok (mF h hf6) hm7
    (rs := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]) (by decide)
  have r7 : ∀ r, calleeSaved r = true → r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,
      .X27, .X28, .X29] → st7.data.regs.getXReg r = m2.regs.getXReg r := fun r hc hr ↦ by
    rw [e7 r hr, r6 r hc hr]
  refine cont st7 rows _ s9 hpc7 ⟨hf7, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hd7]; exact hF6, by rw [hd7]; exact hpw6, by rw [hd7]; exact hrw, hop, hI.size,
    hI.osize, hqn, by rw [hd7]; exact hqb6, by rw [hd7]; exact hnext _ _ hr⟩ ?_
  · exact (r7 .X19 rfl (by simp)).trans ((r2 .X19 (by simp)).trans hI.x19)
  · exact (r7 .X20 rfl (by simp)).trans ((r2 .X20 (by simp)).trans hI.x20)
  · exact (r7 .X21 rfl (by simp)).trans ((r2 .X21 (by simp)).trans hI.x21)
  · rw [show st7.data.regs.X23 = st.data.regs.X23 from
      (r7 .X23 rfl (by simp)).trans (r2 .X23 (by simp))]; exact hI.x23
  · rw [show st7.data.regs.X24 = st.data.regs.X24 from
      (r7 .X24 rfl (by simp)).trans (r2 .X24 (by simp))]; exact hI.x24
  · exact (r7 .X25 rfl (by simp)).trans ((r2 .X25 (by simp)).trans hI.x25)
  · exact (r7 .X26 rfl (by simp)).trans ((r2 .X26 (by simp)).trans hI.x26)
  · exact (r7 .X27 rfl (by simp)).trans m27
  · rw [show st7.data.regs.X28 = m2.regs.X28 from r7 .X28 rfl (by simp)]; exact m28
  · rw [show st7.data.regs.X29 = m2.regs.X29 from r7 .X29 rfl (by simp)]; exact m29
  · rw [hrun]; unfold tail8; rw [hr]; rfl

end

end

end NativeRustcVmArm.Whir.NextLevel
