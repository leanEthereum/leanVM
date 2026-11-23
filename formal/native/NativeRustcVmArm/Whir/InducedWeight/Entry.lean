module

public import NativeRustcVmArm.Code.Vm.InducedWeight.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.InducedWeight.Outer

/-!
# `induced_weight`'s entry

`b0` saves the registers in its 1200-byte frame, spills the queries' and the weights' pointers and
the point's count, and calls `subspace_table(μ)` into the frame at 592; `b1` checks its tag: for
`μ > 30` (`None`) `b16` stores the tag `0` and returns. Else `b2` spills the output and copies the
table's pairs to 96 (`memcpy`), `b3` spills the table's count and the queries' count (the smaller
of the queries' and the weights'): none goes by `b14` to the store (`Done`), else `b4` spills the
cursors and starts the queries' loop (`OInv m0 0`).
-/

namespace NativeRustcVmArm.Whir.InducedWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf WordAt WordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

public section

/-- `memcpy`'s copy: a prefix of the source's bytes. -/
theorem bytesAt_copy {d d' : DataMem} {a a' : BitVec 64} {n : Nat} {bs : List UInt8}
    (hc : NativeRustcVm.BytesAt d a (bytesOf d' a' n)) (hb : NativeRustcVm.BytesAt d' a' bs)
    (hle : bs.length ≤ n) : NativeRustcVm.BytesAt d a bs := by
  intro i hi
  rw [hc i (by simp [NativeRustcArm.bytesOf]; omega)]
  have := hb i hi
  simp only [NativeRustcArm.bytesOf, List.getElem_map, List.getElem_range]
  rw [show (d'.get? (a' + BitVec.ofNat 64 i)) = some bs[i] from this]
  rfl

/-- A frame word kept. -/
theorem word_keep {m0 : MachineData} {d d' : DataMem} {o lo hi : Nat} {v : UInt64}
    (h : WordAt d (fbOf m0 + BitVec.ofNat 64 o) v) (ho : lo ≤ o) (hl : o + 8 ≤ hi)
    (hk : ∀ i, lo ≤ i → i < hi →
      d'.get? (fbOf m0 + BitVec.ofNat 64 i) = d.get? (fbOf m0 + BitVec.ofNat 64 i)) :
    WordAt d' (fbOf m0 + BitVec.ofNat 64 o) v :=
  bytes_keep h ho (by rw [NativeRustcVm.length_wordBytes]; exact hl) hk

/-- Four words from their addresses. -/
theorem words4 {d : DataMem} {a : BitVec 64} {o : Nat} {w0 w1 w2 w3 : UInt64}
    (h0 : WordAt d (a + BitVec.ofNat 64 o) w0) (h1 : WordAt d (a + BitVec.ofNat 64 (o + 8)) w1)
    (h2 : WordAt d (a + BitVec.ofNat 64 (o + 16)) w2)
    (h3 : WordAt d (a + BitVec.ofNat 64 (o + 24)) w3) :
    WordsAt d (a + BitVec.ofNat 64 o) [w0, w1, w2, w3] := by
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h0, ?_⟩
  rw [addr_add]
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h1, ?_⟩
  rw [addr_add, show o + 8 + 8 = o + 16 by omega]
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h2, ?_⟩
  rw [addr_add, show o + 16 + 8 = o + 24 by omega]
  exact NativeRustcVm.wordsAt_singleton_iff.mpr h3

/-- Three words from their addresses. -/
theorem words3 {d : DataMem} {a : BitVec 64} {o : Nat} {w0 w1 w2 : UInt64}
    (h0 : WordAt d (a + BitVec.ofNat 64 o) w0) (h1 : WordAt d (a + BitVec.ofNat 64 (o + 8)) w1)
    (h2 : WordAt d (a + BitVec.ofNat 64 (o + 16)) w2) :
    WordsAt d (a + BitVec.ofNat 64 o) [w0, w1, w2] := by
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h0, ?_⟩
  rw [addr_add]
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h1, ?_⟩
  rw [addr_add, show o + 8 + 8 = o + 16 by omega]
  exact NativeRustcVm.wordsAt_singleton_iff.mpr h2

variable [Host] {k : Nat}

/-- The frame as the one region of a block's environment. -/
theorem fr_env {m0 st : MachineData} (hS : StackOk m0 inducedWeightStack) (hfr : Fr m0 st) :
    (Env.ofMachine st [(fbOf m0, 1200)]).WF ∧ Match (Env.ofMachine st [(fbOf m0, 1200)]) frS st := by
  have hF : 1200 ≤ inducedWeightStack := by decide
  obtain ⟨hfmap, hfnw, -⟩ := frame_ok hS hF
  exact ⟨wf_one (hfr.readable ⟨hfmap, hfnw⟩).1 hfnw,
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial⟩

/-- The frame's bytes from `lo` to `hi` a block keeps. -/
theorem blk_keep {m0 st : MachineData} {S : SState} {m : MachineData}
    (hm : Match (Env.ofMachine st [(fbOf m0, 1200)]) S m)
    (hwf : (Env.ofMachine st [(fbOf m0, 1200)]).WF) {lo hi : Nat} (hlh : lo ≤ hi) (hhi : hi ≤ 1200)
    (hall : ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ lo ∨ hi ≤ w.off)) :
    ∀ i, lo ≤ i → i < hi →
      m.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) := by
  have h := Match.keep hm hwf (r := 0) rfl (o := lo) (len := hi - lo) (by omega)
    (fun w hw ↦ by have := hall w hw; omega)
  intro i h1 h2
  have := h (i - lo) (by omega)
  rwa [show lo + (i - lo) = i by omega] at this

/-- The output region and the frame, for `b15`, `b16`. -/
theorem out_env {m0 st : MachineData} (hpre : InducedWeightPre m0) (hfr : Fr m0 st)
    (h16 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) m0.regs.X0) :
    (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)]).WF ∧
      Match (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)]) outS st := by
  obtain ⟨hS, -, -, -, hout⟩ := hpre
  have hF : 1200 ≤ inducedWeightStack := by decide
  obtain ⟨hfmap, hfnw, -⟩ := frame_ok hS hF
  refine ⟨Env.wf_of ⟨⟨(hfr.readable ⟨hfmap, hfnw⟩).1, hfnw⟩, ⟨(hfr.readable hout.1).1, hout.1.2⟩,
      trivial⟩ (List.pairwise_pair.mpr (apart_frame hout.2 hF hS.2.1).symm), ?_⟩
  exact match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, rfl,
      fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial
    ⟨by
      show Env.load (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)]) 0 16 8 =
        m0.regs.X0.toBitVec + BitVec.ofInt 64 0
      rw [load_fr h16]
      simp, trivial⟩

/-- What the epilogue keeps: memory outside the output and the stack. -/
theorem out_same {m0 st st' : MachineData} {S : SState} (hpre : InducedWeightPre m0)
    (hfr : Fr m0 st)
    (hwf : (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)]).WF)
    (hm : Match (Env.ofMachine st [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)]) S st')
    (hS : ∀ w ∈ S.mem, w.r = 1 ∧ w.off + w.n ≤ 24) :
    ChangesIn m0 st' inducedWeightStack [⟨m0.regs.X0.toBitVec, 24⟩] := by
  intro a ha
  rw [hm.get?_mem0 hwf fun hw ↦ ha (.inl ⟨_, List.mem_singleton_self _,
    Written.inRange (r := 1) rfl hpre.2.2.2.2.1.2 hS hw⟩)]
  exact hfr.same a fun h ↦ ha (h.elim (fun ⟨_, hr, _⟩ ↦ absurd hr List.not_mem_nil) .inr)

/-- A block writing the frame below 96 keeps a body. -/
theorem fr_block {m0 st st' : MachineData} {S' : SState} (hS : StackOk m0 inducedWeightStack)
    (hfr : Fr m0 st) (hm₀ : Match (Env.ofMachine st [(fbOf m0, 1200)]) frS st)
    (hm : Match (Env.ofMachine st [(fbOf m0, 1200)]) S' st')
    (hwf : (Env.ofMachine st [(fbOf m0, 1200)]).WF)
    (hk : keepsRegs frS S' (freeRegs slots) = true)
    (hall : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 96) : Fr m0 st' := by
  have hF : 1200 ≤ inducedWeightStack := by decide
  exact hfr.of_block hm₀ hm hwf rfl hk (r := 0) rfl (by decide) hall
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 96) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq j hj ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 96) (by omega) (slots_le q hq) hj
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)

omit [Host] in
/-- Frame bytes apart from a frame range. -/
theorem frame_out {m0 : MachineData} (hS : StackOk m0 inducedWeightStack) {o n i : Nat}
    (hon : o + n ≤ 1200) (hi : i < 1200) (hap : i < o ∨ o + n ≤ i) :
    ¬InRange (fbOf m0 + BitVec.ofNat 64 o) n (fbOf m0 + BitVec.ofNat 64 i) := by
  obtain ⟨-, hnw, -⟩ := frame_ok hS (show 1200 ≤ inducedWeightStack by decide)
  unfold NoWrap at hnw
  by_cases hn : n = 0
  · subst hn; unfold InRange; omega
  have h1 := NativeRustcVm.NoWrap.sub (show NativeRustcVm.NoWrap (fbOf m0) 1200 from hnw) hon
  unfold NativeRustcVm.NoWrap at h1
  have hfb : (fbOf m0).toNat + 1200 ≤ 2 ^ 64 := hnw
  rw [Sym.inRange_iff h1, toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
  omega

omit [Host] in
/-- The length of a table's bytes. -/
theorem pairs_len (ps : List (UInt64 × UInt64)) :
    ((pairWords ps).flatMap NativeRustcVm.wordBytes).length = 16 * ps.length := by
  rw [NativeRustcVm.length_wordsBytes]
  simp [pairWords]
  omega

/-- **At `b3`**: the output spilled, the arguments spilled, the table's pairs copied to 96. -/
structure AtB3 (m0 st : MachineData) : Prop where
  fr : Fr m0 st
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) m0.regs.X0
  args : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 64) [m0.regs.X2, m0.regs.X4, m0.regs.X7]
  pairs : PairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 96) (tbOf m0).toList
  tlen : (tbOf m0).size ≤ 31
  x21 : st.regs.X21 = (tbOf m0).size.toUInt64
  x23 : st.regs.X23 = m0.regs.X5
  x24 : st.regs.X24 = m0.regs.X3
  x25 : st.regs.X25 = m0.regs.X6
  x26 : st.regs.X26.toBitVec = fbOf m0 + BitVec.ofNat 64 96
  mu : muOf m0 ≤ stackCap

/-- **From the entry to `b3`**, or `None` for `μ > 30`. -/
theorem entry_a (hp : Placed code k)
    (htab : Spec (label NativeRustcVmArm.Vm.SubspaceTable.entryLabel) SubspaceTablePre SubspaceTablePost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0)
    (cont : ∀ st, AtB3 m0 st → Eventually (step1 Host.exe)
      (fun s ↦ s.pc = retOf m0 ∧ InducedWeightPost m0 s.data) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b3Offset)⟩) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ InducedWeightPost m0 s.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b0Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hqin, hwin, hpin, hout⟩ := hpre'
  have hF : 1200 ≤ inducedWeightStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hlt := m0.regs.SP.toBitVec.isLt
  have hSP : inducedWeightStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have hfb : (fbOf m0).toNat = m0.regs.SP.toBitVec.toNat - 1200 := hfe
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env0 := Env.ofMachine m0 [(fbOf m0, 1200)]
  have hwf0 : env0.WF := wf_one hfmap hfnw
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  refine exec_then hk0 run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb0 := after_eq run_b0 ▸ b0_frame
  have hfr1 : Fr m0 s1.data := Frame.of_entry hS hF hwf0 hm1 rfl hb0.1 hb0.2.2 hb0.2.1
  have w64 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 64) m0.regs.X2 :=
    Match.wordAt_write hm1 (r := 0) rfl (o := 64) (by decide) (v := .reg .X2) (by decide)
  have w72 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 72) m0.regs.X4 :=
    Match.wordAt_write hm1 (r := 0) rfl (o := 72) (by decide) (v := .reg .X4) (by decide)
  have w80 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 80) m0.regs.X7 :=
    Match.wordAt_write hm1 (r := 0) rfl (o := 80) (by decide) (v := .reg .X7) (by decide)
  have e1x0 : s1.data.regs.X0.toBitVec = fbOf m0 + BitVec.ofNat 64 592 :=
    (hm1.regs .X0 _ rfl).trans rfl
  have e1x19 : (s1.data.regs.getXReg .X19).toBitVec = fbOf m0 + BitVec.ofNat 64 592 :=
    (hm1.regs .X19 _ rfl).trans rfl
  have e1x1 : s1.data.regs.X1 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have e1 : ∀ r ∈ [(XReg.X20, XReg.X0), (.X23, .X5), (.X24, .X3), (.X25, .X6)],
      s1.data.regs.getXReg r.1 = m0.regs.getXReg r.2 := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp ((hm1.regs _ _ rfl).trans rfl)
  -- `subspace_table(μ)` into the frame at 592
  have hNt : 1200 + subspaceTableStack ≤ inducedWeightStack := by decide
  have hP1 : SubspaceTablePre s1.data :=
    ⟨hfr1.stackOk hS rfl hNt, by rw [e1x0]; exact whirIn_frame hS hfr1 (by decide) hNt⟩
  refine call_then hpc1 htab hP1 fun s2 hpc2 ⟨hval, hch, hsv⟩ ↦ ?_
  rw [e1x0] at hch
  have hfr2 : Fr m0 s2.data :=
    hfr1.call_out hS hNt (o := 592) (n := 8 + tableBytes) (by decide) (by decide) hch hsv
  have hk2 := keep_call_out hfr1 hNt hS (n := 8 + tableBytes) (by decide) hch
  rw [e1x0, e1x1] at hval
  -- `b1`: the table's tag
  obtain ⟨hwf3, hm3⟩ := fr_env hS hfr2
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b1Offset) := hpc2
  refine exec_at hk1 run_b1 hwf3 hpc2' hm3 fun s3 hm3' hpc3 ↦ ?_
  have hb1 := after_eq run_b1 ▸ b1_keeps
  have hfr3 := hfr2.of_regs hm3 hm3' hwf3 rfl hb1.1 hb1.2
  have hd3 : s3.data.dmem = s2.data.dmem := hm3'.dmem_eq hwf3 hb1.2
  have r3 : ∀ r ∈ [XReg.X19, .X20, .X23, .X24, .X25],
      s3.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (Match.reg_eq hm3 hm3' rfl rfl).trans (hsv.1 _ rfl)
  have h20 : s3.data.regs.X20 = m0.regs.X0 :=
    (r3 .X20 (by simp)).trans (e1 (.X20, .X0) (by simp))
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  by_cases hmu : m0.regs.X1.toNat ≤ stackCap
  swap
  · -- `μ > 30`: `None`
    simp only [hmu, ↓reduceIte] at hval
    rw [load_fr (rs := []) hval] at hpc3
    simp only [show ((0 : UInt64).toBitVec == 0#64) = true from rfl, ↓reduceIte] at hpc3
    rw [show Labels.label NativeRustcVmArm.Vm.InducedWeight.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b16Offset) from hp.label (j := NativeRustcVmArm.Vm.InducedWeight.b16Offset) NativeRustcVmArm.Vm.InducedWeight.label_9_at] at hpc3
    let envN := Env.ofMachine s3.data [(fbOf m0, 1200), (m0.regs.X0.toBitVec, 24)]
    have hwfN : envN.WF :=
      Env.wf_of ⟨⟨(hfr3.readable ⟨hfmap, hfnw⟩).1, hfnw⟩, ⟨(hfr3.readable hout.1).1, hout.1.2⟩,
        trivial⟩ (List.pairwise_pair.mpr (apart_frame hout.2 hF hS.2.1).symm)
    have hmN : Match envN noneS s3.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, rfl,
          fun h ↦ absurd h (by decide), trivial⟩
        (by rw [hfr3.sp]; simp [Sym.eval, fbOf])
        ⟨by
          show s3.data.regs.X20.toBitVec = m0.regs.X0.toBitVec + BitVec.ofInt 64 0
          rw [h20]; simp, trivial⟩ trivial trivial trivial
    have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk16 run_b16' hwfN hpc3 hmN fun s4 hm4 hpc4 ↦ .done _ ?_
    have hb16 := after_eq run_b16' ▸ b16'_restores
    obtain ⟨hsaved, hx30⟩ := hfr3.ret hm4 hwfN x30_mem hb16.1
    have h8 : s3.data.regs.X8 = 0 := by
      apply UInt64.toBitVec_inj.mp
      refine (hm3'.regs .X8 _ rfl).trans ?_
      exact load_fr (rs := []) hval
    refine ⟨hpc4.trans (by simp only [retOf, hx30]), ?_, out_same hpre hfr3 hwfN hm4 hb16.2,
      hsaved⟩
    show OptEWAt _ _ (if m0.regs.X1.toNat ≤ stackCap then _ else _)
    simp only [hmu, ↓reduceIte]
    have := Match.wordAt_write hm4 (r := 1) rfl (o := 0) (by decide) (v := .reg .X8) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    rw [show UInt64.ofBitVec ((Sym.reg .X8).eval envN) = s3.data.regs.X8 from rfl, h8] at this
    exact this
  simp only [hmu, ↓reduceIte] at hval
  obtain ⟨htag, htb⟩ := hval
  rw [load_fr (rs := []) htag] at hpc3
  simp only [show ((1 : UInt64).toBitVec == 0#64) = false from rfl, Bool.false_eq_true,
    ↓reduceIte] at hpc3
  have hts : (tbOf m0).size ≤ 31 := by
    have := htb.1
    rw [Array.length_toList] at this
    exact this
  have w600 : WordAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 600) (tbOf m0).size.toUInt64 := by
    have := htb.2.1
    rwa [NativeRustcVm.Transcript.off, addr_add, Array.length_toList] at this
  have p608 : PairsAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 608) (tbOf m0).toList := by
    have := htb.2.2
    rwa [NativeRustcVm.Transcript.off, NativeRustcVm.Transcript.off, addr_add, addr_add] at this
  -- `b2`: the output spilled, `memcpy` of the table's pairs
  obtain ⟨hwf4, hm4⟩ := fr_env hS hfr3
  have hk2' : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b2Offset) := hpc3
  refine exec_at hk2' run_b2 hwf4 hpc3' hm4 fun s4 hm4' hpc4 ↦ ?_
  have hb2 := after_eq run_b2 ▸ b2_keeps
  have hfr4 := fr_block hS hfr3 hm4 hm4' hwf4 hb2.1 hb2.2
  have hk4 := blk_keep hm4' hwf4 (lo := 24) (hi := 1200) (by omega) le_rfl (by decide)
  have w16 : WordAt s4.data.dmem (fbOf m0 + BitVec.ofNat 64 16) m0.regs.X0 := by
    have := Match.wordAt_write hm4' (r := 0) rfl (o := 16) (by decide) (v := .reg .X20) (by decide)
    rwa [show UInt64.ofBitVec ((Sym.reg .X20).eval (Env.ofMachine s3.data [(fbOf m0, 1200)])) =
      s3.data.regs.X20 from rfl, h20] at this
  have e4x0 : s4.data.regs.X0.toBitVec = fbOf m0 + BitVec.ofNat 64 96 :=
    (hm4'.regs .X0 _ rfl).trans rfl
  have e4x1 : s4.data.regs.X1.toBitVec = fbOf m0 + BitVec.ofNat 64 608 := by
    refine (hm4'.regs .X1 _ rfl).trans ?_
    sym_simp
    rw [Env.ofMachine_regs, r3 .X19 (by simp), e1x19, addr_add]
  have e4x2 : s4.data.regs.X2.toNat = 496 := by
    rw [← UInt64.toNat_toBitVec, show s4.data.regs.X2.toBitVec = _ from hm4'.regs .X2 _ rfl]; rfl
  have e4x21 : s4.data.regs.X21 = (tbOf m0).size.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm4'.regs .X21 _ rfl).trans
      (load_fr (rs := []) (by rw [hd3]; exact w600)))
  have e4x26 : s4.data.regs.X26.toBitVec = fbOf m0 + BitVec.ofNat 64 96 :=
    (hm4'.regs .X26 _ rfl).trans rfl
  have r4 : ∀ r ∈ [XReg.X23, .X24, .X25], s4.data.regs.getXReg r = s3.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm4 hm4' rfl rfl
  have hP4 : MemcpyPre s4.data := by
    unfold MemcpyPre
    rw [e4x0, e4x1, e4x2]
    have ha := hfr4.readable (Readable.sub ⟨hfmap, hfnw⟩ (o := 96) (n := 496) (by omega))
    have hb := hfr4.readable (Readable.sub ⟨hfmap, hfnw⟩ (o := 608) (n := 496) (by omega))
    refine ⟨ha.1, hb.1, ha.2, hb.2, Or.inl ?_⟩
    rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  refine call_then hpc4 hmemcpy hP4 fun s5 hpc5 ⟨_, hcopy, hsame5, hsv5⟩ ↦ ?_
  rw [e4x0, e4x1, e4x2] at hcopy
  rw [e4x0, e4x2] at hsame5
  have hfr5 := hfr4.change hsame5
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 96) (n := 496) (by omega) h))
    (fun q hq j hj ↦ not_inRange_slot hS hF (o := 96) (n := 496) (by omega) (slots_le q hq) hj
      (.inl (by have := slots_ge q hq; omega)))
    (fun r hr _ ↦ hsv5.1 r hr) hsv5.2.1 hsv5.2.2
  have hk5 : ∀ i, 16 ≤ i → i < 96 → s5.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) =
      s4.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) := fun i _ h2 ↦
    hsame5 _ (frame_out hS (by omega) (by omega) (.inl h2))
  have hkA : ∀ i, 24 ≤ i → i < 592 → s4.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) =
      s1.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) := fun i h1 h2 ↦ by
    rw [hk4 i h1 (by omega), hd3, hk2 i (by omega) h2]
  have hkB : ∀ i, 1200 > i → 608 ≤ i → s4.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) =
      s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) := fun i h1 h2 ↦ by
    rw [hk4 i (by omega) h1, hd3]
  have hp4 : PairsAt s4.data.dmem (fbOf m0 + BitVec.ofNat 64 608) (tbOf m0).toList := by
    unfold PairsAt NativeRustcVm.WordsAt at p608 ⊢
    refine bytes_keep p608 (lo := 608) (hi := 1200) le_rfl ?_ fun i h1 h2 ↦ hkB i h2 h1
    rw [pairs_len, Array.length_toList]
    omega
  have hk51 : ∀ i, 24 ≤ i → i < 96 → s5.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) =
      s1.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) := fun i h1 h2 ↦ by
    rw [hk5 i (by omega) h2, hkA i h1 (by omega)]
  have hsv' : ∀ r ∈ [(XReg.X23, XReg.X5), (.X24, .X3), (.X25, .X6)],
      s5.data.regs.getXReg r.1 = m0.regs.getXReg r.2 := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv5.1 _ rfl).trans ((r4 _ (by simp)).trans ((r3 _ (by simp)).trans (e1 _ (by simp))))
  obtain ⟨d5, pc5⟩ := s5
  simp only at hpc5
  subst hpc5
  refine cont d5 ⟨hfr5, word_keep w16 (lo := 16) (hi := 96) le_rfl (by omega) hk5,
    words3 (word_keep w64 (lo := 24) (hi := 96) (by omega) (by omega) hk51)
      (word_keep w72 (lo := 24) (hi := 96) (by omega) (by omega) hk51)
      (word_keep w80 (lo := 24) (hi := 96) (by omega) (by omega) hk51), ?_, hts, ?_,
    hsv' (.X23, .X5) (by simp), hsv' (.X24, .X3) (by simp), hsv' (.X25, .X6) (by simp), ?_, hmu⟩
  · unfold PairsAt NativeRustcVm.WordsAt at hp4 ⊢
    exact bytesAt_copy hcopy hp4 (by rw [pairs_len, Array.length_toList]; omega)
  · show d5.regs.getXReg .X21 = _
    rw [hsv5.1 .X21 rfl]
    exact e4x21
  · show (d5.regs.getXReg .X26).toBitVec = _
    rw [hsv5.1 .X26 rfl]
    exact e4x26
end

end NativeRustcVmArm.Whir.InducedWeight
