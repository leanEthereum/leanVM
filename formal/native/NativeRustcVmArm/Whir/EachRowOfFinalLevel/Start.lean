module

public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Entry

/-!
# `each_row` with `final_level`'s closure: into the loop

`b3` stores the table's count at 48 and reads the rows' count: none, `Some(())` (`exit_step`).
`b4` stores the `What`s' address, the table's count and address and the folded scalars' count in
the frame, X19 the queries' bytes, X25 `0`: the loop's invariant before row `0`.
-/

namespace NativeRustcVmArm.Whir.EachRowOfFinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfFinalLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

theorem size_wordSlice (m : MachineData) (a : BitVec 64) (n : Nat) : (wordSlice m a n).size = n := by
  simp [wordSlice]

/-- The rows' count, in their `Rows`. -/
theorem rows_count {d : Mem 64} {r p : BitVec 64} (h : NativeRustcVm.Sumcheck.RowsAt d r p rows) :
    WordAt d (r + BitVec.ofNat 64 16) rows.size.toUInt64 := by
  obtain ⟨-, -, w, -, hw, -⟩ := h
  exact NativeRustcVm.WordsAt.getElem hw (i := 2) (by simp)

variable [Host] {k : Nat}

/-- **From `b3` into the loop.** -/
theorem start_step (hp : Placed code k) (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (h : AtB3 m0 m)
    (cont : ∀ m', Inv rows m0 0 m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b5Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b3Offset)⟩ := by
  have hstk := hpre.1.1
  have hS : 3184 ≤ m0.regs.SP.toNat := hstk.2.1
  have hrows := hpre.1.2.1
  have hrin := hpre.1.2.2.1
  have hargs := hpre.2.1
  have hl := lay hpre
  have hbt : (fb m0).toNat = m0.regs.SP.toNat - 1952 := hl.base_F
  have hSPb : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
  -- `b3`
  let env3 := Env.ofMachine m [(fb m0, 1952), (m0.regs.X3.toBitVec, 32)]
  have hwf3 : env3.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ h.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ h.fr.kept _ (hrin.1.1 i hi), hrin.1.2⟩, trivial⟩
      (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm
        (Ring.apart_frame (F := 1952) hstk.2.1 (by decide) hrin.2)))
  have hm3 : Match env3 rowsS m :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [h.fr.sp]; simp [Sym.eval])
      ⟨by show (m.regs.getXReg .X22).toBitVec = _; rw [h.x22]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hcnt : env3.load 1 16 8 = rows.size.toUInt64.toBitVec := by
    refine Ring.load_word ?_
    show WordAt m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 16) _
    have hsame := EachRow.input_same h.fr hstk.2.1 hrin.1.2 hrin.2 fun _ _ h ↦ h
    refine NativeRustcVm.Transcript.bytesAt_congr (rows_count hrows) fun i hi ↦ ?_
    rw [NativeRustcVm.addr_add_add]
    exact hsame _ (by rw [NativeRustcVm.length_wordBytes] at hi; omega)
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk3 run_b3 hwf3 hm3 fun st6 hm6 hpc6 ↦ ?_
  have hl3 : EachRow.Lay m0 1952 eachRowFinalStack 48 56 := ⟨by decide, by decide, by decide, hS⟩
  have hs6 : SameOutside m.dmem st6.data.dmem (EachRow.Hit m0 1952 eachRowFinalStack 48 56) :=
    EachRow.hit_of_block hl3 hm6 hwf3 (by decide)
  have hfr6 : FR m0 st6.data :=
    EachRow.fr_hit hl3 h.fr (Match.sp_eq hm3 hm6 rfl) (hm6.kept hwf3) hs6 (by decide)
  have k6 : ∀ r, (after b3 rowsS).reg r = some (.reg r) →
      st6.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (rv hm6 (by rw [← after_eq run_b3]; exact hr)).trans rfl
  have hlen6 : WordAt st6.data.dmem (fb m0 + BitVec.ofNat 64 48) (tableOf m0).size.toUInt64 := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm6 (r := 0) (o := 48) rfl (by decide)
      (v := .reg .X29) (by decide)
    rw [show UInt64.ofBitVec ((Sym.reg .X29).eval env3) = _ from (rfl : _ = m.regs.getXReg .X29),
      h.x29] at this
    exact this
  have hcopy6 : PairsAt st6.data.dmem (fb m0 + BitVec.ofNat 64 56) (tableOf m0).toList := by
    refine EachRow.keep_frame hl3 hs6 (.inr ⟨le_rfl, ?_⟩) h.copy
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, Array.length_toList]
    have := h.tlen
    omega
  have hx29 : (m.regs.getXReg .X29).toBitVec = (tableOf m0).size.toUInt64.toBitVec := by
    rw [h.x29]
  have hc6 : ((SBool.cmp .eq .W64 (.load 1 16 8) (.lit 0)).eval env3) = decide (rows.size = 0) := by
    sym_simp
    rw [hcnt]
    have hr := hpre.1.2.1.2.1
    have : LeanVM.Protocol.Compile.wireMaxQueries = 256 := rfl
    by_cases hz : rows.size = 0
    · simp [hz]
    · simp only [hz, decide_false]
      apply beq_eq_false_iff_ne.mpr
      intro he
      have := congrArg BitVec.toNat he
      rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by omega)] at this
      exact hz (this.trans rfl)
  simp only [PcOk, hc6] at hpc6
  by_cases hz : rows.size = 0
  · -- no rows
    simp only [hz, decide_true, ↓reduceIte] at hpc6
    rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b16Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfFinalLevel.b16Offset) NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_9_at]
      at hpc6
    obtain ⟨d6, pc6⟩ := st6
    simp only at hpc6
    subst hpc6
    exact exit_step hp hpre hfr6 true (EachRow.finalOk_of (j := 0) (.inr (by omega))
      fun i _ _ hi ↦ absurd hi (Nat.not_lt_zero _))
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc6
  -- `b4`
  let env4 := Env.ofMachine st6.data [(fb m0, 1952), (m0.regs.SP.toBitVec, 8)]
  have hwf4 : env4.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hfr6.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ hfr6.kept _ (hargs.1 i hi), hargs.2⟩, trivial⟩
      (List.pairwise_pair.mpr (Or.inl (by
        show (fb m0).toNat + 1952 ≤ m0.regs.SP.toBitVec.toNat
        omega)))
  have hm4 : Match env4 argS st6.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hfr6.sp]; simp [Sym.eval])
      ⟨by
        show (st6.data.regs.getXReg .X26).toBitVec = _
        rw [k6 .X26 rfl, h.x26]
        rfl, trivial⟩ trivial trivial
      ⟨by
        show fb m0 + BitVec.ofInt 64 1952 = m0.regs.SP.toBitVec + BitVec.ofInt 64 0
        simp only [fb, base]
        bv_omega, trivial⟩
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk4 run_b4 hwf4 hpc6 hm4 fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨d7, pc7⟩ := st7
  simp only [PcOk] at hpc7
  subst hpc7
  have hl4 : EachRow.Lay m0 1952 eachRowFinalStack 8 40 := ⟨by decide, by decide, by decide, hS⟩
  have hs7 : SameOutside st6.data.dmem d7.dmem (EachRow.Hit m0 1952 eachRowFinalStack 8 40) :=
    EachRow.hit_of_block hl4 hm7 hwf4 (by decide)
  have hfr7 : FR m0 d7 :=
    EachRow.fr_hit hl4 hfr6 (Match.sp_eq hm4 hm7 rfl) (hm7.kept hwf4) hs7 (by decide)
  have k7 : ∀ r, (after b4 argS).reg r = some (.reg r) →
      d7.regs.getXReg r = st6.data.regs.getXReg r := fun r hr ↦
    (rv hm7 (by rw [← after_eq run_b4]; exact hr)).trans rfl
  have hb0 : env4.regions[0]? = some (fb m0, 1952) := rfl
  have hlt32 : (tableOf m0).size < 32 := by have := h.tlen; omega
  have hx29' : env4.regs .X29 = (tableOf m0).size.toUInt64.toBitVec := by
    show (st6.data.regs.getXReg .X29).toBitVec = _
    rw [k6 .X29 rfl, hx29]
  have hult : ((tableOf m0).size.toUInt64.toBitVec).ult (BitVec.ofNat 64 32) = true := by
    rw [toBitVec_ult_ofNat (by decide), natCast_toUInt64_toNat (by omega)]
    simp [hlt32]
  have hw : ∀ (o : Nat) (v : Sym), o + 8 ≤ 1952 →
      (∀ i < 8, findWrite 0 (o + i) (after b4 argS).mem = some (v, i)) →
      WordAt d7.dmem (fb m0 + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env4)) :=
    fun o v ho hv ↦ NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb0 ho
      (by rw [← after_eq run_b4]; exact hv)
  have hqs : (qsOf m0).size = m0.regs.X2.toNat := size_wordSlice _ _ _
  refine cont d7 ⟨hfr7, ⟨?_, ?_, ?_, ?_, ?_⟩, Nat.pos_of_ne_zero hz, Nat.zero_le _,
    fun _ _ _ hi ↦ absurd hi (Nat.not_lt_zero _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw 8 (.ptr 0 1584) (by decide) (by decide)
  · have := hw 16 (.ite (.cmp .ult .W64 (.reg .X29) (.lit 32)) (.reg .X29) (.lit 0)) (by decide)
      (by decide)
    have hv : UInt64.ofBitVec ((Sym.ite (.cmp .ult .W64 (.reg .X29) (.lit 32)) (.reg .X29)
        (.lit 0)).eval env4) = (tableOf m0).size.toUInt64 := by
      sym_simp
      rw [hx29', hult]
      rfl
    rwa [hv] at this
  · have := hw 24 (.ite (.cmp .ult .W64 (.reg .X29) (.lit 32)) (.ptr 0 56) (.lit 8)) (by decide)
      (by decide)
    have hv : UInt64.ofBitVec ((Sym.ite (.cmp .ult .W64 (.reg .X29) (.lit 32)) (.ptr 0 56)
        (.lit 8)).eval env4) = UInt64.ofBitVec (fb m0 + BitVec.ofNat 64 56) := by
      sym_simp
      rw [hx29', hult]
      rfl
    rwa [hv] at this
  · have := hw 32 (.load 1 0 8) (by decide) (by decide)
    have hv : UInt64.ofBitVec ((Sym.load 1 0 8).eval env4) = whirStackArg m0 0 := by
      show UInt64.ofBitVec (env4.load 1 0 8) = _
      rw [Ring.load_eq_wordOf]
      show NativeRustcVm.wordOf st6.data.dmem (m0.regs.SP.toBitVec + BitVec.ofNat 64 0) = _
      refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
      rw [NativeRustcVm.addr_add_add]
      refine hfr6.same _ fun h' ↦ h'.elim (fun hs ↦ ?_) id
      rw [(lay hpre).stack_iff] at hs
      have := NativeRustcVm.toNat_add_ofNat (a := m0.regs.SP.toBitVec) (i := 0 + i)
        (by have := hargs.2; unfold NoWrap at this; omega)
      rw [hSPb] at this
      omega
    rwa [hv] at this
  · refine ⟨h.tlen, EachRow.keep_frame hl4 hs7 (.inr ⟨by decide, by simp [NativeRustcVm.length_wordBytes]⟩) hlen6, ?_⟩
    have e : off (fb m0 + BitVec.ofNat 64 48) 8 = fb m0 + BitVec.ofNat 64 56 :=
      NativeRustcVm.addr_add_add _ _ _
    rw [e]
    refine EachRow.keep_frame hl4 hs7 (.inr ⟨by decide, ?_⟩) hcopy6
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, Array.length_toList]
    have := h.tlen
    omega
  · refine (rv hm7 (r := .X19) rfl).trans ?_
    show UInt64.ofBitVec (UnOp.apply (.ubfm 61 60) .W64 (st6.data.regs.getXReg .X27).toBitVec) = _
    rw [EachRow.lsl3, k6 .X27 rfl, h.x27, hqs, Nat.sub_zero]
    rfl
  · exact (rv hm7 (r := .X25) rfl).trans rfl
  · rw [k7 .X28 rfl]
    refine (rv hm6 (r := .X28) rfl).trans ?_
    show UInt64.ofBitVec (env3.load 1 16 8) = _
    rw [hcnt]
  · rw [k7 .X20 rfl, k6 .X20 rfl, h.x20]
  · rw [k7 .X21 rfl, k6 .X21 rfl, h.x21]
  · rw [k7 .X22 rfl]
    refine (rv hm6 (r := .X22) rfl).trans ?_
    show UInt64.ofBitVec (m0.regs.X3.toBitVec + BitVec.ofInt 64 0) = _
    simp
  · rw [k7 .X23 rfl, k6 .X23 rfl, h.x23]
  · rw [k7 .X24 rfl, k6 .X24 rfl, h.x24]

end

end NativeRustcVmArm.Whir.EachRowOfFinalLevel
