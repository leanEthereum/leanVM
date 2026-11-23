module

public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.Entry
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Start

/-!
# `each_row` with `next_level`'s closure: into the loop

`b3` stores the table's count at 96 and reads the rows' count: none, `Some(())` with the batched
value `0` (`exit_step`). `b4` reads the closure (`μ`'s address, the high part, the batched value's
address, the query weights) and stores the frame's locals, X22 the queries' bytes, X23 the first
query weight's address plus 8, X24 `0`: the loop's invariant before row `0`.
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfNextLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

variable [Host] {k : Nat}

/-- **From `b3` into the loop.** -/
theorem start_step (hp : Placed code k) (hpre : EachRowNextPre rows op m0) {m : MachineData}
    (h : AtB3 m0 m)
    (cont : ∀ m', Inv rows m0 0 m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b3Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨⟨hstk, hrows, hrin, -, -, -, -, -⟩, hcl, -, -, -, -, -, -, -, hapcl, -, haprin, -, -, -,
    -, -⟩ := hpre'
  have hS : 3232 ≤ m0.regs.SP.toNat := hstk.2.1
  have hl := lay hpre
  have hbt : (fb m0).toNat = m0.regs.SP.toNat - 2000 := hl.base_F
  -- `b3`
  let env3 := Env.ofMachine m [(fb m0, 2000), (m0.regs.X3.toBitVec, 32)]
  have hwf3 : env3.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ h.fr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ h.fr.kept _ (hrin.1.1 i hi), hrin.1.2⟩, trivial⟩
      (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm
        (Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hrin.2)))
  have hm3 : Match env3 rowsS m :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [h.fr.sp]; simp [Sym.eval])
      ⟨by show (m.regs.getXReg .X21).toBitVec = _; rw [h.x21]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hcnt : env3.load 1 16 8 = rows.size.toUInt64.toBitVec := by
    refine Ring.load_word ?_
    show WordAt m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 16) _
    have hsame := input_same' hpre h.fr hrin haprin
    refine NativeRustcVm.Transcript.bytesAt_congr (EachRowOfFinalLevel.rows_count hrows)
      fun i hi ↦ ?_
    rw [NativeRustcVm.addr_add_add]
    exact hsame _ (by rw [NativeRustcVm.length_wordBytes] at hi; omega)
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk3 run_b3 hwf3 hm3 fun st6 hm6 hpc6 ↦ ?_
  have hl3 : EachRow.Lay m0 2000 eachRowNextStack 96 104 := ⟨by decide, by decide, by decide, hS⟩
  have hs6 : SameOutside m.dmem st6.data.dmem (EachRow.Hit m0 2000 eachRowNextStack 96 104) :=
    EachRow.hit_of_block hl3 hm6 hwf3 (by decide)
  have hfr6 : FR m0 st6.data :=
    EachRow.fr_hit hl3 h.fr (Match.sp_eq hm3 hm6 rfl) (hm6.kept hwf3) hs6 (by decide)
  have hbat6 : EWAt st6.data.dmem (bOf m0) 0 := bat_keep hpre h.bat hs6 fun q h ↦ hl3.hit_stack h
  have k6 : ∀ r, (after b3 rowsS).reg r = some (.reg r) →
      st6.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (rv hm6 (by rw [← after_eq run_b3]; exact hr)).trans rfl
  have hlen6 : WordAt st6.data.dmem (fb m0 + BitVec.ofNat 64 96) (tableOf m0).size.toUInt64 := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm6 (r := 0) (o := 96) rfl (by decide)
      (v := .reg .X23) (by decide)
    rw [show UInt64.ofBitVec ((Sym.reg .X23).eval env3) = _ from (rfl : _ = m.regs.getXReg .X23),
      h.x23] at this
    exact this
  have hcopy6 : PairsAt st6.data.dmem (fb m0 + BitVec.ofNat 64 104) (tableOf m0).toList := by
    refine EachRow.keep_frame hl3 hs6 (.inr ⟨le_rfl, ?_⟩) h.copy
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, Array.length_toList]
    have := h.tlen
    omega
  have hc6 : ((SBool.cmp .eq .W64 (.load 1 16 8) (.lit 0)).eval env3) = decide (rows.size = 0) := by
    sym_simp
    rw [hcnt]
    have hr := hrows.2.1
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
    rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset) NativeRustcVmArm.Vm.EachRowOfNextLevel.label_13_at]
      at hpc6
    obtain ⟨d6, pc6⟩ := st6
    simp only at hpc6
    subst hpc6
    refine exit_step hp hpre hfr6 ?_
    rw [EachRow.batchedOf_eq, hz, Nat.min_zero]
    exact hbat6
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc6
  -- `b4`
  let env4 := Env.ofMachine st6.data [(fb m0, 2000), (m0.regs.X7.toBitVec, 48)]
  have hwf4 : env4.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hfr6.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩, ⟨fun i hi ↦ hfr6.kept _ (hcl.1.1 i hi), hcl.1.2⟩, trivial⟩
      (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm
        (Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hcl.2)))
  have hm4 : Match env4 envS st6.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hfr6.sp]; simp [Sym.eval])
      ⟨by
        show (st6.data.regs.getXReg .X25).toBitVec = _
        rw [k6 .X25 rfl, h.x25]
        simp [Sym.eval],
       by
        show (st6.data.regs.getXReg .X26).toBitVec = _
        rw [k6 .X26 rfl, h.x26]
        rfl, trivial⟩ trivial trivial trivial
  have hcw : ∀ i, i < 6 → env4.load 1 (8 * i) 8 = (nextEnv m0 i).toBitVec := by
    intro i hi
    rw [Ring.load_eq_wordOf]
    show (NativeRustcVm.wordOf st6.data.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 (8 * i))).toBitVec = _
    have hsame := input_same' hpre hfr6 hcl hapcl
    rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun j hj ↦ by
      rw [NativeRustcVm.addr_add_add]; exact hsame _ (by omega)]
    rfl
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk4 run_b4 hwf4 hpc6 hm4 fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨d7, pc7⟩ := st7
  simp only [PcOk] at hpc7
  rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset) NativeRustcVmArm.Vm.EachRowOfNextLevel.label_5_at]
    at hpc7
  subst hpc7
  have hl4 : EachRow.Lay m0 2000 eachRowNextStack 8 64 := ⟨by decide, by decide, by decide, hS⟩
  have hs7 : SameOutside st6.data.dmem d7.dmem (EachRow.Hit m0 2000 eachRowNextStack 8 64) :=
    EachRow.hit_of_block hl4 hm7 hwf4 (by decide)
  have hfr7 : FR m0 d7 :=
    EachRow.fr_hit hl4 hfr6 (Match.sp_eq hm4 hm7 rfl) (hm7.kept hwf4) hs7 (by decide)
  have k7 : ∀ r, (after b4 envS).reg r = some (.reg r) →
      d7.regs.getXReg r = st6.data.regs.getXReg r := fun r hr ↦
    (rv hm7 (by rw [← after_eq run_b4]; exact hr)).trans rfl
  have hb0 : env4.regions[0]? = some (fb m0, 2000) := rfl
  have hlt32 : (tableOf m0).size < 32 := by have := h.tlen; omega
  have hx23 : env4.regs .X23 = (tableOf m0).size.toUInt64.toBitVec := by
    show (st6.data.regs.getXReg .X23).toBitVec = _
    rw [k6 .X23 rfl, h.x23]
  have hult : ((tableOf m0).size.toUInt64.toBitVec).ult (BitVec.ofNat 64 32) = true := by
    rw [toBitVec_ult_ofNat (by decide), natCast_toUInt64_toNat (by omega)]
    simp [hlt32]
  have hw : ∀ (o : Nat) (v : Sym), o + 8 ≤ 2000 →
      (∀ i < 8, findWrite 0 (o + i) (after b4 envS).mem = some (v, i)) →
      WordAt d7.dmem (fb m0 + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env4)) :=
    fun o v ho hv ↦ NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 hb0 ho
      (by rw [← after_eq run_b4]; exact hv)
  have hwl : ∀ (o i : Nat), i < 6 → o + 8 ≤ 2000 →
      (∀ t < 8, findWrite 0 (o + t) (after b4 envS).mem = some (.load 1 (8 * i) 8, t)) →
      WordAt d7.dmem (fb m0 + BitVec.ofNat 64 o) (nextEnv m0 i) := fun o i hi ho hv ↦ by
    have := hw o (.load 1 (8 * i) 8) ho hv
    rwa [show (Sym.load 1 (8 * i) 8).eval env4 = env4.load 1 (8 * i) 8 from rfl, hcw i hi] at this
  have hqs : (qsOf m0).size = m0.regs.X2.toNat := EachRowOfFinalLevel.size_wordSlice _ _ _
  refine cont d7 ⟨hfr7, ⟨hwl 8 5 (by decide) (by decide) (by decide), ?_, ?_,
    hwl 32 2 (by decide) (by decide) (by decide), hwl 40 1 (by decide) (by decide) (by decide),
    hwl 48 0 (by decide) (by decide) (by decide), ?_, ?_⟩, Nat.pos_of_ne_zero hz, Nat.zero_le _,
    bat_keep hpre hbat6 hs7 (fun q h ↦ hl4.hit_stack h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hw 16 (.ptr 0 1632) (by decide) (by decide)
  · have := hw 24 (.ite (.cmp .ult .W64 (.reg .X23) (.lit 32)) (.reg .X23) (.lit 0)) (by decide)
      (by decide)
    have hv : UInt64.ofBitVec ((Sym.ite (.cmp .ult .W64 (.reg .X23) (.lit 32)) (.reg .X23)
        (.lit 0)).eval env4) = (tableOf m0).size.toUInt64 := by
      sym_simp
      rw [hx23, hult]
      rfl
    rwa [hv] at this
  · have := hw 56 (.ite (.cmp .ult .W64 (.reg .X23) (.lit 32)) (.ptr 0 104) (.lit 8)) (by decide)
      (by decide)
    have hv : UInt64.ofBitVec ((Sym.ite (.cmp .ult .W64 (.reg .X23) (.lit 32)) (.ptr 0 104)
        (.lit 8)).eval env4) = UInt64.ofBitVec (fb m0 + BitVec.ofNat 64 104) := by
      sym_simp
      rw [hx23, hult]
      rfl
    rwa [hv] at this
  · refine ⟨h.tlen, EachRow.keep_frame hl4 hs7 (.inr ⟨by decide, by
      simp [NativeRustcVm.length_wordBytes]⟩) hlen6, ?_⟩
    have e : off (fb m0 + BitVec.ofNat 64 96) 8 = fb m0 + BitVec.ofNat 64 104 :=
      NativeRustcVm.addr_add_add _ _ _
    rw [e]
    refine EachRow.keep_frame hl4 hs7 (.inr ⟨by decide, ?_⟩) hcopy6
    rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, Array.length_toList]
    have := h.tlen
    omega
  · rw [k7 .X19 rfl]
    refine (rv hm6 (r := .X19) rfl).trans ?_
    show UInt64.ofBitVec (env3.load 1 16 8) = _
    rw [hcnt]
  · refine (hm7.regs .X20 _ rfl).trans ?_
    show env4.load 1 (8 * 3) 8 = _
    exact hcw 3 (by decide)
  · rw [k7 .X21 rfl]
    refine (rv hm6 (r := .X21) rfl).trans ?_
    show UInt64.ofBitVec (m0.regs.X3.toBitVec + BitVec.ofInt 64 0) = _
    simp
  · refine (rv hm7 (r := .X22) rfl).trans ?_
    show UInt64.ofBitVec (UnOp.apply (.ubfm 61 60) .W64 (st6.data.regs.getXReg .X28).toBitVec) = _
    rw [EachRow.lsl3, k6 .X28 rfl, h.x28, hqs, Nat.sub_zero]
    rfl
  · refine (hm7.regs .X23 _ rfl).trans ?_
    sym_simp
    rw [show env4.load 1 32 8 = env4.load 1 (8 * 4) 8 from rfl, hcw 4 (by decide)]
  · exact (rv hm7 (r := .X24) rfl).trans rfl

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
