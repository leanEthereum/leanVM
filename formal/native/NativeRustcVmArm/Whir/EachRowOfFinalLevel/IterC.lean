module

public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.IterB

/-!
# `each_row` with `final_level`'s closure: the check of a row

`b11` calls `novel_eval` on the folded scalars and the `What`s, its `Option<EW>` at 1832; `b12`
checks its `Some`, `b13`, `b14` compare it with the folded row limb by limb (a difference: the
outcome `false`); `b15` counts the row: the next iteration, or the outcome `true` after the last
row (`iterC`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfFinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfFinalLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

theorem load_tag {env : Env} {r o : Nat}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) 1) :
    env.load r o 4 = 1#64 := by
  have := (NativeRustcVm.BytesAt.take h 4)
  rw [Env.load_of_bytesAt (bs := (NativeRustcVm.wordBytes 1).take 4) (by decide) this]
  decide

/-- The queries' bytes do not reach `2 ^ 64`. -/
theorem nq_bound (hpre : EachRowFinalPre rows op m0) : 8 * (qsOf m0).size < 2 ^ 64 := by
  have hq := hpre.1.2.2.2.2.1
  have hS : 3184 ≤ m0.regs.SP.toNat := hpre.1.1.2.1
  have hsz : (qsOf m0).size = m0.regs.X2.toNat := size_wordSlice _ _ _
  rw [hsz]
  have h1 : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤ 2 ^ 64 := hq.1.2
  have h2 : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤
      (stackBelow m0 eachRowFinalStack).toNat ∨
      (stackBelow m0 eachRowFinalStack).toNat + eachRowFinalStack ≤ m0.regs.X1.toBitVec.toNat := hq.2
  have h3 : (stackBelow m0 eachRowFinalStack).toNat < 2 ^ 64 := BitVec.isLt _
  rw [stack_eq] at h2
  omega

theorem toBitVec_beq (a b : UInt64) : (a.toBitVec == b.toBitVec) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have : a.toBitVec ≠ b.toBitVec := fun h' ↦ h (UInt64.toBitVec_inj.mp h')
    simp [h, this]

variable [Host] {k : Nat}

/-- **From `b11` to the next iteration or the exit.** -/
theorem iterC (hp : Placed code k) (hnov : Spec (label NativeRustcVmArm.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (hpre : EachRowFinalPre rows op m0) {m : MachineData} (h : Mid rows m0 j m)
    (hF : (⟨m.regs.getXReg .X27, m.regs.getXReg .X26⟩ : EW) =
      foldRow (lanesOf m0.regs.X0.toNat (rows[j]'h.hj)) ((qsOf m0)[j]'h.hjq) (eachRowArgs m0).2)
    (hW : BufWordsAt m.dmem (fb m0 + BitVec.ofNat 64 1576) rootCap
      (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'h.hjq)).toList)
    (cont : ∀ m', Inv rows m0 (j + 1) m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b5Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b11Offset)⟩ := by
  have hl := lay hpre
  have hstk := hpre.1.1
  have hflen : (whirStackArg m0 0).toNat ≤ laneCap := hpre.2.2.1
  have hfold := hpre.2.2.2
  have hjr := h.hj
  have hjq := h.hjq
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr
  let env := Env.ofMachine m [(fb m0, 1952)]
  let W := subspaceAtTable (tableOf m0) ((qsOf m0)[j]'h.hjq)
  have hWs : W.size ≤ 31 := by have := hW.1; rw [Array.length_toList] at this; exact this
  have hl1576 : env.load 0 1576 8 = W.size.toUInt64.toBitVec := by
    have := hW.2.1
    rw [Array.length_toList] at this
    exact Ring.load_word this
  have hl8 : env.load 0 8 8 = fb m0 + BitVec.ofNat 64 1584 := Ring.load_word h.low.w8
  have hl32 : env.load 0 32 8 = (whirStackArg m0 0).toBitVec := Ring.load_word h.low.w32
  have hl40 : env.load 0 40 8 = m0.regs.X7.toBitVec :=
    Ring.load_word (h.fr.slots (40, .X7) (by simp [slots]))
  have hult : (W.size.toUInt64.toBitVec).ult (BitVec.ofNat 64 32) = true := by
    rw [toBitVec_ult_ofNat (by decide), natCast_toUInt64_toNat (by omega)]
    simp
    omega
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk11 run_b11 hwf hm fun st11 hm11 hpc11 ↦ ?_
  have hmid11 : Mid rows m0 j st11.data := h.block hm hm11 hwf rfl rfl (by decide)
  have hd11 : st11.data.dmem = m.dmem := hm11.dmem_eq hwf rfl
  have e0 : st11.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 1832 :=
    (hm11.regs .X0 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 1832)
  have e1 : st11.data.regs.X1 = m0.regs.X7 :=
    (rv hm11 (r := .X1) rfl).trans (by show UInt64.ofBitVec (env.load 0 40 8) = _; rw [hl40])
  have e2 : st11.data.regs.X2 = whirStackArg m0 0 :=
    (rv hm11 (r := .X2) rfl).trans (by show UInt64.ofBitVec (env.load 0 32 8) = _; rw [hl32])
  have e3 : st11.data.regs.X3.toBitVec = fb m0 + BitVec.ofNat 64 1584 := by
    refine (hm11.regs .X3 _ rfl).trans ?_
    sym_simp
    rw [hl1576, hult, hl8]
    rfl
  have e4 : st11.data.regs.X4 = W.size.toUInt64 := by
    refine (rv hm11 (r := .X4) rfl).trans ?_
    sym_simp
    rw [hl1576, hult]
    rfl
  have hWs' : W.size.toUInt64.toNat = W.size := natCast_toUInt64_toNat (by omega)
  have hP : NovelEvalPre st11.data := by
    unfold NovelEvalPre
    rw [e0, e1, e2, e3, e4, hWs']
    exact ⟨hmid11.fr.stackOk hstk (by decide) (by decide),
      ⟨⟨fun i hi ↦ hmid11.fr.kept _ (hfold.1.1 i hi), hfold.1.2⟩,
        hmid11.fr.apart hstk.2.1 hfold.2 (by decide)⟩,
      whirIn_frame hpre hmid11.fr (by show 1584 + 8 * _ ≤ 1952; omega) (by decide) (by decide),
      whirIn_frame hpre hmid11.fr (by decide) (by decide) (by decide)⟩
  refine call_then hpc11 hnov hP fun ⟨d12, pc12⟩ hpc12 ⟨hval, hch, hsv⟩ ↦ ?_
  simp only at hpc12
  subst hpc12
  rw [e0] at hch
  have hs12 : SameOutside st11.data.dmem d12.dmem (HitF m0) :=
    EachRow.hit_of_call hl hmid11.fr.sp (N' := novelEvalStack) (o := 1832) (n := 24)
      (by decide) (by decide) (by decide) hch
  have hmid12 := hmid11.call hpre hs12 hsv
  -- the value
  let r := novelEval (slice m0 m0.regs.X7 (whirStackArg m0 0)) W
  have hr : OptEWAt d12.dmem (fb m0 + BitVec.ofNat 64 1832) (some r) := by
    rw [e0, e1, e2, e3, e4, hWs'] at hval
    simp only [hflen, ↓reduceIte] at hval
    have hsl : slice st11.data m0.regs.X7 (whirStackArg m0 0) =
        slice m0 m0.regs.X7 (whirStackArg m0 0) := by
      unfold slice
      rw [hd11, NativeRustcVm.ewsOf_congr (EachRow.input_same h.fr hstk.2.1 hfold.1.2 hfold.2 fun _ _ h ↦ h)]
    have hws : wordSlice st11.data (fb m0 + BitVec.ofNat 64 1584) W.size = W := by
      unfold wordSlice
      rw [hd11]
      have := hW.2.2
      rw [show fb m0 + BitVec.ofNat 64 1576 + 8#64 = fb m0 + BitVec.ofNat 64 1584 from
        NativeRustcVm.addr_add_add _ _ _] at this
      have := NativeRustcVm.wordsOf_of_wordsAt this
      rw [Array.length_toList] at this
      rw [this, Array.toArray_toList]
    rw [hsl, hws] at hval
    exact hval
  -- `b12` to `b15`
  obtain ⟨hwf12, hm12⟩ := frame_env hpre hmid12.fr
  have htag : (Env.ofMachine d12 [(fb m0, 1952)]).load 0 1832 4 = 1#64 := load_tag hr.1
  have hrc := NativeRustcVm.ewAt_iff.mp hr.2
  have hr0 : (Env.ofMachine d12 [(fb m0, 1952)]).load 0 1840 8 = r.c0.toBitVec := by
    refine Ring.load_word ?_
    have := hrc.1
    rwa [show off (fb m0 + BitVec.ofNat 64 1832) 8 = fb m0 + BitVec.ofNat 64 1840 from
      NativeRustcVm.addr_add_add _ _ _] at this
  have hr1 : (Env.ofMachine d12 [(fb m0, 1952)]).load 0 1848 8 = r.c1.toBitVec := by
    refine Ring.load_word ?_
    have := hrc.2
    rwa [show off (fb m0 + BitVec.ofNat 64 1832) 8 + BitVec.ofNat 64 8 =
      fb m0 + BitVec.ofNat 64 1848 by
        rw [NativeRustcVm.Transcript.off_add]; exact NativeRustcVm.addr_add_add _ _ _] at this
  have k12 : ∀ r, calleeSaved r = true → (after b11 frameS).reg r = some (.reg r) →
      d12.regs.getXReg r = m.regs.getXReg r := fun r hc hr ↦ by
    rw [hsv.1 r hc]
    exact (rv hm11 (by rw [← after_eq run_b11]; exact hr)).trans rfl
  have hx27 : (d12.regs.getXReg .X27) = (foldRow (lanesOf m0.regs.X0.toNat (rows[j]'h.hj))
      ((qsOf m0)[j]'h.hjq) (eachRowArgs m0).2).c0 := by
    rw [k12 .X27 rfl rfl, ← hF]
  have hx26 : (d12.regs.getXReg .X26) = (foldRow (lanesOf m0.regs.X0.toNat (rows[j]'h.hj))
      ((qsOf m0)[j]'h.hjq) (eachRowArgs m0).2).c1 := by
    rw [k12 .X26 rfl rfl, ← hF]
  have hok : okOf m0 ((qsOf m0)[j]'h.hjq) (rows[j]'h.hj) =
      ((foldRow (lanesOf m0.regs.X0.toNat (rows[j]'h.hj)) ((qsOf m0)[j]'h.hjq)
        (eachRowArgs m0).2).c0 == r.c0 &&
      (foldRow (lanesOf m0.regs.X0.toNat (rows[j]'h.hj)) ((qsOf m0)[j]'h.hjq)
        (eachRowArgs m0).2).c1 == r.c1) := EachRow.ew_beq _ _
  have hfalse : ∀ {st : MachineState}, Match (Env.ofMachine d12 [(fb m0, 1952)]) (after b14 (after b13 (after b12 frameS))) st.data ∨
      Match (Env.ofMachine d12 [(fb m0, 1952)]) (after b13 (after b12 frameS)) st.data →
      st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b17Offset) →
      okOf m0 ((qsOf m0)[j]'h.hjq) (rows[j]'h.hj) = false →
      Eventually (step1 Host.exe) (Done rows m0) st := by
    intro st hm' hpc hb
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    have hfr : FR m0 d := by
      rcases hm' with hm' | hm'
      · rw [after_eq run_b14] at hm'
        exact Ring.Fr.ofBlock hmid12.fr hm12 hm' hwf12 rfl rfl rfl (by simp)
      · rw [after_eq run_b13] at hm'
        exact Ring.Fr.ofBlock hmid12.fr hm12 hm' hwf12 rfl rfl rfl (by simp)
    exact exit_step hp hpre hfr false (EachRow.finalOk_false h.hjq h.hj hb)
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hL10 : Labels.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b17Offset) := hp.label (j := NativeRustcVmArm.Vm.EachRowOfFinalLevel.b17Offset) NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_10_at
  refine exec_then hk12 run_b12 hwf12 hm12 fun st12 hm12' hpc12 ↦ ?_
  have hpc12' : st12.pc = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b13Offset) := by
    simp only [PcOk] at hpc12
    sym_simp at hpc12
    rw [htag] at hpc12
    exact hpc12
  refine exec_at hk13 (exec_after run_b12 run_b13) hwf12 hpc12' hm12' fun st13 hm13 hpc13 ↦ ?_
  simp only [PcOk] at hpc13
  sym_simp at hpc13
  simp only [Env.ofMachine_regs, hr0, hx27, toBitVec_beq] at hpc13
  by_cases hc0 : (foldRow (lanesOf m0.regs.X0.toNat (rows[j]'h.hj)) ((qsOf m0)[j]'h.hjq)
      (eachRowArgs m0).2).c0 = r.c0
  swap
  · simp only [beq_false_of_ne hc0, Bool.not_false, ↓reduceIte, hL10] at hpc13
    refine hfalse (.inr (by rw [after_eq run_b13]; exact hm13)) hpc13 ?_
    rw [hok, beq_false_of_ne hc0, Bool.false_and]
  simp only [hc0, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc13
  refine exec_at hk14 (exec_after (exec_after run_b12 run_b13) run_b14) hwf12 hpc13 hm13
    fun st14 hm14 hpc14 ↦ ?_
  simp only [PcOk] at hpc14
  sym_simp at hpc14
  simp only [Env.ofMachine_regs, hr1, hx26, toBitVec_beq] at hpc14
  by_cases hc1 : (foldRow (lanesOf m0.regs.X0.toNat (rows[j]'h.hj)) ((qsOf m0)[j]'h.hjq)
      (eachRowArgs m0).2).c1 = r.c1
  swap
  · simp only [beq_false_of_ne hc1, Bool.not_false, ↓reduceIte, hL10] at hpc14
    refine hfalse (.inl (by rw [after_eq run_b14]; exact hm14)) hpc14 ?_
    rw [hok, beq_false_of_ne hc1, Bool.and_false]
  simp only [hc1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc14
  have hokj : okOf m0 ((qsOf m0)[j]'h.hjq) (rows[j]'h.hj) = true := by
    rw [hok, hc0, hc1]
    simp
  have ok' : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j + 1 →
      okOf m0 (qsOf m0)[i] rows[i] = true := fun i h1 h2 hi ↦ by
    rcases Nat.lt_or_ge i j with hij | hij
    · exact h.ok i h1 h2 hij
    · obtain rfl : i = j := by omega
      exact hokj
  refine exec_at hk15 (exec_after (exec_after (exec_after run_b12 run_b13) run_b14) run_b15)
    hwf12 hpc14 hm14 fun st15 hm15 hpc15 ↦ ?_
  have hfr15 : FR m0 st15.data :=
    Ring.Fr.ofBlock hmid12.fr hm12 hm15 hwf12 rfl rfl rfl (by simp)
  have hx28 : (Env.ofMachine d12 [(fb m0, 1952)]).regs .X28 = rows.size.toUInt64.toBitVec := by
    show (d12.regs.getXReg .X28).toBitVec = _; rw [hmid12.x28]
  have hx25 : (Env.ofMachine d12 [(fb m0, 1952)]).regs .X25 = j.toUInt64.toBitVec := by
    show (d12.regs.getXReg .X25).toBitVec = _; rw [hmid12.x25]
  have hsucc : j.toUInt64.toBitVec + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) := by
    rw [BitVec.ofNat_add]; rfl
  simp only [PcOk] at hpc15
  sym_simp at hpc15
  rw [hx28, hx25, hsucc] at hpc15
  have hrs : rows.size < 2 ^ 64 := by
    have := hpre.1.2.1.2.1
    have : LeanVM.Protocol.Compile.wireMaxQueries = 256 := rfl
    omega
  by_cases hlast : rows.size = j + 1
  · -- the last row
    have hc : (rows.size.toUInt64.toBitVec == BitVec.ofNat 64 (j + 1)) = true := by
      rw [hlast]; exact beq_self_eq_true _
    simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc15
    obtain ⟨d, pc⟩ := st15
    simp only at hpc15
    subst hpc15
    exact exit_step hp hpre hfr15 true (EachRow.finalOk_of (j := j + 1) (.inr (by omega)) ok')
  · have hc : (rows.size.toUInt64.toBitVec == BitVec.ofNat 64 (j + 1)) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have := congrArg BitVec.toNat he
      rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat hrs, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)] at this
      exact hlast this
    simp only [hc, Bool.not_false, ↓reduceIte] at hpc15
    rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfFinalLevel.b5Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfFinalLevel.b5Offset) NativeRustcVmArm.Vm.EachRowOfFinalLevel.label_3_at]
      at hpc15
    obtain ⟨d, pc⟩ := st15
    simp only at hpc15
    subst hpc15
    have k15 : ∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X28],
        d.regs.getXReg r = d12.regs.getXReg r := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (rv hm15 rfl).trans rfl
    have hnq := nq_bound hpre
    refine cont d ⟨hfr15, hm15.dmem_eq hwf12 rfl ▸ hmid12.low, by omega, by omega, ok', ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine (rv hm15 (r := .X19) rfl).trans ?_
      sym_simp
      show UInt64.ofBitVec ((d12.regs.getXReg .X19).toBitVec - BitVec.ofNat 64 8) = _
      rw [hmid12.x19]
      apply UInt64.toBitVec_inj.mp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, UInt64.toNat_toBitVec,
        natCast_toUInt64_toNat (show 8 * ((qsOf m0).size - j) < 2 ^ 64 by omega),
        natCast_toUInt64_toNat (show 8 * ((qsOf m0).size - (j + 1)) < 2 ^ 64 by omega),
        BitVec.toNat_ofNat]
      have := hmid12.hjq
      omega
    · refine (rv hm15 (r := .X25) rfl).trans ?_
      sym_simp
      show UInt64.ofBitVec ((Env.ofMachine d12 [(fb m0, 1952)]).regs .X25 + BitVec.ofNat 64 1) = _
      rw [hx25, hsucc]
      rfl
    · rw [k15 .X28 (by simp), hmid12.x28]
    · rw [k15 .X20 (by simp), hmid12.x20]
    · rw [k15 .X21 (by simp), hmid12.x21]
    · rw [k15 .X22 (by simp), hmid12.x22]
    · rw [k15 .X23 (by simp), hmid12.x23]
    · rw [k15 .X24 (by simp), hmid12.x24]

end

end NativeRustcVmArm.Whir.EachRowOfFinalLevel
