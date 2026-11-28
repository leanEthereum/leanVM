module

public import NativeRustcVmX64.Whir.InducedWeight.Inner
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names

/-!
# `induced_weight`'s queries' loop body (x86-64)

`outer_a`: from the head `b7` after `j` queries (`OInv`), `b7a` spills the sum and loads weight `j`,
`b7b` spills `j`, loads query `j` and calls `subspace_at_table` (the `What`s at 104, the table's
copy at 624 read back, `pairsOf_of_pairsAt`). `outer_b`: `b8` takes the factors' count: none goes
straight to the sum (`Acc`), else `b9` spills `8 · len` and the product loop runs (`inner_a`,
`inner_b`, by `Sym.loop`). `outer_step`: both.
-/

namespace NativeRustcVmX64.Whir.InducedWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region InAny WordAt WordsAt wordOf ewOf BufWordsAt)
open NativeRustcVmX64.Field (midS frameS frameEnv)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq wordAt_of_write eval_reg eval_lit eval_load
  eval_add eval_shl_lit eval_test wf_two apart_symm keepsRegs freeRegs low8_replaceLow)

public section

/-- `b8`'s branch: back to the sum iff no factor (or, impossibly, 32 `What`s or more). -/
theorem b8_cond [Labels] (env : Env) (a b m l : Sym) :
    (SBool.not (.cmp .eq .W8 (.bin .or .W8
        (.bin .merge .W8 a (.ite (.cmp .eq .W64 (.bin .and .W64 m m) (.lit 0)) (.lit 1) (.lit 0)))
        (.bin .merge .W8 b (.ite (.not (.cmp .ult .W64 l (.lit 32))) (.lit 1) (.lit 0))))
      (.lit 0))).eval env =
      (decide ((m.eval env).toNat = 0) || decide (32 ≤ (l.eval env).toNat)) := by
  have h1 : (SBool.cmp .eq .W64 (.bin .and .W64 m m) (.lit 0)).eval env =
      decide ((m.eval env).toNat = 0) := by
    rw [eval_test, bv_beq_toNat]
    rfl
  have h2 : (SBool.not (.cmp .ult .W64 l (.lit 32))).eval env =
      decide (32 ≤ (l.eval env).toNat) := by
    show (!CmpOp.apply .ult .W64 (l.eval env) (BitVec.ofNat 64 32)) = _
    simp only [CmpOp.apply, low_W64, ult_ofNat (show 32 < 2 ^ 64 by decide)]
    by_cases h : (l.eval env).toNat < 32 <;> simp [h]; omega
  show (!CmpOp.apply .eq .W8 (BinOp.apply .or .W8
      (BinOp.apply .merge .W8 (a.eval env)
        (if (SBool.cmp .eq .W64 (.bin .and .W64 m m) (.lit 0)).eval env = true then
          BitVec.ofNat 64 1 else BitVec.ofNat 64 0))
      (BinOp.apply .merge .W8 (b.eval env)
        (if (SBool.not (.cmp .ult .W64 l (.lit 32))).eval env = true then
          BitVec.ofNat 64 1 else BitVec.ofNat 64 0))) (BitVec.ofNat 64 0)) = _
  rw [h1, h2]
  generalize decide ((m.eval env).toNat = 0) = c1
  generalize decide (32 ≤ (l.eval env).toNat) = c2
  cases c1 <;> cases c2 <;>
    simp only [BinOp.apply, CmpOp.apply, low8_replaceLow, ↓reduceIte, Bool.false_eq_true] <;>
    decide

/-- `cmovae`: the unsigned minimum. -/
theorem ite_min' (a b : BitVec 64) :
    (if (!a.ult b) = true then b else a).toNat = min a.toNat b.toNat := by
  rw [bv_ult_toNat]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; omega
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]; omega

/-- **At `b8`**: query `j`'s `What`s at 104, the product the weight. -/
structure AtB8 (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  lp : Loop m0 j st
  hj : j < cntOf m0
  mu : muOf m0 ≤ stackCap
  what : BufWordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 104) rootCap (whatOf m0 j).toList
  rbx : reg st .rbx = (prodOf m0 j 0).c0.toBitVec
  r12 : reg st .r12 = (prodOf m0 j 0).c1.toBitVec
  r14 : reg st .r14 = stackArg m0 0

variable [Host] {k : Nat}

theorem hb7 (hp : Placed code k) : b7a.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset) ∧
    b7b.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset + b7a.length) := by
  have h := b7_in_code.trans hp.1 (by simp [b7])
  rw [← List.take_append_drop 8 b7] at h
  exact h.append
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.InducedWeight.b9Offset) :=
  b9_in_code.trans hp.1 (by simp [b9])

/-- **From the queries' loop head to `b8`**: weight `j`, query `j`'s `What`s. -/
theorem outer_a (hp : Placed code k)
    (hsat : Spec (Labels.label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset)) (hI : OInv m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b8Offset) ∧ AtB8 m0 j s.data) st := by
  obtain ⟨hS, -, hqin, hwin, -, -, -, hgot⟩ := hpre
  obtain ⟨hF, -, hle_a, -, -, -⟩ := stack_le
  have hsl := slots_ok
  have hS1 := hS.1
  have hS2 := hS.2.1
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hsp := hI.sp
  have hjc := hI.hj
  have hjw : j < (reg m0 .r9).toNat := by unfold cntOf at hjc; omega
  have hjq : j < (reg m0 .rcx).toNat := by unfold cntOf at hjc; omega
  have hj64 : j < 2 ^ 64 := by have := (reg m0 .r9).isLt; omega
  have hts : (tbOf m0).size ≤ 31 := by have := hsp.table.1; rwa [Array.length_toList] at this
  -- `b7a`: the sum spilled, weight `j`
  let wa := reg m0 .r8 + BitVec.ofNat 64 (16 * j)
  have hwrd : Readable st.data wa 16 := hfr.readable (Readable.sub hwin.1 (by omega))
  have hapw : Apart (stackBelow m0 1168) (1168 + 8) wa 16 := by
    have h0 := apart_frame' hS hF hwin.2
    have hnw : (reg m0 .r8).toNat + 16 * (reg m0 .r9).toNat ≤ 2 ^ 64 := hwin.1.2
    unfold Apart at h0 ⊢
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  let env1 := Env.ofMachine st.data [(stackBelow m0 1168, 1168 + 8), (wa, 16)]
  have hwf1 : env1.WF := wf_two (stackOk_mono hS hF) hfr.kept hwrd hapw
  have l64 : env1.load 0 64 8 = reg m0 .r8 := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt (word_at hsp.ptrs 4 (by simp)))
  have hsh : BinOp.apply .shl .W64 (reg st.data .rsi) (BitVec.ofNat 64 4) = reg st.data .rsi <<< 4 :=
    eval_shl_lit (env := env1) (a := .reg .rsi) (by decide)
  have hm1 : Match env1 wS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial ⟨by
      show BinOp.apply .add .W64 (env1.load 0 64 8)
        (BinOp.apply .shl .W64 (reg st.data .rsi) (BitVec.ofNat 64 4)) =
          reg m0 .r8 + BitVec.ofNat 64 (16 * j) + BitVec.ofInt 64 0
      rw [add64, l64, hsh, hI.rsi, shl4_eq, Arrays.toNat_ofNat_lt hj64,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine exec_at (hb7 hp).1 run_b7a hwf1 (by intro l h; cases h) hpc hm1 fun s1 hm1' hpc1 ↦ ?_
  obtain ⟨hk1, hsig1, hv88, hv80⟩ := after_eq run_b7a ▸ b7a_write
  have hfr1 := fr_write hS hfr hm1 hm1' hwf1 rfl hk1 rfl (by omega) (hw_of hsig1 (by decide))
  have k1a := fkeep_block hm1' hwf1 (m0 := m0) rfl (lo := 0) (hi := 80) (by omega)
    (hall_of hsig1 (by decide))
  have k1b := fkeep_block hm1' hwf1 (m0 := m0) rfl (lo := 96) (hi := 1176) (by omega)
    (hall_of hsig1 (by decide))
  have w80 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 80) (totOf m0 j).c0 := by
    have := wordAt_of_write hm1' (r := 0) (o := 80) rfl (by decide) (v := .reg .rcx) hv80
    rwa [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .rcx = _ from hI.rcx] at this
  have w88 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 88) (totOf m0 j).c1 := by
    have := wordAt_of_write hm1' (r := 0) (o := 88) rfl (by decide) (v := .reg .rax) hv88
    rwa [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .rax = _ from hI.rax] at this
  have hjws : j < (wsOf m0).size := by rw [wsOf_size]; exact hjw
  have hw : ewOf st.data.dmem wa = prodOf m0 j 0 := by
    rw [prodOf_zero, getD_eq _ _ hjws]
    exact slice_get hfr hS hwin hjw
  have e1rbx : reg s1.data .rbx = (prodOf m0 j 0).c0.toBitVec := by
    refine (hm1'.regs .rbx _ rfl).trans ?_
    show env1.load 1 0 8 = _
    rw [load8_eq, show env1.base 1 = wa from rfl, NativeRustcVm.addr_add_zero, ← hw]
    rfl
  have e1r12 : reg s1.data .r12 = (prodOf m0 j 0).c1.toBitVec := by
    refine (hm1'.regs .r12 _ rfl).trans ?_
    show env1.load 1 8 8 = _
    rw [load8_eq, show env1.base 1 = wa from rfl, ← hw]
    rfl
  have e1 : ∀ r ∈ [Reg64.rsi, .rdx, .r14], reg s1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  have hsp1 : Spills m0 s1.data := hsp.mono (k1a.mono (by omega) (by omega))
    (k1b.mono (by omega) (by omega))
  -- `b7b`: `j` spilled, query `j`, `subspace_at_table`
  let qa := reg m0 .rdx + BitVec.ofNat 64 (8 * j)
  have hqrd : Readable s1.data qa 8 := hfr1.readable (Readable.sub hqin.1 (by omega))
  have hapq : Apart (stackBelow m0 1168) (1168 + 8) qa 8 := by
    have h0 := apart_frame' hS hF hqin.2
    have hnw : (reg m0 .rdx).toNat + 8 * (reg m0 .rcx).toNat ≤ 2 ^ 64 := hqin.1.2
    unfold Apart at h0 ⊢
    rw [toNat_add_ofNat _ _ (by omega)]
    omega
  let env2 := Env.ofMachine s1.data [(stackBelow m0 1168, 1168 + 8), (qa, 8)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b8Offset)).toBitVec
  have hwf2 : env2.WF := wf_two (stackOk_mono hS hF) hfr1.kept hqrd hapq
  have l56 : env2.load 0 56 8 = reg m0 .rdx := by
    rw [load8_eq]
    exact congrArg UInt64.toBitVec
      (NativeRustcVm.wordOf_of_wordAt (word_at hsp1.ptrs 3 (by simp)))
  have hm2 : Match env2 qS s1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr1.rsp, trivial⟩ trivial trivial ⟨by
      show BinOp.apply .add .W64 (env2.load 0 56 8)
        (BinOp.apply .mul .W64 (reg s1.data .rsi) (BitVec.ofNat 64 8)) =
          reg m0 .rdx + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 0
      rw [add64, mul64, l56, e1 .rsi (by simp), hI.rsi, mul_lit, show j * 8 = 8 * j by omega,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset + b7a.length) := hpc1
  refine exec_at (hb7 hp).2 run_b7b hwf2 (fun _ _ ↦ rfl) hpc1' hm2 fun s2 hm2' hpc2 ↦ ?_
  obtain ⟨hk2, hsig2, hv72⟩ := after_eq run_b7b ▸ b7b_call
  have hrsp2 := rsp_call hm2' rfl
  have hkept2 : Kept m0.dmem s2.data.dmem := fun p h ↦ hm2'.kept hwf2 p (hfr1.kept p h)
  have k2 := fkeep_block hm2' hwf2 (m0 := m0) rfl (lo := 8) (hi := 72) (by omega)
    (hall_of hsig2 (by decide))
  have k2b := fkeep_block hm2' hwf2 (m0 := m0) rfl (lo := 80) (hi := 1176) (by omega)
    (hall_of hsig2 (by decide))
  have w72 : WordAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 72) j.toUInt64 := by
    have := wordAt_of_write hm2' (r := 0) (o := 72) rfl (by decide) (v := .reg .rsi) hv72
    rwa [eval_reg, Env.ofMachine_regs,
      show s1.data.regs.get64 .rsi = _ from (e1 .rsi (by simp)).trans hI.rsi] at this
  have hjqs : j < (qsOf m0).size := by rw [qsOf_size]; exact hjq
  let q := (qsOf m0)[j]'hjqs
  have hq : wordOf s1.data.dmem qa = q := by
    have hargs := hfr1.get?_arg hS hqin (fun r hr ↦ absurd hr List.not_mem_nil)
    simp only [q, qsOf, wordSlice, List.getElem_toArray, NativeRustcVm.getElem_wordsOf]
    refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
    rw [addr_add]
    exact hargs _ (by omega)
  have f0 : reg s2.data .rdi = fbOf m0 + BitVec.ofNat 64 104 := hm2'.regs .rdi _ rfl
  have f1 : reg s2.data .rsi = fbOf m0 + BitVec.ofNat 64 624 := by
    refine (hm2'.regs .rsi _ rfl).trans ?_
    show env2.load 0 32 8 = _
    rw [load8_eq]
    exact congrArg UInt64.toBitVec
      (NativeRustcVm.wordOf_of_wordAt (word_at hsp1.ptrs 0 (by simp)))
  have f2 : (reg s2.data .rdx).toNat = (tbOf m0).size := by
    rw [show reg s2.data .rdx = reg st.data .rdx from
      (Match.reg_eq hm2 hm2' rfl rfl).trans (e1 .rdx (by simp)), hI.rdx,
      Arrays.toNat_ofNat_lt (by omega)]
  have f3 : reg s2.data .rcx = q.toBitVec := by
    refine (hm2'.regs .rcx _ rfl).trans ?_
    show env2.load 1 0 8 = _
    rw [load8_eq, show env2.base 1 = qa from rfl, NativeRustcVm.addr_add_zero,
      show env2.mem0 = s1.data.dmem from rfl, hq]
  have h104 : (fbOf m0 + BitVec.ofNat 64 104).toNat = (rspOf m0).toNat - 1168 + 104 :=
    fb_toNat hS hF (by omega)
  have h624 : (fbOf m0 + BitVec.ofNat 64 624).toNat = (rspOf m0).toNat - 1168 + 624 :=
    fb_toNat hS hF (by omega)
  have hP : SubspaceAtTablePre s2.data := by
    unfold SubspaceAtTablePre
    rw [f0, f1, f2]
    refine ⟨stackOk_callee hS hkept2 hrsp2 hle_a, hts, whirIn_fr hS hkept2 hrsp2 hle_a
      (by omega) (by omega), whirIn_fr hS hkept2 hrsp2 hle_a (by omega) (by decide), Or.inl ?_, ?_⟩
    · rw [h104, h624]
      unfold whatBytes rootCap
      omega
    · apply hfr1.got_after hS hle_a hgot hwf2 hm2' (hw_of hsig2 (by decide)) hrsp2
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      have hb := (frame_ok hS hF).2.2
      rcases ha with rfl | rfl
      · rw [h624, hb]
        omega
      · rw [h104, hb]
        unfold whatBytes rootCap
        omega
  refine Frame.call hsat hfr1 hS hle_a (L := 1120) (by omega) hsl out_nil hwf2 hm2 hm2' hpc2 hk2
    rfl (hw_of hsig2 (by decide)) hP
    (fun m' ⟨_, hch, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hch p fun h ↦ hp (h.elim (fun ⟨r, hr, hin⟩ ↦ by
        rw [List.mem_singleton] at hr
        subst hr
        have h' : InRange (reg s2.data .rdi) whatBytes p := hin
        rw [f0] at h'
        exact .inr (.inl (inRange_low_of hS hF (c := 104) (n := whatBytes) (by omega)
          (by decide) h'))) (fun h ↦ .inr (.inr h)))⟩)
    fun s3 hpc3 hfr3 ⟨hval, hch3, hsv3⟩ ↦ ?_
  rw [f0] at hch3
  have k3 := fkeep_call hS hrsp2 hle_a (c := 104) (n := whatBytes) hch3 (by decide) (by omega)
    (lo := 8) (hi := 104) (by omega) (.inl le_rfl)
  have k3b := fkeep_call hS hrsp2 hle_a (c := 104) (n := whatBytes) hch3 (by decide) (by omega)
    (lo := 360) (hi := 1176) le_rfl (.inr (by decide))
  have hsp2 : Spills m0 s2.data := hsp1.mono (k2.mono (by omega) (by omega))
    (k2b.mono (by omega) (by omega))
  have hpairs : pairsOf s2.data.dmem (fbOf m0 + BitVec.ofNat 64 624) (tbOf m0).size =
      (tbOf m0).toList := by
    have := pairsOf_of_pairsAt hsp2.table.2.2
    simp only [NativeRustcVm.Transcript.off, addr_add, Array.length_toList] at this
    exact this
  have hwj : whatOf m0 j = subspaceAtTable (tbOf m0) q := by
    unfold whatOf subspaceAt
    rw [getD_eq _ _ hjqs]
    rfl
  rw [f0, f1, f2, f3, UInt64.ofBitVec_toBitVec, hpairs, Array.toArray_toList, ← hwj] at hval
  have e3 : ∀ r ∈ [Reg64.rbx, .r12, .r14], reg s3.data r = reg s1.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv3.1 _ rfl).trans (Match.reg_eq hm2 hm2' rfl rfl)
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b8Offset) := hpc3
  refine .done _ ⟨hpc3', hfr3, hsp2.mono (k3.mono (by omega) (by omega))
    (k3b.mono (by omega) (by omega)), ⟨word_keep w72 k3 (by omega) (by omega), ?_⟩, hjc, hI.mu,
    hval, (e3 .rbx (by simp)).trans e1rbx, (e3 .r12 (by simp)).trans e1r12,
    (e3 .r14 (by simp)).trans ((e1 .r14 (by simp)).trans hI.r14)⟩
  refine NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩
  · exact word_keep (word_keep w80 k2b (by omega) (by omega)) k3 (by omega) (by omega)
  · rw [addr_add]
    exact word_keep (word_keep w88 k2b (by omega) (by omega)) k3 (by omega) (by omega)

/-- **From `b8`**: the factors' count; the product loop, to the sum. -/
theorem outer_b (hp : Placed code k) (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b8Offset)) (hA : AtB8 m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b6Offset) ∧ Acc m0 j s.data) st := by
  have hpre' := hpre
  obtain ⟨hS, hargs, -, -, -, -, -⟩ := hpre'
  obtain ⟨hF, -, -, -, -, -⟩ := stack_le
  have hfr := hA.fr
  have hw31 : (whatOf m0 j).toList.length ≤ 31 := hA.what.1
  have hlen : lenOf m0 j ≤ 31 := by
    have := Nat.min_le_right (ptOf m0).size (whatOf m0 j).size; simp at hw31; unfold lenOf; omega
  -- `b8`: the count
  obtain ⟨hard, hap, -⟩ := args_ok hS hargs
  let env1 := Env.ofMachine st.data [(stackBelow m0 1168, 1168 + 8), (rspOf m0 + 8#64, 16)]
  have hwf1 : env1.WF := wf_two (stackOk_mono hS hF) hfr.kept (Readable.keep hard hfr.kept) hap
  have hm1 : Match env1 a8S st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial ⟨fb_args8 m0, trivial⟩
  refine exec_at (hb8 hp) run_b8 hwf1 (by intro l h; cases h) hpc hm1 fun s1 hm1' hpc1 ↦ ?_
  obtain ⟨hk1, hsig1, hv16⟩ := after_eq run_b8 ▸ b8_write
  have hfr1 := fr_write hS hfr hm1 hm1' hwf1 rfl hk1 rfl (by omega) (hw_of hsig1 (by decide))
  have k1a := fkeep_block hm1' hwf1 (m0 := m0) rfl (lo := 24) (hi := 1176) (by omega)
    (hall_of hsig1 (by decide))
  have l104 : env1.load 0 104 8 = BitVec.ofNat 64 (whatOf m0 j).size := by
    rw [load8_eq]
    have := congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt hA.what.2.1)
    rw [Array.length_toList] at this
    exact this
  have l18 : env1.load 1 8 8 = stackArg m0 1 := arg_load (i := 1) hS hargs hfr rfl rfl (by omega)
  have hwl : (whatOf m0 j).size ≤ 31 := by simpa using hw31
  have hmin : (Sym.ite (.not (.cmp .ult .W64 (.load 0 104 8) (.load 1 8 8))) (.load 1 8 8)
      (.load 0 104 8)).eval env1 = BitVec.ofNat 64 (lenOf m0 j) := by
    apply BitVec.eq_of_toNat_eq
    show (if (!(CmpOp.apply .ult .W64 (env1.load 0 104 8) (env1.load 1 8 8))) = true then
      env1.load 1 8 8 else env1.load 0 104 8).toNat = _
    simp only [CmpOp.apply, low_W64]
    rw [ite_min', l104, l18, Arrays.toNat_ofNat_lt (by omega), Arrays.toNat_ofNat_lt (by omega)]
    unfold lenOf
    rw [ptOf_size, Nat.min_comm]
  have w16 : WordAt s1.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (lenOf m0 j).toUInt64 := by
    have := wordAt_of_write hm1' (r := 0) (o := 16) rfl (by decide) hv16
    rwa [hmin] at this
  have e1 : ∀ r ∈ [Reg64.rbx, .r12, .r14], reg s1.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm1' rfl rfl
  simp only [PcOk] at hpc1
  rw [b8_cond, hmin, eval_load, l104, Arrays.toNat_ofNat_lt (by omega),
    Arrays.toNat_ofNat_lt (by omega)] at hpc1
  obtain ⟨hT, hF1⟩ := Arrays.pc_cond hpc1
  have hsp1 : Spills m0 s1.data := hA.sp.mono (k1a.mono le_rfl (by omega)) (k1a.mono (by omega)
    (by omega))
  have hlp1 : Loop m0 j s1.data := hA.lp.mono (k1a.mono (by omega) (by omega))
  by_cases h0 : lenOf m0 j = 0
  · refine .done _ ⟨(hT (by simp [h0])).trans (hp.label NativeRustcVmX64.Vm.InducedWeight.label_9_at), hfr1, hsp1, hlp1, hA.hj,
      hA.mu, ?_, ?_, (e1 .r14 (by simp)).trans hA.r14⟩
    · rw [h0]; exact (e1 .rbx (by simp)).trans hA.rbx
    · rw [h0]; exact (e1 .r12 (by simp)).trans hA.r12
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b9Offset) := hF1 (by simp; omega)
  -- `b9`: `8 · len`
  have hwf2 := hfr1.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb9 hp) run_b9 hwf2 (by intro l h; cases h) hpc1' hfr1.mid_match
    fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hsig2, hv16'⟩ := after_eq run_b9 ▸ b9_write
  have hfr2 := fr_write hS hfr1 hfr1.mid_match hm2 hwf2 rfl hk2 rfl (by omega)
    (hw_of hsig2 (by decide))
  have k2 := fkeep_block hm2 hwf2 (m0 := m0) rfl (lo := 24) (hi := 1176) (by omega)
    (hall_of hsig2 (by decide))
  have w16' : WordAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (8 * lenOf m0 j).toUInt64 := by
    have := wordAt_of_write hm2 (r := 0) (o := 16) rfl (by decide) hv16'
    rw [eval_shl_lit _ (by decide), eval_load, load8_eq,
      show (frameEnv m0 s1.data 1168 (fun _ ↦ 0) 0).base 0 = fbOf m0 from rfl,
      Env.ofMachine_mem0, NativeRustcVm.wordOf_of_wordAt w16, shl3_eq,
      show ((lenOf m0 j).toUInt64).toBitVec.toNat = lenOf m0 j from
        Arrays.toNat_ofNat_lt (by omega)] at this
    exact this
  have e2 : ∀ r ∈ [Reg64.rbx, .r12, .r14], reg s2.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (Match.reg_eq hfr1.mid_match hm2 rfl rfl).trans (e1 _ (by simp))
  have hI0 : IInv m0 j 0 s2.data :=
    ⟨hfr2, hsp1.mono (k2.mono le_rfl (by omega)) (k2.mono (by omega) (by omega)),
      hlp1.mono (k2.mono (by omega) (by omega)), hA.hj, hA.mu,
      bufWords_keep (bufWords_keep hA.what k1a (by omega) (by omega)) k2 (by omega) (by omega),
      w16', by omega, (e2 .rbx (by simp)).trans hA.rbx, (e2 .r12 (by simp)).trans hA.r12,
      (e2 .r14 (by simp)).trans hA.r14, (hm2.regs .r15 _ rfl).trans rfl⟩
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset) := hpc2
  -- the product loop
  refine Sym.loop (fun n s ↦ ∃ i, n = lenOf m0 j - i ∧ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b10Offset) ∧
    IInv m0 j i s.data) (fun n s ⟨i, hn, hpc, hI⟩ ↦ ?_) ⟨0, rfl, hpc2', hI0⟩
  have hi := hI.hi
  refine ((inner_a hp hkmul hpre hpc hI).bind fun s ⟨hpc', hA'⟩ ↦
    inner_b hp hmul hpre hpc' hA').mono fun s' h ↦ ?_
  rcases h with ⟨hpc', hI'⟩ | h
  · exact .inr ⟨lenOf m0 j - (i + 1), by omega, i + 1, rfl, hpc', hI'⟩
  · exact .inl h

/-- **A turn of the queries' loop**: query `j`'s product. -/
theorem outer_step (hp : Placed code k)
    (hsat : Spec (Labels.label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hkmul : Spec (Labels.label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b7Offset)) (hI : OInv m0 j st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.InducedWeight.b6Offset) ∧ Acc m0 j s.data) st :=
  (outer_a hp hsat hpre hpc hI).bind fun _ ⟨hpc', hA⟩ ↦ outer_b hp hkmul hmul hpre hpc' hA

end

end NativeRustcVmX64.Whir.InducedWeight
