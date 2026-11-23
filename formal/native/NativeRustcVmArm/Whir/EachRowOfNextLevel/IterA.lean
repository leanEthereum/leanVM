module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.LanesOf.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Code.Vm.RowsRow.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Whir.EachRowOfNextLevel.IterD

/-!
# `each_row` with `next_level`'s closure: an iteration

At `.LEachRowOfNextLevel_5` (`Inv j`): `b8` ends the loop when the queries are exhausted; `b9`
reads query `j`, clears the lanes and calls `Rows::row(j)`; `b10` calls `lanes_of` on the row into
the lanes; then `iterB`, `iterC`, `iterD` (`iter_step`), the batched value gaining row `j`'s term
(`parOf_succ`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfNextLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Compile (wireMaxQueries wireMaxLeafWords)
open NativeVm (openingWords)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- **Row `j`'s term**, added to the batched value. -/
theorem parOf_succ (hj : j < rows.size) (hjq : j < (qsOf m0).size) :
    parOf rows m0 (j + 1) = parOf rows m0 j + (qwOf m0).getD j 0 *
      (foldRow (lanesOf m0.regs.X0.toNat (rows[j]'hj)) ((qsOf m0)[j]'hjq) (eachRowArgs m0).2 +
        EW.scale ((subspaceAtTable (tableOf m0) ((qsOf m0)[j]'hjq)).getD m0.regs.X4.toNat 0)
          (novelEval (highOf m0) (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'hjq)))) := by
  unfold parOf
  rw [EachRow.nextPartial_succ]
  unfold EachRow.nextTerm
  rw [show rows.getD j #[] = rows[j] by simp [Array.getD, hj],
    show (qsOf m0).getD j 0 = (qsOf m0)[j] by simp [Array.getD, hjq]]

/-- **The rows**, unchanged in a body. -/
theorem rowsAt_of_fr (hpre : EachRowNextPre rows op m0) {m : MachineData} (hfr : FR m0 m) :
    NativeRustcVm.Sumcheck.RowsAt m.dmem m0.regs.X3.toBitVec op rows := by
  obtain ⟨hp0, hsz, w, hw, hhdr, hrow⟩ := hpre.1.2.1
  have hr := input_same' hpre hfr hpre.1.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.2.1
  have ho := input_same' hpre hfr hpre.1.2.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨hp0, hsz, w, hw, NativeRustcVm.Transcript.bytesAt_congr hhdr fun i hi ↦ hr i ?_,
    fun j hj ↦ ⟨(hrow j hj).1, NativeRustcVm.Transcript.bytesAt_congr (hrow j hj).2 fun i hi ↦ ?_⟩⟩
  · rw [NativeRustcVm.length_wordsBytes] at hi
    simpa using hi
  · rw [off, NativeRustcVm.addr_add_add]
    refine ho _ ?_
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, (hrow j hj).1] at hi
    have : wireMaxQueries = 256 := rfl
    have : wireMaxLeafWords = 64 := rfl
    have : openingWords = 193 := rfl
    have : NativeRustcVm.Sumcheck.openingsWords = 49408 := rfl
    have hj' : j < 256 := by omega
    show _ < 8 * 49408
    nlinarith

/-- Query `j`'s address, as the executor computes it. -/
theorem qAddr_eval [Labels] {env : Env} (j : Nat)
    (h24 : env.regs .X24 = j.toUInt64.toBitVec) :
    qAddr.eval env = env.load 0 88 8 + BitVec.ofNat 64 (8 * j) := by
  simp only [qAddr, Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64, h24]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq, BitVec.toNat_ofInt]
  omega

/-- Query `j`, as the entry's memory holds it. -/
theorem query_word (hpre : EachRowNextPre rows op m0) {m : MachineData} (hfr : FR m0 m)
    (hj : j < (qsOf m0).size) :
    NativeRustcVm.wordOf m.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * j)) =
      (qsOf m0)[j]'hj := by
  have hsz : (qsOf m0).size = m0.regs.X2.toNat := EachRowOfFinalLevel.size_wordSlice _ _ _
  have hs := input_same' hpre hfr hpre.1.2.2.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]; exact hs _ (by omega)]
  simp [qsOf, eachRowArgs, wordSlice]

/-- The queries' bytes do not reach `2 ^ 64`. -/
theorem nq_bound (hpre : EachRowNextPre rows op m0) : 8 * (qsOf m0).size < 2 ^ 64 := by
  have hq := hpre.1.2.2.2.2.1
  have hsz : (qsOf m0).size = m0.regs.X2.toNat := EachRowOfFinalLevel.size_wordSlice _ _ _
  rw [hsz]
  have h1 : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤ 2 ^ 64 := hq.1.2
  have h2 : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤
      (stackBelow m0 eachRowNextStack).toNat ∨
      (stackBelow m0 eachRowNextStack).toNat + eachRowNextStack ≤ m0.regs.X1.toBitVec.toNat := hq.2
  have h3 : (stackBelow m0 eachRowNextStack).toNat < 2 ^ 64 := BitVec.isLt _
  rw [stack_eq] at h2
  omega

variable [Host] {k : Nat}

/-- **An iteration**: from the invariant before row `j`, the exit or the invariant before row
`j + 1`. -/
theorem iter_step (hp : Placed code k)
    (hrow : Spec (label NativeRustcVmArm.Vm.RowsRow.entryLabel) (RowsRowPre op rows) (RowsRowPost op rows))
    (hlanes : Spec (label NativeRustcVmArm.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost)
    (hfold : Spec (label NativeRustcVmArm.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label NativeRustcVmArm.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hnov : Spec (label NativeRustcVmArm.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : EachRowNextPre rows op m0) {m : MachineData} (h : Inv rows m0 j m)
    (cont : ∀ m', Inv rows m0 (j + 1) m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset)⟩ := by
  have hl := lay hpre
  have hstk := hpre.1.1
  have hS : 3232 ≤ m0.regs.SP.toNat := hstk.2.1
  have hqin := hpre.1.2.2.2.2.1
  have hopin := hpre.1.2.2.2.1
  have hnq := nq_bound hpre
  have hsz : (qsOf m0).size = m0.regs.X2.toNat := EachRowOfFinalLevel.size_wordSlice _ _ _
  have hjr := h.hj
  have hjq := h.hjq
  have hrs : rows.size ≤ 256 := hpre.1.2.1.2.1
  -- `b8`
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk8 run_b8 hwf hm fun st5 hm5 hpc5 ↦ ?_
  have hfr5 : FR m0 st5.data := Ring.Fr.ofBlock h.fr hm hm5 hwf rfl rfl rfl (by simp)
  have hd5 : st5.data.dmem = m.dmem := hm5.dmem_eq hwf rfl
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  simp only [Env.ofMachine_regs, h.x22] at hpc5
  by_cases hjn : j = (qsOf m0).size
  · -- queries exhausted
    have hc : ((8 * ((qsOf m0).size - j)).toUInt64.toBitVec == BitVec.ofNat 64 0) = true := by
      rw [hjn, Nat.sub_self]; rfl
    rw [hc] at hpc5
    simp only [↓reduceIte] at hpc5
    rw [show Labels.label NativeRustcVmArm.Vm.EachRowOfNextLevel.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset) from hp.label (j := NativeRustcVmArm.Vm.EachRowOfNextLevel.b23Offset) NativeRustcVmArm.Vm.EachRowOfNextLevel.label_13_at]
      at hpc5
    obtain ⟨d, pc⟩ := st5
    simp only at hpc5
    subst hpc5
    refine exit_step hp hpre hfr5 ?_
    rw [EachRow.batchedOf_eq, show min (eachRowArgs m0).1.size rows.size = j by
      have : j = (eachRowArgs m0).1.size := hjn
      omega, hd5]
    exact h.bat
  have hjq' : j < (qsOf m0).size := by omega
  have hnq' : 8 * (eachRowArgs m0).1.size < 2 ^ 64 := hnq
  have hjq'' : j < (eachRowArgs m0).1.size := hjq'
  have hc : ((8 * ((qsOf m0).size - j)).toUInt64.toBitVec == BitVec.ofNat 64 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by omega),
      show (BitVec.ofNat 64 0).toNat = 0 from rfl] at this
    omega
  rw [hc] at hpc5
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc5
  -- `b9`: query `j`, `Rows::row(j)`
  obtain ⟨qa, hqad⟩ : ∃ qa, qa = m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * j) := ⟨_, rfl⟩
  have hqnw : m0.regs.X1.toBitVec.toNat + 8 * m0.regs.X2.toNat ≤ 2 ^ 64 := hqin.1.2
  have hqa : qa.toNat = m0.regs.X1.toBitVec.toNat + 8 * j := by
    rw [hqad]; exact NativeRustcVm.toNat_add_ofNat (by omega)
  have hbt : (fb m0).toNat = m0.regs.SP.toNat - 2000 := hl.base_F
  have hfq : Apart (fb m0) 2000 qa 8 := by
    have := Ring.apart_frame (F := 2000) hstk.2.1 (by decide) hqin.2
    unfold Apart at this ⊢
    have hbt' : (base m0 2000).toNat = m0.regs.SP.toNat - 2000 := hl.base_F
    rw [hbt'] at this
    rw [hqa, hbt]
    omega
  let env6 := Env.ofMachine st5.data [(fb m0, 2000), (qa, 8)]
  have hwf6 : env6.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hfr5.kept _ (Ring.frame_mapped hstk (by decide) i hi),
        Ring.base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ by
        rw [hqad, NativeRustcVm.addr_add_add]
        exact hfr5.kept _ (hqin.1.1 _ (by omega)), show qa.toNat + 8 ≤ 2 ^ 64 by omega⟩, trivial⟩
      (List.pairwise_pair.mpr hfq)
  have hx24 : env6.regs .X24 = j.toUInt64.toBitVec := by
    show (st5.data.regs.getXReg .X24).toBitVec = _
    have e : st5.data.regs.getXReg .X24 = m.regs.getXReg .X24 := (rv hm5 (r := .X24) rfl).trans rfl
    rw [e, h.x24]
  have hl88 : env6.load 0 88 8 = m0.regs.X1.toBitVec :=
    Ring.load_word ((hd5 ▸ h.fr.slots (88, .X1) (by simp [slots])) :
      WordAt st5.data.dmem _ _)
  have hm6 : Match env6 queryS st5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hfr5.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        show qAddr.eval env6 = qa + BitVec.ofInt 64 0
        rw [qAddr_eval j hx24, hl88, hqad]
        simp, trivial⟩
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk9 run_b9 hwf6 hpc5 hm6 fun st6 hm6' hpc6 ↦ ?_
  have hs6 : SameOutside st5.data.dmem st6.data.dmem (HitN m0) :=
    EachRow.hit_of_block hl hm6' hwf6 (by decide)
  have k6 : ∀ r ∈ loopRegs, r ≠ .X26 → st6.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr hne
    have h5 : ∀ r ∈ loopRegs, (after b8 frameS).reg r = some (.reg r) := by
      rw [after_eq run_b8]; decide
    rw [(rv hm6' (v := .reg r) (by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl |
        exact absurd rfl hne)).trans rfl]
    exact (rv hm5 (by rw [← after_eq run_b8]; exact h5 r hr)).trans rfl
  have hq : st6.data.regs.getXReg .X26 = (qsOf m0)[j]'hjq' := by
    refine (rv hm6' (r := .X26) rfl).trans ?_
    show UInt64.ofBitVec (env6.load 1 0 8) = _
    rw [Ring.load_eq_wordOf]
    show NativeRustcVm.wordOf st5.data.dmem (qa + BitVec.ofNat 64 0) = _
    rw [NativeRustcVm.addr_add_zero, hd5, hqad]
    exact query_word hpre h.fr hjq'
  have hmid6 : Mid rows m0 j st6.data :=
    ⟨EachRow.fr_hit hl hfr5 (Match.sp_eq hm6 hm6' rfl) (hm6'.kept hwf6) hs6 slots_ok,
      (hd5 ▸ h.low).keep hl hs6, hjr, hjq',
      bat_keep hpre (hd5 ▸ h.bat) hs6 fun q h ↦ hl.hit_stack h,
      (k6 .X19 (by simp [loopRegs]) (by decide)).trans h.x19,
      (k6 .X20 (by simp [loopRegs]) (by decide)) ▸ h.x20,
      (k6 .X21 (by simp [loopRegs]) (by decide)).trans h.x21,
      (k6 .X22 (by simp [loopRegs]) (by decide)).trans h.x22,
      (k6 .X23 (by simp [loopRegs]) (by decide)) ▸ h.x23,
      (k6 .X24 (by simp [loopRegs]) (by decide)).trans h.x24, hq⟩
  have e6x0 : st6.data.regs.X0 = m0.regs.X3 := by
    refine (rv hm6' (r := .X0) rfl).trans ?_
    show st5.data.regs.getXReg .X21 = _
    have e : st5.data.regs.getXReg .X21 = m.regs.getXReg .X21 := (rv hm5 (r := .X21) rfl).trans rfl
    rw [e, h.x21]
  have e6x1 : st6.data.regs.X1 = j.toUInt64 := (rv hm6' (r := .X1) rfl).trans
    (by show UInt64.ofBitVec (env6.regs .X24) = _; rw [hx24])
  have hP6 : RowsRowPre op rows st6.data := by
    unfold RowsRowPre
    rw [e6x0]
    exact ⟨rowsAt_of_fr hpre hmid6.fr, hpre.1.2.2.1.1.2⟩
  refine call_then hpc6 hrow hP6 fun ⟨d7, pc7⟩ hpc7 ⟨hres, hd7, hsv7⟩ ↦ ?_
  simp only at hpc7
  subst hpc7
  have hj6 : st6.data.regs.X1.toNat = j := by
    rw [e6x1, natCast_toUInt64_toNat (by omega)]
  obtain ⟨hw7, ha7, hW7⟩ := hres (hj6 ▸ hjr)
  simp only [hj6] at hw7 ha7 hW7
  have hmid7 : Mid rows m0 j d7 := hmid6.call hpre (fun q _ ↦ by rw [hd7]) hsv7
  -- `b10`: `lanes_of`
  obtain ⟨hwf7, hm7⟩ := frame_env hpre hmid7.fr
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  rw [show k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b9Offset + b9.length =
      k + NativeRustcVmArm.Vm.EachRowOfNextLevel.b10Offset by
    rw [Nat.add_assoc, NativeRustcVmArm.Vm.EachRowOfNextLevel.b9_next]]
  refine exec_then hk10 run_b10 hwf7 hm7 fun st8 hm8 hpc8 ↦ ?_
  have hmid8 : Mid rows m0 j st8.data := hmid7.block hm7 hm8 hwf7 rfl rfl (by decide)
  have hd8 : st8.data.dmem = d7.dmem := hm8.dmem_eq hwf7 rfl
  obtain ⟨ra, hradef⟩ : ∃ ra, ra = off op (8 * (1 + j * openingWords)) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w, w = (rows[j]'hjr).size := ⟨_, rfl⟩
  rw [← hradef] at ha7
  have hw64 : w ≤ 64 := by
    obtain ⟨-, -, w', hw', -, hrow'⟩ := hpre.1.2.1
    rw [hwdef, (hrow' j hjr).1]
    exact hw'
  have hl80 : (Env.ofMachine d7 [(fb m0, 2000)]).load 0 80 8 = m0.regs.X0.toBitVec :=
    Ring.load_word (hmid7.fr.slots (80, .X0) (by simp [slots]))
  have e8x0 : st8.data.regs.X0 = m0.regs.X0 := (rv hm8 (r := .X0) rfl).trans
    (by show UInt64.ofBitVec ((Env.ofMachine d7 [(fb m0, 2000)]).load 0 80 8) = _; rw [hl80])
  have e8x1 : st8.data.regs.X1.toBitVec = ra := (hm8.regs .X1 _ rfl).trans ha7
  have e8x2 : st8.data.regs.X2.toNat = w := by
    rw [show st8.data.regs.X2 = d7.regs.X1 from (rv hm8 (r := .X2) rfl).trans rfl, hwdef]
    exact hw7
  have e8x3 : st8.data.regs.X3.toBitVec = fb m0 + BitVec.ofNat 64 600 :=
    (hm8.regs .X3 _ rfl).trans (EachRow.eval_ptr0 _ _ _ _ 600)
  have hopnw : op.toNat + 8 * 49408 ≤ 2 ^ 64 := hopin.1.2
  have hjo : j * openingWords ≤ 49215 := by
    have ho : openingWords = 193 := rfl
    have hj' : j ≤ 255 := by have : wireMaxQueries = 256 := rfl; omega
    have : j * openingWords ≤ 255 * 193 := Nat.mul_le_mul hj' (le_of_eq ho)
    omega
  have hra : ra.toNat = op.toNat + 8 * (1 + j * openingWords) := by
    rw [hradef]; exact NativeRustcVm.Transcript.toNat_off (by omega)
  have hopst : op.toNat + 8 * 49408 ≤ (stackBelow m0 eachRowNextStack).toNat ∨
      (stackBelow m0 eachRowNextStack).toNat + eachRowNextStack ≤ op.toNat := hopin.2
  have hsb : (stackBelow m0 eachRowNextStack).toNat = m0.regs.SP.toNat - 3232 := by
    rw [← stack_eq]; exact hl.base_N
  rw [hsb, stack_eq] at hopst
  have hf600 := hl.frame_toNat (o := 600) (by decide)
  have hsp8 : (stackBelow st8.data 0).toNat = m0.regs.SP.toNat - 2000 := by
    unfold stackBelow
    rw [hmid8.fr.sp]
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.sub_zero]
    exact hl.base_F
  have hP8 : LanesOfPre st8.data := by
    unfold LanesOfPre
    rw [e8x1, e8x2, e8x3]
    refine ⟨⟨⟨?_, show ra.toNat + 8 * w ≤ 2 ^ 64 by omega⟩, ?_⟩,
      whirIn_frame hpre hmid8.fr (by decide) (by decide) (by decide), ?_⟩
    · have := NativeRustcVm.WordsAt.mapped hW7
      rw [ha7, Array.length_toList, ← hwdef] at this
      rw [hd8]
      exact this
    · show _ ∨ _
      rw [hsp8, hra]
      omega
    · show _ ∨ _
      rw [hf600, hra]
      have hlb : lanesBytes = 1024 := rfl
      omega
  refine call_then hpc8 hlanes hP8 fun ⟨d9, pc9⟩ hpc9 ⟨hval, hch, hsv⟩ ↦ ?_
  simp only at hpc9
  subst hpc9
  have hrow' : wordSlice st8.data ra w = rows[j]'hjr := by
    unfold wordSlice
    rw [hd8]
    have := NativeRustcVm.wordsOf_of_wordsAt hW7
    rw [ha7, Array.length_toList, ← hwdef] at this
    rw [this, Array.toArray_toList]
  simp only [e8x0, e8x1, e8x2, e8x3, hrow'] at hval hch
  have hls : (lanesOf m0.regs.X0.toNat (rows[j]'hjr)).size ≤ 64 := by
    have := EachRow.lanesOf_size_le m0.regs.X0.toNat (rows[j]'hjr)
    rw [← hwdef] at this
    omega
  obtain ⟨hx9, hx9', hew⟩ : _ ∧ _ ∧ _ := by
    split at hval
    · exact hval
    · rename_i hc; exact absurd hls hc
  have hs9 : SameOutside st8.data.dmem d9.dmem (HitN m0) :=
    EachRow.hit_of_call hl hmid8.fr.sp (N' := 0) (o := 600) (n := 1024) (by decide) (by decide)
      (by decide) hch
  have hmid9 := hmid8.call hpre hs9 hsv
  have hx1 : d9.regs.X1 = (lanesOf m0.regs.X0.toNat (rows[j]'hjr)).size.toUInt64 :=
    UInt64.toNat_inj.mp (by rw [hx9', natCast_toUInt64_toNat (by omega)])
  exact iterB hp hfold hsat hpre hmid9 hls hx9 hx1 hew fun m' hmid hF hW ↦
    iterC hp hnov hpre hmid hF hW fun m'' hmid' hF' h27 hr ↦
      iterD hp hkmul hmul hpre hmid' hF' h27 hr (parOf_succ hjr hjq') cont

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
