module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.Clear
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names

/-!
# `each_row` with `next_level`'s closure: inside an iteration (x86-64)

`MidN rows m0 j d`: the memory of iteration `j`: the locals (`Low`), the batched value after `j`
rows, the rows left at 120; kept by a step changing memory in `Hit … lo hi` with `104 ≤ lo`,
`hi ≤ 1432` apart from 120 to 128 (`MidN.keep`). The inputs read back: query `j` (`query_word`),
the rows (`rowsAt_of_fr`). The loop's head (`iter_a`): `b9` ends the loop when the queries are
exhausted; `b10` counts the row and reads query `j`; `b11` clears the lanes: at `b12` (`AtB12`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Compile (wireMaxQueries wireMaxLeafWords)
open NativeVm (openingWords)

@[expose] public section

/-- **The memory of an iteration.** -/
structure MidN (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (d : DataMem) :
    Prop where
  low : Low m0 d
  bat : EWAt d (bOf m0) (parOf rows m0 j)
  w120 : WordAt d (fb m0 + BitVec.ofNat 64 120)
    (UInt64.ofBitVec (BitVec.ofNat 64 (rows.size - (j + 1))))

/-- **At `b12`**, in iteration `j`. -/
structure AtB12 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidN rows m0 j m.dmem
  rbp : reg m .rbp = ((qsOf m0)[j]'hjq).toBitVec
  rbx : reg m .rbx = BitVec.ofNat 64 j
  r15 : reg m .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  r14 : reg m .r14 = bOf m0
  r13 : reg m .r13 = fb m0 + BitVec.ofNat 64 1440
  rdi : reg m .rdi = reg m0 .rcx

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

theorem MidN.keep [Labels] (c : Ctx rows op m0) {lo hi : Nat} {d d' : DataMem} (hlh : lo ≤ hi)
    (hlo : 104 ≤ lo) (hhi : hi ≤ 1432) (h120 : 128 ≤ lo ∨ hi ≤ 120) (h : MidN rows m0 j d)
    (hs : SameOutside d d' (EachRow.Hit m0 1984 eachRowNextStack lo hi)) : MidN rows m0 j d' :=
  ⟨h.low.keepR hs (hitR c hlh hlo hhi), bat_hit c hlh (by omega) hs h.bat,
    keepW (lay c) hlh (by omega) hs (by decide) (by omega) h.w120⟩

/-- The queries' count. -/
theorem qs_size : (qsOf m0).size = (reg m0 .rdx).toNat := size_wordSlice _ _ _

/-- Query `j`, as the entry's memory holds it. -/
theorem query_word [Labels] (c : Ctx rows op m0) {o : Nat} {m : MachineData} (hfr : FR m0 o m)
    (hj : j < (qsOf m0).size) :
    NativeRustcVm.wordOf m.dmem (reg m0 .rsi + BitVec.ofNat 64 (8 * j)) = (qsOf m0)[j]'hj := by
  have hsz := qs_size (m0 := m0)
  have hs := hfr.input_same (lay c) c.qin (notB_in c c.qin c.bq)
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]; exact hs _ (by omega)]
  simp [qsOf, eachRowArgs, wordSlice]

/-- **The rows**, unchanged in a body. -/
theorem rowsAt_of_fr [Labels] (c : Ctx rows op m0) {o : Nat} {m : MachineData} (hfr : FR m0 o m) :
    NativeRustcVm.Sumcheck.RowsAt m.dmem (reg m0 .rcx) op rows := by
  obtain ⟨hp0, hsz, w, hw, hhdr, hrow⟩ := c.rowsAt
  have hr := hfr.input_same (lay c) c.rin (notB_in c c.rin c.brows)
  have ho := hfr.input_same (lay c) c.opin (notB_in c c.opin c.bop)
  refine ⟨hp0, hsz, w, hw, NativeRustcVm.Transcript.bytesAt_congr hhdr fun i hi ↦ hr i ?_,
    fun j hj ↦ ⟨(hrow j hj).1, NativeRustcVm.Transcript.bytesAt_congr (hrow j hj).2 fun i hi ↦ ?_⟩⟩
  · rw [NativeRustcVm.length_wordsBytes] at hi
    simpa using hi
  · rw [off, NativeRustcVm.addr_add_add]
    refine ho _ ?_
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, (hrow j hj).1] at hi
    have : wireMaxQueries = 256 := rfl
    have : wireMaxLeafWords = 64 := rfl
    have : NativeRustcVm.Sumcheck.openingsWords = 49408 := rfl
    have hj' : j < 256 := by omega
    show _ < 8 * 49408
    have : j * openingWords ≤ 255 * 193 := by
      rw [show openingWords = 193 from rfl]; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- The queries' bytes, as numbers. -/
theorem qs_bound [Labels] (c : Ctx rows op m0) :
    (reg m0 .rsi).toNat + 8 * (qsOf m0).size ≤ 2 ^ 64 ∧
      ((reg m0 .rsi).toNat + 8 * (qsOf m0).size ≤ (rspOf m0).toNat - eachRowNextStack ∨
        (rspOf m0).toNat + 8 ≤ (reg m0 .rsi).toNat) := by
  have hq := c.qin
  have hl := lay c
  have hsb := hl.baseN
  have hN := hl.sp
  rw [qs_size]
  refine ⟨hq.1.2, ?_⟩
  have := hq.2
  unfold OffStack Apart at this
  rw [hsb] at this
  omega

theorem sub_one_ofNat {n : Nat} (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `batchedOf` once the loop ends after `j` rows, `j` the smaller count. -/
theorem batched_end (hj : j = min (qsOf m0).size rows.size) :
    batchedOf (reg m0 .rdi).toNat (reg m0 .r8).toNat (eachRowArgs m0).2 (highOf m0)
      (eachRowArgs m0).1 rows (qwOf m0) = parOf rows m0 j := by
  rw [EachRow.batchedOf_eq, hj]

variable [Host] {k : Nat}

/-- **An iteration's head**: from the invariant before row `j`, the exit or `b12`. -/
theorem iter_a (hp : Placed code k) (c : Ctx rows op m0) {m : MachineData}
    (h : Inv rows m0 j m)
    (cont : ∀ m', AtB12 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b12Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b9Offset)⟩ := by
  have hl := lay c
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowNextStack = 3136 := rfl
  have hqb := qs_bound c
  have hqin := c.qin
  have hsz := qs_size (m0 := m0)
  have hjq := h.hjq
  have hrs : rows.size ≤ 256 := c.rowsAt.2.1
  -- `b9`
  obtain ⟨hwf, hm⟩ := frame_env c h.fr 0
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl80 : (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0) 0).load 0 80 8 = qEnd m0 :=
    NativeRustcVmX64.Arrays.load_word h.low.w80
  have hr15 : (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0) 0).regs .r15 =
      reg m0 .rsi + BitVec.ofNat 64 (8 * j) := h.r15
  refine exec_then hk9 run_b9 hwf (fun _ h ↦ by cases h) hm fun st5 hm5 hpc5 ↦ ?_
  have hfr5 : FR m0 8 st5.data := h.fr.ofBlock hwf hm5 rfl (by decide)
  have hd5 : st5.data.dmem = m.dmem := hm5.dmem_eq hwf rfl
  simp only [PcOk] at hpc5
  split at hpc5
  · -- queries exhausted
    rename_i hc
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl80, hr15, beq_iff_eq] at hc
    have hjn : j = (qsOf m0).size := by
      have := congrArg BitVec.toNat hc
      simp only [qEnd, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      rw [hsz] at hjq hqb ⊢
      omega
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_17 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b27Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_17_at]
      at hpc5
    obtain ⟨d, pc⟩ := st5
    simp only at hpc5 hfr5 hd5
    subst hpc5
    refine exit_17 hp c hfr5 ?_
    rw [batched_end (j := j) (by have := h.hj; omega), hd5]
    exact h.bat
  rename_i hc
  have hjlt : j < (qsOf m0).size := by
    rcases Nat.lt_or_ge j (qsOf m0).size with h' | h'
    · exact h'
    · exfalso
      apply hc
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl80, hr15, beq_iff_eq]
      unfold qEnd
      rw [show j = (qsOf m0).size by omega, hsz]
  -- `b10`
  have e5 : ∀ r, (after b9 frameS).reg r = some (.reg r) → reg st5.data r = reg m r :=
    fun r hr ↦ rv hm5 (by rw [← after_eq run_b9]; exact hr)
  have hqa : (reg m0 .rsi + BitVec.ofNat 64 (8 * j)).toNat = (reg m0 .rsi).toNat + 8 * j :=
    toNat_add_ofNat _ _ (by omega)
  have hqin8 : WhirIn m0 (reg m0 .rsi + BitVec.ofNat 64 (8 * j)) 8 eachRowNextStack :=
    ⟨⟨fun i hi ↦ by rw [addr_add]; exact hqin.1.1 _ (by rw [← hsz]; omega),
      show _ + 8 ≤ _ by rw [hqa]; omega⟩, by
      unfold OffStack Apart
      rw [hqa, hl.baseN]
      omega⟩
  let env6 := EachRow.envE m0 st5.data 1984 0 [(reg m0 .rsi + BitVec.ofNat 64 (8 * j), 8)]
    (fun _ ↦ 0) 0
  have hwf6 : env6.WF := env1 c hfr5 hqin8 0
  have hm6 : Match env6 headS st5.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hfr5.match_rsp, by
        show reg st5.data .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 0
        rw [e5 .r15 rfl, h.r15]
        exact (BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk10 run_b10 hwf6 (fun _ h ↦ by cases h) hpc5 hm6 fun st6 hm6' hpc6 ↦ ?_
  have hs6 : SameOutside st5.data.dmem st6.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 120 128) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm6' hwf6 (by decide)
  have hfr6 : FR m0 8 st6.data :=
    hfr5.step hl (by decide) (by decide) ((rv hm6' (v := .ptr 0 8) rfl).trans (EachRow.eval_ptr0 8))
      (hm6'.kept hwf6) hs6 (by decide)
  have hrdx : env6.regs .rdx = BitVec.ofNat 64 (rows.size - j) := (e5 .rdx rfl).trans h.rdx
  have hdec : (Sym.bin .sub .W64 (.reg .rdx) (.lit 1)).eval env6 =
      BitVec.ofNat 64 (rows.size - (j + 1)) := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hrdx]
    rw [sub_one_ofNat (by have := h.hj; omega) (by omega)]
    congr 1
  have w120 : WordAt st6.data.dmem (fb m0 + BitVec.ofNat 64 120)
      (UInt64.ofBitVec (BitVec.ofNat 64 (rows.size - (j + 1)))) := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm6' (r := 0) (o := 120) rfl (by decide)
      (v := .bin .sub .W64 (.reg .rdx) (.lit 1)) (by decide)
    rwa [hdec] at this
  have hq6 : env6.load 1 0 8 = ((qsOf m0)[j]'hjlt).toBitVec := by
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st5.data.dmem
      (reg m0 .rsi + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, query_word c hfr5 hjlt]
  have e6 : ∀ r, (after b10 headS).reg r = some (.reg r) → reg st6.data r = reg st5.data r :=
    fun r hr ↦ rv hm6' (by rw [← after_eq run_b10]; exact hr)
  have hrbp6 : reg st6.data .rbp = ((qsOf m0)[j]'hjlt).toBitVec :=
    (rv hm6' (v := .load 1 0 8) rfl).trans hq6
  have hrax6 : reg st6.data .rax = BitVec.ofNat 64 (56 + 64 * 0) := rv hm6' (v := .lit 56) rfl
  have hmm6 : MidN rows m0 j st6.data.dmem :=
    ⟨(hd5 ▸ h.low).keepR hs6 (hitR c (by decide) (by decide) (by decide)),
      bat_hit c (by decide) (by decide) hs6 (hd5 ▸ h.bat), w120⟩
  obtain ⟨d6, pc6⟩ := st6
  simp only [PcOk] at hpc6
  simp only at hfr6 hs6 e6 hrbp6 hrax6 hm6' hmm6
  subst hpc6
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b10Offset + b10.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b11Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b10_next]]
  -- `b11`
  refine clear_loop hp c (ms := d6) ?_ 15 0 d6 rfl (by decide) hfr6 hrax6 (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
  intro m8 hfr8 hs8 hk8
  refine cont m8 ⟨hfr8, h.hj, hjlt,
    hmm6.keep c (by decide) (by decide) (by decide) (by decide) hs8, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk8 .rbp (by simp [keepL]), hrbp6]
  · rw [hk8 .rbx (by simp [keepL]), e6 .rbx rfl, e5 .rbx rfl, h.rbx]
  · rw [hk8 .r15 (by simp [keepL]), rv hm6' (v := .ptr 1 0) rfl]
    exact BitVec.add_zero _
  · rw [hk8 .r14 (by simp [keepL]), e6 .r14 rfl, e5 .r14 rfl, h.r14]
  · rw [hk8 .r13 (by simp [keepL]), e6 .r13 rfl, e5 .r13 rfl, h.r13]
  · rw [hk8 .rdi (by simp [keepL]), e6 .rdi rfl, e5 .rdi rfl, h.rdi]

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
