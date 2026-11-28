module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Clear
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names

/-!
# `each_row` with `final_level`'s closure: an iteration's head (x86-64)

At `NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_3` (`Inv j`): `b5` ends the loop when the queries are exhausted (the
outcome `true`); `b6` counts the row and stores query `j` at 72; `b7` clears the lanes
(`clear_loop`): at `b8` (`AtB8`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)

@[expose] public section

/-- **At `b8`**, in iteration `j`. -/
structure AtB8 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  low : Low m0 m.dmem
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  ok : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j →
    okOf m0 (qsOf m0)[i] rows[i] = true
  w72 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 72) ((qsOf m0)[j]'hjq)
  rbp : reg m .rbp = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  rsi : reg m .rsi = BitVec.ofNat 64 j
  r13 : reg m .r13 = BitVec.ofNat 64 (rows.size - (j + 1))
  r14 : reg m .r14 = reg m0 .rcx
  r12 : reg m .r12 = BitVec.ofNat 64 (tableOf m0).size
  r15 : reg m .r15 = fb m0 + BitVec.ofNat 64 1392
  rbx : reg m .rbx = fb m0 + BitVec.ofNat 64 104

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

theorem sub_one_ofNat {n : Nat} (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

variable [Host] {k : Nat}

/-- **An iteration's head**: from the invariant before row `j`, the exit or `b8`. -/
theorem iter_a (hp : Placed code k) (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (h : Inv rows m0 j m)
    (cont : ∀ m', AtB8 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b8Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b5Offset)⟩ := by
  have hl := lay hpre
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowFinalStack = 3088 := rfl
  have hqb := qs_bound hpre
  have hqin := hpre.1.2.2.2.2.2.1
  have hsz := qs_size (m0 := m0)
  have hjq := h.hjq
  have hrs : rows.size ≤ 256 := hpre.1.2.2.1.2.1
  -- `b5`
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr 0
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl24 : (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0) 0).load 0 24 8 = qEnd m0 :=
    NativeRustcVmX64.Arrays.load_word h.low.w24
  have hrbp : (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0) 0).regs .rbp =
      reg m0 .rsi + BitVec.ofNat 64 (8 * j) := h.rbp
  refine exec_then hk5 run_b5 hwf (fun _ h ↦ by cases h) hm fun st5 hm5 hpc5 ↦ ?_
  have hfr5 : FR m0 8 st5.data := h.fr.ofBlock hwf hm5 rfl (by decide)
  simp only [PcOk] at hpc5
  split at hpc5
  · -- queries exhausted
    rename_i hc
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl24, hrbp, beq_iff_eq] at hc
    have hjn : j = (qsOf m0).size := by
      have := congrArg BitVec.toNat hc
      simp only [qEnd, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      rw [hsz] at hjq hqb ⊢
      omega
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_14 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b18Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_14_at]
      at hpc5
    obtain ⟨d, pc⟩ := st5
    simp only at hpc5 hfr5
    subst hpc5
    exact exit_true hp hpre hfr5 (EachRow.finalOk_of (j := j) (.inl (by omega)) h.ok)
  rename_i hc
  have hjlt : j < (qsOf m0).size := by
    rcases Nat.lt_or_ge j (qsOf m0).size with h' | h'
    · exact h'
    · exfalso
      apply hc
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl24, hrbp, beq_iff_eq]
      unfold qEnd
      rw [show j = (qsOf m0).size by omega, hsz]
  -- `b6`
  have hd5 : st5.data.dmem = m.dmem := hm5.dmem_eq hwf rfl
  have e5 : ∀ r, (after b5 frameS).reg r = some (.reg r) → reg st5.data r = reg m r :=
    fun r hr ↦ rv hm5 (by rw [← after_eq run_b5]; exact hr)
  have hqa : (reg m0 .rsi + BitVec.ofNat 64 (8 * j)).toNat = (reg m0 .rsi).toNat + 8 * j :=
    toNat_add_ofNat _ _ (by omega)
  let env6 := EachRow.envE m0 st5.data 1936 0 [(reg m0 .rsi + BitVec.ofNat 64 (8 * j), 8)]
    (fun _ ↦ 0) 0
  have hwf6 : env6.WF :=
    EachRow.envE_wf hl (Nat.zero_le _) hfr5.kept
      (by
        simp only [List.mem_singleton]
        rintro x rfl
        refine ⟨fun i hi ↦ ?_, show _ + 8 ≤ 2 ^ 64 by rw [hqa]; omega⟩
        rw [addr_add]
        exact hfr5.kept _ (hqin.1.1 _ (by omega)))
      (List.pairwise_pair.mpr (by unfold Apart; rw [hl.base, hqa]; omega))
  have hm6 : Match env6 headS st5.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hfr5.match_rsp, by
        show reg st5.data .rbp = reg m0 .rsi + BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 0
        rw [e5 .rbp rfl, h.rbp]
        exact (BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk6 run_b6 hwf6 (fun _ h ↦ by cases h) hpc5 hm6 fun st6 hm6' hpc6 ↦ ?_
  have hs6 : SameOutside st5.data.dmem st6.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 72 80) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm6' hwf6 (by decide)
  have hfr6 : FR m0 8 st6.data :=
    hfr5.step hl (by decide) (by decide) ((rv hm6' (v := .ptr 0 8) rfl).trans (EachRow.eval_ptr0 8))
      (hm6'.kept hwf6) hs6 (by decide)
  have hq6 : env6.load 1 0 8 = ((qsOf m0)[j]'hjlt).toBitVec := by
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st5.data.dmem
      (reg m0 .rsi + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 0)).toBitVec = _
    rw [NativeRustcVm.addr_add_zero, query_word hpre hfr5 hjlt]
  have w72 : WordAt st6.data.dmem (fb m0 + BitVec.ofNat 64 72) ((qsOf m0)[j]'hjlt) := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm6' (r := 0) (o := 72) rfl (by decide)
      (v := .load 1 0 8) (by decide)
    rw [show (Sym.load 1 0 8).eval env6 = _ from hq6] at this
    exact this
  have e6 : ∀ r, (after b6 headS).reg r = some (.reg r) → reg st6.data r = reg st5.data r :=
    fun r hr ↦ rv hm6' (by rw [← after_eq run_b6]; exact hr)
  have hr13 : reg st6.data .r13 = BitVec.ofNat 64 (rows.size - (j + 1)) := by
    rw [rv hm6' (v := .bin .sub .W64 (.reg .r13) (.lit 1)) rfl]
    have : env6.regs .r13 = BitVec.ofNat 64 (rows.size - j) := (e5 .r13 rfl).trans h.r13
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, this]
    rw [sub_one_ofNat (by have := h.hj; omega) (by omega)]
    congr 1
  have hrbp6 : reg st6.data .rbp = reg m0 .rsi + BitVec.ofNat 64 (8 * j) :=
    (rv hm6' (v := .ptr 1 0) rfl).trans (BitVec.add_zero _)
  have hrax6 : reg st6.data .rax = BitVec.ofNat 64 (56 + 64 * 0) := rv hm6' (v := .lit 56) rfl
  obtain ⟨d6, pc6⟩ := st6
  simp only [PcOk] at hpc6
  simp only at hfr6 hs6 w72 e6 hr13 hrbp6 hrax6 hm6'
  subst hpc6
  rw [show k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b6Offset + b6.length = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b7Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b6_next]]
  -- `b7`
  have hlow6 : Low m0 d6.dmem := (hd5 ▸ h.low).keep hl (by decide) (by decide) (by decide) hs6
  refine clear_loop hp hpre (ms := d6) ?_ 15 0 d6 rfl (by decide) hfr6 hrax6 (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
  intro m8 hfr8 hs8 hk8
  refine cont m8 ⟨hfr8, hlow6.keep hl (by decide) (by decide) (by decide) hs8, h.hj, hjlt,
    h.ok, keepW hl (by decide) (by decide) hs8 (by decide) (by decide) w72, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hk8 .rbp (by simp [keepL]), hrbp6]
  · rw [hk8 .rsi (by simp [keepL]), e6 .rsi rfl, e5 .rsi rfl, h.rsi]
  · rw [hk8 .r13 (by simp [keepL]), hr13]
  · rw [hk8 .r14 (by simp [keepL]), e6 .r14 rfl, e5 .r14 rfl, h.r14]
  · rw [hk8 .r12 (by simp [keepL]), e6 .r12 rfl, e5 .r12 rfl, h.r12]
  · rw [hk8 .r15 (by simp [keepL]), e6 .r15 rfl, e5 .r15 rfl, h.r15]
  · rw [hk8 .rbx (by simp [keepL]), e6 .rbx rfl, e5 .rbx rfl, h.rbx]

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
