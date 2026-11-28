module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.Entry
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names

/-!
# `each_row` with `next_level`'s closure: into the loop (x86-64)

`b3` stores the table's count at 1432 and reads the rows' count: none, `Some(())` with the batched
value `0` (`exit_at`). `b4` loads the closure's address (its first two instructions), then stores
the closure's words, the `Rows`, the table's address and count and the queries' end in the frame:
the loop's invariant before row `0` (`start_step`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData}

/-- The rows' count, in their `Rows`. -/
theorem rows_count {d : DataMem} {r p : BitVec 64} (h : NativeRustcVm.Sumcheck.RowsAt d r p rows) :
    WordAt d (r + BitVec.ofNat 64 16) rows.size.toUInt64 := by
  obtain ⟨-, -, w, -, hw, -⟩ := h
  exact NativeRustcVm.WordsAt.getElem hw (i := 2) (by simp)

theorem size_wordSlice (m : MachineData) (a : BitVec 64) (n : Nat) : (wordSlice m a n).size = n := by
  simp [wordSlice]

/-- `leaq (%r15,%rbx,8)`: the queries' end. -/
theorem eval_qend [Labels] (env : Env) {a b : BitVec 64} (ha : env.regs .r15 = a)
    (hb : env.regs .rbx = b) :
    (Sym.bin .add .W64 (.reg .r15) (.bin .mul .W64 (.reg .rbx) (.lit 8))).eval env =
      a + BitVec.ofNat 64 (8 * b.toNat) := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, ha, hb]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
  rw [Nat.mul_comm]

/-- `cmpq $32; cmovae`: a count below 32 kept. -/
theorem eval_cap [Labels] (env : Env) (c v : Sym) {n : Nat} (h : env.regs .r14 = BitVec.ofNat 64 n)
    (hn : n < 32) :
    (Sym.ite (.not (.cmp .ult .W64 (.reg .r14) (.lit 32))) c v).eval env = v.eval env := by
  have hu : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 32) = true := by
    rw [BitVec.ult, decide_eq_true_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, hu, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

/-- The closure's words, in a body. -/
theorem env_word [Labels] (c : Ctx rows op m0) {o : Nat} {m : MachineData} (hfr : FR m0 o m) (i : Nat)
    (hi : i < 6) :
    NativeRustcVm.wordOf m.dmem (stackArg m0 1 + BitVec.ofNat 64 (8 * i)) =
      UInt64.ofBitVec (nextEnv m0 i) := by
  have hs := hfr.input_same (lay c) c.envin (notB_in c c.envin c.benv)
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun j hj ↦ by
    rw [NativeRustcVm.addr_add_add]; exact hs _ (by omega)]
  rfl

variable [Host] {k : Nat}

/-- **From `b3` into the loop.** -/
theorem start_step (hp : Placed code k) (c : Ctx rows op m0) {m : MachineData}
    (h : AtB3 m0 m)
    (cont : ∀ m', Inv rows m0 0 m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b9Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b3Offset)⟩ := by
  have hl := lay c
  have hrows := c.rowsAt
  have hrin := c.rin
  have hrs : rows.size ≤ 256 := hrows.2.1
  -- `b3`
  let env3 := EachRow.envE m0 m 1984 0 [(reg m0 .rcx, 32)] (fun _ ↦ 0) 0
  have hwf3 : env3.WF := env1 c h.fr hrin 0
  have hm3 : Match env3 rowsS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨h.fr.match_rsp, by
        show reg m .r12 = reg m0 .rcx + BitVec.ofInt 64 0
        rw [h.r12]
        simp, trivial⟩ trivial trivial trivial
  have hw16 : WordAt m.dmem (reg m0 .rcx + BitVec.ofNat 64 16) rows.size.toUInt64 := by
    have hs := h.fr.input_same hl hrin (notB_in c hrin c.brows)
    intro i hi
    rw [NativeRustcVm.addr_add_add, hs _ (by rw [NativeRustcVm.length_wordBytes] at hi; omega),
      ← NativeRustcVm.addr_add_add]
    exact rows_count hrows i hi
  have hcnt : env3.load 1 16 8 = BitVec.ofNat 64 rows.size :=
    NativeRustcVmX64.Arrays.load_word hw16
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk3 run_b3 hwf3 (fun _ h ↦ by cases h) hm3 fun st6 hm6 hpc6 ↦ ?_
  have hs6 : SameOutside m.dmem st6.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 1432 1440) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm6 hwf3 (by decide)
  have hfr6 : FR m0 8 st6.data :=
    h.fr.step hl (by decide) (by decide) ((rv hm6 (v := .ptr 0 8) rfl).trans (EachRow.eval_ptr0 8))
      (hm6.kept hwf3) hs6 (by decide)
  have hbat6 := bat_hit c (by decide) (by decide) hs6 h.bat
  have hcnt6 : WordAt st6.data.dmem (fb m0 + BitVec.ofNat 64 1432) (tableOf m0).size.toUInt64 := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm6 (r := 0) (o := 1432) rfl (by decide)
      (v := .reg .r14) (by decide)
    rw [show (Sym.reg .r14).eval env3 = BitVec.ofNat 64 (tableOf m0).size from h.r14] at this
    exact this
  simp only [PcOk] at hpc6
  split at hpc6
  · -- no rows
    rename_i hc
    rw [NativeRustcVmX64.Arrays.eval_test, Sym.eval, hcnt,
      NativeRustcVmX64.Arrays.beq_ofNat _ (by decide), decide_eq_true_iff,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_15 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b26Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_15_at]
      at hpc6
    obtain ⟨d6, pc6⟩ := st6
    simp only at hpc6 hfr6 hm6 hbat6
    subst hpc6
    refine exit_at hp c hfr6 ?_ ?_
    · show (reg d6 .rax).toNat % 256 = 1
      rw [rv hm6 (v := .bin .merge .W8 (.reg .rax) (.lit 1)) rfl]
      exact NativeRustcVmX64.Arrays.merge_one_mod _
    · rw [EachRow.batchedOf_eq, hc, Nat.min_zero]
      exact hbat6
  rename_i hc
  have hz : rows.size ≠ 0 := fun hz ↦ hc (by
    rw [NativeRustcVmX64.Arrays.eval_test, Sym.eval, hcnt, hz]
    rfl)
  have e6r12 : reg st6.data .r12 = reg m0 .rcx :=
    (rv hm6 (v := .ptr 1 0) rfl).trans (by show reg m0 .rcx + BitVec.ofInt 64 0 = _; simp)
  -- `b4`, its first two instructions
  obtain ⟨hwf, hm⟩ := frame_env c hfr6 0
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk4a : (b4.take 2).IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b4Offset) :=
    (NativeRustcVmX64.Transcript.infix_take b4 2).trans hk4 (by decide)
  have hk4b : (b4.drop 2).IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b4Offset + (b4.take 2).length) :=
    (NativeRustcVmX64.Transcript.infix_drop b4 2).trans hk4 (by decide)
  refine exec_at hk4a run_b4a hwf (fun _ h ↦ by cases h) hpc6 hm fun st7 hm7 hpc7 ↦ ?_
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf rfl
  have hfr7 : FR m0 8 st7.data := hfr6.ofBlock hwf hm7 rfl rfl
  have e7 : ∀ r, (after (b4.take 2) frameS).reg r = some (.reg r) →
      reg st7.data r = reg st6.data r := fun r hr ↦
    rv hm7 (by rw [← after_eq run_b4a]; exact hr)
  have hrax7 : reg st7.data .rax = stackArg m0 1 :=
    (rv hm7 (v := .load 0 2000 8) rfl).trans (argW c hfr6 1 (by decide))
  have hrdi7 : reg st7.data .rdi = reg m0 .rcx :=
    (rv hm7 (v := .reg .r12) rfl).trans e6r12
  -- the rest of `b4`
  let env8 := EachRow.envE m0 st7.data 1984 0 [(stackArg m0 1, 48)] (fun _ ↦ 0) 0
  have hwf8 : env8.WF := env1 c hfr7 c.envin 0
  have hm8 : Match env8 argS st7.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨hfr7.match_rsp, by
        show reg st7.data .rax = stackArg m0 1 + BitVec.ofInt 64 0
        rw [hrax7]
        simp, trivial⟩ trivial trivial trivial
  have hpc7' : st7.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b4Offset + (b4.take 2).length) := hpc7
  refine exec_at hk4b run_b4b hwf8 (fun _ h ↦ by cases h) hpc7' hm8 fun st8 hm8' hpc8 ↦ ?_
  have hs8 : SameOutside st7.data.dmem st8.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 8 88) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm8' hwf8 (by decide)
  have hfr8 : FR m0 8 st8.data :=
    hfr7.step hl (by decide) (by decide) ((rv hm8' (v := .ptr 0 8) rfl).trans (EachRow.eval_ptr0 8))
      (hm8'.kept hwf8) hs8 (by decide)
  obtain ⟨d8, pc8⟩ := st8
  simp only [PcOk] at hpc8
  simp only at hfr8 hs8 hm8'
  subst hpc8
  rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_5 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b9Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_5_at]
  have e6 : ∀ r, (after b3 rowsS).reg r = some (.reg r) → reg st6.data r = reg m r := fun r hr ↦
    rv hm6 (by rw [← after_eq run_b3]; exact hr)
  have e8 : ∀ r, (after (b4.drop 2) argS).reg r = some (.reg r) → reg d8 r = reg st7.data r :=
    fun r hr ↦ rv hm8' (by rw [← after_eq run_b4b]; exact hr)
  have hlen : (tableOf m0).toList.length = (tableOf m0).size := Array.length_toList
  have hr14 : reg st7.data .r14 = BitVec.ofNat 64 (tableOf m0).size := by
    rw [e7 .r14 rfl, e6 .r14 rfl]; exact h.r14
  have hlt : (tableOf m0).size < 32 := by have := h.tlen; omega
  have hld : ∀ i, i < 6 → env8.load 1 (8 * i) 8 = nextEnv m0 i := fun i hi ↦ by
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf st7.data.dmem (stackArg m0 1 + BitVec.ofNat 64 (8 * i))).toBitVec = _
    rw [env_word c hfr7 i hi]
  have wr : ∀ (o : Nat) (v : Sym) (w : BitVec 64), o + 8 ≤ 1992 →
      (∀ i < 8, findWrite 0 (o + i) (after (b4.drop 2) argS).mem = some (v, i)) → v.eval env8 = w →
      WordAt d8.dmem (fb m0 + BitVec.ofNat 64 o) (UInt64.ofBitVec w) := fun o v w ho hv he ↦ by
    have := NativeRustcVmX64.Transcript.wordAt_write hm8' (r := 0) (o := o) rfl ho (v := v)
      (by rw [← after_eq run_b4b]; exact hv)
    rwa [he] at this
  have hb7 := bat_hit c (by decide) (by decide) hs8 (hd7 ▸ hbat6)
  refine cont d8 ⟨hfr8, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    Nat.pos_of_ne_zero hz, Nat.zero_le _, hb7,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact wr 8 (.load 1 32 8) _ (by decide) (by rw [after_eq run_b4b]; decide) (hld 4 (by decide))
  · exact wr 16 (.load 1 40 8) _ (by decide) (by rw [after_eq run_b4b]; decide) (hld 5 (by decide))
  · exact wr 24 (.reg .r12) _ (by decide) (by rw [after_eq run_b4b]; decide)
      ((e7 .r12 rfl).trans e6r12)
  · exact wr 32 (.load 1 24 8) _ (by decide) (by rw [after_eq run_b4b]; decide) (hld 3 (by decide))
  · exact wr 40 (.ite (.not (.cmp .ult .W64 (.reg .r14) (.lit 32))) (.lit 8) (.reg .r13)) _
      (by decide) (by rw [after_eq run_b4b]; decide)
      ((eval_cap _ _ _ hr14 hlt).trans ((e7 .r13 rfl).trans ((e6 .r13 rfl).trans h.r13)))
  · exact wr 48 (.load 1 16 8) _ (by decide) (by rw [after_eq run_b4b]; decide) (hld 2 (by decide))
  · exact wr 56 (.load 1 8 8) _ (by decide) (by rw [after_eq run_b4b]; decide) (hld 1 (by decide))
  · exact wr 64 (.load 1 0 8) _ (by decide) (by rw [after_eq run_b4b]; decide) (hld 0 (by decide))
  · exact wr 72 (.ite (.not (.cmp .ult .W64 (.reg .r14) (.lit 32))) (.lit 0) (.reg .r14)) _
      (by decide) (by rw [after_eq run_b4b]; decide) ((eval_cap _ _ _ hr14 hlt).trans hr14)
  · exact wr 80 (.bin .add .W64 (.reg .r15) (.bin .mul .W64 (.reg .rbx) (.lit 8))) _ (by decide)
      (by rw [after_eq run_b4b]; decide)
      (eval_qend _ ((e7 .r15 rfl).trans ((e6 .r15 rfl).trans h.r15))
        ((e7 .rbx rfl).trans ((e6 .rbx rfl).trans h.rbx)))
  · rw [hd7] at hs8
    exact keepW hl (by decide) (by decide) hs8 (by decide) (by decide)
      (keepW hl (by decide) (by decide) hs6 (by decide) (by decide) h.w88)
  · rw [hd7] at hs8
    exact keepW hl (by decide) (by decide) hs8 (by decide) (by decide)
      (keepW hl (by decide) (by decide) hs6 (by decide) (by decide) h.w96)
  · refine ⟨by rw [hlen]; exact h.tlen, ?_, ?_⟩
    · rw [hlen, hd7] at *
      exact keepW hl (by decide) (by decide) hs8 (by decide) (by decide) hcnt6
    · rw [show off (fb m0 + BitVec.ofNat 64 1432) 8 = fb m0 + BitVec.ofNat 64 1440 from
        NativeRustcVm.addr_add_add _ _ _]
      have hc := h.copy
      rw [hd7] at hs8
      unfold PairsAt at hc ⊢
      have hle : 1440 + ((pairWords (tableOf m0).toList).flatMap
          NativeRustcVm.wordBytes).length ≤ 1984 := by
        rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, hlen]
        have := h.tlen; omega
      exact EachRow.keep_frame hl (by decide) (by decide) hs8 (by decide) (.inr ⟨by decide, by omega⟩)
        (EachRow.keep_frame hl (by decide) (by decide) hs6 (by decide)
          (.inr ⟨by decide, by omega⟩) hc)
  · rw [e8 .r15 rfl, e7 .r15 rfl, e6 .r15 rfl, h.r15]
    simp
  · exact rv hm8' (v := .lit 0) rfl
  · rw [e8 .rdx rfl, e7 .rdx rfl, rv hm6 (v := .load 1 16 8) rfl]
    exact hcnt
  · rw [e8 .rdi rfl]; exact hrdi7
  · rw [rv hm8' (v := .ite (.not (.cmp .ult .W64 (.reg .r14) (.lit 32))) (.lit 8) (.reg .r13)) rfl,
      eval_cap _ _ _ hr14 hlt]
    exact (e7 .r13 rfl).trans ((e6 .r13 rfl).trans h.r13)
  · rw [rv hm8' (v := .load 1 24 8) rfl]
    exact hld 3 (by decide)

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
