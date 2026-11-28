module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.Entry
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names

/-!
# `each_row` with `final_level`'s closure: into the loop (x86-64)

`b3` stores the table's count at 1384 and reads the rows' count: none, `Some(())` (`exit_at`).
`b4` stores the `Rows`' address and the queries' end, caps the table's count (`< 32`), sets RBX
to the lanes, RSI to `0`: the loop's invariant before row `0` (`start_step`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
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

/-- `addq (%rbp,%rbx,8)`: the queries' end. -/
theorem eval_qend [Labels] (env : Env) {a b : BitVec 64} (ha : env.regs .rbp = a)
    (hb : env.regs .rbx = b) :
    (Sym.bin .add .W64 (.reg .rbp) (.bin .mul .W64 (.reg .rbx) (.lit 8))).eval env =
      a + BitVec.ofNat 64 (8 * b.toNat) := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, ha, hb]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
  rw [Nat.mul_comm]

/-- `cmpq $32; cmovae`: a count below 32 kept. -/
theorem eval_cap [Labels] (env : Env) (c v : Sym) {n : Nat} (h : env.regs .r12 = BitVec.ofNat 64 n)
    (hn : n < 32) :
    (Sym.ite (.not (.cmp .ult .W64 (.reg .r12) (.lit 32))) c v).eval env = v.eval env := by
  have hu : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 32) = true := by
    rw [BitVec.ult, decide_eq_true_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, hu, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

variable [Host] {k : Nat}

/-- **From `b3` into the loop.** -/
theorem start_step (hp : Placed code k) (hpre : EachRowFinalPre rows op m0) {m : MachineData}
    (h : AtB3 m0 m)
    (cont : ∀ m', Inv rows m0 0 m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b5Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b3Offset)⟩ := by
  have hl := lay hpre
  have hrows := hpre.1.2.2.1
  have hrin : WhirIn m0 (reg m0 .rcx) 32 eachRowFinalStack := hpre.1.2.2.2.1
  have hrs : rows.size ≤ 256 := hrows.2.1
  -- `b3`
  let env3 := EachRow.envE m0 m 1936 0 [(reg m0 .rcx, 32)] (fun _ ↦ 0) 0
  have hwf3 : env3.WF :=
    EachRow.envE_wf hl (Nat.zero_le _) h.fr.kept
      (by
        simp only [List.mem_singleton]
        rintro x rfl
        exact ⟨fun i hi ↦ h.fr.kept _ (hrin.1.1 i hi), hrin.1.2⟩)
      (List.pairwise_pair.mpr (hl.apart0 hrin.2))
  have hm3 : Match env3 rowsS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨h.fr.match_rsp, by
        show reg m .r14 = reg m0 .rcx + BitVec.ofInt 64 0
        rw [h.r14]
        simp, trivial⟩ trivial trivial trivial
  have hw16 : WordAt m.dmem (reg m0 .rcx + BitVec.ofNat 64 16) rows.size.toUInt64 := by
    have hs := h.fr.input_same hl hrin fun _ _ h ↦ h
    intro i hi
    rw [NativeRustcVm.addr_add_add, hs _ (by rw [NativeRustcVm.length_wordBytes] at hi; omega),
      ← NativeRustcVm.addr_add_add]
    exact rows_count hrows i hi
  have hcnt : env3.load 1 16 8 = BitVec.ofNat 64 rows.size :=
    NativeRustcVmX64.Arrays.load_word hw16
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk3 run_b3 hwf3 (fun _ h ↦ by cases h) hm3 fun st6 hm6 hpc6 ↦ ?_
  have hs6 : SameOutside m.dmem st6.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 1384 1392) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm6 hwf3 (by decide)
  have hfr6 : FR m0 8 st6.data :=
    h.fr.step hl (by decide) (by decide) ((rv hm6 (v := .ptr 0 8) rfl).trans (EachRow.eval_ptr0 8))
      (hm6.kept hwf3) hs6 (by decide)
  have hcnt6 : WordAt st6.data.dmem (fb m0 + BitVec.ofNat 64 1384) (tableOf m0).size.toUInt64 := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm6 (r := 0) (o := 1384) rfl (by decide) (v := .reg .r12)
      (by decide)
    rw [show (Sym.reg .r12).eval env3 = BitVec.ofNat 64 (tableOf m0).size from h.r12] at this
    exact this
  simp only [PcOk] at hpc6
  split at hpc6
  · -- no rows
    rename_i hc
    rw [NativeRustcVmX64.Arrays.eval_test, Sym.eval, hcnt,
      NativeRustcVmX64.Arrays.beq_ofNat _ (by decide), decide_eq_true_iff,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_13 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b20Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_13_at]
      at hpc6
    obtain ⟨d6, pc6⟩ := st6
    simp only at hpc6 hfr6 hm6
    subst hpc6
    refine exit_at hp hpre hfr6 ?_ (EachRow.finalOk_of (j := 0) (.inr (by omega))
      fun i _ _ hi ↦ absurd hi (Nat.not_lt_zero _))
    show (reg d6 .rax).toNat % 256 = 1
    rw [rv hm6 (v := .bin .merge .W8 (.reg .rax) (.lit 1)) rfl]
    exact NativeRustcVmX64.Arrays.merge_one_mod _
  rename_i hc
  have hz : rows.size ≠ 0 := fun hz ↦ hc (by
    rw [NativeRustcVmX64.Arrays.eval_test, Sym.eval, hcnt, hz]
    rfl)
  -- `b4`
  obtain ⟨hwf, hm⟩ := frame_env hpre hfr6 0
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk4 run_b4 hwf (fun _ h ↦ by cases h) hpc6 hm fun st7 hm7 hpc7 ↦ ?_
  have hs7 : SameOutside st6.data.dmem st7.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 16 32) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm7 hwf (by decide)
  have hfr7 : FR m0 8 st7.data :=
    hfr6.step hl (by decide) (by decide) ((rv hm7 (v := .ptr 0 8) rfl).trans (EachRow.eval_ptr0 8))
      (hm7.kept hwf) hs7 (by decide)
  obtain ⟨d7, pc7⟩ := st7
  simp only [PcOk] at hpc7
  simp only at hfr7 hs7 hm7
  subst hpc7
  have e6 : ∀ r, (after b3 rowsS).reg r = some (.reg r) → reg st6.data r = reg m r := fun r hr ↦
    rv hm6 (by rw [← after_eq run_b3]; exact hr)
  have e7 : ∀ r, (after b4 frameS).reg r = some (.reg r) → reg d7 r = reg st6.data r := fun r hr ↦
    rv hm7 (by rw [← after_eq run_b4]; exact hr)
  have e6r14 : reg st6.data .r14 = reg m0 .rcx :=
    (rv hm6 (v := .ptr 1 0) rfl).trans (by show reg m0 .rcx + BitVec.ofInt 64 0 = _; simp)
  have hlen : (tableOf m0).toList.length = (tableOf m0).size := Array.length_toList
  have hr12 : reg st6.data .r12 = BitVec.ofNat 64 (tableOf m0).size := (e6 .r12 rfl).trans h.r12
  have hlt : (tableOf m0).size < 32 := by have := h.tlen; omega
  refine cont d7 ⟨hfr7, ⟨?_, ?_, ?_, ?_, ?_⟩, Nat.pos_of_ne_zero hz, Nat.zero_le _,
    fun _ _ _ hi ↦ absurd hi (Nat.not_lt_zero _), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := NativeRustcVmX64.Transcript.wordAt_write hm7 (r := 0) (o := 16) rfl (by decide)
      (v := .reg .r14) (by decide)
    rw [show (Sym.reg .r14).eval (EachRow.envE m0 st6.data 1936 24 [] (fun _ ↦ 0) 0) =
      reg m0 .rcx from e6r14] at this
    exact this
  · have := NativeRustcVmX64.Transcript.wordAt_write hm7 (r := 0) (o := 24) rfl (by decide)
      (v := .bin .add .W64 (.reg .rbp) (.bin .mul .W64 (.reg .rbx) (.lit 8))) (by decide)
    rw [eval_qend _ ((e6 .rbp rfl).trans h.rbp) ((e6 .rbx rfl).trans h.rbx)] at this
    exact this
  · exact keepW hl (by decide) (by decide) hs7 (by decide) (by decide)
      (keepW hl (by decide) (by decide) hs6 (by decide) (by decide) h.w32)
  · exact keepW hl (by decide) (by decide) hs7 (by decide) (by decide)
      (keepW hl (by decide) (by decide) hs6 (by decide) (by decide) h.w40)
  · refine ⟨by rw [hlen]; exact h.tlen, ?_, ?_⟩
    · rw [hlen]
      exact keepW hl (by decide) (by decide) hs7 (by decide) (by decide) hcnt6
    · rw [show off (fb m0 + BitVec.ofNat 64 1384) 8 = fb m0 + BitVec.ofNat 64 1392 from
        NativeRustcVm.addr_add_add _ _ _]
      have hc := h.copy
      unfold PairsAt at hc ⊢
      exact EachRow.keep_frame hl (by decide) (by decide) hs7 (by decide)
        (.inr ⟨by decide, by
          rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, hlen]
          have := h.tlen; omega⟩)
        (EachRow.keep_frame hl (by decide) (by decide) hs6 (by decide)
          (.inr ⟨by decide, by
            rw [NativeRustcVm.length_wordsBytes, EachRow.length_pairWords, hlen]
            have := h.tlen; omega⟩) hc)
  · rw [e7 .rbp rfl, e6 .rbp rfl, h.rbp]
    simp
  · exact rv hm7 (v := .lit 0) rfl
  · rw [e7 .r13 rfl, rv hm6 (v := .load 1 16 8) rfl]
    exact hcnt
  · rw [e7 .r14 rfl, e6r14]
  · rw [rv hm7 (v := .ite (.not (.cmp .ult .W64 (.reg .r12) (.lit 32))) (.lit 0) (.reg .r12)) rfl,
      eval_cap _ _ _ hr12 hlt]
    exact hr12
  · rw [rv hm7 (v := .ite (.not (.cmp .ult .W64 (.reg .r12) (.lit 32))) (.lit 8) (.reg .r15)) rfl,
      eval_cap _ _ _ hr12 hlt]
    exact (e6 .r15 rfl).trans h.r15
  · exact (rv hm7 (v := .ptr 0 104) rfl).trans (EachRow.eval_ptr0 104)

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
