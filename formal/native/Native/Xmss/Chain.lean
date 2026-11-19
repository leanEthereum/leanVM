module

public import Native.Xmss.Mem

/-!
# The chains

`chainStep_spec`: a chain step hashes the buffer `bufA` (`P`, the step's address, `0`, the value,
the chain's index, `0`) and puts the digest back as the value.
-/

@[expose] public section

namespace Native.XmssVerifier

open Keccak

/-- The words a chain step writes: the address and the value. -/
def StepW (k : Nat) : Prop := k = bufA + 2 ∨ k = bufA + 4 ∨ k = bufA + 5

theorem chainStep_spec {E : QState → Prop} {s : QState} {b : UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem) {P0 P1 v0 v1 i : UInt64} {t : Nat}
    (ht : s.reg .r10 = t.toUInt64)
    (hA0 : s.mem (wd b bufA) = some P0) (hA1 : s.mem (wd b (bufA + 1)) = some P1)
    (hA3 : s.mem (wd b (bufA + 3)) = some 0) (hA4 : s.mem (wd b (bufA + 4)) = some v0)
    (hA5 : s.mem (wd b (bufA + 5)) = some v1) (hA6 : s.mem (wd b (bufA + 6)) = some i)
    (hA7 : s.mem (wd b (bufA + 7)) = some 0) :
    WP chainStep s (fun s' ↦
      s'.mem (wd b (bufA + 4)) =
        some (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i t (v0, v1)).1 ∧
      s'.mem (wd b (bufA + 5)) =
        some (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i t (v0, v1)).2 ∧
      s'.reg .r10 = t.toUInt64 + 1 ∧
      MemFrame b StepW s s' ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10] s s') E := by
  simp only [bufA_val, Nat.reduceAdd] at hA0 hA1 hA3 hA4 hA5 hA6 hA7 ⊢
  unfold chainStep
  simp only [tweakWord, List.cons_append, List.nil_append, bufA_val, Nat.reduceAdd]
  rstep; rstep; rstep; rstep; rstep; rstep; rstep; rstep
  refine WP.store' (b := b) (k := 1154) (by rw [eval_ctx]; simp [hrdi])
    (by simp only [QState.setReg_mem]; exact hdom 1154 (by decide)) ?_
  rstep; rstep
  refine WP.then (hash_call (b := b) (k0 := 1152)
    (ws := [P0, P1, tweakW (s.reg .r15) (s.reg .r13) ((t.toUInt64 <<< 5) + 1), 0, v0, v1, i, 0])
    ?_ ?_ (by decide) (by simp [ctxWords_val]) ?_ ?_ ?_) ?_
  · simp [hrdi]
  · simp only [QState.setReg_mem]
    exact hdom.setMem _ _
  · simp [eval_ctx, hrdi]
  · simp
  · intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    simp only [QState.setReg_mem]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wd_inj, hA0, hA1, hA3, hA4, hA5, hA6, hA7, tweakW, ht]
  rintro s₁ ⟨h0, h1, hfr, hreg⟩
  have hdom₁ := hfr.1
  have hrdi₁ : s₁.reg .rdi = b := by rw [hreg .rdi (by simp)]; simp [hrdi]
  refine WP.load' (b := b) (k := 0) (by rw [eval_ctx, hrdi₁]) h0 ?_
  refine WP.store' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdi₁])
    (by simp only [QState.setReg_mem]; exact hfr.1 1156 (by decide)) ?_
  refine WP.load' (b := b) (k := 1) (by rw [eval_ctx]; simp [hrdi₁])
    (by simpa [wd_inj, hrdi₁] using h1) ?_
  refine WP.store' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdi₁])
    (by simp only [QState.setReg_mem]; exact (hfr.1.setMem _ _) 1157 (by decide)) ?_
  rstep
  refine WP.blk_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [QState.setReg_mem, QState.setMem_mem, wd_inj, ite_true, ite_false,
      Nat.reduceEqDiff]
    rfl
  · simp (disch := omega) only [QState.setReg_mem, QState.setMem_mem, wd_inj, ite_true, ite_false,
      Nat.reduceEqDiff]
    rfl
  · simp only [QState.setReg_reg, QState.setMem_reg, ite_true]
    rw [hreg .r10 (by simp)]
    simp [ht]
  · refine ⟨by dom_tac, fun k h1 h2 h3 ↦ ?_⟩
    rw [ctxWords_val] at h2
    rw [scratchWords_val] at h1
    simp only [StepW, bufA_val, Nat.reduceAdd, not_or] at h3
    obtain ⟨h3a, h3b, h3c⟩ := h3
    simp (disch := omega) only [QState.setReg_mem, QState.setMem_mem, wd_inj, h3b, h3c,
      ite_false]
    rw [hfr.2 k (by rw [scratchWords_val]; omega) (by rw [ctxWords_val]; omega) id]
    simp (disch := omega) only [QState.setReg_mem, QState.setMem_mem, wd_inj, h3a, ite_false]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    simp only [QState.setReg_reg, QState.setMem_reg, h7, ite_false]
    rw [hreg r (by simp [h1, h2, h3, h4, h5, h6])]
    simp [h1, h4, h5, h2]

/-- The steps of a chain from position `d` to the end. -/
theorem chainSteps_spec {E : QState → Prop} {s : QState} {b : UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem) {P0 P1 i : UInt64} {v : W2} {d : Nat}
    (hd : d ≤ 3) (ht : s.reg .r10 = d.toUInt64)
    (hA0 : s.mem (wd b bufA) = some P0) (hA1 : s.mem (wd b (bufA + 1)) = some P1)
    (hA3 : s.mem (wd b (bufA + 3)) = some 0) (hA4 : s.mem (wd b (bufA + 4)) = some v.1)
    (hA5 : s.mem (wd b (bufA + 5)) = some v.2) (hA6 : s.mem (wd b (bufA + 6)) = some i)
    (hA7 : s.mem (wd b (bufA + 7)) = some 0) :
    WP (.loop (.cmp .ltu .r10 (.imm 3)) chainStep) s (fun s' ↦
      s'.mem (wd b (bufA + 4)) =
        some (walkW (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i) d (3 - d) v).1 ∧
      s'.mem (wd b (bufA + 5)) =
        some (walkW (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i) d (3 - d) v).2 ∧
      MemFrame b StepW s s' ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10] s s') E := by
  have hfix : ∀ {u : QState}, MemFrame b StepW s u → ∀ k, k = bufA ∨ k = bufA + 1 ∨
      k = bufA + 3 ∨ k = bufA + 6 ∨ k = bufA + 7 → u.mem (wd b k) = s.mem (wd b k) :=
    fun hu k hk ↦ hu.get (by rw [scratchWords_val, bufA_val] at *; omega)
      (by rw [ctxWords_val, bufA_val] at *; omega)
      (by simp only [StepW, bufA_val] at *; omega)
  refine WP.loop (fun u ↦ ∃ t, d ≤ t ∧ t ≤ 3 ∧ u.reg .r10 = t.toUInt64 ∧
      u.mem (wd b (bufA + 4)) =
        some (walkW (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i) d (t - d) v).1 ∧
      u.mem (wd b (bufA + 5)) =
        some (walkW (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i) d (t - d) v).2 ∧
      MemFrame b StepW s u ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10] s u)
    (fun u ↦ 3 - (u.reg .r10).toNat)
    ⟨d, le_rfl, hd, ht, by simpa [walkW] using hA4, by simpa [walkW] using hA5,
      MemFrame.refl hdom, fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro u ⟨t, hdt, ht3, hut, hu4, hu5, hfr, hreg⟩ hc
    simp only [Cond.eval, Rhs.eval, hut, int64Lit_toUInt64, decide_eq_true_eq] at hc
    have ht3' : t < 3 := (toUInt64_lt_iff (n := 3) (by omega) (by omega)).mp hc
    have hr15 : u.reg .r15 = s.reg .r15 := hreg .r15 (by simp)
    have hr13 : u.reg .r13 = s.reg .r13 := hreg .r13 (by simp)
    refine WP.mono (chainStep_spec (b := b) (by rw [hreg .rdi (by simp), hrdi]) hfr.1 hut
      (by rw [hfix hfr _ (by omega), hA0]) (by rw [hfix hfr _ (by omega), hA1])
      (by rw [hfix hfr _ (by omega), hA3]) hu4 hu5
      (by rw [hfix hfr _ (by omega), hA6]) (by rw [hfix hfr _ (by omega), hA7])) ?_ fun _ h ↦ h
    rintro u' ⟨h4, h5, h10, hfr', hreg'⟩
    have hwalk : walkW (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i) d (t + 1 - d) v =
        chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i t
          (walkW (chainStepW (P0, P1) (s.reg .r15) (s.reg .r13) i) d (t - d) v) := by
      rw [show t + 1 - d = (t - d) + 1 by omega, walkW, show d + (t - d) = t by omega]
    refine ⟨⟨t + 1, by omega, by omega, by rw [h10, toUInt64_add_one], ?_, ?_,
      hfr.trans hfr' (by intro k h; simpa using h), rf_trans hreg hreg'⟩, ?_⟩
    · rw [h4, hwalk, hr15, hr13]
    · rw [h5, hwalk, hr15, hr13]
    · rw [h10, hut, toUInt64_add_one, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨t, hdt, ht3, hut, hu4, hu5, hfr, hreg⟩ hc
    simp only [Cond.eval, Rhs.eval, hut, int64Lit_toUInt64, decide_eq_false_iff_not] at hc
    have ht3' : t = 3 := by
      have := (toUInt64_lt_iff (t := t) (n := 3) (by omega) (by omega)).not.mp hc
      omega
    subst ht3'
    exact ⟨hu4, hu5, hfr, hreg⟩

/-! ## The digits -/

theorem shiftW_succ (D : W2) {i : Nat} (hi : i < 58) (h : i + 1 ≠ 32) :
    shiftW D i >>> 2 = shiftW D (i + 1) := by
  unfold shiftW
  by_cases h1 : i < 32
  · simp only [h1, show i + 1 < 32 by omega, ↓reduceIte]
    rw [show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, shiftRight_toUInt64_add _ (by omega)]
    congr 2
  · simp only [h1, show ¬ i + 1 < 32 by omega, ↓reduceIte]
    rw [show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, shiftRight_toUInt64_add _ (by omega)]
    congr 2
    omega

theorem shiftW_32 (D : W2) : shiftW D 32 = D.2 := by
  simp [shiftW]

theorem digitW_le (D : W2) (i : Nat) : (digitW D i).toNat ≤ 3 := by
  unfold digitW
  rw [UInt64.toNat_and]
  exact Nat.and_le_right

/-! ## One chain -/

/-- The words chain `i` writes: a step's, its index and zero, its end in the leaf's buffer. -/
def ChainW (i k : Nat) : Prop :=
  StepW k ∨ k = bufA + 6 ∨ k = bufA + 7 ∨ k = bufL + 4 + 2 * i ∨ k = bufL + 5 + 2 * i

theorem chain_spec {E : QState → Prop} {s : QState} {b : UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem) {P0 P1 : UInt64} {D : W2} {K i : Nat}
    {sw : Nat → UInt64} (hi : i < 58) (hK : scratchWords ≤ K) (hK' : K + 150 ≤ bufA)
    (hr11 : s.reg .r11 = i.toUInt64) (hbp : i ≠ 32 → s.reg .rbp = shiftW D i)
    (hdhi : s.mem (wd b dhiW) = some D.2) (hr14 : s.reg .r14 = wd b K)
    (hsw : ∀ k < 150, s.mem (wd b (K + k)) = some (sw k))
    (hA0 : s.mem (wd b bufA) = some P0) (hA1 : s.mem (wd b (bufA + 1)) = some P1)
    (hA3 : s.mem (wd b (bufA + 3)) = some 0) :
    WP chain s (fun s' ↦
      s'.reg .r11 = (i + 1).toUInt64 ∧
      (i + 1 ≠ 32 → s'.reg .rbp = shiftW D (i + 1)) ∧
      s'.reg .r9 = s.reg .r9 + digitW D i ∧
      s'.mem (wd b (bufL + 4 + 2 * i)) =
        some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D i (sw (2 + 2 * i), sw (3 + 2 * i))).1 ∧
      s'.mem (wd b (bufL + 5 + 2 * i)) =
        some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D i (sw (2 + 2 * i), sw (3 + 2 * i))).2 ∧
      MemFrame b (ChainW i) s s' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10, .r11, .rbp, .r9] s s') E := by
  rw [scratchWords_val] at hK
  simp only [bufA_val, dhiW_val, Nat.reduceAdd] at hK' hA0 hA1 hA3 hdhi
  unfold chain
  refine WP.then (Q := fun u ↦ u.reg .rbp = shiftW D i ∧ u.mem = s.mem ∧ RegsFrame [.rbp] s u)
    (WP.ite ?_) ?_
  · by_cases h32 : i = 32
    · subst h32
      have hc : Cond.eval (.cmp .eq .r11 (.imm 32)) s = true := by
        simp [Cond.eval, Rhs.eval, hr11, int64Lit_toUInt64]
      simp only [hc, ↓reduceIte]
      refine WP.ins' ?_
      simp only [QInstr.step, eval_ctx, hrdi, dhiW_val, hdhi, Option.map_some]
      exact ⟨by simp [shiftW_32], rfl, rf_setReg (rf_refl _ _) (by simp) _⟩
    · have hc : Cond.eval (.cmp .eq .r11 (.imm 32)) s = false := by
        simp only [Cond.eval, Rhs.eval, hr11, int64Lit_toUInt64, beq_eq_false_iff_ne, ne_eq]
        rw [show (32 : UInt64) = (32 : Nat).toUInt64 from rfl,
          toUInt64_eq_iff (by omega) (by omega)]
        exact h32
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact WP.skip ⟨hbp h32, rfl, rf_refl _ _⟩
  rintro u ⟨hbpu, hmem, hrf⟩
  have hdomu : Dom b u.mem := hmem ▸ hdom
  have hrdiu : u.reg .rdi = b := (hrf .rdi (by simp)).trans hrdi
  have hr11u : u.reg .r11 = i.toUInt64 := (hrf .r11 (by simp)).trans hr11
  have hr14u : u.reg .r14 = wd b K := (hrf .r14 (by simp)).trans hr14
  have hr9u : u.reg .r9 = s.reg .r9 := hrf .r9 (by simp)
  have hr15u : u.reg .r15 = s.reg .r15 := hrf .r15 (by simp)
  have hr13u : u.reg .r13 = s.reg .r13 := hrf .r13 (by simp)
  rstep [hbpu]; rstep; rstep [hr9u]; rstep; rstep [hr11u]
  rstep [toUInt64_shl4 (by omega : i < 2 ^ 59)]
  refine WP.load' (b := b) (k := K + 2 * i + 2) (eval_sigAt (by simp [hr14u]) (by simp) 2)
    (by
      rw [show K + 2 * i + 2 = K + (2 + 2 * i) by omega]
      simpa [hmem] using hsw _ (by omega)) ?_
  refine WP.store' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdiu, bufA_val])
    (by isSome_tac) ?_
  refine WP.load' (b := b) (k := K + 2 * i + 3) (eval_sigAt (by simp [hr14u]) (by simp) 3)
    (by
      rw [show K + 2 * i + 3 = K + (3 + 2 * i) by omega]
      mem_simp [show K + (3 + 2 * i) ≠ 1156 by omega, hmem]
      exact hsw _ (by omega)) ?_
  refine WP.store' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdiu, bufA_val])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 1158) (by rw [eval_ctx]; simp [hrdiu, bufA_val])
    (by isSome_tac) ?_
  refine WP.storei' (b := b) (k := 1159) (by rw [eval_ctx]; simp [hrdiu, bufA_val])
    (by isSome_tac) ?_
  refine WP.then (chainSteps_spec (b := b) (by simp [hrdiu]) (by dom_tac) (P0 := P0) (P1 := P1)
    (i := i.toUInt64) (v := (sw (2 + 2 * i), sw (3 + 2 * i))) (d := (digitW D i).toNat)
    (digitW_le D i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · simp [digitW]
  · mem_simp [hmem, hA0]
  · mem_simp [hmem, hA1]
  · mem_simp [hmem, hA3]
  · mem_simp
  · mem_simp
  · mem_simp [hr11u]
  · mem_simp
  rintro u₂ ⟨h4, h5, hfr₂, hrf₂⟩
  have hdom₂ := hfr₂.1
  simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false, ite_true] at h4 h5
  have hreg₂ : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10] → u₂.reg r = _ :=
    fun r hr ↦ hrf₂ r hr
  have hrdi₂ : u₂.reg .rdi = b := by rw [hreg₂ .rdi (by simp)]; simp [hrdiu]
  have hr11₂ : u₂.reg .r11 = i.toUInt64 := by rw [hreg₂ .r11 (by simp)]; simp [hr11u]
  rstep [hr11₂]; rstep [toUInt64_shl4 (by omega : i < 2 ^ 59)]
  refine WP.load' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdi₂, bufA_val])
    (by simpa [bufA_val] using h4) ?_
  refine WP.store' (b := b) (k := 1172 + 2 * i)
    (by rw [eval_ctxAt (j := 2 * i) (by simp)]; simp only [QState.setReg_reg, reduceCtorEq,
      ite_false, hrdi₂, bufL_val, Nat.reduceAdd]; congr 1; omega) (by isSome_tac) ?_
  refine WP.load' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdi₂, bufA_val])
    (by mem_simp [show ¬ (1157 = 1172 + 2 * i) by omega]; simpa [bufA_val] using h5) ?_
  refine WP.store' (b := b) (k := 1173 + 2 * i)
    (by rw [eval_ctxAt (j := 2 * i) (by simp)]; simp only [QState.setReg_reg, QState.setMem_reg,
      reduceCtorEq, ite_false, hrdi₂, bufL_val, Nat.reduceAdd]; congr 1; omega) (by isSome_tac) ?_
  rstep [hr11₂]
  refine WP.blk_nil ⟨?_, fun h ↦ ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [QState.setReg_reg, QState.setMem_reg, ite_true, hr11₂]
    exact toUInt64_add_one i
  · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false]
    rw [hreg₂ .rbp (by simp)]
    simp [hbpu, shiftW_succ D hi h]
  · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false]
    rw [hreg₂ .r9 (by simp)]
    simp [digitW]
  · mem_simp
    simp [chainEndW, hr15u, hr13u]
  · mem_simp
    simp [chainEndW, hr15u, hr13u]
  · have hsu : MemFrame b (ChainW i) s u := ⟨hdomu, fun k _ _ _ ↦ by rw [hmem]⟩
    frame_tac
    · refine MemFrame.trans (W := ChainW i) (W' := StepW) ?_ hfr₂ (fun k h ↦ ?_)
      · frame_tac
        · exact hsu
        all_goals first
          | simp [ChainW, StepW, bufA_val, bufL_val]
          | (rw [ctxWords_val]; omega)
      · rcases h with h | h
        · exact h
        · exact Or.inl h
    all_goals first
      | simp [ChainW, StepW, bufA_val, bufL_val]
      | (rw [ctxWords_val]; omega)
  · rf_tac
    refine rf_trans (l := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10, .r11, .rbp, .r9])
      (l'' := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10, .r11, .rbp, .r9]) ?_ hrf₂ (by simp)
      (by simp)
    rf_tac
    exact rf_mono hrf (by simp)

/-! ## The chains -/

/-- The words the chains write: a step's, a chain's index and zero, the leaf's chain ends. -/
def ChainsW (k : Nat) : Prop :=
  StepW k ∨ k = bufA + 6 ∨ k = bufA + 7 ∨ (bufL + 4 ≤ k ∧ k < bufL + 120)

theorem shiftW_zero (D : W2) : shiftW D 0 = D.1 := by
  simp [shiftW]

theorem chains_spec {E : QState → Prop} {s : QState} {b : UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem) {P0 P1 : UInt64} {D : W2} {K : Nat}
    {sw : Nat → UInt64} (hK : scratchWords ≤ K) (hK' : K + 150 ≤ bufA)
    (hbp : s.reg .rbp = D.1) (hdhi : s.mem (wd b dhiW) = some D.2) (hr14 : s.reg .r14 = wd b K)
    (hsw : ∀ k < 150, s.mem (wd b (K + k)) = some (sw k))
    (hA0 : s.mem (wd b bufA) = some P0) (hA1 : s.mem (wd b (bufA + 1)) = some P1)
    (hA3 : s.mem (wd b (bufA + 3)) = some 0) :
    WP chains s (fun s' ↦
      (∀ c < 58, s'.mem (wd b (bufL + 4 + 2 * c)) =
          some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D c
            (sw (2 + 2 * c), sw (3 + 2 * c))).1 ∧
        s'.mem (wd b (bufL + 5 + 2 * c)) =
          some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D c
            (sw (2 + 2 * c), sw (3 + 2 * c))).2) ∧
      s'.reg .r12 = s.reg .r12 ||| (digitSumW D 58 ^^^ 106) ∧
      MemFrame b ChainsW s s' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10, .r11, .rbp, .r9, .r12] s s') E := by
  have hK0 := hK
  have hK1 := hK'
  rw [scratchWords_val] at hK0
  rw [bufA_val] at hK1
  have hget : ∀ {u : QState}, MemFrame b ChainsW s u → ∀ k, scratchWords ≤ k → k < bufA →
      u.mem (wd b k) = s.mem (wd b k) := fun hu k h1 h2 ↦ hu.get h1
    (by rw [ctxWords_val]; rw [bufA_val] at h2; omega)
    (by simp only [ChainsW, StepW, bufA_val, bufL_val] at h2 ⊢; omega)
  have hfixA : ∀ {u : QState}, MemFrame b ChainsW s u → ∀ k, k = bufA ∨ k = bufA + 1 ∨
      k = bufA + 3 ∨ k = dhiW → u.mem (wd b k) = s.mem (wd b k) := fun hu k hk ↦ hu.get
    (by rw [scratchWords_val]; simp only [bufA_val, dhiW_val] at hk; omega)
    (by rw [ctxWords_val]; simp only [bufA_val, dhiW_val] at hk; omega)
    (by simp only [ChainsW, StepW, bufA_val, bufL_val, dhiW_val] at hk ⊢; omega)
  unfold chains
  rstep; rstep
  refine WP.then (Q := fun u ↦ (∀ c < 58, u.mem (wd b (bufL + 4 + 2 * c)) =
          some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D c
            (sw (2 + 2 * c), sw (3 + 2 * c))).1 ∧
        u.mem (wd b (bufL + 5 + 2 * c)) =
          some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D c
            (sw (2 + 2 * c), sw (3 + 2 * c))).2) ∧
      u.reg .r9 = digitSumW D 58 ∧ MemFrame b ChainsW s u ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10, .r11, .rbp, .r9] s u)
    (WP.loop (fun u ↦ ∃ i ≤ 58, u.reg .r11 = i.toUInt64 ∧ (i ≠ 32 → u.reg .rbp = shiftW D i) ∧
        u.reg .r9 = digitSumW D i ∧
        (∀ c < i, u.mem (wd b (bufL + 4 + 2 * c)) =
            some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D c
              (sw (2 + 2 * c), sw (3 + 2 * c))).1 ∧
          u.mem (wd b (bufL + 5 + 2 * c)) =
            some (chainEndW (P0, P1) (s.reg .r15) (s.reg .r13) D c
              (sw (2 + 2 * c), sw (3 + 2 * c))).2) ∧
        MemFrame b ChainsW s u ∧
        RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10, .r11, .rbp, .r9] s u)
      (fun u ↦ 58 - (u.reg .r11).toNat)
      ⟨0, by omega, by simp, fun _ ↦ by simp [hbp, shiftW_zero], by simp [digitSumW],
        fun c hc ↦ absurd hc (by omega), ⟨by dom_tac, fun _ _ _ _ ↦ rfl⟩,
        by rf_tac; exact rf_refl _ _⟩
      ?_ ?_) ?_
  · rintro u ⟨i, hi, hr11, hbpu, hr9, hL, hfr, hrf⟩ hc
    simp only [Cond.eval, Rhs.eval, hr11, int64Lit_toUInt64, decide_eq_true_eq] at hc
    have hi' : i < 58 := (toUInt64_lt_iff (n := 58) (by omega) (by omega)).mp hc
    refine WP.mono (chain_spec (b := b) (by rw [hrf .rdi (by simp), hrdi]) hfr.1 (P0 := P0) (P1 := P1)
      (sw := sw) hi' hK hK' hr11 hbpu
      (by rw [hfixA hfr _ (by omega), hdhi]) (by rw [hrf .r14 (by simp), hr14])
      (fun k hk ↦ by rw [hget hfr _ (by rw [scratchWords_val]; omega)
        (by rw [bufA_val]; omega), hsw k hk])
      (by rw [hfixA hfr _ (by omega), hA0]) (by rw [hfixA hfr _ (by omega), hA1])
      (by rw [hfixA hfr _ (by omega), hA3])) ?_ fun _ h ↦ h
    rintro u' ⟨h11, hbp', h9, hL4, hL5, hfr', hrf'⟩
    have h15 : u.reg .r15 = s.reg .r15 := hrf .r15 (by simp)
    have h13 : u.reg .r13 = s.reg .r13 := hrf .r13 (by simp)
    rw [h15, h13] at hL4 hL5
    refine ⟨⟨i + 1, by omega, h11, hbp', by rw [h9, hr9]; rfl, fun c hc ↦ ?_,
      hfr.trans hfr' fun k h ↦ ?_, rf_trans hrf hrf' (by simp) (by simp)⟩, ?_⟩
    · by_cases hci : c = i
      · subst hci
        exact ⟨hL4, hL5⟩
      · have hc' : c < i := by omega
        rw [hfr'.get (by rw [scratchWords_val, bufL_val]; omega)
            (by rw [ctxWords_val, bufL_val]; omega)
            (by simp only [ChainW, StepW, bufA_val, bufL_val]; omega),
          hfr'.get (by rw [scratchWords_val, bufL_val]; omega)
            (by rw [ctxWords_val, bufL_val]; omega)
            (by simp only [ChainW, StepW, bufA_val, bufL_val]; omega)]
        exact hL c hc'
    · rcases h with h | h
      · exact h
      · simp only [ChainW, ChainsW, StepW, bufA_val, bufL_val] at h ⊢
        omega
    · rw [h11, hr11, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨i, hi, hr11, -, hr9, hL, hfr, hrf⟩ hc
    simp only [Cond.eval, Rhs.eval, hr11, int64Lit_toUInt64, decide_eq_false_iff_not] at hc
    have hi' : i = 58 := by
      have := (toUInt64_lt_iff (t := i) (n := 58) (by omega) (by omega)).not.mp hc
      omega
    subst hi'
    exact ⟨hL, hr9, hfr, hrf⟩
  rintro u ⟨hL, hr9, hfr, hrf⟩
  rstep; rstep [hr9]
  refine WP.blk_nil ⟨hL, ?_, hfr, ?_⟩
  · simp only [QState.setReg_reg, ite_true, reduceCtorEq, ite_false]
    rw [hrf .r12 (by simp)]
  · rf_tac
    exact rf_mono hrf (by simp)

end Native.XmssVerifier
