module

public import X86.Xmss.Layer

/-!
# `body` computes the model

`body_spec`: from a context holding the input words `inp`, `body` ends normally with `rax = 1` if
`verifyW inp` and `0` if not, and the callee-saved registers as they were.
-/

@[expose] public section

namespace X86.XmssVerifier

open Keccak

/-- The layers loop's invariant after `n` layers: the registers of layer `n`, the checks so far in
`r12`, the last root in the buffer's payload; the words outside the buffers as after `init`. -/
def LayersInv (b : UInt64) (inp : Nat → UInt64) (s₁ : QState) (n : Nat) (u : QState) : Prop :=
  n ≤ 2 ∧ u.reg .r15 = n.toUInt64 ∧ u.reg .r14 = wd b (sigW + 150 * n) ∧
  u.reg .r13 = inp 8 >>> (16 * n).toUInt64 ∧ (u.reg .r12 = 0 ↔ (afterLayers inp n).1 = true) ∧
  (n ≠ 0 → u.mem (wd b (bufA + 4)) = some (afterLayers inp n).2.1 ∧
    u.mem (wd b (bufA + 5)) = some (afterLayers inp n).2.2) ∧
  u.reg .rdi = b ∧ MemFrame b WorkW s₁ u ∧
  RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .rbp, .r12, .r13, .r14, .r15] s₁ u

theorem layers_spec {E : QState → Prop} {s₁ : QState} {b : UInt64} {inp : Nat → UInt64}
    (hin : ∀ i < 309, s₁.mem (wd b (inputW + i)) = some (inp i))
    (hA0 : s₁.mem (wd b bufA) = some (inp 2)) (hA1 : s₁.mem (wd b (bufA + 1)) = some (inp 3))
    (hA3 : s₁.mem (wd b (bufA + 3)) = some 0)
    (hL0 : s₁.mem (wd b bufL) = some (inp 2)) (hL1 : s₁.mem (wd b (bufL + 1)) = some (inp 3))
    (hL3 : s₁.mem (wd b (bufL + 3)) = some 0) (h0 : LayersInv b inp s₁ 0 s₁) :
    WP (.loop (.cmp .ltu .r15 (.imm 2)) layer) s₁ (LayersInv b inp s₁ 2) E := by
  refine WP.loop (fun u ↦ ∃ n, LayersInv b inp s₁ n u) (fun u ↦ 2 - (u.reg .r15).toNat)
    ⟨0, h0⟩ ?_ ?_
  · rintro u ⟨n, hn, h15, h14, h13, h12, hroot, hrdi, hfr, hrf⟩ hc
    simp only [Cond.eval, Rhs.eval, h15, int64Lit_toUInt64, decide_eq_true_eq] at hc
    have hn' : n < 2 := (toUInt64_lt_iff (n := 2) (by omega) (by omega)).mp hc
    have hget : ∀ k, scratchWords ≤ k → (k < bufA ∨ k = bufA ∨ k = bufA + 1 ∨ k = bufA + 3 ∨
        k = bufL ∨ k = bufL + 1 ∨ k = bufL + 3) → u.mem (wd b k) = s₁.mem (wd b k) :=
      fun k h1 h2 ↦ WorkW.get hfr h1 h2
    refine WP.mono (layer_spec (b := b) hrdi hfr.1 (K := sigW + 150 * n) (P0 := inp 2) (P1 := inp 3)
      (sw := fun k ↦ inp (9 + 150 * n + k)) (m := fun j ↦ inp (4 + j))
      (r := (afterLayers inp n).2)
      (by simp only [sigW, inputW_val, scratchWords_val]; omega)
      (by simp only [sigW, inputW_val, bufA_val]; omega) h14
      (fun k hk ↦ by
        rw [hget _ (by simp only [sigW, inputW_val, scratchWords_val]; omega)
          (Or.inl (by simp only [sigW, inputW_val, bufA_val]; omega))]
        have := hin (9 + 150 * n + k) (by omega)
        rwa [show inputW + (9 + 150 * n + k) = sigW + 150 * n + k by simp only [sigW]; omega]
          at this)
      (by rw [hget _ (by decide) (by simp), hA0]) (by rw [hget _ (by decide) (by simp), hA1])
      (by rw [hget _ (by decide) (by simp), hA3]) (by rw [hget _ (by decide) (by simp), hL0])
      (by rw [hget _ (by decide) (by simp), hL1]) (by rw [hget _ (by decide) (by simp), hL3])
      (fun h j hj ↦ by
        rw [hget _ (by simp only [msgW, inputW_val, scratchWords_val]; omega)
          (Or.inl (by simp only [msgW, inputW_val, bufA_val]; omega))]
        have := hin (4 + j) (by omega)
        rwa [show inputW + (4 + j) = msgW + j by simp only [msgW]; omega] at this)
      (fun h ↦ hroot (by rintro rfl; exact h (by rw [h15]; rfl)))) ?_ fun _ h ↦ h
    rintro u' ⟨hr4, hr5, h12', h15', h14', h13', hrdi', hfr', hrf'⟩
    have hif : (if u.reg .r15 = 0 then [inp (4 + 0), inp (4 + 1), inp (4 + 2), inp (4 + 3)]
        else [(afterLayers inp n).2.1, (afterLayers inp n).2.2]) =
        (if n = 0 then [inp 4, inp 5, inp 6, inp 7]
        else [(afterLayers inp n).2.1, (afterLayers inp n).2.2]) := by
      rw [h15]
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> rfl
    rw [hif, h15, h13] at hr4 hr5 h12'
    refine ⟨⟨n + 1, by omega, by rw [h15', h15, toUInt64_add_one], ?_, ?_, ?_, fun _ ↦ ⟨?_, ?_⟩,
      hrdi', hfr.trans hfr' fun k h ↦ h.elim id id, rf_trans hrf hrf' (by simp) (by simp)⟩, ?_⟩
    · rw [h14']
      congr 1
    · rw [h13', h13, show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
        shiftRight_toUInt64_add _ (by omega)]
      congr 2
    · rw [h12', h12]
      simp [afterLayers]
    · rw [hr4]
      rfl
    · rw [hr5]
      rfl
    · rw [h15', h15, toUInt64_add_one, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨n, hinv⟩ hc
    simp only [Cond.eval, Rhs.eval, hinv.2.1, int64Lit_toUInt64, decide_eq_false_iff_not] at hc
    have hn2 := hinv.1
    have hn : n = 2 := by
      have := (toUInt64_lt_iff (t := n) (n := 2) (by omega) (by omega)).not.mp hc
      omega
    subst hn
    exact hinv

/-- `rax` from the checks: `1` when they all passed. -/
theorem final_spec {E : QState → Prop} {u : QState} {b : UInt64} {inp : Nat → UInt64}
    (hrdi : u.reg .rdi = b)
    (h12 : u.reg .r12 = 0 ↔ (afterLayers inp 2).1 = true)
    (h4 : u.mem (wd b (bufA + 4)) = some (afterLayers inp 2).2.1)
    (h5 : u.mem (wd b (bufA + 5)) = some (afterLayers inp 2).2.2)
    (hr0 : u.mem (wd b rootW) = some (inp 0)) (hr1 : u.mem (wd b (rootW + 1)) = some (inp 1)) :
    WP final u (fun u' ↦ u'.reg .rax = (if verifyW inp then 1 else 0) ∧ u'.mem = u.mem ∧
      RegsFrame [.rax, .rdx, .r12] u u') E := by
  simp only [bufA_val, rootW, inputW_val, Nat.reduceAdd] at h4 h5 hr0 hr1
  unfold final
  refine WP.load' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdi, bufA_val]) h4 ?_
  refine WP.load' (b := b) (k := 128) (by rw [eval_ctx]; simp [hrdi, rootW, inputW_val]) hr0 ?_
  rstep; rstep
  refine WP.load' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdi, bufA_val]) h5 ?_
  refine WP.load' (b := b) (k := 129) (by rw [eval_ctx]; simp [hrdi, rootW, inputW_val]) hr1 ?_
  rstep; rstep; rstep
  have hv : (u.reg .r12 ||| ((afterLayers inp 2).2.1 ^^^ inp 0) |||
      ((afterLayers inp 2).2.2 ^^^ inp 1) = 0) ↔ verifyW inp = true := by
    simp only [UInt64.or_eq_zero_iff, UInt64.xor_eq_zero_iff, h12, verifyW, Bool.and_eq_true,
      beq_iff_eq, Prod.ext_iff, and_assoc]
  by_cases hver : verifyW inp = true
  · refine WP.ite_true (by simp [Cond.eval, Rhs.eval, int64Lit_toUInt64, hv.mpr hver]) ?_
    refine WP.ins' ?_
    simp only [QInstr.step]
    refine ⟨by simp [hver, int64Lit_toUInt64], rfl, ?_⟩
    rf_tac
    exact rf_refl _ _
  · refine WP.ite_false (by simp [Cond.eval, Rhs.eval, int64Lit_toUInt64, hv, hver]) ?_
    refine WP.skip ⟨by simp [hver], rfl, ?_⟩
    rf_tac
    exact rf_refl _ _

/-- The save area's word of each callee-saved register. -/
theorem save_spec {E : QState → Prop} {s : QState} {b : UInt64} (hrdi : s.reg .rdi = b)
    (hdom : Dom b s.mem) :
    WP save s (fun u ↦ u.reg = s.reg ∧ MemFrame b (fun k ↦ 88 ≤ k ∧ k < 94) s u ∧
      u.mem (wd b 88) = some (s.reg .rbx) ∧ u.mem (wd b 89) = some (s.reg .rbp) ∧
      u.mem (wd b 90) = some (s.reg .r12) ∧ u.mem (wd b 91) = some (s.reg .r13) ∧
      u.mem (wd b 92) = some (s.reg .r14) ∧ u.mem (wd b 93) = some (s.reg .r15)) E := by
  unfold save
  refine WP.store' (b := b) (k := 88) (by rw [eval_rdi _ (k := 88) (by decide), hrdi])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 89) (by rw [eval_rdi _ (k := 89) (by decide)]; simp [hrdi])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 90) (by rw [eval_rdi _ (k := 90) (by decide)]; simp [hrdi])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 91) (by rw [eval_rdi _ (k := 91) (by decide)]; simp [hrdi])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 92) (by rw [eval_rdi _ (k := 92) (by decide)]; simp [hrdi])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 93) (by rw [eval_rdi _ (k := 93) (by decide)]; simp [hrdi])
    (by isSome_tac) ?_
  refine WP.blk_nil ⟨by simp, ?_, by mem_simp, by mem_simp, by mem_simp, by mem_simp,
    by mem_simp, by mem_simp⟩
  frame_tac
  · exact MemFrame.refl hdom
  all_goals decide

/-- `P` and the zero word into both buffers, the bottom layer's registers. -/
theorem init_spec {E : QState → Prop} {s : QState} {b : UInt64} {inp : Nat → UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem)
    (hin : ∀ i < 309, s.mem (wd b (inputW + i)) = some (inp i)) :
    WP init s (fun u ↦ u.reg .r15 = 0 ∧ u.reg .r12 = 0 ∧ u.reg .r13 = inp 8 ∧
      u.reg .r14 = wd b sigW ∧ u.reg .rdi = b ∧
      u.mem (wd b bufA) = some (inp 2) ∧ u.mem (wd b (bufA + 1)) = some (inp 3) ∧
      u.mem (wd b (bufA + 3)) = some 0 ∧ u.mem (wd b bufL) = some (inp 2) ∧
      u.mem (wd b (bufL + 1)) = some (inp 3) ∧ u.mem (wd b (bufL + 3)) = some 0 ∧
      MemFrame b (fun k ↦ k = bufA ∨ k = bufA + 1 ∨ k = bufA + 3 ∨ k = bufL ∨ k = bufL + 1 ∨
        k = bufL + 3) s u ∧
      RegsFrame [.rax, .r12, .r13, .r14, .r15] s u) E := by
  have h2 := hin 2 (by omega)
  have h3 := hin 3 (by omega)
  have h8 := hin 8 (by omega)
  simp only [inputW_val, Nat.reduceAdd] at h2 h3 h8
  unfold init
  refine WP.load' (b := b) (k := 130) (by rw [eval_ctx]; simp [hrdi, paramW, inputW_val]) h2 ?_
  refine WP.store' (b := b) (k := 1152) (by rw [eval_ctx]; simp [hrdi, bufA_val])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 1168) (by rw [eval_ctx]; simp [hrdi, bufL_val])
    (by isSome_tac) ?_
  refine WP.load' (b := b) (k := 131) (by rw [eval_ctx]; simp [hrdi, paramW, inputW_val])
    (by mem_simp; exact h3) ?_
  refine WP.store' (b := b) (k := 1153) (by rw [eval_ctx]; simp [hrdi, bufA_val])
    (by isSome_tac) ?_
  refine WP.store' (b := b) (k := 1169) (by rw [eval_ctx]; simp [hrdi, bufL_val])
    (by isSome_tac) ?_
  refine WP.storei' (b := b) (k := 1155) (by rw [eval_ctx]; simp [hrdi, bufA_val])
    (by isSome_tac) ?_
  refine WP.storei' (b := b) (k := 1171) (by rw [eval_ctx]; simp [hrdi, bufL_val])
    (by isSome_tac) ?_
  rstep; rstep
  refine WP.load' (b := b) (k := 136) (by rw [eval_ctx]; simp [hrdi, idxW, inputW_val])
    (by mem_simp; exact h8) ?_
  rstep
  refine WP.blk_nil ⟨by simp, by simp, by simp, ?_, by simp [hrdi], by mem_simp, by mem_simp,
    by mem_simp, by mem_simp, by mem_simp, by mem_simp, ?_, ?_⟩
  · simp only [QState.setReg_reg, ite_true, eval_ctx, reduceCtorEq, ite_false, QState.setMem_reg,
      hrdi]
  · frame_tac
    · exact MemFrame.refl hdom
    all_goals first
      | simp [bufA_val, bufL_val]
      | decide
  · rf_tac
    exact rf_refl _ _

/-- Restore the callee-saved registers from the save area. -/
theorem restore_spec {E : QState → Prop} {u : QState} {b : UInt64} {sv : Reg64 → UInt64}
    (hrdi : u.reg .rdi = b)
    (h88 : u.mem (wd b 88) = some (sv .rbx)) (h89 : u.mem (wd b 89) = some (sv .rbp))
    (h90 : u.mem (wd b 90) = some (sv .r12)) (h91 : u.mem (wd b 91) = some (sv .r13))
    (h92 : u.mem (wd b 92) = some (sv .r14)) (h93 : u.mem (wd b 93) = some (sv .r15)) :
    WP restore u (fun u' ↦ u'.reg .rax = u.reg .rax ∧ ∀ r ∈ Context.calleeSaved, u'.reg r = sv r)
      E := by
  unfold restore
  refine WP.load' (b := b) (k := 88) (by rw [eval_rdi _ (k := 88) (by decide), hrdi]) h88 ?_
  refine WP.load' (b := b) (k := 89) (by rw [eval_rdi _ (k := 89) (by decide)]; simp [hrdi]) h89 ?_
  refine WP.load' (b := b) (k := 90) (by rw [eval_rdi _ (k := 90) (by decide)]; simp [hrdi]) h90 ?_
  refine WP.load' (b := b) (k := 91) (by rw [eval_rdi _ (k := 91) (by decide)]; simp [hrdi]) h91 ?_
  refine WP.load' (b := b) (k := 92) (by rw [eval_rdi _ (k := 92) (by decide)]; simp [hrdi]) h92 ?_
  refine WP.load' (b := b) (k := 93) (by rw [eval_rdi _ (k := 93) (by decide)]; simp [hrdi]) h93 ?_
  refine WP.blk_nil ⟨by simp, ?_⟩
  simp [Context.calleeSaved]

/-- **`body` computes `verifyW`** on the input words, and keeps the callee-saved registers. -/
theorem body_spec {s : QState} {b : UInt64} {inp : Nat → UInt64} (hrdi : s.reg .rdi = b)
    (hctx : Context.At s.mem b) (hin : Context.InputAt s.mem b 309 inp) :
    WP body s (fun s' ↦ s'.reg .rax = (if verifyW inp then 1 else 0) ∧
      ∀ r ∈ Context.calleeSaved, s'.reg r = s.reg r) (fun _ ↦ False) := by
  have hdom : Dom b s.mem := hctx.words
  have hin' : ∀ i < 309, s.mem (wd b (inputW + i)) = some (inp i) := fun i hi ↦ by
    have := hin i hi
    rwa [show b + (Context.inputOff + 8 * i).toUInt64 = wd b (inputW + i) by
      unfold wd
      congr 2
      simp only [Context.inputOff, inputW_val]
      omega] at this
  unfold body
  refine WP.then (save_spec hrdi hdom) ?_
  rintro s₁ ⟨hreg₁, hfr₁, h88, h89, h90, h91, h92, h93⟩
  have hrdi₁ : s₁.reg .rdi = b := by rw [hreg₁, hrdi]
  have hin₁ : ∀ i < 309, s₁.mem (wd b (inputW + i)) = some (inp i) := fun i hi ↦ by
    rw [hfr₁.get (by rw [scratchWords_val, inputW_val]; omega)
      (by rw [ctxWords_val, inputW_val]; omega) (by rw [inputW_val]; omega), hin' i hi]
  refine WP.then (init_spec hrdi₁ hfr₁.1 hin₁) ?_
  rintro s₂ ⟨h15, h12, h13, h14, hrdi₂, hA0, hA1, hA3, hL0, hL1, hL3, hfr₂, hrf₂⟩
  have hlow : ∀ k, scratchWords ≤ k → k < bufA → s₂.mem (wd b k) = s₁.mem (wd b k) :=
    fun k h1 h2 ↦ hfr₂.get h1 (by rw [ctxWords_val]; rw [bufA_val] at h2; omega)
      (by simp only [bufA_val, bufL_val] at h2 ⊢; omega)
  refine WP.then (layers_spec (inp := inp) (b := b)
    (fun i hi ↦ by
      rw [hlow _ (by rw [scratchWords_val, inputW_val]; omega)
        (by rw [inputW_val, bufA_val]; omega), hin₁ i hi])
    hA0 hA1 hA3 hL0 hL1 hL3
    ⟨by omega, by simp [h15], by simp [h14], by simp [h13], by simp [h12, afterLayers],
      fun h ↦ absurd rfl h, hrdi₂, MemFrame.refl hfr₂.1, rf_refl _ _⟩) ?_
  rintro s₃ ⟨-, -, -, -, h12₃, hroot, hrdi₃, hfr₃, hrf₃⟩
  have hlow₃ : ∀ k, scratchWords ≤ k → k < bufA → s₃.mem (wd b k) = s₁.mem (wd b k) :=
    fun k h1 h2 ↦ by rw [WorkW.get hfr₃ h1 (Or.inl h2), hlow k h1 h2]
  have hr0 := hin₁ 0 (by omega)
  have hr1 := hin₁ 1 (by omega)
  refine WP.then (final_spec (inp := inp) hrdi₃ h12₃ (hroot (by omega)).1 (hroot (by omega)).2
    (by rw [rootW, hlow₃ _ (by rw [scratchWords_val, inputW_val]; omega)
      (by rw [inputW_val, bufA_val]; omega)]; simpa using hr0)
    (by rw [rootW, hlow₃ _ (by rw [scratchWords_val, inputW_val]; omega)
      (by rw [inputW_val, bufA_val]; omega)]; exact hr1)) ?_
  rintro s₄ ⟨hrax, hmem₄, hrf₄⟩
  have hsv : ∀ k, 88 ≤ k → k < 94 → s₄.mem (wd b k) = s₁.mem (wd b k) := fun k h1 h2 ↦ by
    rw [hmem₄, hlow₃ k (by rw [scratchWords_val]; omega) (by rw [bufA_val]; omega)]
  refine WP.mono (restore_spec (sv := s.reg) (by rw [hrf₄ .rdi (by simp), hrdi₃])
    (by rw [hsv 88 (by omega) (by omega), h88]) (by rw [hsv 89 (by omega) (by omega), h89])
    (by rw [hsv 90 (by omega) (by omega), h90]) (by rw [hsv 91 (by omega) (by omega), h91])
    (by rw [hsv 92 (by omega) (by omega), h92]) (by rw [hsv 93 (by omega) (by omega), h93]))
    (fun s₅ ⟨h5, hcs⟩ ↦ ⟨by rw [h5, hrax], hcs⟩) fun _ h ↦ h

end X86.XmssVerifier
