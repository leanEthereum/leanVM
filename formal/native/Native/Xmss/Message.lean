module

public import Native.Xmss.Mem

/-!
# The message digest

`message_spec`: the buffer `bufA` gets `P`, the message address and the payload (the bottom layer:
the message and the randomizer; the top layer: the bottom root, already in place, and the
randomizer), its hash is the digest, whose low word goes to `rbp` and high word to `dhiW`, and its
last six digits into the checks.
-/

@[expose] public section

namespace Native.XmssVerifier

open Keccak

/-- The words the message digest writes. -/
def MsgW (k : Nat) : Prop := k = bufA + 2 ∨ (bufA + 4 ≤ k ∧ k < bufA + 10) ∨ k = dhiW

theorem message_spec {E : QState → Prop} {t : QState} {b : UInt64}
    (hrdi : t.reg .rdi = b) (hdom : Dom b t.mem) {P0 P1 : UInt64} {K : Nat}
    {sw m : Nat → UInt64} {r : W2} (hK : scratchWords ≤ K) (hK' : K + 150 ≤ bufA)
    (hr14 : t.reg .r14 = wd b K) (hsw : ∀ k < 150, t.mem (wd b (K + k)) = some (sw k))
    (hA0 : t.mem (wd b bufA) = some P0) (hA1 : t.mem (wd b (bufA + 1)) = some P1)
    (hA3 : t.mem (wd b (bufA + 3)) = some 0)
    (hm : t.reg .r15 = 0 → ∀ j < 4, t.mem (wd b (msgW + j)) = some (m j))
    (hr : t.reg .r15 ≠ 0 →
      t.mem (wd b (bufA + 4)) = some r.1 ∧ t.mem (wd b (bufA + 5)) = some r.2) :
    WP message t (fun t' ↦
      t'.reg .rbp = (msgDigestW (P0, P1) (t.reg .r15) (t.reg .r13)
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) (sw 0, sw 1)).1 ∧
      t'.mem (wd b dhiW) = some (msgDigestW (P0, P1) (t.reg .r15) (t.reg .r13)
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) (sw 0, sw 1)).2 ∧
      t'.reg .r12 = t.reg .r12 ||| ((msgDigestW (P0, P1) (t.reg .r15) (t.reg .r13)
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) (sw 0, sw 1)).2 >>> 52) ∧
      MemFrame b MsgW t t' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp, .r12] t t') E := by
  rw [scratchWords_val] at hK
  simp only [bufA_val, Nat.reduceAdd] at hK' hA0 hA1 hA3 hr
  have hsw' : ∀ k < 150, t.mem (wd b (K + k)) = some (sw k) := hsw
  unfold message
  simp only [tweakWord, List.cons_append, List.nil_append]
  rstep; rstep; rstep; rstep; rstep; rstep
  refine WP.store' (b := b) (k := 1154) (by rw [eval_ctx]; simp [hrdi, bufA_val])
    (by isSome_tac) ?_
  refine WP.then (Q := fun u ↦ WordsIn b u.mem 1152
      ([P0, P1, tweakW (t.reg .r15) (t.reg .r13) 12, 0] ++
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) ++ [sw 0, sw 1]) ∧
      u.reg .rbx = (8 * (if t.reg .r15 = 0 then 10 else 8)).toUInt64 ∧
      u.reg .rdi = b ∧ MemFrame b MsgW t u ∧ RegsFrame [.rax, .rbx, .rdx] t u) ?_ ?_
  · by_cases h0 : t.reg .r15 = 0
    · refine WP.ite_true (by simp [Cond.eval, Rhs.eval, h0, int64Lit_toUInt64]) ?_
      have hm' := hm h0
      unfold msgBottom
      refine WP.load' (b := b) (k := 132) (by rw [eval_ctx]; simp [hrdi, msgW, inputW_val])
        (by mem_simp; simpa [msgW, inputW_val] using hm' 0 (by omega)) ?_
      refine WP.store' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.load' (b := b) (k := 133) (by rw [eval_ctx]; simp [hrdi, msgW, inputW_val])
        (by mem_simp; simpa [msgW, inputW_val] using hm' 1 (by omega)) ?_
      refine WP.store' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.load' (b := b) (k := 134) (by rw [eval_ctx]; simp [hrdi, msgW, inputW_val])
        (by mem_simp; simpa [msgW, inputW_val] using hm' 2 (by omega)) ?_
      refine WP.store' (b := b) (k := 1158) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.load' (b := b) (k := 135) (by rw [eval_ctx]; simp [hrdi, msgW, inputW_val])
        (by mem_simp; simpa [msgW, inputW_val] using hm' 3 (by omega)) ?_
      refine WP.store' (b := b) (k := 1159) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.load' (b := b) (k := K) (eval_r14 (by simp [hr14])).1
        (by mem_simp [show ¬ K = 1159 by omega, show ¬ K = 1158 by omega,
          show ¬ K = 1157 by omega, show ¬ K = 1156 by omega, show ¬ K = 1154 by omega]
            simpa using hsw' 0 (by omega)) ?_
      refine WP.store' (b := b) (k := 1160) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.load' (b := b) (k := K + 1) (eval_r14 (by simp [hr14])).2
        (by mem_simp [show ¬ K + 1 = 1160 by omega, show ¬ K + 1 = 1159 by omega,
          show ¬ K + 1 = 1158 by omega, show ¬ K + 1 = 1157 by omega,
          show ¬ K + 1 = 1156 by omega, show ¬ K + 1 = 1154 by omega]
            exact hsw' 1 (by omega)) ?_
      refine WP.store' (b := b) (k := 1161) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      rstep
      refine WP.blk_nil ⟨?_, by simp [h0], by simp [hrdi], ?_, ?_⟩
      · simp only [h0, ↓reduceIte, List.cons_append, List.nil_append, wordsIn_cons]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wordsIn_nil _ _ _⟩ <;>
          mem_simp [hA0, hA1, hA3, h0, tweakW]
      · frame_tac
        · exact MemFrame.refl hdom
        all_goals first
          | simp [MsgW, bufA_val, dhiW_val]
          | (rw [ctxWords_val]; omega)
      · rf_tac
        exact rf_refl _ _
    · refine WP.ite_false (by simp [Cond.eval, Rhs.eval, h0, int64Lit_toUInt64]) ?_
      obtain ⟨hr4, hr5⟩ := hr h0
      unfold msgTop
      refine WP.load' (b := b) (k := K) (eval_r14 (by simp [hr14])).1
        (by mem_simp [show ¬ K = 1154 by omega]; simpa using hsw' 0 (by omega)) ?_
      refine WP.store' (b := b) (k := 1158) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.load' (b := b) (k := K + 1) (eval_r14 (by simp [hr14])).2
        (by mem_simp [show ¬ K + 1 = 1158 by omega, show ¬ K + 1 = 1154 by omega]
            exact hsw' 1 (by omega)) ?_
      refine WP.store' (b := b) (k := 1159) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      rstep
      refine WP.blk_nil ⟨?_, by simp [h0], by simp [hrdi], ?_, ?_⟩
      · simp only [h0, ↓reduceIte, List.cons_append, List.nil_append, wordsIn_cons]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wordsIn_nil _ _ _⟩ <;>
          mem_simp [hA0, hA1, hA3, hr4, hr5, h0, tweakW]
      · frame_tac
        · exact MemFrame.refl hdom
        all_goals first
          | simp [MsgW, bufA_val, dhiW_val]
          | (rw [ctxWords_val]; omega)
      · rf_tac
        exact rf_refl _ _
  rintro u ⟨hws, hrbx, hrdiu, hfr, hrf⟩
  have hdomu := hfr.1
  rstep
  refine WP.then (hash_call (b := b) (k0 := 1152) (by simp [hrdiu]) (by dom_tac) (by decide)
    (by split <;> simp [ctxWords_val]) (by simp [eval_ctx, hrdiu, bufA_val])
    (by split <;> simp [*]) hws) ?_
  rintro u₁ ⟨h0, h1, hfr₁, hrf₁⟩
  have hdom₁ := hfr₁.1
  have hrdi₁ : u₁.reg .rdi = b := by rw [hrf₁ .rdi (by simp)]; simp [hrdiu]
  refine WP.load' (b := b) (k := 0) (by rw [eval_ctx, hrdi₁]) h0 ?_
  refine WP.load' (b := b) (k := 1) (by rw [eval_ctx]; simp [hrdi₁]) (by simpa using h1) ?_
  refine WP.store' (b := b) (k := 1162) (by rw [eval_ctx]; simp [hrdi₁, dhiW_val])
    (by isSome_tac) ?_
  rstep; rstep
  have hr12 : u₁.reg .r12 = t.reg .r12 := by
    rw [hrf₁ .r12 (by simp)]
    simp only [QState.setReg_reg, reduceCtorEq, ite_false]
    exact hrf .r12 (by simp)
  refine WP.blk_nil ⟨by simp [msgDigestW], ?_, by simp [hr12, msgDigestW], ?_, ?_⟩
  · mem_simp
    simp [msgDigestW]
  · frame_tac
    · exact hfr.trans hfr₁.of_setReg fun k h ↦ h.elim id False.elim
    all_goals first
      | simp [MsgW, bufA_val, dhiW_val]
      | (rw [ctxWords_val]; omega)
  · rf_tac
    refine rf_trans (l := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp, .r12]) ?_ hrf₁ (by simp)
      (by simp)
    rf_tac
    exact rf_mono hrf (by simp)

end Native.XmssVerifier
