module

public import X86.Xmss.Message
public import X86.Xmss.Chain
public import X86.Xmss.Tree

/-!
# One layer

`layer_spec`: from the layer's registers (`r15` the layer, `r14` its signature, `r13` its key),
`layer` leaves the root the layer's signature reaches in the buffer's payload, adds the codeword
checks of its digest to `r12`, and moves the registers to the next layer.
-/

@[expose] public section

namespace X86.XmssVerifier

open Keccak

/-- The working words a layer writes: every word of the two buffers but `P` and the zero word. -/
def WorkW (k : Nat) : Prop :=
  k = bufA + 2 ∨ (bufA + 4 ≤ k ∧ k ≤ dhiW) ∨ k = bufL + 2 ∨ (bufL + 4 ≤ k ∧ k < bufL + 120)

theorem WorkW.get {b : UInt64} {u u' : QState} (h : MemFrame b WorkW u u') {k : Nat}
    (hk : scratchWords ≤ k) (hk' : k < bufA ∨ k = bufA ∨ k = bufA + 1 ∨ k = bufA + 3 ∨
      k = bufL ∨ k = bufL + 1 ∨ k = bufL + 3) :
    u'.mem (wd b k) = u.mem (wd b k) :=
  h.get hk (by simp only [ctxWords_val, bufA_val, bufL_val] at hk' ⊢; omega)
    (by simp only [WorkW, bufA_val, bufL_val, dhiW_val] at hk' ⊢; omega)

theorem layer_spec {E : QState → Prop} {t : QState} {b : UInt64}
    (hrdi : t.reg .rdi = b) (hdom : Dom b t.mem) {P0 P1 : UInt64} {K : Nat}
    {sw m : Nat → UInt64} {r : W2} (hK : scratchWords ≤ K) (hK' : K + 150 ≤ bufA)
    (hr14 : t.reg .r14 = wd b K) (hsw : ∀ k < 150, t.mem (wd b (K + k)) = some (sw k))
    (hA0 : t.mem (wd b bufA) = some P0) (hA1 : t.mem (wd b (bufA + 1)) = some P1)
    (hA3 : t.mem (wd b (bufA + 3)) = some 0)
    (hL0 : t.mem (wd b bufL) = some P0) (hL1 : t.mem (wd b (bufL + 1)) = some P1)
    (hL3 : t.mem (wd b (bufL + 3)) = some 0)
    (hm : t.reg .r15 = 0 → ∀ j < 4, t.mem (wd b (msgW + j)) = some (m j))
    (hr : t.reg .r15 ≠ 0 →
      t.mem (wd b (bufA + 4)) = some r.1 ∧ t.mem (wd b (bufA + 5)) = some r.2) :
    WP layer t (fun t' ↦
      t'.mem (wd b (bufA + 4)) = some (layerW (P0, P1) (t.reg .r15) (t.reg .r13)
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) sw).2.1 ∧
      t'.mem (wd b (bufA + 5)) = some (layerW (P0, P1) (t.reg .r15) (t.reg .r13)
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) sw).2.2 ∧
      (t'.reg .r12 = 0 ↔ t.reg .r12 = 0 ∧ (layerW (P0, P1) (t.reg .r15) (t.reg .r13)
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) sw).1 = true) ∧
      t'.reg .r15 = t.reg .r15 + 1 ∧ t'.reg .r14 = wd b (K + 150) ∧
      t'.reg .r13 = t.reg .r13 >>> 16 ∧ t'.reg .rdi = b ∧
      MemFrame b WorkW t t' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .rbp, .r12, .r13, .r14, .r15]
        t t') E := by
  have hK0 := hK
  have hK1 := hK'
  rw [scratchWords_val] at hK0
  rw [bufA_val] at hK1
  unfold layer
  refine WP.then (message_spec (b := b) hrdi hdom hK hK' hr14 hsw hA0 hA1 hA3 hm hr) ?_
  rintro t₁ ⟨hbp₁, hdhi₁, hr12₁, hfr₁, hrf₁⟩
  have hw₁ : MemFrame b WorkW t t₁ := hfr₁.mono fun k h ↦ by
    simp only [MsgW, WorkW, bufA_val, bufL_val, dhiW_val] at h ⊢
    omega
  have hreg₁ : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .rbp, .r12] → t₁.reg r = t.reg r :=
    hrf₁
  refine WP.then (chains_spec (b := b) (by rw [hreg₁ .rdi (by simp), hrdi]) hfr₁.1 (P0 := P0)
    (P1 := P1) (sw := sw) hK hK' hbp₁ hdhi₁ (by rw [hreg₁ .r14 (by simp), hr14])
    (fun k hk ↦ by
      rw [WorkW.get hw₁ (k := K + k) (by rw [scratchWords_val]; omega)
          (Or.inl (by rw [bufA_val]; omega)),
        hsw k hk])
    (by rw [WorkW.get hw₁ (k := bufA) (by decide) (by simp), hA0])
    (by rw [WorkW.get hw₁ (k := bufA + 1) (by decide) (by simp), hA1])
    (by rw [WorkW.get hw₁ (k := bufA + 3) (by decide) (by simp), hA3])) ?_
  rintro t₂ ⟨hends, hr12₂, hfr₂, hrf₂⟩
  have hw₂ : MemFrame b WorkW t t₂ := hw₁.trans hfr₂ fun k h ↦ by
    rcases h with h | h
    · exact h
    · simp only [ChainsW, StepW, WorkW, bufA_val, bufL_val, dhiW_val] at h ⊢
      omega
  have hreg₂ : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r10, .r11, .rbp, .r9, .r12] →
      t₂.reg r = t₁.reg r := hrf₂
  have h15₂ : t₂.reg .r15 = t.reg .r15 := by rw [hreg₂ .r15 (by simp), hreg₁ .r15 (by simp)]
  have h13₂ : t₂.reg .r13 = t.reg .r13 := by rw [hreg₂ .r13 (by simp), hreg₁ .r13 (by simp)]
  have h14₂ : t₂.reg .r14 = wd b K := by rw [hreg₂ .r14 (by simp), hreg₁ .r14 (by simp), hr14]
  have hrdi₂ : t₂.reg .rdi = b := by rw [hreg₂ .rdi (by simp), hreg₁ .rdi (by simp), hrdi]
  rw [hreg₁ .r15 (by simp), hreg₁ .r13 (by simp)] at hends
  refine WP.then (leaf_spec (b := b) hrdi₂ hfr₂.1
    (ends := fun c ↦ chainEndW (P0, P1) (t.reg .r15) (t.reg .r13)
      (msgDigestW (P0, P1) (t.reg .r15) (t.reg .r13)
        (if t.reg .r15 = 0 then [m 0, m 1, m 2, m 3] else [r.1, r.2]) (sw 0, sw 1)) c
      (sw (2 + 2 * c), sw (3 + 2 * c)))
    (by rw [WorkW.get hw₂ (k := bufL) (by decide) (by simp), hL0])
    (by rw [WorkW.get hw₂ (k := bufL + 1) (by decide) (by simp), hL1])
    (by rw [WorkW.get hw₂ (k := bufL + 3) (by decide) (by simp), hL3])
    (fun c hc ↦ ⟨(hends c hc).1, by
      rw [show bufL + 4 + 2 * c + 1 = bufL + 5 + 2 * c by omega]
      exact (hends c hc).2⟩)) ?_
  rintro t₃ ⟨hl0, hl1, hfr₃, hrf₃⟩
  have hw₃ : MemFrame b WorkW t t₃ := hw₂.trans hfr₃ fun k h ↦ by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h))
  have hreg₃ : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8] → t₃.reg r = t₂.reg r := hrf₃
  rw [h15₂, h13₂] at hl0 hl1
  refine WP.then (fold_spec (b := b) (by rw [hreg₃ .rdi (by simp), hrdi₂]) hfr₃.1 (P0 := P0)
    (P1 := P1) (sw := sw) hK hK' (by rw [hreg₃ .r14 (by simp), h14₂])
    (fun k hk ↦ by
      rw [WorkW.get hw₃ (k := K + k) (by rw [scratchWords_val]; omega)
        (Or.inl (by rw [bufA_val]; omega)), hsw k hk])
    hl0 hl1
    (by rw [WorkW.get hw₃ (k := bufA) (by decide) (by simp), hA0])
    (by rw [WorkW.get hw₃ (k := bufA + 1) (by decide) (by simp), hA1])
    (by rw [WorkW.get hw₃ (k := bufA + 3) (by decide) (by simp), hA3])) ?_
  rintro t₄ ⟨hf0, hf1, hfr₄, hrf₄⟩
  have hw₄ : MemFrame b WorkW t t₄ := hw₃.trans hfr₄ fun k h ↦ by
    rcases h with h | h
    · exact h
    · simp only [NodeW, WorkW, bufA_val, bufL_val, dhiW_val] at h ⊢
      omega
  have hreg₄ : ∀ r, r ∉ [Reg64.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11] →
      t₄.reg r = t₃.reg r := hrf₄
  have h15₄ : t₄.reg .r15 = t.reg .r15 := by rw [hreg₄ .r15 (by simp), hreg₃ .r15 (by simp), h15₂]
  have h13₄ : t₄.reg .r13 = t.reg .r13 := by rw [hreg₄ .r13 (by simp), hreg₃ .r13 (by simp), h13₂]
  have h14₄ : t₄.reg .r14 = wd b K := by rw [hreg₄ .r14 (by simp), hreg₃ .r14 (by simp), h14₂]
  have hrdi₄ : t₄.reg .rdi = b := by rw [hreg₄ .rdi (by simp), hreg₃ .rdi (by simp), hrdi₂]
  have h12₄ : t₄.reg .r12 = t₂.reg .r12 := by rw [hreg₄ .r12 (by simp), hreg₃ .r12 (by simp)]
  have hdom₄ := hfr₄.1
  rw [hreg₃ .r15 (by simp), hreg₃ .r13 (by simp), h15₂, h13₂] at hf0 hf1
  refine WP.load' (b := b) (k := 0) (by rw [eval_ctx, hrdi₄]) hf0 ?_
  refine WP.store' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdi₄, bufA_val])
    (by isSome_tac) ?_
  refine WP.load' (b := b) (k := 1) (by rw [eval_ctx]; simp [hrdi₄]) (by mem_simp; exact hf1) ?_
  refine WP.store' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdi₄, bufA_val])
    (by isSome_tac) ?_
  rstep [h13₄]; rstep [h14₄]; rstep [h15₄]
  refine WP.blk_nil ⟨by mem_simp; rfl, by mem_simp; rfl, ?_, by simp [h15₄], ?_, by simp [h13₄],
    by simp [hrdi₄], ?_, ?_⟩
  · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false, h12₄, hr12₂,
      hr12₁, UInt64.or_eq_zero_iff, UInt64.xor_eq_zero_iff, layerW, codewordW,
      Bool.and_eq_true, beq_iff_eq, and_assoc]
  · simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false, ite_true]
    rw [h14₄, wdisp_toUInt64, show sigStride = 150 from rfl, wd_add]
  · frame_tac
    · exact hw₄
    all_goals first
      | simp [WorkW, bufA_val, dhiW_val]
      | decide
  · rf_tac
    refine rf_trans (l := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .rbp, .r12, .r13,
      .r14, .r15]) ?_ hrf₄ (by simp) (by simp)
    refine rf_trans (l := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .rbp, .r12, .r13,
      .r14, .r15]) (l'' := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .rbp, .r12, .r13,
      .r14, .r15]) ?_ hrf₃ (by simp) (by simp)
    refine rf_trans (l := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .rbp, .r12, .r13,
      .r14, .r15]) (l'' := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .rbp, .r12, .r13,
      .r14, .r15]) ?_ hrf₂ (by simp) (by simp)
    exact rf_mono hrf₁ (by simp)

end X86.XmssVerifier
