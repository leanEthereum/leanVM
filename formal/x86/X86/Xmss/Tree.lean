module

public import X86.Xmss.Mem

/-!
# The leaf and the path

`leaf_spec`: the leaf is the hash of the buffer `bufL` (`P`, the leaf address, `0`, the chain
ends). `node_spec`: a node is the hash of `P`, the node address and the current node and its
sibling in the order of the key's bit. `fold_spec`: the 16 levels give the root.
-/

@[expose] public section

namespace X86.XmssVerifier

open Keccak

theorem leaf_spec {E : QState → Prop} {t : QState} {b : UInt64}
    (hrdi : t.reg .rdi = b) (hdom : Dom b t.mem) {P0 P1 : UInt64} {ends : Nat → W2}
    (hL0 : t.mem (wd b bufL) = some P0) (hL1 : t.mem (wd b (bufL + 1)) = some P1)
    (hL3 : t.mem (wd b (bufL + 3)) = some 0)
    (hends : ∀ c < 58, t.mem (wd b (bufL + 4 + 2 * c)) = some (ends c).1 ∧
      t.mem (wd b (bufL + 4 + 2 * c + 1)) = some (ends c).2) :
    WP leaf t (fun t' ↦
      t'.mem (wd b 0) = some (leafW (P0, P1) (t.reg .r15) (t.reg .r13) ends).1 ∧
      t'.mem (wd b 1) = some (leafW (P0, P1) (t.reg .r15) (t.reg .r13) ends).2 ∧
      MemFrame b (fun k ↦ k = bufL + 2) t t' ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8] t t') E := by
  simp only [bufL_val, Nat.reduceAdd] at hL0 hL1 hL3 hends
  unfold leaf
  simp only [tweakWord, List.cons_append, List.nil_append]
  rstep; rstep; rstep; rstep; rstep; rstep
  refine WP.store' (b := b) (k := 1170) (by rw [eval_ctx]; simp [hrdi, bufL_val])
    (by isSome_tac) ?_
  rstep; rstep
  refine WP.blk_cons (WP.mono (hash_call (b := b) (k0 := 1168)
    (ws := [P0, P1, tweakW (t.reg .r15) (t.reg .r13) 2, 0] ++ pairWords 58 ends)
    (by simp [hrdi]) (by dom_tac) (by decide)
    (by simp [ctxWords_val, pairWords_length]) (by simp [eval_ctx, hrdi, bufL_val])
    (by simp [pairWords_length]) ?_) ?_ fun _ h ↦ h)
  · rw [wordsIn_append]
    refine ⟨?_, wordsIn_pairWords fun c hc ↦ ?_⟩
    · simp only [wordsIn_cons]
      refine ⟨?_, ?_, ?_, ?_, wordsIn_nil _ _ _⟩ <;> mem_simp [hL0, hL1, hL3, tweakW]
    · simp only [List.length_cons, List.length_nil]
      mem_simp [show ¬ 1168 + 4 + 2 * c = 1170 by omega,
        show ¬ 1168 + 4 + 2 * c + 1 = 1170 by omega]
      exact hends c hc
  rintro t₁ ⟨h0, h1, hfr, hrf⟩
  refine WP.blk_nil ⟨h0, h1, ?_, ?_⟩
  · refine MemFrame.trans (W := fun k ↦ k = bufL + 2) (W' := fun _ ↦ False) ?_
      hfr.of_setReg.of_setReg fun k h ↦ ?_
    · frame_tac
      · exact MemFrame.refl hdom
      · simp [bufL_val]
      · decide
    · rcases h with h | h
      · exact h
      · exact h.elim
  · refine rf_trans (l := [.rax, .rbx, .rcx, .rdx, .rsi, .r8]) ?_ hrf (by simp) (by simp)
    rf_tac
    exact rf_refl _ _

/-- The words a node writes: the address and the payload. -/
def NodeW (k : Nat) : Prop := k = bufA + 2 ∨ (bufA + 4 ≤ k ∧ k < bufA + 8)

theorem node_spec {E : QState → Prop} {s : QState} {b : UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem) {P0 P1 : UInt64} {K j : Nat}
    {sw : Nat → UInt64} {cur : W2} (hj : j < 16)
    (hr11 : s.reg .r11 = j.toUInt64) (hr9 : s.reg .r9 = s.reg .r13 >>> j.toUInt64)
    (hr14 : s.reg .r14 = wd b K) (hsw : ∀ k < 150, s.mem (wd b (K + k)) = some (sw k))
    (hc0 : s.mem (wd b 0) = some cur.1) (hc1 : s.mem (wd b 1) = some cur.2)
    (hA0 : s.mem (wd b bufA) = some P0) (hA1 : s.mem (wd b (bufA + 1)) = some P1)
    (hA3 : s.mem (wd b (bufA + 3)) = some 0) :
    WP node s (fun s' ↦
      s'.mem (wd b 0) = some (nodeW (P0, P1) (s.reg .r15) (s.reg .r13)
        (fun j ↦ (sw (118 + 2 * j), sw (119 + 2 * j))) j cur).1 ∧
      s'.mem (wd b 1) = some (nodeW (P0, P1) (s.reg .r15) (s.reg .r13)
        (fun j ↦ (sw (118 + 2 * j), sw (119 + 2 * j))) j cur).2 ∧
      s'.reg .r11 = (j + 1).toUInt64 ∧ s'.reg .r9 = s.reg .r13 >>> (j + 1).toUInt64 ∧
      MemFrame b NodeW s s' ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11] s s') E := by
  simp only [bufA_val, Nat.reduceAdd] at hA0 hA1 hA3
  unfold node
  rstep [hr11]; rstep [toUInt64_shl4 (by omega : j < 2 ^ 59)]
  refine WP.load' (b := b) (k := K + 2 * j + 118) (eval_sigAt (by simp [hr14]) (by simp) 118)
    (by
      rw [show K + 2 * j + 118 = K + (118 + 2 * j) by omega]
      simpa using hsw _ (by omega)) ?_
  refine WP.load' (b := b) (k := K + 2 * j + 119) (eval_sigAt (by simp [hr14]) (by simp) 119)
    (by
      rw [show K + 2 * j + 119 = K + (119 + 2 * j) by omega]
      simpa using hsw _ (by omega)) ?_
  refine WP.load' (b := b) (k := 0) (by rw [eval_ctx]; simp [hrdi]) (by simpa using hc0) ?_
  refine WP.load' (b := b) (k := 1) (by rw [eval_ctx]; simp [hrdi]) (by simpa using hc1) ?_
  refine WP.then (Q := fun u ↦ WordsIn b u.mem 1156
      (if s.reg .r13 >>> j.toUInt64 &&& 1 = 0
        then [cur.1, cur.2, sw (118 + 2 * j), sw (119 + 2 * j)]
        else [sw (118 + 2 * j), sw (119 + 2 * j), cur.1, cur.2]) ∧
      MemFrame b NodeW s u ∧ RegsFrame [.rax, .rcx, .rdx, .r8] s u) ?_ ?_
  · by_cases hbit : s.reg .r13 >>> j.toUInt64 &&& 1 = 0
    · refine WP.ite_true (by simp [Cond.eval, Rhs.eval, hr9, hbit, int64Lit_toUInt64]) ?_
      refine WP.store' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.store' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.store' (b := b) (k := 1158) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.store' (b := b) (k := 1159) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.blk_nil ⟨?_, ?_, ?_⟩
      · simp only [hbit, ↓reduceIte, wordsIn_cons]
        refine ⟨?_, ?_, ?_, ?_, wordsIn_nil _ _ _⟩ <;> mem_simp
      · frame_tac
        · exact MemFrame.refl hdom
        all_goals first
          | simp [NodeW, bufA_val]
          | decide
      · rf_tac
        exact rf_refl _ _
    · refine WP.ite_false (by simp [Cond.eval, Rhs.eval, hr9, hbit, int64Lit_toUInt64]) ?_
      refine WP.store' (b := b) (k := 1156) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.store' (b := b) (k := 1157) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.store' (b := b) (k := 1158) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.store' (b := b) (k := 1159) (by rw [eval_ctx]; simp [hrdi, bufA_val])
        (by isSome_tac) ?_
      refine WP.blk_nil ⟨?_, ?_, ?_⟩
      · simp only [hbit, ↓reduceIte, wordsIn_cons]
        refine ⟨?_, ?_, ?_, ?_, wordsIn_nil _ _ _⟩ <;> mem_simp
      · frame_tac
        · exact MemFrame.refl hdom
        all_goals first
          | simp [NodeW, bufA_val]
          | decide
      · rf_tac
        exact rf_refl _ _
  rintro u ⟨hpl, hfr, hrf⟩
  have hdomu := hfr.1
  have hrdiu : u.reg .rdi = b := (hrf .rdi (by simp)).trans hrdi
  have hr9u : u.reg .r9 = s.reg .r13 >>> j.toUInt64 := (hrf .r9 (by simp)).trans hr9
  have hr11u : u.reg .r11 = j.toUInt64 := (hrf .r11 (by simp)).trans hr11
  have hr15u : u.reg .r15 = s.reg .r15 := hrf .r15 (by simp)
  have hA0u : u.mem (wd b 1152) = some P0 := by
    rw [hfr.get (by decide) (by decide) (by simp [NodeW, bufA_val]), hA0]
  have hA1u : u.mem (wd b 1153) = some P1 := by
    rw [hfr.get (by decide) (by decide) (by simp [NodeW, bufA_val]), hA1]
  have hA3u : u.mem (wd b 1155) = some 0 := by
    rw [hfr.get (by decide) (by decide) (by simp [NodeW, bufA_val]), hA3]
  rstep [hr9u]; rstep [hr11u]; rstep [hr15u]; rstep; rstep; rstep; rstep; rstep; rstep; rstep
  refine WP.store' (b := b) (k := 1154) (by rw [eval_ctx]; simp [hrdiu, bufA_val])
    (by isSome_tac) ?_
  rstep; rstep
  refine WP.blk_cons (WP.mono (hash_call (b := b) (k0 := 1152)
    (ws := [P0, P1, nodeTweakW (s.reg .r15) (j + 1).toUInt64 (s.reg .r13 >>> j.toUInt64 >>> 1),
      0] ++
      (if s.reg .r13 >>> j.toUInt64 &&& 1 = 0
        then [cur.1, cur.2, sw (118 + 2 * j), sw (119 + 2 * j)]
        else [sw (118 + 2 * j), sw (119 + 2 * j), cur.1, cur.2]))
    (by simp [hrdiu]) (by dom_tac) (by decide)
    (by split <;> simp [ctxWords_val]) (by simp [eval_ctx, hrdiu, bufA_val])
    (by split <;> simp) ?_) ?_ fun _ h ↦ h)
  · rw [wordsIn_append]
    refine ⟨?_, ?_⟩
    · simp only [wordsIn_cons]
      refine ⟨?_, ?_, ?_, ?_, wordsIn_nil _ _ _⟩ <;>
        mem_simp [hA0u, hA1u, hA3u, nodeTweakW, toUInt64_add_one]
    · simp only [List.length_cons, List.length_nil]
      split
      all_goals
        rename_i hb
        simp only [hb, ↓reduceIte, wordsIn_cons] at hpl ⊢
        obtain ⟨h0, h1, h2, h3, -⟩ := hpl
        exact ⟨by mem_simp [h0], by mem_simp [h1], by mem_simp [h2], by mem_simp [h3],
          wordsIn_nil _ _ _⟩
  rintro u₁ ⟨h0, h1, hfr₁, hrf₁⟩
  refine WP.blk_nil ⟨h0, h1, ?_, ?_, ?_, ?_⟩
  · rw [hrf₁ .r11 (by simp)]
    simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false, ite_true, hr11u]
    exact toUInt64_add_one j
  · rw [hrf₁ .r9 (by simp)]
    simp only [QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false, ite_true, hr9u]
    rw [natOne_toUInt64.symm, shiftRight_toUInt64_add _ (by omega)]
  · refine MemFrame.trans (W := NodeW) (W' := fun _ ↦ False) ?_ hfr₁.of_setReg.of_setReg
      fun k h ↦ h.elim id False.elim
    frame_tac
    · exact hfr
    · simp [NodeW, bufA_val]
    · decide
  · refine rf_trans (l := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11]) ?_ hrf₁ (by simp)
      (by simp)
    rf_tac
    exact rf_mono hrf (by simp)

theorem fold_spec {E : QState → Prop} {s : QState} {b : UInt64}
    (hrdi : s.reg .rdi = b) (hdom : Dom b s.mem) {P0 P1 : UInt64} {K : Nat}
    {sw : Nat → UInt64} {leaf : W2} (hK : scratchWords ≤ K) (hK' : K + 150 ≤ bufA)
    (hr14 : s.reg .r14 = wd b K) (hsw : ∀ k < 150, s.mem (wd b (K + k)) = some (sw k))
    (hc0 : s.mem (wd b 0) = some leaf.1) (hc1 : s.mem (wd b 1) = some leaf.2)
    (hA0 : s.mem (wd b bufA) = some P0) (hA1 : s.mem (wd b (bufA + 1)) = some P1)
    (hA3 : s.mem (wd b (bufA + 3)) = some 0) :
    WP fold s (fun s' ↦
      s'.mem (wd b 0) = some (foldW (P0, P1) (s.reg .r15) (s.reg .r13)
        (fun j ↦ (sw (118 + 2 * j), sw (119 + 2 * j))) 16 leaf).1 ∧
      s'.mem (wd b 1) = some (foldW (P0, P1) (s.reg .r15) (s.reg .r13)
        (fun j ↦ (sw (118 + 2 * j), sw (119 + 2 * j))) 16 leaf).2 ∧
      MemFrame b NodeW s s' ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11] s s') E := by
  have hK0 := hK
  have hK1 := hK'
  rw [scratchWords_val] at hK0
  rw [bufA_val] at hK1
  have hget : ∀ {u : QState}, MemFrame b NodeW s u → ∀ k, scratchWords ≤ k → k < bufA →
      u.mem (wd b k) = s.mem (wd b k) := fun hu k h1 h2 ↦ hu.get h1
    (by rw [ctxWords_val]; rw [bufA_val] at h2; omega)
    (by simp only [NodeW, bufA_val] at h2 ⊢; omega)
  have hfixA : ∀ {u : QState}, MemFrame b NodeW s u → ∀ k, k = bufA ∨ k = bufA + 1 ∨
      k = bufA + 3 → u.mem (wd b k) = s.mem (wd b k) := fun hu k hk ↦ hu.get
    (by rw [scratchWords_val]; simp only [bufA_val] at hk; omega)
    (by rw [ctxWords_val]; simp only [bufA_val] at hk; omega)
    (by simp only [NodeW, bufA_val] at hk ⊢; omega)
  unfold fold
  rstep; rstep
  refine WP.loop (fun u ↦ ∃ j ≤ 16, u.reg .r11 = j.toUInt64 ∧
      u.reg .r9 = s.reg .r13 >>> j.toUInt64 ∧
      u.mem (wd b 0) = some (foldW (P0, P1) (s.reg .r15) (s.reg .r13)
        (fun j ↦ (sw (118 + 2 * j), sw (119 + 2 * j))) j leaf).1 ∧
      u.mem (wd b 1) = some (foldW (P0, P1) (s.reg .r15) (s.reg .r13)
        (fun j ↦ (sw (118 + 2 * j), sw (119 + 2 * j))) j leaf).2 ∧
      MemFrame b NodeW s u ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r11] s u)
    (fun u ↦ 16 - (u.reg .r11).toNat)
    ⟨0, by omega, by simp, by simp, by simpa [foldW] using hc0,
      by simpa [foldW] using hc1, ⟨by dom_tac, fun _ _ _ _ ↦ rfl⟩,
      by rf_tac; exact rf_refl _ _⟩ ?_ ?_
  · rintro u ⟨j, hj, hr11, hr9, h0, h1, hfr, hrf⟩ hc
    simp only [Cond.eval, Rhs.eval, hr11, int64Lit_toUInt64, decide_eq_true_eq] at hc
    have hj' : j < 16 := (toUInt64_lt_iff (n := 16) (by omega) (by omega)).mp hc
    have h13 : u.reg .r13 = s.reg .r13 := hrf .r13 (by simp)
    have h15 : u.reg .r15 = s.reg .r15 := hrf .r15 (by simp)
    refine WP.mono (node_spec (b := b) (by rw [hrf .rdi (by simp), hrdi]) hfr.1 (P0 := P0) (P1 := P1)
      (sw := sw) hj' hr11 (by rw [hr9, h13]) (by rw [hrf .r14 (by simp), hr14])
      (fun k hk ↦ by rw [hget hfr _ (by rw [scratchWords_val]; omega)
        (by rw [bufA_val]; omega), hsw k hk]) h0 h1
      (by rw [hfixA hfr _ (by omega), hA0]) (by rw [hfixA hfr _ (by omega), hA1])
      (by rw [hfixA hfr _ (by omega), hA3])) ?_ fun _ h ↦ h
    rintro u' ⟨h0', h1', h11, h9, hfr', hrf'⟩
    rw [h13, h15] at h0' h1'
    rw [h13] at h9
    refine ⟨⟨j + 1, by omega, h11, h9, by rw [h0']; rfl, by rw [h1']; rfl,
      hfr.trans hfr' fun k h ↦ h.elim id id, rf_trans hrf hrf' (by simp) (by simp)⟩, ?_⟩
    rw [h11, hr11, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
    omega
  · rintro u ⟨j, hj, hr11, -, h0, h1, hfr, hrf⟩ hc
    simp only [Cond.eval, Rhs.eval, hr11, int64Lit_toUInt64, decide_eq_false_iff_not] at hc
    have hj' : j = 16 := by
      have := (toUInt64_lt_iff (t := j) (n := 16) (by omega) (by omega)).not.mp hc
      omega
    subst hj'
    exact ⟨h0, h1, hfr, hrf⟩

end X86.XmssVerifier
