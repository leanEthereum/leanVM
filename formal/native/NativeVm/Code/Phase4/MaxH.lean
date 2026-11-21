module

public import NativeVm.Code.Phase4.Frames

/-!
# The rounds' count

`maxC_spec`: the tallest table's log-height (`heights.foldl max 0`, the table sumcheck's rounds)
into `r14` and `oNR`, the working area's address into `rbp`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {s : QState} {E : QState → Prop}

/-- A load through an index register counting words. -/
theorem wp_ldX {d base ix : Reg64} {w : UInt64} {j i k : Nat} {v : UInt64} {xs : List Stmt}
    {P : QState → Prop} (hb : s.reg base = wd w j) (hi : s.reg ix = i.toUInt64)
    (hv : s.mem (wd w (j + i + k)) = some v) (h : WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d (wx base ix k)) :: xs)) s P E :=
  wp_load (eval_idx64 hb hi k) hv h

theorem cond_ltu_nat {s : QState} {a b : Reg64} {m n : Nat} (ha : s.reg a = m.toUInt64)
    (hb : s.reg b = n.toUInt64) (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) :
    (Cond.cmp .ltu a (.reg b)).eval s = decide (m < n) := by
  rw [cond_ltu, rhs_reg, ha, hb, decide_eq_decide]
  exact toUInt64_lt hm hn

theorem cond_ltu_imm {s : QState} {a : Reg64} {m n : Nat} {k : Int64} (ha : s.reg a = m.toUInt64)
    (hk : k.toUInt64 = n.toUInt64) (hm : m < 2 ^ 64) (hn : n < 2 ^ 64) :
    (Cond.cmp .ltu a (.imm k)).eval s = decide (m < n) := by
  rw [cond_ltu, rhs_imm, ha, hk, decide_eq_decide]
  exact toUInt64_lt hm hn

/-- The running maximum of the first `i` heights. -/
def pmax (heights : Array Nat) (i : Nat) : Nat := (heights.toList.take i).foldl max 0

theorem pmax_succ (heights : Array Nat) {i : Nat} (hi : i < heights.size) :
    pmax heights (i + 1) = max (pmax heights i) (heights.getD i 0) := by
  unfold pmax
  rw [List.take_add_one, List.foldl_append, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    List.getElem?_eq_getElem (by simpa using hi)]
  rfl

theorem pmax_le (heights : Array Nat) (hb : ∀ i < heights.size, heights.getD i 0 ≤ 30) :
    ∀ i, pmax heights i ≤ 30
  | 0 => by simp [pmax]
  | i + 1 => by
    rcases Nat.lt_or_ge i heights.size with h | h
    · rw [pmax_succ heights h]; exact max_le (pmax_le heights hb i) (hb i h)
    · unfold pmax
      rw [List.take_of_length_le (by simp; omega)]
      have := pmax_le heights hb heights.size
      unfold pmax at this
      rwa [List.take_of_length_le (by simp)] at this

theorem pmax_size (heights : Array Nat) : pmax heights heights.size = heights.foldl max 0 := by
  unfold pmax
  rw [List.take_of_length_le (by simp)]
  exact Array.foldl_toList ..

/-- **The rounds' count.** -/
theorem maxC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    (heights : Array Nat) (hh : heights.size = 6)
    (hhw : ∀ i < 6, s.mem (wd env.work (oL + 4 + i)) = some (heights.getD i 0).toUInt64)
    (hhb : ∀ i < 6, heights.getD i 0 ≤ 30) :
    WP maxC s (fun s' ↦ s'.reg .rbp = wd env.work 0 ∧
      s'.reg .r14 = (heights.foldl max 0).toUInt64 ∧
      s'.mem (wd env.work oNR) = some (heights.foldl max 0).toUInt64 ∧
      Wr env.work (fun k ↦ k = oNR) s s' ∧ RegsFrame [.rax, .rcx, .rbp, .r14] s s') E := by
  have hb30 := pmax_le heights (by rw [hh]; exact hhb)
  unfold maxC
  wst; wst; wst
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ i ≤ 6, t.reg .rcx = i.toUInt64 ∧ t.reg .r14 = (pmax heights i).toUInt64 ∧
      t.reg .rbp = wd env.work 0 ∧ t.mem = s.mem ∧ RegsFrame [.rax, .rcx, .rbp, .r14] s t)
    (fun t ↦ 6 - (t.reg .rcx).toNat)
  · exact ⟨0, by omega, by rsimp; rfl, by rsimp; rfl, by rsimp, rfl, by rfw⟩
  · rintro t ⟨i, hi, hc, h14, hbp, hm, hf⟩ hcond
    rw [cond_ltu_imm hc (k := 6) (n := 6) rfl (by omega) (by omega)] at hcond
    have hi6 : i < 6 := by simpa using hcond
    refine wp_ldX (i := i) hbp hc (by rw [hm, show 0 + i + (oL + 4) = oL + 4 + i by omega]; exact hhw i hi6) ?_
    apply WP.blk_cons
    apply WP.ite
    rw [cond_ltu_nat (m := pmax heights i) (n := heights.getD i 0) (by rsimp; exact h14) (by rsimp)
      (by have := hb30 i; omega) (by have := hhb i hi6; omega)]
    have hs := pmax_succ heights (i := i) (by omega)
    by_cases hlt : pmax heights i < heights.getD i 0
    · simp only [hlt, decide_true, ↓reduceIte]
      apply WP.ins'
      simp only [QInstr.step]
      fstep
      fdone
      refine ⟨⟨i + 1, by omega, ?_, ?_, hbp, hm, by rfw⟩, ?_⟩
      · rw [hc, toUInt64_succ]
      · rw [hs, max_eq_right (by omega)]
      · rw [hc, toUInt64_succ, Transcript.toNat_toUInt64 (by omega),
          Transcript.toNat_toUInt64 (by omega)]
        omega
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      apply WP.skip
      refine wp_regGuard (by decide) ?_
      fstep
      fdone
      refine ⟨⟨i + 1, by omega, ?_, ?_, hbp, hm, by rfw⟩, ?_⟩
      · rw [hc, toUInt64_succ]
      · rw [hs, max_eq_left (by omega)]; exact h14
      · rw [hc, toUInt64_succ, Transcript.toNat_toUInt64 (by omega),
          Transcript.toNat_toUInt64 (by omega)]
        omega
  · rintro t ⟨i, hi, hc, h14, hbp, hm, hf⟩ hcond
    rw [cond_ltu_imm hc (k := 6) (n := 6) rfl (by omega) (by omega)] at hcond
    have hi6 : i = 6 := by simp at hcond; omega
    subst hi6
    rw [← hh, pmax_size] at h14
    refine wp_stA (k := oNR) hbp (by rw [hm]; exact hws _ (by decide) (by decide)) ?_
    refine wp_done_gen fun s' hs' ↦ ?_
    subst hs'
    simp only [Nat.zero_add]
    refine ⟨hbp, h14, ?_, ?_, by rfw⟩
    · rw [mem_setMem_self, h14]
    · intro a ha
      rw [QState.setMem_mem, ite_eq_right (ha _ rfl), hm]

end NativeVm.Code.P4
