/-
  LeanVM.Guest.B1.VerifySub.Inv5

  The deployed stack bound bounds the bus's depth and the tables' log-heights.
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv4
public import LeanVM.Guest.B1.Tables.Kappas

/-!
# The stack's bound and the layout

`stackTotal_expand`, `pushTotal_expand`: the stack's and the push side's totals over the memory's
log-size and the tables' log-heights. Every table pushes fewer blocks than it commits columns, so
the push side's total is at most the stack's plus one (`pushTotal_le_stack`): a stack of at most
`2^28` words bounds the GKR depth below 33 and every table's log-height below 29.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem stackTotal_expand (m h0 h1 h2 h3 h4 h5 : ℕ) :
    stackTotal (columnKappas m 18 [h0, h1, h2, h3, h4, h5]) =
      4 * 2 ^ m + 2 ^ 18 + 2 ^ (h5 + 8) + 15 * 2 ^ h0 + 15 * 2 ^ h1 + 8 * 2 ^ h2 +
        15 * 2 ^ h3 + 14 * 2 ^ h4 + 19 * 2 ^ h5 := by
  rw [stackTotal_eq, committedKappas, columnKappas_length_110, blockCols_110, columnKappas_eq]
  simp only [List.replicate, List.cons_append, List.nil_append, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, List.sum_cons,
    List.sum_nil]
  ring

theorem pushTotal_expand (m h0 h1 h2 h3 h4 h5 : ℕ) :
    ((pushKappas m [h0, h1, h2, h3, h4, h5]).map (2 ^ ·)).sum =
      1 + 2 ^ m + 2 ^ 18 + 5 * 2 ^ h0 + 5 * 2 ^ h1 + 3 * 2 ^ h2 + 5 * 2 ^ h3 + 5 * 2 ^ h4 +
        11 * 2 ^ h5 := by
  simp only [pushKappas, List.zip_cons_cons, List.zip_nil_left, List.flatMap_cons,
    List.flatMap_nil, List.replicate, List.cons_append, List.nil_append, List.append_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem list6 {α : Type} {l : List α} (h : l.length = 6) :
    ∃ a0 a1 a2 a3 a4 a5, l = [a0, a1, a2, a3, a4, a5] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, l⟩⟩⟩⟩⟩⟩ <;> simp at h
  subst h
  exact ⟨_, _, _, _, _, _, rfl⟩

/-- **The stack's bound bounds the layout**: a stack of log-size at most 28 has a push side of
depth below 33, and tables of log-height below 29. -/
theorem layout_bounds {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {m : ℕ} {rows : List ℕ}
    (hl : rows.length = 6) (hs : (layoutOf bytecode m rows).stackLog ≤ 28) :
    pushDepth (layoutOf bytecode m rows) < 33 ∧ ∀ n ∈ rows, log2Ceil n < 29 := by
  rw [stackLog_eq hb] at hs
  have hst := le_trans (le_two_pow_log2Ceil _) (Nat.pow_le_pow_right (by decide)
    (le_trans (le_max_right _ _) hs))
  clear hs
  obtain ⟨r0, r1, r2, r3, r4, r5, rfl⟩ := list6 hl
  simp only [List.map_cons, List.map_nil] at hst
  rw [stackTotal_expand] at hst
  have hb8 := Nat.zero_le (2 ^ (log2Ceil r5 + 8))
  refine ⟨?_, ?_⟩
  · rw [pushDepth_eq hb _ _ hl]
    simp only [List.map_cons, List.map_nil]
    rw [pushTotal_expand]
    have : log2Ceil (1 + 2 ^ m + 2 ^ 18 + 5 * 2 ^ log2Ceil r0 + 5 * 2 ^ log2Ceil r1 +
        3 * 2 ^ log2Ceil r2 + 5 * 2 ^ log2Ceil r3 + 5 * 2 ^ log2Ceil r4 + 11 * 2 ^ log2Ceil r5) ≤ 29 :=
      log2Ceil_le_iff.mpr (by
        have : (2 : ℕ) ^ 29 = 2 * 2 ^ 28 := by norm_num
        omega)
    omega
  · have hk : ∀ k, 2 ^ k ≤ 2 ^ 28 → k < 29 := fun k hk => by
      have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hk
      omega
    intro n hn
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hk _ (by omega)

/-- **`q_flock`'s log-size below the stack's**: a stack of log-size at most 28 holds `q_flock`'s
column of `2^(τ + 8)` words. -/
theorem qflock_bound {bytecode : List K} (hb : bytecode.length = 2 ^ 22) {m : ℕ} {rows : List ℕ}
    (hl : rows.length = 6) (hs : (layoutOf bytecode m rows).stackLog ≤ 28) :
    (rows.map log2Ceil).getD 5 0 + 8 ≤ 28 := by
  rw [stackLog_eq hb] at hs
  have hst := le_trans (le_two_pow_log2Ceil _) (Nat.pow_le_pow_right (by decide)
    (le_trans (le_max_right _ _) hs))
  clear hs
  obtain ⟨r0, r1, r2, r3, r4, r5, rfl⟩ := list6 hl
  simp only [List.map_cons, List.map_nil] at hst ⊢
  rw [stackTotal_expand] at hst
  have h := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2 ^ (log2Ceil r5 + 8) ≤ 2 ^ 28 by omega)
  simpa using h

end
end LeanVM.Guest.B1.VerifySub
