/-
  LeanVM.Guest.B1.Tables.VtC.ZLoop10

  `verify_tables_loop0`, completely: every iteration's facts give its relation from `1` below `g^n`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Rounds
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.B1.Common.Vc
import LeanVM.Guest.B1.Common.Find

/-!
# `verify_tables_loop0`, completely

`l10_complete`: when every iteration `j < n` has its facts (`L10B`: the round on the record
`rounds·g^(7j)` with the tables `tabs`, the next record's cursor and claim, the challenge in `rk`, the running product
in `cprod`), `verify_tables_loop0` holds from `1` below `g^n`. An iteration's body, its round
inlined, holds at any depth reaching the next iteration (`l10_body`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **An iteration of `verify_tables_loop0`**, at a depth reaching the next iteration. -/
theorem l10_body {rd : Reader} {N rounds tabs rkb cprod x : E} (e : ℕ)
    {cur claim ncur nclaim rk cp : E}
    (l5 : LoadHolds rd (rounds * x ^ 7) 5 cur) (l6 : LoadHolds rd (rounds * x ^ 7) 6 claim)
    (hm : MeaningSumcheckRound4 rd [rounds * x ^ 7, cur, claim, tabs] [ncur, nclaim, rk])
    (l12 : LoadHolds rd (rounds * x ^ 7) 12 ncur) (l13 : LoadHolds rd (rounds * x ^ 7) 13 nclaim)
    (lrk : LoadHolds rd (rkb * x) 0 rk)
    (lc0 : LoadHolds rd (cprod * x) 0 cp) (lc1 : LoadHolds rd (cprod * x) 1 (cp * rk))
    (hK : IsInK (x * gen + N)) (hnext : x * gen + N ≠ 0 →
      coreProgram.relN rd e name% «verify_tables_loop0» (x * gen :: [N, rounds, tabs, rkb, cprod]) []) :
    coreProgram.relN rd (e + 1) name% «verify_tables_loop0» (x :: [N, rounds, tabs, rkb, cprod]) [] := by
  simp only [MeaningSumcheckRound4, exists_and_left, exists_capAt] at hm
  simp only [capAt5, ReadsAt, round4_sponge, Fs.squeeze, capOf, perm_eq_cells, pendCells,
    List.flatMap_cons, List.flatMap_nil, List.replicate, scalarCells_eq, word_dsObserve,
    Keccak.challengeOf_cells, loadHolds_mul_gen_pow, List.length_cons, List.length_nil,
    Nat.forall_lt_succ_left', Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
    List.getElem_cons_zero, List.getElem_cons_succ, and_true, Nat.zero_add, Nat.mul_one,
    Nat.add_zero, List.cons_append, List.nil_append, exists_and_left, and_assoc,
    ← round4_eval, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLeDiff,
    List.cons.injEq] at hm
  obtain ⟨a0, m0, a1, m1, a2, m2, a3, m3, a4, m4, c0, r0, c2, r2, c3, r3, n7, n8, n9, n10, n11,
    rfl, rfl, rfl⟩ := hm
  rw [B1.relN_succ_iff_fnSem (coreProgram_find?_at (j := idx% «verify_tables_loop0») rfl)]
  vc [B1.word_gen, keccakF_cells, word_zero, word_one, word_eight]
  simp only [show x * x * x * (x * x * x) * x = x ^ 7 by ring]
  exact ⟨cur, l5, claim, l6, a0, m0, a1, m1, a2, m2, a3, m3, a4, m4, c0, r0, c2, r2, c3, r3, n7, n8,
    n9, n10, n11, lrk, l12, l13, cp, lc0, lc1, hK, hnext, trivial⟩

/-- One depth bounds finitely many depth-monotone facts. -/
theorem l10_depth {P : ℕ → ℕ → Prop} (hmono : ∀ j a b, a ≤ b → P j a → P j b) :
    ∀ n, (∀ j < n, ∃ d, P j d) → ∃ D, ∀ j < n, P j D
  | 0, _ => ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, h => by
    obtain ⟨D, hD⟩ := l10_depth hmono n fun j hj => h j (by omega)
    obtain ⟨d, hd⟩ := h n (by omega)
    refine ⟨max D d, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j n with hj' | hj'
    · exact hmono j D _ (le_max_left _ _) (hD j hj')
    · rw [show j = n by omega]; exact hmono n d _ (le_max_right _ _) hd

/-- **`verify_tables_loop0`, completely**: every iteration's facts give the loop from `1` below
`g^n`. -/
theorem l10_complete {rd : Reader} {rounds tabs rkb cprod : E} {n : ℕ} (hn0 : 0 < n)
    (hB : ∀ j < n, L10B rd rounds tabs rkb cprod (gen ^ j)) :
    coreProgram.Rel rd name% «verify_tables_loop0» [1, gen ^ n, rounds, tabs, rkb, cprod] [] := by
  have hK : ∀ j, IsInK (gen ^ j * gen + gen ^ n) := fun j =>
    isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have key : ∀ t k, k + 1 + t = n → coreProgram.relN rd (t + 1) name% «verify_tables_loop0»
      (gen ^ k :: [gen ^ n, rounds, tabs, rkb, cprod]) [] := by
    intro t
    induction t with
    | zero =>
      intro k hk
      obtain ⟨c1, c2, c3, c4, c5, l5, l6, hm, l12, l13, lrk, cp, lc0, lc1⟩ := hB k (by omega)
      refine l10_body 0 l5 l6 hm l12 l13 lrk lc0 lc1 (hK k) fun h0 => ?_
      exact absurd ((gen_pow_add_eq_zero_iff k).mpr (by rw [show k + 1 = n by omega])) h0
    | succ t ih =>
      intro k hk
      obtain ⟨c1, c2, c3, c4, c5, l5, l6, hm, l12, l13, lrk, cp, lc0, lc1⟩ := hB k (by omega)
      refine l10_body (t + 1) l5 l6 hm l12 l13 lrk lc0 lc1 (hK k) fun _ => ?_
      rw [gen_pow_mul_gen]
      exact ih (k + 1) (by omega)
  have := key (n - 1) 0 (by omega)
  rw [pow_zero] at this
  exact ⟨_, this⟩

end
end LeanVM.Guest.B1.Tables
