/-
  LeanVM.Guest.B1.Tables.VtC.ZLoop10

  `verify_tables_loop0`, completely: every iteration's facts give its relation from `1` below `g^n`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Rounds
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_tables_loop0`, completely (G:2349-2362)

`l10_complete`: when every iteration `j < n` has its facts (`L10B`: the round on the record
`rounds·g^(7j)` with the tables `tabs`, the next record's cursor and claim, the challenge in `rk`, the running product
in `cprod`), `verify_tables_loop0` holds from `1` below `g^n`. `l11_complete`: `verify_tables_loop1`, given
`chi[x] = rk[n - 1 - x]`. An iteration's body holds on the
evident valuation at any depth reaching its `sumcheck_round4` call and the next iteration
(`l10_body`); one depth bounds every round's call (`l10_depth`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
/-- **An iteration of `verify_tables_loop0`**, at a depth reaching its round's call and the next
iteration. -/
theorem l10_body {rd : Reader} {N rounds tabs rkb cprod x : E} (e : ℕ)
    {cur claim ncur nclaim rk cp : E}
    (l5 : LoadHolds rd (rounds * x ^ 7) 5 cur) (l6 : LoadHolds rd (rounds * x ^ 7) 6 claim)
    (hc : coreProgram.relN rd e "sumcheck_round4" [rounds * x ^ 7, cur, claim, tabs]
      [ncur, nclaim, rk])
    (l12 : LoadHolds rd (rounds * x ^ 7) 12 ncur) (l13 : LoadHolds rd (rounds * x ^ 7) 13 nclaim)
    (lrk : LoadHolds rd (rkb * x) 0 rk)
    (lc0 : LoadHolds rd (cprod * x) 0 cp) (lc1 : LoadHolds rd (cprod * x) 1 (cp * rk))
    (hK : IsInK (x * gen + N)) (hnext : x * gen + N ≠ 0 →
      coreProgram.relN rd e name% «verify_tables_loop0» (x * gen :: [N, rounds, tabs, rkb, cprod]) []) :
    coreProgram.relN rd (e + 1) name% «verify_tables_loop0» (x :: [N, rounds, tabs, rkb, cprod]) [] := by
  obtain ⟨fn, hf, hp, hb⟩ := l10Found
  have hx7 : rounds * x ^ 7 = rounds * (x * x * x * (x * x * x) * x) := by ring
  rw [hx7] at l5 l6 hc l12 l13
  refine (relN_succ_iff hf e _ _).mpr ⟨B1.Val.ofArgs [x, N, rounds, tabs, rkb, cprod, x * x,
    x * x * x, x * x * x * (x * x * x), x * x * x * (x * x * x) * x,
    rounds * (x * x * x * (x * x * x) * x), cur, claim, ncur, nclaim, rk, rkb * x, cprod * x, cp,
    cp * rk, cprod * x, word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0], ?_, ?_⟩
  · rw [hp]; rfl
  rw [hb]
  simp only [l10Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, rfl, rfl, rfl, l5, l6, hc, rfl, lrk, l12, l13, rfl, lc0, rfl, rfl,
    lc1, rfl, rfl, rfl, rfl, rfl, ?_, ?_, trivial⟩
  · show IsInK (x * word 2 0 + N)
    rw [tb_word_gen]; exact hK
  · intro h0
    change x * word 2 0 + N ≠ 0 at h0
    change coreProgram.relN rd e name% «verify_tables_loop0» [x * word 2 0, N, rounds, tabs, rkb,
        cprod] []
    rw [tb_word_gen] at h0 ⊢
    exact hnext h0

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
  obtain ⟨D, hD⟩ := l10_depth (P := fun j d => ∃ cur claim ncur nclaim rk : E,
      coreProgram.relN rd d "sumcheck_round4" [rounds * (gen ^ j) ^ 7, cur, claim, tabs]
        [ncur, nclaim, rk] ∧ L10B rd rounds tabs rkb cprod (gen ^ j) ∧
      LoadHolds rd (rounds * (gen ^ j) ^ 7) 5 cur ∧ LoadHolds rd (rounds * (gen ^ j) ^ 7) 6 claim ∧
      LoadHolds rd (rounds * (gen ^ j) ^ 7) 12 ncur ∧ LoadHolds rd (rounds * (gen ^ j) ^ 7) 13 nclaim ∧
      LoadHolds rd (rkb * gen ^ j) 0 rk ∧
      ∃ cp, LoadHolds rd (cprod * gen ^ j) 0 cp ∧ LoadHolds rd (cprod * gen ^ j) 1 (cp * rk))
    (fun j a b hab ⟨c1, c2, c3, c4, c5, hc, rest⟩ =>
      ⟨c1, c2, c3, c4, c5, relN_mono coreProgram hab _ _ _ hc, rest⟩) n (fun j hj => by
      obtain ⟨c1, c2, c3, c4, c5, l5, l6, ⟨d, hc⟩, l12, l13, hy, hcp⟩ := hB j hj
      exact ⟨d, c1, c2, c3, c4, c5, hc, hB j hj, l5, l6, l12, l13, hy, hcp⟩)
  have hK : ∀ j, IsInK (gen ^ j * gen + gen ^ n) := fun j =>
    isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have key : ∀ t k, k + 1 + t = n → coreProgram.relN rd (D + t + 1) name% «verify_tables_loop0»
      (gen ^ k :: [gen ^ n, rounds, tabs, rkb, cprod]) [] := by
    intro t
    induction t with
    | zero =>
      intro k hk
      obtain ⟨c1, c2, c3, c4, c5, hc, -, l5, l6, l12, l13, lrk, cp, lc0, lc1⟩ := hD k (by omega)
      refine l10_body (D + 0) l5 l6 hc l12 l13 lrk lc0 lc1 (hK k) fun h0 => ?_
      exact absurd ((gen_pow_add_eq_zero_iff k).mpr (by rw [show k + 1 = n by omega])) h0
    | succ t ih =>
      intro k hk
      obtain ⟨c1, c2, c3, c4, c5, hc, -, l5, l6, l12, l13, lrk, cp, lc0, lc1⟩ := hD k (by omega)
      refine l10_body (D + (t + 1)) l5 l6 (relN_mono coreProgram (by omega) _ _ _ hc) l12 l13
        lrk lc0 lc1 (hK k) fun _ => ?_
      rw [gen_pow_mul_gen]
      exact ih (k + 1) (by omega)
  have := key (n - 1) 0 (by omega)
  rw [pow_zero] at this
  exact ⟨_, this⟩

set_option maxRecDepth 10000 in
/-- **An iteration of `verify_tables_loop1`**, at a depth reaching the next iteration. -/
theorem l11_body {rd : Reader} {N chi rkb gn x : E} (e : ℕ) {y v : E} (hy : gn * vtWInvGen = y * x)
    (lr : LoadHolds rd (rkb * y) 0 v) (lc : LoadHolds rd (chi * x) 0 v)
    (hK : IsInK (x * gen + N)) (hnext : x * gen + N ≠ 0 →
      coreProgram.relN rd e name% «verify_tables_loop1» (x * gen :: [N, chi, rkb, gn]) []) :
    coreProgram.relN rd (e + 1) name% «verify_tables_loop1» (x :: [N, chi, rkb, gn]) [] := by
  obtain ⟨fn, hf, hp, hb⟩ := l11Found
  refine (relN_succ_iff hf e _ _).mpr ⟨B1.Val.ofArgs [x, N, chi, rkb, gn, vtWInvGen, gn * vtWInvGen,
    y, rkb * y, v, chi * x, word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0], ?_, ?_⟩
  · rw [hp]; rfl
  rw [hb]
  simp only [l11Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, hy, rfl, lr, rfl, lc, rfl, rfl, rfl, rfl, rfl, ?_, ?_, trivial⟩
  · show IsInK (x * word 2 0 + N)
    rw [tb_word_gen]; exact hK
  · intro h0
    change x * word 2 0 + N ≠ 0 at h0
    change coreProgram.relN rd e name% «verify_tables_loop1» [x * word 2 0, N, chi, rkb, gn] []
    rw [tb_word_gen] at h0 ⊢
    exact hnext h0

/-- **`verify_tables_loop1`, completely**: when `chi[x] = rk[n - 1 - x]` for every `x < n`, the loop
holds from `1` below `g^n`. -/
theorem l11_complete {rd : Reader} {chi rkb : E} {n : ℕ} (hn0 : 0 < n)
    (hC : ∀ x < n, ∃ v, LoadHolds rd rkb (n - 1 - x) v ∧ LoadHolds rd chi x v) :
    coreProgram.Rel rd name% «verify_tables_loop1» [1, gen ^ n, chi, rkb, gen ^ n] [] := by
  have hK : ∀ j, IsInK (gen ^ j * gen + gen ^ n) := fun j =>
    isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have hit : ∀ k < n, ∃ y v, gen ^ n * vtWInvGen = y * gen ^ k ∧ LoadHolds rd (rkb * y) 0 v ∧
      LoadHolds rd (chi * gen ^ k) 0 v := by
    intro k hk
    obtain ⟨v, hr, hc⟩ := hC k hk
    refine ⟨gen ^ (n - 1 - k), v, ?_, ?_, ?_⟩
    · have h1 : gen ^ n * vtWInvGen * gen = gen ^ n := by rw [mul_assoc, vtWInvGen_mul, mul_one]
      apply mul_right_cancel₀ gen_ne_zero
      rw [h1, mul_assoc, ← pow_succ, ← pow_add, show n - 1 - k + (k + 1) = n by omega]
    · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hr
    · rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hc
  have key : ∀ t k, k + 1 + t = n → coreProgram.relN rd (t + 1) name% «verify_tables_loop1»
      (gen ^ k :: [gen ^ n, chi, rkb, gen ^ n]) [] := by
    intro t
    induction t with
    | zero =>
      intro k hk
      obtain ⟨y, v, hy, hr, hc⟩ := hit k (by omega)
      refine l11_body 0 hy hr hc (hK k) fun h0 => ?_
      exact absurd ((gen_pow_add_eq_zero_iff k).mpr (by rw [show k + 1 = n by omega])) h0
    | succ t ih =>
      intro k hk
      obtain ⟨y, v, hy, hr, hc⟩ := hit k (by omega)
      refine l11_body (t + 1) hy hr hc (hK k) fun _ => ?_
      rw [gen_pow_mul_gen]
      exact ih (k + 1) (by omega)
  have := key (n - 1) 0 (by omega)
  rw [pow_zero] at this
  exact ⟨_, this⟩

end
end LeanVM.Guest.B1.Tables
