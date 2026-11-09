/-
  LeanVM.Guest.B1.Tables.VtC.ZLoop10

  `__loop9`, completely: every iteration's facts give its relation from `1` below `g^n`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Rounds

/-!
# `__loop9`, completely (G:2399-2412)

`l10_complete`: when every iteration `j < n` has its facts (`L10B`: the round on the record
`rounds·g^(7j)`, the next record's cursor and claim, the challenge in `chi`, the running product
in `cprod`), `__loop9` holds from `1` below `g^n`. An iteration's body holds on the evident
valuation at any depth reaching its `sumcheck_round4` call and the next iteration (`l10_body`);
one depth bounds every round's call (`l10_depth`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 10000 in
/-- **An iteration of `__loop9`**, at a depth reaching its round's call and the next
iteration. -/
theorem l10_body {rd : Reader} {N rounds chi gn cprod x : E} (e : ℕ)
    {cur claim ncur nclaim rk y cp : E}
    (l5 : LoadHolds rd (rounds * x ^ 7) 5 cur) (l6 : LoadHolds rd (rounds * x ^ 7) 6 claim)
    (hc : coreProgram.relN rd e "sumcheck_round4" [rounds * x ^ 7, cur, claim] [ncur, nclaim, rk])
    (l12 : LoadHolds rd (rounds * x ^ 7) 12 ncur) (l13 : LoadHolds rd (rounds * x ^ 7) 13 nclaim)
    (hy : gn * vtWInvGen = y * x) (lch : LoadHolds rd (chi * y) 0 rk)
    (lc0 : LoadHolds rd (cprod * x) 0 cp) (lc1 : LoadHolds rd (cprod * x) 1 (cp * rk))
    (hK : IsInK (x * gen + N)) (hnext : x * gen + N ≠ 0 →
      coreProgram.relN rd e "__loop9" (x * gen :: [N, rounds, chi, gn, cprod]) []) :
    coreProgram.relN rd (e + 1) "__loop9" (x :: [N, rounds, chi, gn, cprod]) [] := by
  obtain ⟨fn, hf, hp, hb⟩ := l10Found
  have hx7 : rounds * x ^ 7 = rounds * (x * x * x * (x * x * x) * x) := by ring
  rw [hx7] at l5 l6 hc l12 l13
  refine (relN_succ_iff hf e _ _).mpr ⟨B1.Val.ofArgs [x, N, rounds, chi, gn, cprod, x * x,
    x * x * x, x * x * x * (x * x * x), x * x * x * (x * x * x) * x,
    rounds * (x * x * x * (x * x * x) * x), cur, claim, ncur,
    nclaim, rk, vtWInvGen, gn * vtWInvGen, y, chi * y, cprod * x, cp, cp * rk, cprod * x,
    word 2 0 0, x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], ?_, ?_⟩
  · rw [hp]; rfl
  rw [hb]
  simp only [l10Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨rfl, rfl, rfl, rfl, rfl, l5, l6, hc, rfl, rfl, hy, rfl, lch, l12, l13, rfl, lc0, rfl, rfl,
    lc1, rfl, rfl, rfl, rfl, rfl, ?_, ?_, trivial⟩
  · show IsInK (x * word 2 0 0 + N)
    rw [tb_word_gen]; exact hK
  · intro h0
    change x * word 2 0 0 + N ≠ 0 at h0
    change coreProgram.relN rd e "__loop9" [x * word 2 0 0, N, rounds, chi, gn, cprod] []
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

/-- **`__loop9`, completely**: every iteration's facts give the loop from `1` below `g^n`. -/
theorem l10_complete {rd : Reader} {rounds chi cprod : E} {n : ℕ} (hn0 : 0 < n)
    (hB : ∀ j < n, L10B rd rounds chi (gen ^ n) cprod (gen ^ j)) :
    coreProgram.Rel rd "__loop9" [1, gen ^ n, rounds, chi, gen ^ n, cprod] [] := by
  obtain ⟨D, hD⟩ := l10_depth (P := fun j d => ∃ cur claim ncur nclaim rk : E,
      coreProgram.relN rd d "sumcheck_round4" [rounds * (gen ^ j) ^ 7, cur, claim]
        [ncur, nclaim, rk] ∧ L10B rd rounds chi (gen ^ n) cprod (gen ^ j) ∧
      LoadHolds rd (rounds * (gen ^ j) ^ 7) 5 cur ∧ LoadHolds rd (rounds * (gen ^ j) ^ 7) 6 claim ∧
      LoadHolds rd (rounds * (gen ^ j) ^ 7) 12 ncur ∧ LoadHolds rd (rounds * (gen ^ j) ^ 7) 13 nclaim ∧
      (∃ y, gen ^ n * vtWInvGen = y * gen ^ j ∧ LoadHolds rd (chi * y) 0 rk) ∧
      ∃ cp, LoadHolds rd (cprod * gen ^ j) 0 cp ∧ LoadHolds rd (cprod * gen ^ j) 1 (cp * rk))
    (fun j a b hab ⟨c1, c2, c3, c4, c5, hc, rest⟩ =>
      ⟨c1, c2, c3, c4, c5, relN_mono coreProgram hab _ _ _ hc, rest⟩) n (fun j hj => by
      obtain ⟨c1, c2, c3, c4, c5, l5, l6, ⟨d, hc⟩, l12, l13, hy, hcp⟩ := hB j hj
      exact ⟨d, c1, c2, c3, c4, c5, hc, hB j hj, l5, l6, l12, l13, hy, hcp⟩)
  have hK : ∀ j, IsInK (gen ^ j * gen + gen ^ n) := fun j =>
    isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have key : ∀ t k, k + 1 + t = n → coreProgram.relN rd (D + t + 1) "__loop9"
      (gen ^ k :: [gen ^ n, rounds, chi, gen ^ n, cprod]) [] := by
    intro t
    induction t with
    | zero =>
      intro k hk
      obtain ⟨c1, c2, c3, c4, c5, hc, -, l5, l6, l12, l13, ⟨y, hy, lch⟩, cp, lc0, lc1⟩ :=
        hD k (by omega)
      refine l10_body (D + 0) l5 l6 hc l12 l13 hy lch lc0 lc1 (hK k) fun h0 => ?_
      exact absurd ((gen_pow_add_eq_zero_iff k).mpr (by rw [show k + 1 = n by omega])) h0
    | succ t ih =>
      intro k hk
      obtain ⟨c1, c2, c3, c4, c5, hc, -, l5, l6, l12, l13, ⟨y, hy, lch⟩, cp, lc0, lc1⟩ :=
        hD k (by omega)
      refine l10_body (D + (t + 1)) l5 l6 (relN_mono coreProgram (by omega) _ _ _ hc) l12 l13 hy
        lch lc0 lc1 (hK k) fun _ => ?_
      rw [gen_pow_mul_gen]
      exact ih (k + 1) (by omega)
  have := key (n - 1) 0 (by omega)
  rw [pow_zero] at this
  exact ⟨_, this⟩

end
end LeanVM.Guest.B1.Tables
