/-
  LeanVM.Guest.B1.Tables.Vt.Rounds

  `verify_tables`' table sumcheck as a run: the `n` rounds of `__loop9` from the first record are
  the specification's plain sumcheck of `n` rounds.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Loop10

/-!
# The table sumcheck's rounds as a run

* `l10_loop`: `__loop9` from `1` below `g^n` gives every iteration's facts, `j < n`;
* `l10_chain`: from record `j` (capacity `cap`, cursor `cur`, claim `claim`), the remaining `k`
  rounds run `sumcheck claim 4 (replicate k none)` on the words at the cursor, to the last record,
  their challenges stored in `chi` from its top.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`__loop9` from `1` below `g^n`.** -/
theorem l10_loop {rd : Reader} {rounds chi cprod : E} {n : ℕ} (hn0 : 0 < n) (hn : n < 2 ^ 62)
    (h : coreProgram.Rel rd "__loop9" [1, gen ^ n, rounds, chi, gen ^ n, cprod] []) :
    ∀ j < n, L10B rd rounds chi (gen ^ n) cprod (gen ^ j) := by
  rw [← pow_zero gen] at h
  obtain ⟨m, -, hN, hall⟩ := tb_loop_sound (B := L10B rd rounds chi (gen ^ n) cprod)
    (fun d x hx => l10_step d x hx) 0 h
  have hm : n ≤ m := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) hN
    omega
  intro j hj
  exact hall j (by omega) (by omega)

theorem capAt_unique' {rd : Reader} {rec : E} {off stride : ℕ} {c1 c2 : List E}
    (h1 : CapAt rd rec off stride c1) (h2 : CapAt rd rec off stride c2) : c1 = c2 :=
  List.ext_getElem (h1.1.trans h2.1.symm) fun j hj1 hj2 =>
    tb_loadHolds_unique (h1.2 j hj1) (h2.2 j hj2)

/-- **The rounds as a run.** -/
theorem l10_chain {rd : Reader} {rounds chi cprod : E} {n : ℕ} (hn : n < 2 ^ 30)
    (hB : ∀ j < n, L10B rd rounds chi (gen ^ n) cprod (gen ^ j)) :
    ∀ k ≤ n, ∀ j, j + k = n → ∀ (cap : List E) (cur claim : E),
      CapAt rd (rounds * gen ^ (7 * j)) 0 1 cap →
      LoadHolds rd (rounds * gen ^ (7 * j)) 5 cur → LoadHolds rd (rounds * gen ^ (7 * j)) 6 claim →
      ∃ (xs pts : List E) (claimN : E) (capN : List E),
        RunsTo (sumcheck claim 4 (List.replicate k none)) ⟨cap, []⟩ xs (pts, claimN) ⟨capN, []⟩ ∧
        ReadsAt rd cur xs ∧ xs.length = 3 * k ∧ pts.length = k ∧
        CapAt rd (rounds * gen ^ (7 * n)) 0 1 capN ∧
        LoadHolds rd (rounds * gen ^ (7 * n)) 5 (cur * gen ^ (3 * k)) ∧
        LoadHolds rd (rounds * gen ^ (7 * n)) 6 claimN ∧
        ∀ i < k, LoadHolds rd chi (n - 1 - (j + i)) (pts.getD i 0) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj cap cur claim hc hcur hcl
    simp only [Nat.add_zero] at hj
    subst hj
    exact ⟨[], [], claim, cap, runsTo_sumcheck_nil _ _ _, readsAt_nil _ _, rfl, rfl, hc,
      by simpa using hcur, hcl, fun i hi => absurd hi (by omega)⟩
  | succ k ih =>
    intro hk j hj cap cur claim hc hcur hcl
    obtain ⟨cur', claim', ncur, nclaim, rk, lcur, lcl, hrel, lnc, lncl, ⟨y, hy, lch⟩, -⟩ :=
      hB j (by omega)
    rw [← pow_mul, mul_comm j 7] at lcur lcl hrel lnc lncl
    obtain rfl := tb_loadHolds_unique lcur hcur
    obtain rfl := tb_loadHolds_unique lcl hcl
    have hm := (sumcheck_round4_holds rd _ _).mp hrel
    simp only [MeaningSumcheckRound4] at hm
    obtain ⟨cap', c0, c2, c3, hc', -, hrd, hcap1, hrets⟩ := hm
    obtain rfl := capAt_unique' hc' hc
    simp only [List.cons.injEq, and_true] at hrets
    obtain ⟨rfl, rfl, rfl⟩ := hrets
    -- the next record
    have hrec : rounds * gen ^ (7 * j) * gen ^ 7 = rounds * gen ^ (7 * (j + 1)) := by ring
    rw [hrec] at hcap1
    have lnc' : LoadHolds rd (rounds * gen ^ (7 * (j + 1))) 5 (cur' * gen ^ 3) := by
      rw [← hrec, tb_loadHolds_mul_gen_pow]; exact lnc
    have lncl' : LoadHolds rd (rounds * gen ^ (7 * (j + 1))) 6
        (polyEval [c0, claim' + sumE [c2, c3], c2, c3]
          ((⟨cap', []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve).squeeze.1) := by
      rw [← hrec, tb_loadHolds_mul_gen_pow]; exact lncl
    obtain ⟨xs, pts, claimN, capN, hrun, hxs, hxl, hpl, hcN, hcurN, hclN, hchi⟩ :=
      ih (by omega) (j + 1) (by omega) _ _ _ hcap1 lnc' lncl'
    have hround := sumcheck_round4_run cap' c0 c2 c3 claim'
    refine ⟨[c0, c2, c3] ++ xs, ((⟨cap', []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve).squeeze.1 :: pts,
      claimN, capN, ?_, ?_, by simp [hxl]; ring,
      by simp [hpl], hcN, ?_, hclN, fun i hi => ?_⟩
    · have hr := runsTo_sumcheck_cons (runsTo_roundPolyNone ⟨cap', []⟩ claim' c0 [c2, c3] 4 rfl)
        (hrun.of_eq rfl rfl rfl rfl)
      rw [List.replicate_succ]
      exact hr.of_eq rfl rfl rfl rfl
    · intro i hi
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · rw [List.getElem_append_left (by simpa using h3)]
        exact hrd i (by simpa using h3)
      · rw [List.getElem_append_right (by simpa using h3)]
        have := hxs (i - 3) (by simp at hi; omega)
        rw [tb_loadHolds_mul_gen_pow] at this
        simp only [List.length_cons, List.length_nil] at this ⊢
        rwa [show 3 + (i - 3) = i by omega] at this
    · rw [show cur' * gen ^ (3 * (k + 1)) = cur' * gen ^ 3 * gen ^ (3 * k) by ring]
      exact hcurN
    · rcases i with _ | i
      · simp only [List.getD_cons_zero, Nat.add_zero]
        have hyv : y = gen ^ (n - 1 - j) := by
          have h1 : gen ^ n * vtWInvGen * gen = gen ^ n := by
            rw [mul_assoc, vtWInvGen_mul, mul_one]
          rw [hy, mul_assoc, ← pow_succ, show j + 1 = j + 1 from rfl] at h1
          have e : y * gen ^ (j + 1) = gen ^ (n - 1 - j) * gen ^ (j + 1) := by
            rw [h1, ← pow_add, show n - 1 - j + (j + 1) = n by omega]
          exact mul_right_cancel₀ (pow_ne_zero _ gen_ne_zero) e
        rw [hyv, tb_loadHolds_mul_gen_pow, Nat.add_zero] at lch
        exact lch
      · simp only [List.getD_cons_succ]
        rw [show j + (i + 1) = j + 1 + i by ring]
        exact hchi i (by omega)

end
end LeanVM.Guest.B1.Tables
