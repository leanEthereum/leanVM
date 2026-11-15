/-
  LeanVM.Guest.B1.Tables.Vt.Rounds

  `verify_tables`' table sumcheck as a run: the `n` rounds of `verify_tables_loop0` from the first
  record are the specification's plain sumcheck of `n` rounds.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Loop10
public import LeanVM.Guest.B1.Sumcheck.Run
public import LeanVM.Guest.Data.NameStrings

/-!
# The table sumcheck's rounds as a run

* `l10_loop`: `verify_tables_loop0` from `1` below `g^n` gives every iteration's facts, `j < n`;
* `l10_chain`: from record `j` (capacity `cap`, cursor `cur`, claim `claim`), the remaining `k`
  rounds run `sumcheck claim 4 (replicate k none)` on the words at the cursor, to the last record,
  their challenges stored in `rk` from `j`;
* `l11_loop`: `verify_tables_loop1` copies `rk` into `chi` reversed, `chi[x] = rk[n - 1 - x]`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_tables_loop0` from `1` below `g^n`.** -/
theorem l10_loop {rd : Reader} {rounds tabs rkb cprod : E} {n : ℕ} (hn0 : 0 < n) (hn : n < 2 ^ 62)
    (h : coreProgram.Rel rd name% «verify_tables_loop0» [1, gen ^ n, rounds, tabs, rkb, cprod] []) :
    ∀ j < n, L10B rd rounds tabs rkb cprod (gen ^ j) := by
  rw [← pow_zero gen] at h
  obtain ⟨m, -, hN, hall⟩ := tb_loop_sound (B := L10B rd rounds tabs rkb cprod)
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
theorem l10_chain {rd : Reader} {rounds tabs rkb cprod : E} {n : ℕ} (hn : n < 2 ^ 30)
    (hB : ∀ j < n, L10B rd rounds tabs rkb cprod (gen ^ j)) :
    ∀ k ≤ n, ∀ j, j + k = n → ∀ (cap : List E) (cur claim : E),
      CapAt rd (rounds * gen ^ (7 * j)) 0 1 cap →
      LoadHolds rd (rounds * gen ^ (7 * j)) 5 cur → LoadHolds rd (rounds * gen ^ (7 * j)) 6 claim →
      ∃ (xs pts : List E) (claimN : E) (capN : List E),
        RunsTo (sumcheck claim 4 (List.replicate k none)) ⟨cap, []⟩ xs (pts, claimN) ⟨capN, []⟩ ∧
        ReadsAt rd cur xs ∧ xs.length = 3 * k ∧ pts.length = k ∧
        CapAt rd (rounds * gen ^ (7 * n)) 0 1 capN ∧
        LoadHolds rd (rounds * gen ^ (7 * n)) 5 (cur * gen ^ (3 * k)) ∧
        LoadHolds rd (rounds * gen ^ (7 * n)) 6 claimN ∧
        ∀ i < k, LoadHolds rd rkb (j + i) (pts.getD i 0) := by
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
    obtain ⟨cur', claim', ncur, nclaim, rk, lcur, lcl, hrel, lnc, lncl, lch, -⟩ :=
      hB j (by omega)
    rw [← pow_mul, mul_comm j 7] at lcur lcl hrel lnc lncl
    obtain rfl := tb_loadHolds_unique lcur hcur
    obtain rfl := tb_loadHolds_unique lcl hcl
    have hm := (sumcheck_round4_holds rd _ _).mp hrel
    simp only [MeaningSumcheckRound4] at hm
    obtain ⟨cap', c0, c2, c3, hc', hrd, hcap1, hrets⟩ := hm
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
    · have hr := runsTo_sumcheck_cons (runsTo_roundPolyNone ⟨cap', []⟩ claim' c0 [c2, c3] 4 rfl (by decide))
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
        rw [tb_loadHolds_mul_gen_pow, Nat.add_zero] at lch
        exact lch
      · simp only [List.getD_cons_succ]
        rw [show j + (i + 1) = j + 1 + i by ring]
        exact hchi i (by omega)

/-- What an iteration of `verify_tables_loop1` at `x` gives: the word at `rk·y`, `g^n·g⁻¹ = y·x`, stored
at `chi·x`. -/
def L11B (rd : Reader) (chi rkb gn x : E) : Prop :=
  ∃ y v, gn * vtWInvGen = y * x ∧ LoadHolds rd (rkb * y) 0 v ∧ LoadHolds rd (chi * x) 0 v

/-- **An iteration of `verify_tables_loop1`.** -/
theorem l11_step {rd : Reader} {N chi rkb gn : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «verify_tables_loop1» (x :: [N, chi, rkb, gn]) []) :
    L11B rd chi rkb gn x ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «verify_tables_loop1» (x * gen :: [N, chi, rkb, gn]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := l11Found
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb] at hbody
  simp only [l11Body, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hbody
  obtain ⟨c5, m6, m6', m8, l9, m10, l9', c11, m12, a13, c14, m15, ⟨-, hnext, -⟩⟩ := hbody
  simp only [Atom.Holds] at c5 m6 m6' m8 l9 m10 l9' c11 m12 a13 c14 m15
  refine ⟨⟨σ (.n 7), σ (.n 9), by rw [← m6', m6, c5], by rw [← m8]; exact l9,
    by rw [← m10]; exact l9'⟩, fun hne => ?_⟩
  rw [tb_word_gen] at c11 c14
  have := hnext (by rw [a13, m12, c11]; exact hne)
  rw [m15, c14] at this
  exact this

/-- **`verify_tables_loop1` from `1` below `g^n`**: `chi[x] = rk[n - 1 - x]`, `x < n`. -/
theorem l11_loop {rd : Reader} {chi rkb : E} {n : ℕ} (hn0 : 0 < n) (hn : n < 2 ^ 62)
    (h : coreProgram.Rel rd name% «verify_tables_loop1» [1, gen ^ n, chi, rkb, gen ^ n] []) :
    ∀ x < n, ∃ v, LoadHolds rd rkb (n - 1 - x) v ∧ LoadHolds rd chi x v := by
  rw [← pow_zero gen] at h
  obtain ⟨m, -, hN, hall⟩ := tb_loop_sound (B := L11B rd chi rkb (gen ^ n))
    (fun d x hx => l11_step d x hx) 0 h
  have hm : n ≤ m := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) hN
    omega
  intro x hx
  obtain ⟨y, v, hy, hr, hc⟩ := hall x (by omega) (by omega)
  have h1 : gen ^ n * vtWInvGen * gen = gen ^ n := by rw [mul_assoc, vtWInvGen_mul, mul_one]
  rw [hy, mul_assoc, ← pow_succ] at h1
  have e : y * gen ^ (x + 1) = gen ^ (n - 1 - x) * gen ^ (x + 1) := by
    rw [h1, ← pow_add, show n - 1 - x + (x + 1) = n by omega]
  rw [mul_right_cancel₀ (pow_ne_zero _ gen_ne_zero) e, tb_loadHolds_mul_gen_pow, Nat.add_zero] at hr
  rw [tb_loadHolds_mul_gen_pow, Nat.add_zero] at hc
  exact ⟨v, hr, hc⟩

end
end LeanVM.Guest.B1.Tables
