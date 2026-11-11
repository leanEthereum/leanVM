/-
  LeanVM.Protocol.Compile.Rom.Step

  The step inequality of the random-oracle theorem: one fresh answer raises the potential, in
  expectation, by at most the largest proof-of-work-discounted escape bound of the certificate
  plus the probability that the answer fails.
-/

module

public import LeanVM.Protocol.Compile.Rom.Potential

/-!
# The step inequality

For the potential `pot C.D σ P` of a certificate `C : Cert P` and the family of seedings `σ`,
every log `ℓ`:

* `step_ineqH`: for a hash input `x` the log does not answer,
  `(∑ u, pot (ℓ ++ [(x, u)])) / |Digest| ≤ pot ℓ + (5 + |σ.offs|)(|ℓ| + 1) / 2^256`;
* `step_ineqF`: for a permutation input `s` the log does not answer,
  `(∑ u, pot (ℓ ++ [(s, u)])) / |KState| ≤ pot ℓ + (εmax + (5 + |σ.offs|)(|ℓ| + 1) / 2^256)`,

where `εmax` bounds `2^-min(grindBits h, 64) · C.ε h` for every history `h`.

The proof (see `LeanVM.Protocol.Compile.Rom.Potential` for the terms):

* a failed log has potential `1`, and the potential never exceeds `1`;
* a hash entry changes no record and no term: only its failure (`sum_badH_le`) raises the
  potential;
* a permutation entry fails with probability at most `(2|ℓ| + 2) · 2^-256`
  (`sum_badF_div_le`), and on the other answers the answer is fresh and the potential is the
  capped sum of the terms;
* each old record's term is a supermartingale on fresh answers (`term_step_old`);
* the new record's term averages to at most `εmax` (`term_step_new`): on fresh answers it is
  `[D h] · esc D h p` at the start of its group, times the proof of work's success on the new
  state's challenge after a nonce, whose average is at most `2^-min(b, 64)`, and
  `esc D h p ≤ C.ε h` at a doomed boundary (`esc_le_eps`). The proof-of-work factor reads the
  answer's first lane; the escape after it reads only later permutation answers, whose inputs
  carry the answer's capacity, so the two multiply.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

variable {X : Type} {σ : Seeds X} {P : VerifierProgram Bool}

/-- The certificate's bound at a doomed boundary, discounted by the proof of work before it. -/
theorem ind_mul_esc_le (C : Cert P) {εmax : ℝ≥0∞}
    (hε : ∀ h, 2⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) {h : List Ev} {p : VerifierProgram Bool}
    (hr : P.Reachable h) (hb : Boundary h) (ha : P.after h = some p) :
    ind (C.D h) * (2⁻¹ ^ min (grindBits h) 64 * esc C.D h p) ≤ εmax := by
  by_cases hD : C.D h
  · rw [ind_of hD, one_mul]
    exact (mul_le_mul_right (esc_le_eps C hr hb ha hD) _).trans (hε h)
  · rw [ind_of_not hD, zero_mul]; exact bot_le

/-- The average proof-of-work factor of a record. -/
theorem powF_avg (pw : Option (ℕ × E)) :
    (∑ u : KeccakState, powF pw u) / Fintype.card KeccakState ≤ 2⁻¹ ^ min ((pw.map Prod.fst).getD 0) 64 := by
  rcases pw with _ | ⟨b, n⟩
  · simp only [Option.map_none, Option.getD_none, Nat.zero_min, pow_zero]
    exact avg_le_of_le fun _ ↦ le_rfl
  · exact sum_powOk_div_le b

/-- **The new record averages to at most `εmax`.** -/
theorem term_step_new (C : Cert P) {εmax : ℝ≥0∞}
    (hε : ∀ h, 2⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) (ℓ : Log) (t : KeccakState) :
    (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) *
        term C.D (ℓ ++ [.inr (t, u)]) ((stepF σ P ℓ (decode σ P ℓ) t).1, u)) /
          Fintype.card KeccakState ≤ εmax := by
  have hok := stepF_shapeOk (σ := σ) (P := P) ℓ t
  generalize (stepF σ P ℓ (decode σ P ℓ) t).1 = s at hok ⊢
  cases s with
  | none =>
    simp only [term, mul_zero, Finset.sum_const_zero, ENNReal.zero_div]
    exact bot_le
  | st h p pw =>
    obtain ⟨hr, hb, ha, hg⟩ := hok
    have hcert := ind_mul_esc_le C hε hr hb ha
    rw [hg] at hcert
    have h1 : (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) *
        term C.D (ℓ ++ [.inr (t, u)]) (Shape.st h p pw, u)) / Fintype.card KeccakState ≤
          (∑ u, powF pw u * (ind (C.D h) * esc C.D h p)) / Fintype.card KeccakState := by
      refine ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _
      simp only [term]
      by_cases hf : Fresh (ℓ ++ [.inr (t, u)]) u
      · rw [ind_of hf, one_mul, gv_fresh C.D hf]
        exact le_of_eq (by ring)
      · rw [ind_of_not hf, zero_mul]; exact bot_le
    have h2 : (∑ u, powF pw u * (ind (C.D h) * esc C.D h p)) / Fintype.card KeccakState =
        ((∑ u, powF pw u) / Fintype.card KeccakState) * (ind (C.D h) * esc C.D h p) := by
      rw [← Finset.sum_mul, ENNReal.mul_div_right_comm]
    rw [h2] at h1
    refine h1.trans ((mul_le_mul_left (powF_avg pw) _).trans ?_)
    rw [mul_left_comm]
    exact hcert
  | sq h p =>
    obtain ⟨hr, hb, ha, hg⟩ := hok
    have hcert := ind_mul_esc_le C hε hr hb ha
    rw [hg, min_eq_left (Nat.zero_le _), pow_zero, one_mul] at hcert
    have heq : (∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) *
        term C.D (ℓ ++ [.inr (t, u)]) (Shape.sq h p, u)) / Fintype.card KeccakState =
          ind (C.D h) * ((∑ u, ind (Fresh (ℓ ++ [.inr (t, u)]) u) *
            gv1 C.D (ℓ ++ [.inr (t, u)]) u h p) / Fintype.card KeccakState) := by
      simp only [term]
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun u _ ↦ by ring
    rw [heq]
    exact (mul_le_mul_right (gv1_new C.D h p) _).trans hcert

/-- Averaging `f + c` adds `c` to the average of `f`. -/
theorem avg_add_const {γ : Type} [Fintype γ] [Nonempty γ] (f : γ → ℝ≥0∞) (c : ℝ≥0∞) :
    (∑ u, (f u + c)) / Fintype.card γ = (∑ u, f u) / Fintype.card γ + c := by
  have hcard : (Fintype.card γ : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_comm, ENNReal.mul_div_cancel_right hcard (ENNReal.natCast_ne_top _)]

/-- A capped sum grows by at most the increment. -/
theorem min_one_add_le (a ε : ℝ≥0∞) : min 1 (a + ε) ≤ min 1 a + ε := by
  rcases le_total a 1 with h | h
  · rw [min_eq_right h]; exact min_le_right _ _
  · rw [min_eq_left h]; exact (min_le_left _ _).trans le_self_add

/-- A list sum divided by a constant. -/
theorem list_sum_div {β : Type} (L : List β) (f : β → ℝ≥0∞) (c : ℝ≥0∞) :
    (L.map f).sum / c = (L.map fun x ↦ f x / c).sum := by
  simp only [div_eq_mul_inv, List.sum_map_mul_right]

/-- The failure bound of one hash answer, over `2^256`. -/
theorem sum_badH_div_le (σ : Seeds X) (ℓ : Log) (x : Bytes) :
    (∑ u, ind (BadH σ ℓ x u)) / Fintype.card Digest ≤
      ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) / 2 ^ 256 := by
  rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (sum_badH_le σ ℓ x) _

/-- The failure bound of one permutation answer, over `2^256`. -/
theorem sum_badF_div_le' (σ : Seeds X) (ℓ : Log) (s : KeccakState) :
    (∑ u, ind (BadF ℓ s u)) / Fintype.card KeccakState ≤
      ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) / 2 ^ 256 := by
  refine (sum_badF_div_le ℓ s).trans ?_
  rw [div_eq_mul_inv, ENNReal.inv_pow]
  gcongr
  calc 2 * ℓ.length + 2 = 2 * (ℓ.length + 1) := by ring
    _ ≤ (5 + σ.offs.length) * (ℓ.length + 1) := Nat.mul_le_mul_right _ (by omega)

/-- A hash entry raises the potential only by failing. -/
theorem pot_append_inl_le (D : List Ev → Prop) (ℓ : Log) (x : Bytes) (u : Digest) :
    pot D σ P (ℓ ++ [.inl (x, u)]) ≤ ind (BadH σ ℓ x u) + pot D σ P ℓ := by
  by_cases hb : BadH σ ℓ x u
  · rw [ind_of hb]; exact (pot_le_one D σ P _).trans le_self_add
  · rw [ind_of_not hb, zero_add]
    by_cases hf : Fail σ ℓ
    · have h1 : pot D σ P ℓ = 1 := by simp only [pot, hf, ↓reduceIte]
      rw [h1]; exact pot_le_one D σ P _
    · have hnf : ¬ Fail σ (ℓ ++ [.inl (x, u)]) := by
        rw [fail_append]; exact fun h ↦ h.elim hf hb
      simp only [pot, hnf, hf, ↓reduceIte, termSum_append_inl, le_refl]

/-- **The step inequality for the hash.** A fresh hash answer raises the potential only by
failing. -/
theorem step_ineqH (D : List Ev → Prop) (ℓ : Log) (x : Bytes) :
    (∑ u, pot D σ P (ℓ ++ [.inl (x, u)])) / Fintype.card Digest ≤
      pot D σ P ℓ + ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) / 2 ^ 256 := by
  have h1 : (∑ u, pot D σ P (ℓ ++ [.inl (x, u)])) / Fintype.card Digest ≤
      (∑ u, (ind (BadH σ ℓ x u) + pot D σ P ℓ)) / Fintype.card Digest :=
    ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ pot_append_inl_le D ℓ x u) _
  rw [avg_add_const] at h1
  refine h1.trans ?_
  rw [add_comm (pot D σ P ℓ)]
  exact add_le_add (sum_badH_div_le σ ℓ x) le_rfl

/-- **The step inequality for the permutation.** For every log `ℓ` and permutation input `s` it
does not answer, the average of the potential after one fresh answer at `s` is at most the
potential before it plus `εmax` plus the bound on the probability that the answer fails. -/
theorem step_ineqF (C : Cert P) {εmax : ℝ≥0∞}
    (hε : ∀ h, 2⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) (ℓ : Log) (t : KeccakState)
    (ht : lookF ℓ t = none) :
    (∑ u, pot C.D σ P (ℓ ++ [.inr (t, u)])) / Fintype.card KeccakState ≤
      pot C.D σ P ℓ + (εmax + ((5 + σ.offs.length) * (ℓ.length + 1) : ℕ) / 2 ^ 256) := by
  by_cases hf : Fail σ ℓ
  · have h1 : pot C.D σ P ℓ = 1 := by simp only [pot, hf, ↓reduceIte]
    rw [h1]
    exact (avg_le_of_le fun u ↦ pot_le_one C.D σ P _).trans le_self_add
  have hpot : pot C.D σ P ℓ = min 1 (termSum C.D σ P ℓ) := by simp only [pot, hf, ↓reduceIte]
  set ℓ' := fun u : KeccakState ↦ ℓ ++ [.inr (t, u)] with hℓ'
  set s := (stepF σ P ℓ (decode σ P ℓ) t).1
  -- the potential after the entry, pointwise
  have hpt : ∀ u, pot C.D σ P (ℓ' u) ≤
      ind (BadF ℓ t u) + ind (Fresh (ℓ' u) u) * min 1 (termSum C.D σ P (ℓ' u)) := by
    intro u
    by_cases hb : BadF ℓ t u
    · rw [ind_of hb]; exact (pot_le_one C.D σ P _).trans le_self_add
    · have hnf : ¬ Fail σ (ℓ' u) := by
        rw [hℓ', fail_append]; exact fun h ↦ h.elim hf hb
      rw [ind_of_not hb, zero_add, ind_of (fresh_of_not_badF hb), one_mul]
      simp only [pot, hnf, ↓reduceIte, le_refl]
  -- the sum of the terms after the entry, on fresh answers
  have hsum : (∑ u, ind (Fresh (ℓ' u) u) * termSum C.D σ P (ℓ' u)) / Fintype.card KeccakState ≤
      termSum C.D σ P ℓ + εmax := by
    have hsplit : ∀ u, ind (Fresh (ℓ' u) u) * termSum C.D σ P (ℓ' u) =
        ((decode σ P ℓ).kinds.map fun κ ↦ ind (Fresh (ℓ' u) u) * term C.D (ℓ' u) κ).sum +
          ind (Fresh (ℓ' u) u) * term C.D (ℓ' u) (s, u) := by
      intro u
      simp only [termSum, hℓ', kinds_decode_append_inr, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, mul_add, List.sum_map_mul_left]
      rfl
    simp only [hsplit, Finset.sum_add_distrib]
    rw [ENNReal.add_div, sum_list_sum_comm, list_sum_div]
    refine add_le_add ?_ (term_step_new C hε ℓ t)
    exact List.sum_le_sum fun κ _ ↦ term_step_old C.D ht κ
  -- assemble
  have hfresh : (∑ u, ind (Fresh (ℓ' u) u) * min 1 (termSum C.D σ P (ℓ' u))) /
      Fintype.card KeccakState ≤ min 1 (termSum C.D σ P ℓ) + εmax := by
    refine (le_min ?_ ?_).trans (min_one_add_le _ _)
    · exact avg_le_of_le fun u ↦
        (mul_le_mul_left (ind_le_one _) _).trans ((one_mul _).le.trans (min_le_left _ _))
    · refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _) hsum
      exact mul_le_mul_right (min_le_right _ _) _
  have hbad := sum_badF_div_le' σ ℓ t
  have h1 : (∑ u, pot C.D σ P (ℓ ++ [.inr (t, u)])) / Fintype.card KeccakState ≤
      (∑ u, (ind (BadF ℓ t u) +
        ind (Fresh (ℓ' u) u) * min 1 (termSum C.D σ P (ℓ' u)))) / Fintype.card KeccakState :=
    ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
  rw [Finset.sum_add_distrib, ENNReal.add_div] at h1
  refine h1.trans ((add_le_add hbad hfresh).trans (le_of_eq ?_))
  rw [hpot]
  ring

end
end LeanVM.Protocol.Compile.Rom
