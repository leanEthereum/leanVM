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

`step_ineq`: for the potential `pot C.D σ P` of a certificate `C : Cert P` and the seeding `σ`,
every log `ℓ` and every input `t` it does not answer,

  `(∑ u, pot (ℓ ++ [(t, u)])) / |Digest| ≤ pot ℓ + (εmax + (4 + k)(|ℓ| + 1) / |Digest|)`,

where `εmax` bounds `2^-min(grindBits h, 64) · C.ε h` for every history `h` and `k` is the number
of seeding steps.

The proof (see `LeanVM.Protocol.Compile.Rom.Potential` for the terms):

* a failed log has potential `1`, and the potential never exceeds `1`;
* otherwise the new entry fails for at most `(4 + k)(|ℓ| + 1)` answers (`sum_badEntry_le`), and
  on the others the answer is fresh and the potential is the capped sum of the terms;
* each old record's term is a supermartingale on fresh answers (`term_step_old`);
* the new record's term averages to at most `εmax` (`term_step_new`): it is, on fresh answers,
  `[D h] · esc D h p` at the start of its group, times the proof-of-work factor for a group
  after a nonce, and `esc D h p ≤ C.ε h` at a doomed boundary (`esc_le_eps`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

variable {X : Type} {σ : Seeds X} {P : Prog Bool}

/-- An average of terms each at most `c` is at most `c`. -/
theorem avg_le_of_le {f : Digest → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ u, f u ≤ c) :
    (∑ u, f u) / Fintype.card Digest ≤ c := by
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ u, f u ≤ ∑ _u : Digest, c := Finset.sum_le_sum fun u _ ↦ h u
    _ = c * Fintype.card Digest := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- The certificate's bound at a doomed boundary, discounted by the proof of work before it. -/
theorem ind_mul_esc_le (C : Cert P) {εmax : ℝ≥0∞}
    (hε : ∀ h, 2⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) {h : List Ev} {p : Prog Bool}
    (hr : P.Reachable h) (hb : Boundary h) (ha : P.after h = some p) :
    ind (C.D h) * (2⁻¹ ^ min (grindBits h) 64 * esc C.D h p) ≤ εmax := by
  by_cases hD : C.D h
  · rw [ind_of hD, one_mul]
    exact (mul_le_mul_right (esc_le_eps C hr hb ha hD) _).trans (hε h)
  · rw [ind_of_not hD, zero_mul]; exact bot_le

/-- The proof-of-work factor of a fresh record after a nonce: bounded pointwise by a function of
average at most `2^-min(b, 64)`. -/
theorem rho_new_le {ℓ : Log} {t : Bytes} {cv : Digest} {n : E} (b : ℕ)
    (htn : t = digestBytes cv ++ blockOf n 4) (hpow : powIn ℓ cv n = none) :
    ∃ g : Digest → ℝ≥0∞, (∀ u, rho (ℓ ++ [(t, u)]) b cv n ≤ g u) ∧
      (∑ u, g u) / Fintype.card Digest ≤ 2⁻¹ ^ min b 64 := by
  have hne : digestBytes cv ++ blockOf 0 3 ≠ t := by
    rw [htn]; exact chain_ne_of_tag (by norm_num) (by norm_num) (by norm_num)
  rcases hb : look ℓ (digestBytes cv ++ blockOf 0 3) with _ | base
  · refine ⟨fun _ ↦ 2⁻¹ ^ min b 64, fun u ↦ ?_, avg_le_of_le fun _ ↦ le_rfl⟩
    simp only [rho, powIn, look_append_single_of_ne hne, hb, Option.bind_none, le_refl]
  · have hp : look ℓ (digestBytes base ++ blockOf n 4) = none := by
      simpa [powIn, hb] using hpow
    by_cases hx : digestBytes base ++ blockOf n 4 = t
    · refine ⟨fun u ↦ ind (powOk b n u = true), fun u ↦ ?_, powOk_avg b n⟩
      have hpt : look ℓ t = none := hx ▸ hp
      simp only [rho, powIn, look_append_single_of_ne hne, hb, Option.bind_some, hx,
        look_append_single_self hpt, le_refl]
    · refine ⟨fun _ ↦ 2⁻¹ ^ min b 64, fun u ↦ ?_, avg_le_of_le fun _ ↦ le_rfl⟩
      simp only [rho, powIn, look_append_single_of_ne hne, hb, Option.bind_some,
        look_append_single_of_ne hx, hp, le_refl]

/-- **The new record averages to at most `εmax`.** -/
theorem term_step_new (C : Cert P) {εmax : ℝ≥0∞}
    (hε : ∀ h, 2⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) {ℓ : Log} {t : Bytes}
    (ht : look ℓ t = none) :
    (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
        term C.D (ℓ ++ [(t, u)]) ((step σ P ℓ (decode σ P ℓ) t).1, u)) / Fintype.card Digest ≤
      εmax := by
  have hok := step_shapeOk (σ := σ) (P := P) ℓ t
  generalize hs : (step σ P ℓ (decode σ P ℓ) t).1 = s at hok
  cases s with
  | none =>
    simp only [term, mul_zero, Finset.sum_const_zero, ENNReal.zero_div]
    exact bot_le
  | bnd h p =>
    obtain ⟨hr, hb, ha, hg⟩ := hok
    refine avg_le_of_le fun u ↦ ?_
    have hcert := ind_mul_esc_le C hε hr hb ha
    rw [hg, min_eq_left (Nat.zero_le _), pow_zero, one_mul] at hcert
    simp only [term]
    by_cases hf : Fresh (ℓ ++ [(t, u)]) u
    · rw [ind_of hf, one_mul, gv_fresh C.D hf]; exact hcert
    · rw [ind_of_not hf, zero_mul]; exact bot_le
  | grd h p b cv n =>
    obtain ⟨hr, hb, ha, hg⟩ := hok
    obtain ⟨htn, hpow⟩ := step_grd hs
    obtain ⟨g, hg1, hg2⟩ := rho_new_le (ℓ := ℓ) b htn hpow
    have hcert := ind_mul_esc_le C hε hr hb ha
    rw [hg] at hcert
    calc (∑ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
            term C.D (ℓ ++ [(t, u)]) (Shape.grd h p b cv n, u)) / Fintype.card Digest
        ≤ (∑ u, g u * (ind (C.D h) * esc C.D h p)) / Fintype.card Digest := by
          refine ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _
          simp only [term]
          by_cases hf : Fresh (ℓ ++ [(t, u)]) u
          · rw [ind_of hf, one_mul, gv_fresh C.D hf]
            calc ind (C.D h) * (rho (ℓ ++ [(t, u)]) b cv n * esc C.D h p)
                ≤ ind (C.D h) * (g u * esc C.D h p) :=
                  mul_le_mul_right (mul_le_mul_left (hg1 u) _) _
              _ = g u * (ind (C.D h) * esc C.D h p) := by ring
          · rw [ind_of_not hf, zero_mul]; exact bot_le
      _ = ((∑ u, g u) / Fintype.card Digest) * (ind (C.D h) * esc C.D h p) := by
          rw [← Finset.sum_mul, ENNReal.mul_div_right_comm]
      _ ≤ 2⁻¹ ^ min b 64 * (ind (C.D h) * esc C.D h p) := mul_le_mul_left hg2 _
      _ = ind (C.D h) * (2⁻¹ ^ min b 64 * esc C.D h p) := by ring
      _ ≤ εmax := hcert
  | pow h p b cv n =>
    obtain ⟨hr, hb, ha, hg⟩ := hok
    have hlook := step_pow hs
    have hcert := ind_mul_esc_le C hε hr hb ha
    rw [hg] at hcert
    have hpt : ∀ u, ind (Fresh (ℓ ++ [(t, u)]) u) *
        term C.D (ℓ ++ [(t, u)]) (Shape.pow h p b cv n, u) ≤
          ind (powOk b n u = true) * (ind (C.D h) * esc C.D h p) := by
      intro u
      simp only [term]
      by_cases hf : Fresh (ℓ ++ [(t, u)]) u
      · rw [ind_of hf, one_mul]
        have hgv : gvOpt C.D (ℓ ++ [(t, u)]) (look (ℓ ++ [(t, u)])
            (digestBytes cv ++ blockOf n 4)) h p = esc C.D h p := by
          by_cases hx : digestBytes cv ++ blockOf n 4 = t
          · rw [hx, look_append_single_self ht]
            exact gv_fresh C.D hf h p
          · rw [look_append_single_of_ne hx, hlook]; rfl
        rw [hgv]
        exact le_of_eq (by ring)
      · rw [ind_of_not hf, zero_mul]; exact bot_le
    calc _ ≤ (∑ u, ind (powOk b n u = true) * (ind (C.D h) * esc C.D h p)) /
            Fintype.card Digest := ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
      _ = ((∑ u, ind (powOk b n u = true)) / Fintype.card Digest) *
            (ind (C.D h) * esc C.D h p) := by
          rw [← Finset.sum_mul, ENNReal.mul_div_right_comm]
      _ ≤ 2⁻¹ ^ min b 64 * (ind (C.D h) * esc C.D h p) := mul_le_mul_left (powOk_avg b n) _
      _ = ind (C.D h) * (2⁻¹ ^ min b 64 * esc C.D h p) := by ring
      _ ≤ εmax := hcert

/-- A capped sum grows by at most the increment. -/
theorem min_one_add_le (a ε : ℝ≥0∞) : min 1 (a + ε) ≤ min 1 a + ε := by
  rcases le_total a 1 with h | h
  · rw [min_eq_right h]; exact min_le_right _ _
  · rw [min_eq_left h]; exact (min_le_left _ _).trans le_self_add

/-- A list sum divided by a constant. -/
theorem list_sum_div {β : Type} (L : List β) (f : β → ℝ≥0∞) (c : ℝ≥0∞) :
    (L.map f).sum / c = (L.map fun x ↦ f x / c).sum := by
  simp only [div_eq_mul_inv, List.sum_map_mul_right]

/-- **The step inequality.** For every log `ℓ` and input `t` it does not answer, the average of
the potential after one fresh answer at `t` is at most the potential before it plus `εmax` plus
the bound `(4 + k)(|ℓ| + 1) / |Digest|` on the probability that the answer fails. -/
theorem step_ineq (C : Cert P) {εmax : ℝ≥0∞}
    (hε : ∀ h, 2⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax) (ℓ : Log) (t : Bytes)
    (ht : t ∉ ℓ.map Prod.fst) :
    (∑ u, pot C.D σ P (ℓ ++ [(t, u)])) / Fintype.card Digest ≤
      pot C.D σ P ℓ +
        (εmax + ((4 + σ.steps.length) * (ℓ.length + 1) : ℕ) / Fintype.card Digest) := by
  have ht' : look ℓ t = none := (logLookup_eq_none_iff ℓ t).mpr ht
  have hc : (Fintype.card Digest : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card Digest : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  by_cases hf : Fail σ ℓ
  · have h1 : pot C.D σ P ℓ = 1 := by simp only [pot, hf, ↓reduceIte]
    rw [h1]
    exact (avg_le_of_le fun u ↦ pot_le_one C.D σ P _).trans le_self_add
  have hpot : pot C.D σ P ℓ = min 1 (termSum C.D σ P ℓ) := by simp only [pot, hf, ↓reduceIte]
  set ℓ' := fun u : Digest ↦ ℓ ++ [(t, u)] with hℓ'
  set s := (step σ P ℓ (decode σ P ℓ) t).1
  -- the potential after the entry, pointwise
  have hpt : ∀ u, pot C.D σ P (ℓ' u) ≤
      ind (BadEntry σ ℓ t u) + ind (Fresh (ℓ' u) u) * min 1 (termSum C.D σ P (ℓ' u)) := by
    intro u
    by_cases hb : BadEntry σ ℓ t u
    · rw [ind_of hb]; exact (pot_le_one C.D σ P _).trans le_self_add
    · have hnf : ¬ Fail σ (ℓ' u) := by
        rw [hℓ', fail_append]; tauto
      rw [ind_of_not hb, zero_add, ind_of (fresh_of_not_bad hb), one_mul]
      simp only [pot, hnf, ↓reduceIte, le_refl]
  -- the sum of the terms after the entry, on fresh answers
  have hsum : (∑ u, ind (Fresh (ℓ' u) u) * termSum C.D σ P (ℓ' u)) / Fintype.card Digest ≤
      termSum C.D σ P ℓ + εmax := by
    have hsplit : ∀ u, ind (Fresh (ℓ' u) u) * termSum C.D σ P (ℓ' u) =
        ((decode σ P ℓ).kinds.map fun κ ↦ ind (Fresh (ℓ' u) u) * term C.D (ℓ' u) κ).sum +
          ind (Fresh (ℓ' u) u) * term C.D (ℓ' u) (s, u) := by
      intro u
      simp only [termSum, hℓ', kinds_decode_append, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, mul_add, List.sum_map_mul_left]
      rfl
    simp only [hsplit, Finset.sum_add_distrib]
    rw [ENNReal.add_div, sum_list_sum_comm, list_sum_div]
    refine add_le_add ?_ (term_step_new C hε ht')
    exact List.sum_le_sum fun κ _ ↦ term_step_old C.D ht' κ
  -- assemble
  have hfresh : (∑ u, ind (Fresh (ℓ' u) u) * min 1 (termSum C.D σ P (ℓ' u))) /
      Fintype.card Digest ≤ min 1 (termSum C.D σ P ℓ) + εmax := by
    refine (le_min ?_ ?_).trans (min_one_add_le _ _)
    · exact avg_le_of_le fun u ↦
        (mul_le_mul_left (ind_le_one _) _).trans ((one_mul _).le.trans (min_le_left _ _))
    · refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _) hsum
      exact mul_le_mul_right (min_le_right _ _) _
  have hbad := sum_badEntry_le σ ℓ t
  calc (∑ u, pot C.D σ P (ℓ ++ [(t, u)])) / Fintype.card Digest
      ≤ (∑ u, (ind (BadEntry σ ℓ t u) +
          ind (Fresh (ℓ' u) u) * min 1 (termSum C.D σ P (ℓ' u)))) / Fintype.card Digest :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hpt u) _
    _ = (∑ u, ind (BadEntry σ ℓ t u)) / Fintype.card Digest +
          (∑ u, ind (Fresh (ℓ' u) u) * min 1 (termSum C.D σ P (ℓ' u))) / Fintype.card Digest := by
        rw [Finset.sum_add_distrib, ENNReal.add_div]
    _ ≤ ((4 + σ.steps.length) * (ℓ.length + 1) : ℕ) / Fintype.card Digest +
          (min 1 (termSum C.D σ P ℓ) + εmax) :=
        add_le_add (ENNReal.div_le_div_right hbad _) hfresh
    _ = _ := by rw [hpot]; ring

end
end LeanVM.Protocol.Compile.Rom
