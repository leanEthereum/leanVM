import KeccakGkr.LayerMath

/-!
# A layer

Layer `e` (`§keccak:layer`, step 2 of `keccak:protocol`) takes a claim on the states after
`e + 1` rounds of each segment to one on the states after `e`:

1. the prover sends the product polynomial `G` (degree at most `46`), which the verifier checks
   against the claim through the projection and the round constants;
2. the verifier samples `s`;
3. sumcheck over packs and segments, `n + 1` rounds of degree `3`;
4. sumcheck over positions, `11` rounds of degree `3`;
5. the prover sends `e₀, e₁, e₂`, which the verifier checks against the sumcheck's last value;
6. the verifier samples `β`, and the next claim is `(e₀ + β e₁ + β² e₂, μ(s), fc, Lᵀ w♭)`.

The verifier carries some other data `α` along unchanged. `layer_sound`: from a false claim (or
data failing `Px`), every prover makes the next claim true (with `Px`) with probability at most
`(3n + 84) / |E|`, the annex's `(3κ + 72) / |E|` with `κ = n + 4`.
-/

open Polynomial OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (e : ℕ) {α : Type}

/-! ## A quadratic in `β` -/

/-- `u₀ + u₁ X + u₂ X²`. -/
noncomputable def quad (u : Fin 3 → E) : E[X] := C (u 0) + C (u 1) * X + C (u 2) * X ^ 2

omit [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E] in
theorem quad_eval (u : Fin 3 → E) (β : E) : (quad u).eval β = u 0 + β * u 1 + β ^ 2 * u 2 := by
  simp [quad]; ring

omit [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E] in
theorem quad_natDegree (u : Fin 3 → E) : (quad u).natDegree ≤ 2 := by
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · simp
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by norm_num))
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)

omit [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E] in
theorem quad_injective : Function.Injective (quad : (Fin 3 → E) → E[X]) := fun u v h => by
  have hc : ∀ k : ℕ, (quad u).coeff k = (quad v).coeff k := fun k => by rw [h]
  funext k
  fin_cases k
  · simpa [quad, coeff_X, coeff_X_pow] using hc 0
  · simpa [quad, coeff_X, coeff_X_pow] using hc 1
  · simpa [quad, coeff_X, coeff_X_pow] using hc 2

omit [CharP E 2] in
theorem prob_quad_le {u v : Fin 3 → E} (h : u ≠ v) :
    Pr{let β ← $ᵗ E}[u 0 + β * u 1 + β ^ 2 * u 2 = v 0 + β * v 1 + β ^ 2 * v 2] ≤
      2 / Fintype.card E := by
  have := prob_eval_eq_le (fun hq => h (quad_injective hq)) (quad_natDegree u) (quad_natDegree v)
  simpa [quad_eval] using this

/-! ## The phase -/

/-- The context of the sumcheck over packs: the carried data, the claim and `s`. -/
abbrev PackCtx (α : Type) (E : Type) (n : ℕ) := α × Claim E n × E

/-- The context of the sumcheck over positions: also the point over packs. -/
abbrev PosCtx (α : Type) (E : Type) (n : ℕ) := PackCtx α E n × (Fin (n + 1) → E)

/-- The summand over packs and segments. -/
noncomputable def packSum : Summand E (PackCtx α E n) (n + 1) 3 where
  f c := packSummand P D Q e c.2.1.r c.2.1.w c.2.2
  deg c := packSummand_deg P D Q e c.2.1.r c.2.1.w c.2.2

/-- The summand over positions. -/
noncomputable def posSum : Summand E (PosCtx α E n) 11 3 where
  f c := posSummand P D Q e c.1.2.1.r c.1.2.1.w c.1.2.2 c.2
  deg c := posSummand_deg P D Q e c.1.2.1.r c.1.2.1.w c.1.2.2 c.2

/-- Step 1's check. -/
def checkProd (st : Option (α × Claim E n)) (G : RoundPoly E 46) :
    Option (α × Claim E n × RoundPoly E 46) :=
  st.bind fun xc => if projMu xc.2.μ G.1 + rcTerm P D e xc.2.μ xc.2.r xc.2.w = xc.2.c
    then some (xc.1, xc.2, G) else none

/-- Step 5's check. -/
noncomputable def checkEvals (st : Option (PosCtx α E n × (Fin 11 → E) × E)) (ev : Fin 3 → E) :
    Option (PosCtx α E n × (Fin 11 → E) × (Fin 3 → E)) :=
  st.bind fun c => if c.2.2 = eqPoly c.1.1.2.1.r c.1.2 * mle (pad posCube c.1.1.2.1.w) c.2.1 *
      ((∑ i, μs c.1.1.2.2 i) * ev 0 + ((∑ i, μs c.1.1.2.2 i) + ev 1) * ev 2)
    then some (c.1, c.2.1, ev) else none

/-- Step 6's next claim. -/
noncomputable def nextClaim (c : PosCtx α E n × (Fin 11 → E) × (Fin 3 → E)) (β : E) :
    α × Claim E n :=
  (c.1.1.1, { c := c.2.2 0 + β * c.2.2 1 + β ^ 2 * c.2.2 2
              μ := μs c.1.1.2.2
              r := c.1.2
              w := linT P (wflat c.2.1 β) })

/-- Layer `e`: from a claim at level `e + 1` to one at level `e`. -/
noncomputable def layer : Phase (Option (α × Claim E n)) (Option (α × Claim E n)) :=
  (Phase.receive (RoundPoly E 46) (checkProd P D e) fun st =>
      match st with
      | some xc => ⟨prodTrue P D Q e xc.2.r xc.2.w, prodTrue_natDegree P D Q e _ _⟩
      | none => ⟨0, by simp⟩).comp <|
  (Phase.sample E fun st s => st.map fun c => ((c.1, c.2.1, s), c.2.2.1.eval s)).comp <|
  ((sumcheck (n + 1) (packSum P D Q e (α := α))).map fun st =>
      st.map fun c => ((c.1, c.2.1), c.2.2)).comp <|
  (sumcheck 11 (posSum P D Q e (α := α))).comp <|
  (Phase.receive (Fin 3 → E) checkEvals fun st =>
      match st with
      | some c => eTrue P D Q e c.1.1.2.2 c.1.2 c.2.1
      | none => 0).comp <|
  Phase.sample E fun st β => st.map fun c => nextClaim P c β

/-- The claim holds at level `e`, and the carried data satisfies `Px`. -/
def ClaimGood (Px : α → Prop) : Option (α × Claim E n) → Prop
  | none => False
  | some xc => Px xc.1 ∧ xc.2.Holds P D Q e

section sound

variable (Px : α → Prop)

/-- After step 1: `G` is accepted and the true product polynomial. -/
def ProdGood : Option (α × Claim E n × RoundPoly E 46) → Prop
  | none => False
  | some c => Px c.1 ∧ c.2.2.1 = prodTrue P D Q e c.2.1.r c.2.1.w

/-- After step 5: the evaluations are accepted and true. -/
def EvalsGood : Option (PosCtx α E n × (Fin 11 → E) × (Fin 3 → E)) → Prop
  | none => False
  | some c => Px c.1.1.1 ∧ c.2.2 = eTrue P D Q e c.1.1.2.2 c.1.2 c.2.1

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem total_packSum (c : PackCtx α E n) :
    (packSum P D Q e).total c = (prodTrue P D Q e c.2.1.r c.2.1.w).eval c.2.2 := by
  rw [prodTrue_eval]; rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem total_posSum (c : PosCtx α E n) :
    (posSum P D Q e).total c = (packSum P D Q e).f c.1 c.2 := sum_posSummand P D Q e _ _ _ _

theorem layer_sound :
    (layer (E := E) P D Q e (α := α)).Sound (fun st => ¬ ClaimGood P D Q (e + 1) Px st)
      (ClaimGood P D Q e Px) ((3 * n + 84) / Fintype.card E) := by
  have h1 : (Phase.receive (RoundPoly E 46) (checkProd P D e (α := α)) fun st =>
      match st with
      | some xc => ⟨prodTrue P D Q e xc.2.r xc.2.w, prodTrue_natDegree P D Q e _ _⟩
      | none => ⟨0, by simp⟩).Sound (fun st => ¬ ClaimGood P D Q (e + 1) Px st)
        (ProdGood P D Q e Px) 0 := by
    refine Phase.receive_sound fun st hst G => ?_
    rcases st with _ | ⟨x, cl⟩
    · simp [checkProd, ProdGood]
    · simp only [checkProd, Option.bind_some]
      split_ifs with hc
      · rintro ⟨hPx, hG⟩
        refine hst ⟨hPx, ?_⟩
        simp only at hG hc
        rw [Claim.Holds, ← hc, hG, proj_prodTrue]
      · simp [ProdGood]
  have h2 : (Phase.sample E fun (st : Option (α × Claim E n × RoundPoly E 46)) s =>
      st.map fun c => ((c.1, c.2.1, s), c.2.2.1.eval s)).Sound
        (fun st => ¬ ProdGood P D Q e Px st) ((packSum P D Q e).True' fun c => Px c.1)
        (46 / Fintype.card E) := by
    refine Phase.sample_sound fun st hst => ?_
    rcases st with _ | ⟨x, cl, G⟩
    · simp [Summand.True']
    · by_cases hPx : Px x
      · have hne : G.1 ≠ prodTrue P D Q e cl.r cl.w := fun h => hst ⟨hPx, h⟩
        refine le_of_eq_of_le (prEvent_congr _ _ _ fun s => ?_)
          (prob_eval_eq_le hne G.2 (prodTrue_natDegree P D Q e _ _))
        simp [Summand.True', total_packSum, hPx]
      · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun s h => ?_) zero_le
        exact hPx h.1
  have h3 : ((sumcheck (n + 1) (packSum (E := E) P D Q e (α := α))).map fun st =>
      st.map fun c => ((c.1, c.2.1), c.2.2)).Sound
        (fun st => ¬ (packSum P D Q e).True' (fun c => Px c.1) st)
        ((posSum P D Q e).True' fun c => Px c.1.1) (((n + 1 : ℕ) : ℝ≥0∞) * (3 : ℕ) / Fintype.card E) := by
    refine Phase.Sound.map ((sumcheck_sound (n + 1) (packSum P D Q e) fun c => Px c.1).mono
      (fun _ h => h) (fun st h => ?_) le_rfl)
    rcases st with _ | ⟨c, fc, v⟩
    · exact h
    · obtain ⟨hPx, hv⟩ := h
      exact ⟨hPx, hv.trans (total_posSum P D Q e (c, fc))⟩
  have h4 := sumcheck_sound 11 (posSum (E := E) P D Q e (α := α)) fun c => Px c.1.1
  have h5 : (Phase.receive (Fin 3 → E) checkEvals fun st =>
      match st with
      | some c => eTrue P D Q e c.1.1.2.2 c.1.2 c.2.1
      | none => 0).Sound (fun st => ¬ (posSum (E := E) P D Q e (α := α)).Good (fun c => Px c.1.1) st)
        (EvalsGood P D Q e Px) 0 := by
    refine Phase.receive_sound fun st hst ev => ?_
    rcases st with _ | ⟨c, fp, v⟩
    · simp [checkEvals, EvalsGood]
    · simp only [checkEvals, Option.bind_some]
      split_ifs with hc
      · rintro ⟨hPx, hev⟩
        refine hst ⟨hPx, ?_⟩
        simp only at hev hc ⊢
        rw [hc, hev]
        rfl
      · simp [EvalsGood]
  have h6 : (Phase.sample E fun (st : Option (PosCtx α E n × (Fin 11 → E) × (Fin 3 → E))) β =>
      st.map fun c => nextClaim P c β).Sound (fun st => ¬ EvalsGood P D Q e Px st)
        (ClaimGood P D Q e Px) (2 / Fintype.card E) := by
    refine Phase.sample_sound fun st hst => ?_
    rcases st with _ | ⟨c, fp, ev⟩
    · simp [ClaimGood]
    · by_cases hPx : Px c.1.1
      · have hne : ev ≠ eTrue P D Q e c.1.2.2 c.2 fp := fun h => hst ⟨hPx, h⟩
        refine le_of_eq_of_le (prEvent_congr _ _ _ fun β => ?_) (prob_quad_le hne)
        simp only [Option.map_some, ClaimGood, nextClaim, Claim.Holds, next_value]
        exact ⟨fun h => h.2, fun h => ⟨hPx, h⟩⟩
      · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun s h => ?_) zero_le
        exact hPx h.1
  refine (h1.comp (h2.comp (h3.comp (h4.comp (h5.comp h6))))).mono (fun _ h => h)
    (fun _ h => h) (le_of_eq ?_)
  simp only [ENNReal.div_eq_inv_mul, zero_add]
  push_cast
  ring

omit [Fintype E] in
theorem layer_complete :
    (layer (E := E) P D Q e (α := α)).Complete (ClaimGood P D Q (e + 1) Px)
      (ClaimGood P D Q e Px) := by
  have c1 : (Phase.receive (RoundPoly E 46) (checkProd P D e (α := α)) fun st =>
      match st with
      | some xc => ⟨prodTrue P D Q e xc.2.r xc.2.w, prodTrue_natDegree P D Q e _ _⟩
      | none => ⟨0, by simp⟩).Complete (ClaimGood P D Q (e + 1) Px) (ProdGood P D Q e Px) := by
    refine Phase.receive_complete fun st hst => ?_
    rcases st with _ | ⟨x, cl⟩
    · exact hst.elim
    · obtain ⟨hPx, hcl⟩ := hst
      simp only [checkProd, Option.bind_some]
      split_ifs with hc
      · exact ⟨hPx, rfl⟩
      · exact hc (by rw [proj_prodTrue]; exact hcl.symm)
  have c2 : (Phase.sample E fun (st : Option (α × Claim E n × RoundPoly E 46)) s =>
      st.map fun c => ((c.1, c.2.1, s), c.2.2.1.eval s)).Complete
        (ProdGood P D Q e Px) ((packSum P D Q e).True' fun c => Px c.1) := by
    refine Phase.sample_complete fun st hst s => ?_
    rcases st with _ | ⟨x, cl, G⟩
    · exact hst.elim
    · obtain ⟨hPx, hG⟩ := hst
      simp only at hPx hG
      simp [Summand.True', total_packSum, hPx, hG]
  have c3 : ((sumcheck (n + 1) (packSum (E := E) P D Q e (α := α))).map fun st =>
      st.map fun c => ((c.1, c.2.1), c.2.2)).Complete
        ((packSum P D Q e).True' fun c => Px c.1) ((posSum P D Q e).True' fun c => Px c.1.1) := by
    refine Phase.Complete.map ((sumcheck_complete (n + 1) (packSum P D Q e) fun c => Px c.1).mono
      (fun _ h => h) fun st h => ?_)
    rcases st with _ | ⟨c, fc, v⟩
    · exact h
    · obtain ⟨hPx, hv⟩ := h
      exact ⟨hPx, hv.trans (total_posSum P D Q e (c, fc)).symm⟩
  have c4 := sumcheck_complete 11 (posSum (E := E) P D Q e (α := α)) fun c => Px c.1.1
  have c5 : (Phase.receive (Fin 3 → E) checkEvals fun st =>
      match st with
      | some c => eTrue P D Q e c.1.1.2.2 c.1.2 c.2.1
      | none => 0).Complete ((posSum (E := E) P D Q e (α := α)).Good fun c => Px c.1.1)
        (EvalsGood P D Q e Px) := by
    refine Phase.receive_complete fun st hst => ?_
    rcases st with _ | ⟨c, fp, v⟩
    · exact hst.elim
    · obtain ⟨hPx, hv⟩ := hst
      simp only [checkEvals, Option.bind_some]
      split_ifs with hc
      · exact ⟨hPx, rfl⟩
      · exact hc (hv.trans (posSummand_eq P D Q e _ _ _ _ _))
  have c6 : (Phase.sample E fun (st : Option (PosCtx α E n × (Fin 11 → E) × (Fin 3 → E))) β =>
      st.map fun c => nextClaim P c β).Complete (EvalsGood P D Q e Px)
        (ClaimGood P D Q e Px) := by
    refine Phase.sample_complete fun st hst β => ?_
    rcases st with _ | ⟨c, fp, ev⟩
    · exact hst.elim
    · obtain ⟨hPx, hev⟩ := hst
      simp only at hPx hev
      refine ⟨hPx, ?_⟩
      simp only [nextClaim, Claim.Holds, next_value, hev]
  exact c1.comp (c2.comp (c3.comp (c4.comp (c5.comp c6))))

end sound

/-- The layers from level `k` down to level `0`. -/
noncomputable def layers : (k : ℕ) → Phase (Option (α × Claim E n)) (Option (α × Claim E n))
  | 0 => Phase.compute id
  | k + 1 => (layer P D Q k).comp (layers k)

theorem layers_sound (Px : α → Prop) : (k : ℕ) →
    (layers (E := E) P D Q (α := α) k).Sound (fun st => ¬ ClaimGood P D Q k Px st)
      (ClaimGood P D Q 0 Px) (k * ((3 * n + 84) / Fintype.card E))
  | 0 => (Phase.compute_sound fun _ h => h).mono (fun _ h => h) (fun _ h => h) zero_le
  | k + 1 => ((layer_sound P D Q k Px).comp (layers_sound Px k)).mono (fun _ h => h)
      (fun _ h => h) (by rw [Nat.cast_succ, add_mul, one_mul, add_comm])

omit [Fintype E] in
theorem layers_complete (Px : α → Prop) : (k : ℕ) →
    (layers (E := E) P D Q (α := α) k).Complete (ClaimGood P D Q k Px) (ClaimGood P D Q 0 Px)
  | 0 => Phase.compute_complete fun _ h => h
  | k + 1 => (layer_complete P D Q k Px).comp (layers_complete Px k)

end KeccakGkr
