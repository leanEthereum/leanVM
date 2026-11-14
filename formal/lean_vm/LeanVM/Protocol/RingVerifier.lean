/-
  LeanVM.Protocol.RingVerifier

  The statement's ring switching (`ringSwitch` of `Statement/LeanVmVerifier.lean`) on
  `RingMap`'s definitions: the same map, target, coefficients and weight, and the bad challenges
  of the sixteen it draws counted as one group.
-/

module

public import LeanVM.Protocol.RingMap
public import Statement.LeanVmVerifier

/-!
# The verifier's ring switching

`LeanVM.Protocol.Verifier.ringSwitch point s` (`crates/verifier/src/ring_switch.rs` at
leanVM) grinds `batchGrindingBits`, draws sixteen challenges, `f` the first eight and `g`
the last eight, and returns the target and the weight. Its helpers transcribe the Rust as
`RingMap`'s do, `frobenius8` by a power rather than by squarings:

* `verifier_frobenius8`, `verifier_ringPsi`, `verifier_polyEval`, `verifier_gen`: the helpers are
  `RingMap`'s;
* `verifier_ringTarget`, `verifier_ringCoefficients`: so are the target and the coefficients;
* `verifier_ringWeight`: the weight at points of `μ` coordinates is
  `Σ_k c_k eq(r^(2^k), r')` (`idxSum`), the extension `ringWeight_mle` computes;
* `ringSwitch_eq`: the program is the grind, the sixteen challenges, and `RingMap`'s target and
  coefficients at their halves;
* `card_ringBad_le`, `ringBad_ratio_le`: slice claims `s ≠ z` meet the honest value
  `Σ_i x^i Φ(z_i)` at no more than `2·|E|^15` of the `|E|^16` challenge lists, a fraction
  `2/|E|`. The bound holds for the sixteen jointly, not per challenge (`f` is drawn before `g`),
  so the specification charges them as one group.
-/

namespace LeanVM.Protocol.Ring

open LeanVM.Parameters Finset
open scoped ENNReal

@[expose] public section

/-! ## The helpers -/

theorem verifier_ringMapWidth : Verifier.ringMapWidth = ringMapWidth := rfl

theorem verifier_frobenius8 : (Verifier.frobenius8 : E → ℕ → E) = frobenius8 := by
  funext v p
  rw [frobenius8_eq]
  rfl

theorem verifier_ringPsi : (Verifier.ringPsi : E → List E → E) = ringPsi := rfl

theorem verifier_polyEval : (Verifier.polyEval : List E → E → E) = hornerEval := rfl

theorem verifier_gen : Verifier.gen = genE := rfl

/-- The statement's target is `RingMap`'s. -/
theorem verifier_ringTarget : (Verifier.ringTarget : List E → List E → List E → E) = ringTarget := by
  funext s f g
  unfold Verifier.ringTarget ringTarget
  rw [verifier_frobenius8, verifier_ringPsi, verifier_polyEval, verifier_gen,
    verifier_ringMapWidth]

/-- The statement's coefficients are `RingMap`'s. -/
theorem verifier_ringCoefficients :
    (Verifier.ringCoefficients : List E → List E → List E) = ringCoefficients := by
  funext f g
  unfold Verifier.ringCoefficients ringCoefficients
  rw [verifier_frobenius8]

/-! ## The weight -/

/-- `eq_eval` is the product of the zipped factors. -/
theorem eqEval_eq_prod (l r : List E) :
    Verifier.eqEval l r = (List.zipWith (fun x z ↦ 1 + x + z) l r).prod := by
  rw [Verifier.eqEval, List.prod_eq_foldl]

/-- `eq_eval` at two points of `μ` coordinates is `eqP`. -/
theorem eqEval_ofFn {μ : ℕ} (a b : Fin μ → E) :
    Verifier.eqEval (List.ofFn a) (List.ofFn b) = eqP a b := by
  rw [eqEval_eq_prod, eqP, ← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The weight's inner fold is `eq_eval` times its start. -/
theorem foldl_zip_eqEval (c : E) : ∀ (r y : List E),
    (List.zip r y).foldl (fun product (p : E × E) ↦ product * (1 + p.1 + p.2)) c =
      c * Verifier.eqEval r y
  | [], _ => by simp [eqEval_eq_prod]
  | _ :: _, [] => by simp [eqEval_eq_prod]
  | a :: r, b :: y => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_eqEval _ r y, eqEval_eq_prod,
      eqEval_eq_prod, List.zipWith_cons_cons, List.prod_cons]
    ring

/-- The weight's outer fold from any start. -/
theorem ringWeight_fold (y : List E) :
    ∀ (cs : List E) (a : E) (r : List E),
      (cs.foldl (fun (acc : E × List E) c ↦
        ((acc.1 + (List.zip acc.2 y).foldl (fun product (p : E × E) ↦
          product * (1 + p.1 + p.2)) c), acc.2.map fun value ↦ value * value)) (a, r)).1 =
        a + idxSum cs fun k ↦ Verifier.eqEval (r.map (· ^ 2 ^ k)) y
  | [], a, r => by simp [idxSum]
  | c :: cs, a, r => by
    rw [List.foldl_cons]
    dsimp only
    rw [ringWeight_fold y cs, foldl_zip_eqEval, idxSum]
    have e : ((fun x : E ↦ x ^ 2 ^ 0) = id) := by funext x; simp
    have e' : ∀ k : ℕ, ((fun x : E ↦ x ^ 2 ^ k) ∘ fun value ↦ value * value) =
        fun x ↦ x ^ 2 ^ (k + 1) := fun k ↦ by
      funext x
      simp only [Function.comp]
      rw [← sq, ← pow_mul, pow_succ 2 k, mul_comm]
    simp only [List.map_map, e, List.map_id, e']
    ring

/-- **The statement's weight** at points of `μ` coordinates is `Σ_k c_k eq(r^(2^k), r')`. -/
theorem verifier_ringWeight {μ : ℕ} (r r' : Fin μ → E) (cs : List E) :
    Verifier.ringWeight (List.ofFn r) (List.ofFn r') cs =
      idxSum cs fun k ↦ eqP (frobPt r k) r' := by
  rw [Verifier.ringWeight, ringWeight_fold, zero_add]
  congr 1
  funext k
  rw [List.map_ofFn, ← eqEval_ofFn]
  rfl

/-! ## The program -/

/-- **The statement's ring switching** is the grind, the sixteen challenges, and `RingMap`'s
target and coefficients at their two halves. -/
theorem ringSwitch_eq (point s : List E) :
    Verifier.ringSwitch point s =
      (Compile.VerifierProgram.grindProofOfWork Whir.batchGrindingBits).bind fun _ ↦
        (Compile.VerifierProgram.sampleChallenges 16).bind fun ch ↦
          Compile.VerifierProgram.ret (ringTarget s (ch.take 8) (ch.drop 8),
            fun r' ↦ Verifier.ringWeight point r' (ringCoefficients (ch.take 8) (ch.drop 8))) := by
  rw [Verifier.ringSwitch, ← verifier_ringTarget, ← verifier_ringCoefficients]
  rfl

/-! ## The bad challenges -/

/-- The challenges' halves of a list of sixteen: `f_p = ch_p`, `g_b = ch_(8 + b)`. -/
def fOf (ch : List E) : Fin 8 → E := fun p ↦ ch.getD p 0

/-- The second half of a challenge list. -/
def gOf (ch : List E) : Fin 8 → E := fun b ↦ ch.getD (8 + b) 0

/-- **The bad challenges** for slice claims `sv` against the true slices `z`: the target meets the
honest value `Σ_i x^i Φ(z_i)` of the drawn map. -/
def RingBad (sv : List E) (z : Fin 64 → E) (ch : List E) : Prop :=
  ringTarget sv (ch.take 8) (ch.drop 8) = ∑ i : Fin 64, ringW i * frobPhi 8 (fOf ch) (gOf ch) (z i)

theorem take_ofFn_append (a b : Fin 8 → E) : (List.ofFn (Fin.append a b : Fin 16 → E)).take 8 = List.ofFn a := by
  rw [List.ofFn_fin_append, List.take_left' (by simp)]

theorem drop_ofFn_append (a b : Fin 8 → E) : (List.ofFn (Fin.append a b : Fin 16 → E)).drop 8 = List.ofFn b := by
  rw [List.ofFn_fin_append, List.drop_left' (by simp)]

theorem fOf_append (a b : Fin 8 → E) : fOf (List.ofFn (Fin.append a b : Fin 16 → E)) = a := by
  funext p
  rw [fOf, List.ofFn_fin_append, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp),
    List.getElem?_ofFn]
  simp

theorem gOf_append (a b : Fin 8 → E) : gOf (List.ofFn (Fin.append a b : Fin 16 → E)) = b := by
  funext p
  rw [gOf, List.ofFn_fin_append, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp), List.getElem?_ofFn]
  simp

/-- A list of sixteen challenges is its two halves. -/
theorem take_eq_ofFn_fOf {ch : List E} (h : ch.length = 16) : ch.take 8 = List.ofFn (fOf ch) := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_ofFn, fOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h2; omega), Option.getD_some]

theorem drop_eq_ofFn_gOf {ch : List E} (h : ch.length = 16) : ch.drop 8 = List.ofFn (gOf ch) := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.getElem_drop, List.getElem_ofFn, gOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h2; omega), Option.getD_some]

/-- **The bad event at a list of sixteen**: the target at its halves meets the honest value. -/
theorem ringBad_iff {sv : List E} {z : Fin 64 → E} {ch : List E} (h : ch.length = 16) :
    RingBad sv z ch ↔ ringTarget sv (List.ofFn (fOf ch)) (List.ofFn (gOf ch)) =
      ∑ i : Fin 64, ringW i * frobPhi 8 (fOf ch) (gOf ch) (z i) := by
  rw [RingBad, take_eq_ofFn_fOf h, drop_eq_ofFn_gOf h]

open Classical in
/-- **The bad challenge lists are few**: for slice claims `s ≠ z`, at most `2·|E|^15` of the
`|E|^16` lists. -/
theorem card_ringBad_le {s z : Fin 64 → E} (h : s ≠ z) :
    (univ.filter fun v : Fin 16 → E ↦ RingBad (List.ofFn s) z (List.ofFn v)).card ≤
      2 * Fintype.card E ^ 15 := by
  have hc := card_ringTarget_bad_le (z := z) h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card] at hc
  refine Eq.trans_le ?_ hc
  refine Finset.card_equiv (Fin.appendEquiv 8 8).symm fun v ↦ ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := (Fin.appendEquiv 8 8).surjective v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  show RingBad (List.ofFn s) z (List.ofFn (Fin.append a b : Fin 16 → E)) ↔ _
  rw [RingBad, take_ofFn_append, drop_ofFn_append, fOf_append, gOf_append, Equiv.symm_apply_apply]

/-- `|E|⁻¹^16 · 2|E|^15 = 2/|E|`. -/
theorem ringBad_pow_eq : (Fintype.card E : ℝ≥0∞)⁻¹ ^ 16 * ((2 * Fintype.card E ^ 15 : ℕ) : ℝ≥0∞) =
    2 / (Fintype.card E : ℝ≥0∞) := by
  have hE : (Fintype.card E : ℝ≥0∞) ≠ 0 := by simp
  have hT : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  push_cast
  rw [ENNReal.div_eq_inv_mul, pow_succ, mul_comm 2, ← mul_assoc, mul_assoc _ _ (_ ^ 15),
    mul_comm (Fintype.card E : ℝ≥0∞)⁻¹ (_ ^ 15), ← mul_assoc, ← mul_pow,
    ENNReal.inv_mul_cancel hE hT, one_pow, one_mul, mul_comm]

open Classical in
/-- **Ring switching's group escape**: for slice claims `s ≠ z`, the average over the sixteen
challenges of the bad event is at most `2/|E|`. -/
theorem ringBad_ratio_le {s z : Fin 64 → E} (h : s ≠ z) :
    (Fintype.card E : ℝ≥0∞)⁻¹ ^ 16 *
        ∑ v : Fin 16 → E, (if RingBad (List.ofFn s) z (List.ofFn v) then 1 else 0 : ℝ≥0∞) ≤
      2 / (Fintype.card E : ℝ≥0∞) := by
  rw [Finset.sum_boole, ← ringBad_pow_eq]
  gcongr
  exact_mod_cast card_ringBad_le h

end
end LeanVM.Protocol.Ring
