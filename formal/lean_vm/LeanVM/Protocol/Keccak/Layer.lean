/-
  LeanVM.Protocol.Keccak.Layer

  The round-by-round soundness of one layer, `verifyKeccakLayer`: a specification from doom of
  "the claim holds of the states after the round" to doom of "the next claim holds of the states
  before it", with the escape of each challenge.
-/

module

public import LeanVM.Protocol.Keccak.LayerSum

/-!
# One layer as a specification

`verifyKeccakLayer (P + 4) step claim` (`crates/verifier/src/keccak.rs:115-196`) is `layerProg`, by
`rfl`. A candidate `q` with states `Tq q` before the round (and `afterRound (Tq q) step` after it)
is *alive*:

| after | alive | escape of the next challenge |
| --- | --- | --- |
| the start | the claim holds after the round (`ClaimTrue`) | |
| `product`, check | `product` is `G`'s coefficient list | `s`: `46/|E|` (`G` has degree `46`) |
| `s` | `product(s) = G(s)` | |
| pack rounds | `value = scale · FP acc` | each: `3/|E|` |
| position rounds | `value = FX acc` | each: `3/|E|` |
| `t`, check | `t_k = T_k` | `β`: `2/|E|` |
| `β` | the next claim holds before the round | |

The reads keep doom with the alive predicate unchanged; a check replaces it by one that, with the
check, implies it (`product_check`, `final_check`). The carried predicate `R` rides along.

`layerSpec`: lead `0`; the groups' leads are `L₀·46/|E|` (`s`), `L₀·3/|E|` (each round) and
`L₀·2/|E| + T` (`β`, then the follower's lead `T`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset Polynomial
open scoped ENNReal

@[expose] public section

/-! ## The program -/

/-- The verifier's projected value (`keccak.rs:125-132`). -/
def projectedOf (claim : KeccakClaim) (product : List E) : E :=
  sumE ((List.range productBits).map fun c ↦
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)

/-- The verifier's `iota` (`keccak.rs:133-139`). -/
def iotaOf (P step : ℕ) (claim : KeccakClaim) : E :=
  sumE ((List.range keccakSegments).map fun segment ↦
    let constant := keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0
    (eqKernel (claim.point.drop P)).getD segment 0 * sumE ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))

/-- Steps 4 (after the sumcheck) and 5 of a layer. -/
def layerTail (claim : KeccakClaim) (s : E) (res : E × E × List E) (res2 : List E × E) :
    VerifierProgram KeccakClaim :=
  VerifierProgram.readScalars 3 >>= fun t ↦
  VerifierProgram.require (res.2.1 * dot ((eqKernel res2.1).take keccakBits) claim.weights *
    (sumE (keccakInstanceWeights s) * t.getD 0 0 +
      (sumE (keccakInstanceWeights s) + t.getD 1 0) * t.getD 2 0) = res2.2) >>= fun _ ↦
  VerifierProgram.grindProofOfWork (grindingBits 2) >>= fun _ ↦
  VerifierProgram.sampleChallenge >>= fun beta ↦
  VerifierProgram.ret ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0),
      keccakInstanceWeights s,
    res.2.2, keccakLinearTranspose (batchW res2.1 beta)⟩

/-- A layer, with the tuples of the `do` block as projections. -/
def layerProg (P step : ℕ) (claim : KeccakClaim) : VerifierProgram KeccakClaim :=
  VerifierProgram.readScalars productBits >>= fun product ↦
  VerifierProgram.require (projectedOf claim product + iotaOf P step claim * sumE claim.mu =
      claim.value) >>=
    fun _ ↦
  VerifierProgram.grindProofOfWork (grindingBits (productBits - 1)) >>= fun _ ↦
  VerifierProgram.sampleChallenge >>= fun s ↦
  keccakPackRounds claim.point (polyEval product s) 1 >>= fun res ↦
  sumcheck res.1 4 (List.replicate keccakLocalBits none) >>= fun res2 ↦
  layerTail claim s res res2

theorem verifyKeccakLayer_eq (P step : ℕ) (claim : KeccakClaim) :
    verifyKeccakLayer (P + 4) step claim = layerProg P step claim := rfl

/-! ## The checks -/

/-- A claim's shape: sixteen instance weights, a (pack, segment) point, `1600` position
weights. -/
def ClaimShape (P : ℕ) (c : KeccakClaim) : Prop :=
  c.mu.length = 16 ∧ c.point.length = P + 1 ∧ c.weights.length = 1600

theorem sumE_mu {mu : List E} (h : mu.length = 16) : sumE mu = ∑ i ∈ range 16, mu.getD i 0 := by
  rw [sumE_eq_sum, list_sum_getD, h]

/-- **The product check** (eq. `keccak:eq:projection`): if `product` is `G`'s coefficient list
and the check passes, the claim holds after the round. -/
theorem product_check (T : States) (step P : ℕ) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    (product : List E)
    (hG : ∀ c < 47, product.getD c 0 = (Gpoly T P claim.point claim.weights).coeff c)
    (hc : projectedOf claim product + iotaOf P step claim * sumE claim.mu = claim.value) :
    ClaimTrue (afterRound T step) P claim := by
  rw [ClaimTrue, claimSum_round T step P _ _ _ hshape.2.1, ← hc, projectedOf,
    projected_eq claim.mu product hshape.1 _ hG, iotaOf, iota_eq step P _ _ hshape.2.1,
    sumE_mu hshape.1]

/-- **The evaluation point's escape**: a product list other than `G`'s coefficients agrees with
`G` at `46` points at most. -/
theorem s_escape {product : List E} (hlen : product.length = 47) {G : E[X]} (hG : G.natDegree ≤ 46)
    (h : ¬ ∀ c < 47, product.getD c 0 = G.coeff c) :
    avgE (fun s ↦ indE (polyEval product s = G.eval s)) ≤ errE 46 := by
  have hne : listPoly product ≠ G := by
    intro he
    refine h fun c hc ↦ ?_
    rw [← he, listPoly, finsetSum_coeff, Finset.sum_eq_single c]
    · simp
    · intro b _ hb; simp [coeff_C_mul, coeff_X_pow, Ne.symm hb]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  refine (avgE_mono fun s ↦ indE_mono fun hs ↦ ?_).trans
    (sz_escape hne ((natDegree_listPoly product).trans (by omega)) hG)
  rw [eval_listPoly]; exact hs

/-- **β's escape**: distinct triples give distinct quadratics in `β`. -/
theorem quad_escape {t0 t1 t2 a0 a1 a2 : E} (h : ¬ (t0 = a0 ∧ t1 = a1 ∧ t2 = a2)) :
    avgE (fun b ↦ indE (t0 + b * (t1 + b * t2) = a0 + b * (a1 + b * a2))) ≤ errE 2 := by
  let p : E[X] := C t0 + C t1 * X + C t2 * X ^ 2
  let q : E[X] := C a0 + C a1 * X + C a2 * X ^ 2
  have hdeg : ∀ x y z : E, (C x + C y * X + C z * X ^ 2 : E[X]).natDegree ≤ 2 := fun x y z ↦
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      ((natDegree_C _).trans_le (by norm_num)) ((natDegree_C_mul_le _ _).trans (by simp)))
      ((natDegree_C_mul_le _ _).trans (by simp))
  have hne : p ≠ q := by
    intro he
    refine h ⟨?_, ?_, ?_⟩
    · have := congrArg (coeff · 0) he; simpa [p, q] using this
    · have := congrArg (coeff · 1) he; simpa [p, q, coeff_X] using this
    · have := congrArg (coeff · 2) he; simpa [p, q, coeff_X] using this
  refine (avgE_mono fun b ↦ indE_mono fun hb ↦ ?_).trans (sz_escape hne (hdeg _ _ _) (hdeg _ _ _))
  simp only [p, q, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination hb

/-- **The final check** (eq. `keccak:eq:terminal`): with `t_k = T_k`, the check gives the
position rounds' last claim. -/
theorem final_check (T : States) (P : ℕ) (s : E) (w c L : List E) (scale value : E) (t : List E)
    (hL : L.length = 11) (hw : w.length = 1600)
    (ht : t.getD 0 0 = Tk T P s c 0 L ∧ t.getD 1 0 = Tk T P s c 1 L ∧ t.getD 2 0 = Tk T P s c 2 L)
    (hc : scale * dot ((eqKernel L).take keccakBits) w *
      (sumE (keccakInstanceWeights s) * t.getD 0 0 +
        (sumE (keccakInstanceWeights s) + t.getD 1 0) * t.getD 2 0) = value) :
    value = scale * phi T P s w c L := by
  rw [← hc, dot_weights w L hL hw, kappa_eq, ht.1, ht.2.1, ht.2.2, phi]
  ring

/-! ## The specification -/

variable {β : Type} [Finite β] {C : List Ev → Set β} {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- The tail of a layer: `t`, the final check, `β`, the next claim. -/
noncomputable def tailSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (Tq : β → States) (P : ℕ) (claim : KeccakClaim) (hshape : ClaimShape P claim) (s : E)
    (res : E × E × List E) (hres : res.2.2.length = P + 1) (res2 : List E × E)
    (hres2 : res2.1.length = 11)
    (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    Spec (layerTail claim s res res2)
      (Doomed C (fun q ↦ res2.2 = res.2.1 * phi (Tq q) P s claim.weights res.2.2 res2.1 ∧ R q))
      (fun c h ↦ ClaimShape P c ∧ Doomed C (fun q ↦ ClaimTrue (Tq q) P c ∧ R q) h) εmax 0 T :=
  (doomReadN (T := if grindingBits 2 = 0 then (L₀ : ℝ≥0∞) * errE 2 + T else 0) hst _
    (grindLead_le' _ hβ) 2).bind' fun t ↦
    (Spec.require (Pre := fun h ↦ t.length = 2 + 1 ∧ Doomed C (fun q ↦ res2.2 =
        res.2.1 * phi (Tq q) P s claim.weights res.2.2 res2.1 ∧ R q) h)
      (Post := fun _ h ↦ Doomed C (fun q ↦ (t.getD 0 0 = Tk (Tq q) P s res.2.2 0 res2.1 ∧
        t.getD 1 0 = Tk (Tq q) P s res.2.2 1 res2.1 ∧
        t.getD 2 0 = Tk (Tq q) P s res.2.2 2 res2.1) ∧ R q) h)
      fun _ hpre hc ↦ Doomed.mono hpre.2 fun q ⟨ht, hR⟩ ↦
        ⟨final_check (Tq q) P s claim.weights res.2.2 res2.1 res.2.1 res2.2 t hres2
          hshape.2.2 ht hc, hR⟩).bind' fun _ ↦
      ((doomGrind hst _ True (grindingBits 2) (discount_le _ hβ)).mono (fun _ h ↦ ⟨trivial, h⟩)
        (fun _ _ h ↦ h.2) le_rfl le_rfl le_rfl).bind' fun _ ↦
      (doomSample (εmax := εmax) (T := T) hst hcard _
        (fun b q ↦ t.getD 0 0 + b * (t.getD 1 0 + b * t.getD 2 0) =
          Tk (Tq q) P s res.2.2 0 res2.1 + b * (Tk (Tq q) P s res.2.2 1 res2.1 +
            b * Tk (Tq q) P s res.2.2 2 res2.1) ∧ R q) (errE 2)
        fun q hq ↦ by
          by_cases hR : R q
          · exact (avgE_mono fun b ↦ indE_mono fun hb ↦ hb.1).trans
              (quad_escape fun h ↦ hq ⟨h, hR⟩)
          · exact (avgE_mono fun b ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
              ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)).bind' fun b ↦
        (Spec.ret _).mono (fun h hd ↦ ⟨⟨keccakInstanceWeights_length s, hres,
            keccakLinearTranspose_length _⟩,
          Doomed.mono hd fun q ⟨htrue, hR⟩ ↦
            ⟨htrue.trans (batch_eq (Tq q) P s res.2.2 res2.1 hres2 b).symm, hR⟩⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **One layer** (`verify_layer`, `keccak.rs:115-196`): from doom of "the claim
holds of the states after the round" to doom of "the next claim holds of the states before it",
a claim of the same shape. Lead `0`; the evaluation point's group `L₀·46/|E|`, each sumcheck
round's `L₀·3/|E|`, `β`'s `L₀·2/|E|` plus the follower's lead `T`. -/
noncomputable def layerSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (R : β → Prop)
    (Tq : β → States) (step P : ℕ) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    (h46 : (2 : ℝ≥0∞)⁻¹ ^ grindingBits (productBits - 1) * ((L₀ : ℝ≥0∞) * errE 46) ≤ εmax)
    (h3 : (L₀ : ℝ≥0∞) * errE 3 ≤ εmax) (hβ : (L₀ : ℝ≥0∞) * errE 2 + T ≤ εmax) :
    Spec (verifyKeccakLayer (P + 4) step claim)
      (Doomed C (fun q ↦ ClaimTrue (afterRound (Tq q) step) P claim ∧ R q))
      (fun c h ↦ ClaimShape P c ∧ Doomed C (fun q ↦ ClaimTrue (Tq q) P c ∧ R q) h) εmax 0 T :=
  have h3 : (L₀ : ℝ≥0∞) * errE 3 + 0 ≤ εmax := by rw [add_zero]; exact h3
  have h0 : (0 : ℝ≥0∞) ≤ εmax := zero_le
  have hb : grindingBits (productBits - 1) ≠ 0 := by rw [grindingBits_product]; norm_num
  Spec.congr (verifyKeccakLayer_eq P step claim).symm <|
  (doomReadN (T := 0) hst _ h0 46).bind' fun product ↦
  (Spec.require
    (Pre := fun h ↦ product.length = 46 + 1 ∧
      Doomed C (fun q ↦ ClaimTrue (afterRound (Tq q) step) P claim ∧ R q) h)
    (Post := fun _ h ↦ product.length = 47 ∧ Doomed C (fun q ↦ (∀ c < 47, product.getD c 0 =
      (Gpoly (Tq q) P claim.point claim.weights).coeff c) ∧ R q) h)
    fun _ hpre hc ↦ ⟨hpre.1, Doomed.mono hpre.2 fun q ⟨hG, hR⟩ ↦
      ⟨product_check (Tq q) step P claim hshape product hG hc, hR⟩⟩).bind' fun _ ↦
  ((doomGrind (T := (L₀ : ℝ≥0∞) * errE 46 + 0) hst _ (product.length = 47)
    (grindingBits (productBits - 1)) (by rw [add_zero]; exact h46)).mono (fun _ h ↦ h)
    (fun _ _ h ↦ h) le_rfl (by simp [hb]) le_rfl).bind' fun _ ↦
  if hlen : product.length = 47 then
    ((doomSample (εmax := εmax) (T := 0) hst hcard _
      (fun s q ↦ polyEval product s = (Gpoly (Tq q) P claim.point claim.weights).eval s ∧ R q)
      (errE 46) fun q hq ↦ by
        by_cases hR : R q
        · exact (avgE_mono fun s ↦ indE_mono fun hs ↦ hs.1).trans
            (s_escape hlen (natDegree_Gpoly _ _ _ _) fun h ↦ hq ⟨h, hR⟩)
        · exact (avgE_mono fun s ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
            ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)).mono
      (fun _ h ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun s ↦
    ((packSpec (T := 0) hst hcard R (FP_eqFamily P s claim.weights Tq claim.point hshape.2.1)
      le_rfl h0 h3 claim.point [] (polyEval product s) 1 rfl).mono
      (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, hR⟩ ↦ ⟨by
        rw [hv, one_mul, FP_nil], hR⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res ↦
    if hres : res.2.2.length = P + 1 then
      ((sumcheckSpec (T := 0) hst hcard R
        (FX_plainFamily P s claim.weights Tq res.2.2 res.2.1) (count := 4) (by norm_num)
        (by norm_num) h0 h3 11 [] res.1 (by simp)).mono
        (fun _ (hd : res.2.2.length = claim.point.length ∧ Doomed C _ _) ↦ Doomed.mono hd.2
          fun q ⟨hv, hR⟩ ↦ ⟨by
            rw [hv, FX_nil, List.nil_append, FP_full _ _ _ _ _ _ hshape.2.1 hres], hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res2 ↦
      if hres2 : res2.1.length = 11 then
        (tailSpec hst hcard R Tq P claim hshape s res hres res2 hres2 hβ).mono
          (fun _ (hd : res2.1.length = 11 ∧ Doomed C _ _) ↦ Doomed.mono hd.2 fun q ⟨hv, hR⟩ ↦
            ⟨by rw [hv, List.nil_append, FX_full _ _ _ _ _ _ _ hres2], hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h ↦ hres2 h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h ↦ hres (h.1.trans hshape.2.1)) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl
  else Spec.dead.mono (fun _ h ↦ hlen h.1) (fun _ _ h ↦ h) le_rfl zero_le le_rfl

end
end LeanVM.Protocol.KeccakGkr
