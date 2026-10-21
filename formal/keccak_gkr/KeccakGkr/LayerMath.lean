import KeccakGkr.Statement
import KeccakGkr.Sumcheck

/-!
# The algebra of a layer

Layer `e` (layer `D - 1 - e` of `§keccak:layer` of `doc/leanvm`, with the segment variable of
`§keccak:segments`) turns a claim on the states after `e + 1` rounds of each segment into a claim on
the states after `e`. With `b` the state round `D m + e` applies chi to (`chiIn`), the prover's
product polynomial is `prodTrue` (equation `keccak:eq:product`), and:

* `proj_prodTrue`: its projection plus the round constants' share is the claimed value
  (equation `keccak:eq:projection`), by the embedding lemma;
* `prodTrue_eval`: its value at `s` is the sum over packs and segments of `packSummand`
  (equation `keccak:eq:at-s`);
* `sum_posSummand`: at the point `fc` the pack sumcheck ends on, that summand is the sum over
  positions of `posSummand` (equation `keccak:eq:after-packs`);
* `next_value`: the batched evaluations `e₀ + β e₁ + β² e₂` are the value of the next claim, with
  weights `linT (wflat β)` (equations `keccak:eq:flat` and step 6).
-/

open Polynomial

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (e : ℕ)

/-- The state round `D m + e` applies chi to, in segment `m` of the pack and segment `y`. -/
def chiIn (y : Cube (n + 1)) (i : Cube 4) : State :=
  P.lin.mulVec (segState P D Q (y (Fin.last n)) e i (Fin.init y))

/-- The embedding of instance `i`'s unit vector. -/
noncomputable def emb (i : Cube 4) : E[X] := embPoly (instEquiv i)

/-- The embedding of the all-ones vector. -/
noncomputable def embOnes : E[X] := ∑ i, emb i

/-- The embedding of a pack's bits at position `j`. -/
noncomputable def packPoly (y : Cube (n + 1)) (j : Pos) : E[X] :=
  ∑ i, C (ι (chiIn P D Q e y i j)) * emb i

/-- The product the embedding projects to chi's output, less the round constant. -/
noncomputable def prodPoly (y : Cube (n + 1)) (j : Pos) : E[X] :=
  embOnes * packPoly P D Q e y j +
    (embOnes + packPoly P D Q e y (along j 1)) * packPoly P D Q e y (along j 2)

/-- The honest product polynomial: equation `keccak:eq:product`. -/
noncomputable def prodTrue (r : Fin (n + 1) → E) (w : Pos → E) : E[X] :=
  ∑ y, C (eqPoly r (toPt y)) * ∑ j, C (w j) * prodPoly P D Q e y j

/-- The projection against instance weights. -/
def projMu (μ : Cube 4 → E) (G : E[X]) : E := ∑ i, μ i * projE (instEquiv i) G

/-- `eq` of a field element and a bit. -/
def eqBit (t : E) (b : Bool) : E := if b then t else 1 - t

/-- The round constants' share of a claim: the left side of `keccak:eq:projection` less the
projection. -/
def rcTerm (μ : Cube 4 → E) (r : Fin (n + 1) → E) (w : Pos → E) : E :=
  (∑ i, μ i) * ∑ m : Bool, eqBit (r (Fin.last n)) m *
    ∑ z : Slice, ι (P.rc (D * m.toNat + e) z) * w (0, z)

/-! ## The projection -/

omit [CharP E 2] in
theorem emb_natDegree (i : Cube 4) : (emb i : E[X]).natDegree ≤ 23 := embPoly_natDegree _

theorem projE_emb_mul_emb (k a b : Cube 4) :
    projE (instEquiv k) (emb a * emb b : E[X]) = if a = k ∧ b = k then 1 else 0 := by
  rw [emb, emb, rmfe]
  simp [instEquiv.injective.eq_iff]

omit [CharP E 2] in
theorem sum_sum_ite_diag {M : Type} [AddCommMonoid M] (k : Cube 4) (f : Cube 4 → Cube 4 → M) :
    ∑ a, ∑ b, (if a = k ∧ b = k then f a b else 0) = f k k := by
  rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro a _ ha; simp [ha]
  · simp

theorem projE_embOnes_mul (k : Cube 4) (u : Cube 4 → E) :
    projE (instEquiv k) (embOnes * ∑ i, C (u i) * emb i : E[X]) = u k := by
  simp only [embOnes, Finset.sum_mul, Finset.mul_sum, projE_sum]
  simp only [mul_left_comm _ (C _), projE_C_mul, projE_emb_mul_emb, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  exact sum_sum_ite_diag k fun a b => u b

theorem projE_mul (k : Cube 4) (u v : Cube 4 → E) :
    projE (instEquiv k) ((∑ i, C (u i) * emb i) * ∑ i, C (v i) * emb i : E[X]) = u k * v k := by
  simp only [Finset.sum_mul, Finset.mul_sum, projE_sum]
  simp only [show ∀ a b, (C (u a) * emb a * (C (v b) * emb b) : E[X]) =
    C (u a * v b) * (emb a * emb b) from fun a b => by rw [C_mul]; ring]
  simp only [projE_C_mul, projE_emb_mul_emb, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  exact sum_sum_ite_diag k fun a b => u a * v b

theorem projE_prodPoly (k : Cube 4) (y : Cube (n + 1)) (j : Pos) :
    projE (instEquiv k) (prodPoly P D Q e y j) = (ι (chiIn P D Q e y k j +
      (1 + chiIn P D Q e y k (along j 1)) * chiIn P D Q e y k (along j 2)) : E) := by
  simp only [prodPoly, packPoly, projE_add, add_mul, projE_embOnes_mul, projE_mul]
  simp only [map_add, map_mul, map_one]
  ring

omit [CharP E 2] in
theorem sum_cube_succ_eqPoly (r : Fin (n + 1) → E) (g : Bool → E) :
    ∑ y : Cube (n + 1), eqPoly r (toPt y) * g (y (Fin.last n)) =
      ∑ m : Bool, eqBit (r (Fin.last n)) m * g m := by
  rw [sum_cube_snoc]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Fin.snoc_init_self r]
  simp only [toPt_snoc, eqPoly_snoc, Fin.snoc_last, ← Finset.sum_mul, sum_eqPoly, one_mul]
  cases m <;> simp [eqBit, bit]

end KeccakGkr

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (e : ℕ)

theorem segState_succ (m : Bool) (i : Cube 4) (p : Cube n) :
    segState P D Q m (e + 1) i p =
      chi (P.rc (D * m.toNat + e)) (P.lin.mulVec (segState P D Q m e i p)) := rfl

/-- Equation `keccak:eq:projection`: the honest product polynomial passes the check against the
true value. -/
theorem proj_prodTrue (μ : Cube 4 → E) (r : Fin (n + 1) → E) (w : Pos → E) :
    projMu μ (prodTrue P D Q e r w) + rcTerm P D e μ r w = claimValue P D Q (e + 1) μ r w := by
  have hcore : projMu μ (prodTrue P D Q e r w) = ∑ y : Cube (n + 1), eqPoly r (toPt y) *
      ∑ i, μ i * ∑ j, w j * (ι (chiIn P D Q e y i j +
        (1 + chiIn P D Q e y i (along j 1)) * chiIn P D Q e y i (along j 2)) : E) := by
    simp only [projMu, prodTrue, projE_sum, projE_C_mul, projE_prodPoly, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hrc : rcTerm P D e μ r w = ∑ y : Cube (n + 1), eqPoly r (toPt y) *
      ∑ i, μ i * ∑ j : Pos, w j *
        (ι (if j.1 = 0 then P.rc (D * (y (Fin.last n)).toNat + e) j.2 else 0) : E) := by
    have : ∀ y : Cube (n + 1), (∑ i, μ i * ∑ j : Pos, w j *
        (ι (if j.1 = 0 then P.rc (D * (y (Fin.last n)).toNat + e) j.2 else 0) : E)) =
        (∑ i, μ i) * ∑ z : Slice, ι (P.rc (D * (y (Fin.last n)).toNat + e) z) * w (0, z) := by
      intro y
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [Fintype.sum_prod_type, Finset.sum_eq_single (0 : Lane)]
      · exact Finset.sum_congr rfl fun z _ => by simp [mul_comm]
      · intro ℓ _ hℓ; simp [hℓ]
      · simp
    simp only [this, rcTerm]
    rw [sum_cube_succ_eqPoly r (fun m => (∑ i, μ i) *
      ∑ z : Slice, ι (P.rc (D * m.toNat + e) z) * w (0, z))]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun z _ => by ring
  rw [hcore, hrc, ← Finset.sum_add_distrib, claimValue]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← map_add, segState_succ]
  rfl

omit [CharP E 2] in
theorem embOnes_natDegree : (embOnes : E[X]).natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ => emb_natDegree i

theorem packPoly_natDegree (y : Cube (n + 1)) (j : Pos) :
    (packPoly P D Q e y j : E[X]).natDegree ≤ 23 :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_C_mul_le _ _).trans (emb_natDegree i)

theorem prodTrue_natDegree (r : Fin (n + 1) → E) (w : Pos → E) :
    (prodTrue P D Q e r w).natDegree ≤ 46 := by
  refine natDegree_sum_le_of_forall_le _ _ fun y _ => (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact natDegree_mul_le.trans (add_le_add embOnes_natDegree (packPoly_natDegree P D Q e y j))
  · refine natDegree_mul_le.trans (add_le_add ?_ (packPoly_natDegree P D Q e y _))
    exact (natDegree_add_le _ _).trans (max_le embOnes_natDegree (packPoly_natDegree P D Q e y _))

/-! ## At `s` -/

/-- The instance weights `s` gives: the value of each unit embedding at `s`. -/
noncomputable def μs (s : E) (i : Cube 4) : E := (emb i).eval s

/-- A pack's bits at position `j`, embedded and evaluated at `s`. -/
noncomputable def packVal (s : E) (y : Cube (n + 1)) (j : Pos) : E :=
  ∑ i, μs s i * ι (chiIn P D Q e y i j)

/-- The summand of the sumcheck over packs and segments: equation `keccak:eq:at-s`. -/
noncomputable def packSummand (r : Fin (n + 1) → E) (w : Pos → E) (s : E)
    (z : Fin (n + 1) → E) : E :=
  eqPoly r z * ∑ j, w j * ((∑ i, μs s i) * mle (fun y => packVal P D Q e s y j) z +
    ((∑ i, μs s i) + mle (fun y => packVal P D Q e s y (along j 1)) z) *
      mle (fun y => packVal P D Q e s y (along j 2)) z)

theorem prodTrue_eval (r : Fin (n + 1) → E) (w : Pos → E) (s : E) :
    (prodTrue P D Q e r w).eval s = ∑ y : Cube (n + 1), packSummand P D Q e r w s (toPt y) := by
  have hp : ∀ y j, (packPoly P D Q e y j).eval s = packVal P D Q e s y j := fun y j => by
    simp [packPoly, packVal, μs, eval_finsetSum, mul_comm]
  simp only [prodTrue, prodPoly, packSummand, eval_finsetSum, eval_mul, eval_C, eval_add, hp,
    mle_toPt]
  simp [embOnes, eval_finsetSum, μs]

theorem packSummand_deg (r : Fin (n + 1) → E) (w : Pos → E) (s : E) :
    IndivDeg 3 (packSummand P D Q e r w s) := by
  have hj : ∀ j, IndivDeg 2 fun z => w j * ((∑ i, μs s i) * mle (fun y => packVal P D Q e s y j) z +
      ((∑ i, μs s i) + mle (fun y => packVal P D Q e s y (along j 1)) z) *
        mle (fun y => packVal P D Q e s y (along j 2)) z) := fun j => by
    refine IndivDeg.smul (w j) ?_
    have h1 : IndivDeg 2 fun z => (∑ i, μs s i) * mle (fun y => packVal P D Q e s y j) z :=
      (IndivDeg.smul _ (IndivDeg.mle _)).mono (by omega)
    have h2 := ((IndivDeg.const (n := n + 1) (∑ i, μs s i)).add
      (IndivDeg.mle (fun y => packVal P D Q e s y (along j 1)))).mul
      (IndivDeg.mle (fun y => packVal P D Q e s y (along j 2)))
    exact (h1.add h2).mono (by omega)
  exact (IndivDeg.eqPoly_right r).mul (IndivDeg.sum Finset.univ fun j _ => hj j)

end KeccakGkr

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (e : ℕ)

/-! ## Positions -/

/-- The embedded state at the positions `k` columns along, at the point `fc` of packs. -/
noncomputable def posTable (s : E) (fc : Fin (n + 1) → E) (k : ℕ) (j : Pos) : E :=
  mle (fun y => packVal P D Q e s y (along j k)) fc

/-- The summand of the sumcheck over positions. -/
noncomputable def posSummand (r : Fin (n + 1) → E) (w : Pos → E) (s : E) (fc : Fin (n + 1) → E)
    (xp : Fin 11 → E) : E :=
  eqPoly r fc * mle (pad posCube w) xp *
    ((∑ i, μs s i) * mle (pad posCube (posTable P D Q e s fc 0)) xp +
      ((∑ i, μs s i) + mle (pad posCube (posTable P D Q e s fc 1)) xp) *
        mle (pad posCube (posTable P D Q e s fc 2)) xp)

theorem along_zero (j : Pos) : along j 0 = j := by
  have : alongLane j.1 0 = j.1 := by ext; simp only [alongLane]; omega
  simp [along, this]

theorem sum_posSummand (r : Fin (n + 1) → E) (w : Pos → E) (s : E) (fc : Fin (n + 1) → E) :
    ∑ x : Cube 11, posSummand P D Q e r w s fc (toPt x) = packSummand P D Q e r w s fc := by
  simp only [posSummand, mle_toPt, mul_assoc, ← Finset.mul_sum]
  rw [sum_pad_mul]
  simp only [pad_enc posCube posCube_injective, packSummand, posTable, along_zero]

theorem posSummand_deg (r : Fin (n + 1) → E) (w : Pos → E) (s : E) (fc : Fin (n + 1) → E) :
    IndivDeg 3 (posSummand P D Q e r w s fc) := by
  have h1 : IndivDeg 2 fun xp : Fin 11 → E =>
      (∑ i, μs s i) * mle (pad posCube (posTable P D Q e s fc 0)) xp +
        ((∑ i, μs s i) + mle (pad posCube (posTable P D Q e s fc 1)) xp) *
          mle (pad posCube (posTable P D Q e s fc 2)) xp :=
    (((IndivDeg.smul _ (IndivDeg.mle _)).mono (d' := 2) (by omega)).add
      (((IndivDeg.const _).add (IndivDeg.mle _)).mul (IndivDeg.mle _))).mono (by omega)
  exact (IndivDeg.smul (eqPoly r fc) (IndivDeg.mle (pad posCube w))).mul h1

/-- The true evaluations the prover sends at the end of a layer. -/
noncomputable def eTrue (s : E) (fc : Fin (n + 1) → E) (fp : Fin 11 → E) (k : Fin 3) : E :=
  mle (pad posCube (posTable P D Q e s fc k.val)) fp

theorem posSummand_eq (r : Fin (n + 1) → E) (w : Pos → E) (s : E) (fc : Fin (n + 1) → E)
    (fp : Fin 11 → E) :
    posSummand P D Q e r w s fc fp = eqPoly r fc * mle (pad posCube w) fp *
      ((∑ i, μs s i) * eTrue P D Q e s fc fp 0 +
        ((∑ i, μs s i) + eTrue P D Q e s fc fp 1) * eTrue P D Q e s fc fp 2) := rfl

/-! ## The next claim -/

/-- The weights of the batched claim on the state chi applies to: equation `keccak:eq:flat`. -/
def wflat (fp : Fin 11 → E) (β : E) (j : Pos) : E :=
  eqPoly fp (toPt (posCube j)) + β * eqPoly fp (toPt (posCube (along j 4))) +
    β ^ 2 * eqPoly fp (toPt (posCube (along j 3)))

/-- Weights moved through the linear map: `Lᵀ w`. -/
def linT (w : Pos → E) (k : Pos) : E := ∑ j, w j * ι (P.lin j k)

theorem sum_linT_mul (w : Pos → E) (a : State) :
    ∑ k, linT P w k * (ι (a k) : E) = ∑ j, w j * ι (P.lin.mulVec a j) := by
  simp only [linT, Finset.sum_mul, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

omit [CharP E 2] in
theorem sum_along_shift (f : Pos → E) (a b : ℕ) (hab : a + b = 5) :
    ∑ j, f (along j a) = ∑ j, f j := by
  have h := (alongEquiv a (by omega)).sum_comp f
  exact h

theorem next_value (s : E) (fc : Fin (n + 1) → E) (fp : Fin 11 → E) (β : E) :
    claimValue P D Q e (μs s) fc (linT P (wflat fp β)) =
      eTrue P D Q e s fc fp 0 + β * eTrue P D Q e s fc fp 1 + β ^ 2 * eTrue P D Q e s fc fp 2 := by
  set Bt : Pos → E := fun j => mle (fun y => packVal P D Q e s y j) fc with hBt
  have h1 : claimValue P D Q e (μs s) fc (linT P (wflat fp β)) = ∑ j, wflat fp β j * Bt j := by
    simp only [claimValue, sum_linT_mul, hBt, mle, packVal, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [chiIn]
    ring
  have hshift : ∀ (a b : ℕ), a + b = 5 →
      ∑ j, eqPoly fp (toPt (posCube (along j b))) * Bt j =
        ∑ j, eqPoly fp (toPt (posCube j)) * Bt (along j a) := fun a b hab => by
    rw [← sum_along_shift (fun j => eqPoly fp (toPt (posCube (along j b))) * Bt j) a b hab]
    simp only [along_along, show a + b = 5 from hab, along_five]
  have hE : ∀ k : Fin 3, eTrue P D Q e s fc fp k =
      ∑ j, eqPoly fp (toPt (posCube j)) * Bt (along j k.val) := fun k => by
    simp only [eTrue, mle_pad, posTable, hBt]
  rw [h1, hE, hE, hE]
  simp only [wflat, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hshift 1 4 rfl, hshift 2 3 rfl]
  simp [along_zero]

end KeccakGkr
