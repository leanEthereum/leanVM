/-
  LeanVM.Protocol.EndToEnd.Front.RingFidelity

  The program's ring switching computes ArkLib's: its staged map, its target and the pairing of
  its weight with the stack, given the layout's reading of the Flock region.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.RingSwitch

/-!
# The fidelity of ring switching

The program (`_phi`, `_ring_weight`, `ring_switch`, `verifier.py:1304-1340` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) against ArkLib's ring switching
(`ToArkLib/Flock/RingSwitch.lean`):

* `phiMap_eq`: the program's `Φ`, a fold over the six coefficients with shifts
  `32, 16, 8, 4, 2, 1`, is ArkLib's staged map `frobMap (ringStages 5 fs)`;
* `target_eq`: the target `poly_eval([Φ(s_i)], GEN)` is ArkLib's `Σ_i g^i Φ(s_i)`;
* `ringWeight_eq`: the program's weight is `Σ_k c_k eq(r^(2^k), ·)`;
* `ringCoefficients_sum`: the program's coefficients `c_k`, computed in closed form, are the
  coefficients of ArkLib's Frobenius terms (`frobTerms`), a computation over the six coefficients
  (each `c_k` is the product, over the stages whose shift is a bit of `k`, of the stage's
  coefficient to the power `2^(k mod shift)`);
* `ringFaithful`: hence, with the layout's reading of the region (`ringLayoutHyp`), the program's
  ring claim holding of a candidate is ArkLib's switched claim holding of its reading.

No mismatch.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

/-! ## Horner, folds and products -/

/-- Horner's rule is the sum of the coefficients times the powers. -/
theorem polyEval_eq_sum (l : List E) (x : E) :
    LeanVM.Protocol.Verifier.polyEval l x =
      ∑ i ∈ Finset.range l.length, l.getD i 0 * x ^ i := by
  induction l with
  | nil => simp [LeanVM.Protocol.Verifier.polyEval]
  | cons a l ih =>
    have h : LeanVM.Protocol.Verifier.polyEval (a :: l) x =
        LeanVM.Protocol.Verifier.polyEval l x * x + a := rfl
    rw [h, ih, List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    have e : ∀ i ∈ Finset.range l.length,
        l.getD i 0 * x ^ i * x = (a :: l).getD (i + 1) 0 * x ^ (i + 1) := fun i _ ↦ by
      simp only [List.getD_cons_succ, pow_succ, mul_assoc]
    rw [Finset.sum_congr rfl e]
    simp

/-- A fold multiplying by a function of each entry is the product. -/
theorem foldl_mul_map {α : Type} (f : α → E) (c : E) (l : List α) :
    l.foldl (fun p a ↦ p * f a) c = c * (l.map f).prod := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- Mapping over a zip is zipping with. -/
theorem map_zip_eq_zipWith {α β γ : Type} (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), (List.zip l₁ l₂).map (fun p ↦ f p.1 p.2) = List.zipWith f l₁ l₂
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l₁, b :: l₂ => by
    rw [List.zip_cons_cons, List.map_cons, map_zip_eq_zipWith f l₁ l₂, List.zipWith_cons_cons]

/-- The program's product over a pair of points is the equality kernel `eq_eval`. -/
theorem foldl_zip_eq_eqEval (c : E) (r y : List E) :
    (List.zip r y).foldl (fun product (p : E × E) ↦ product * (1 + p.1 + p.2)) c =
      c * LeanVM.Protocol.Verifier.eqEval r y := by
  rw [foldl_mul_map (fun p : E × E ↦ 1 + p.1 + p.2), LeanVM.Protocol.Verifier.eqEval,
    foldl_mul_eq, one_mul, map_zip_eq_zipWith (fun x z : E ↦ 1 + x + z)]

/-- The weight fold from any start: the start plus `Σ_k c_k eq(r^(2^k), y)`. -/
theorem ringWeight_fold (y : List E) :
    ∀ (cs : List E) (a : E) (r : List E),
      (cs.foldl (fun (acc : E × List E) c ↦
        ((acc.1 + (List.zip acc.2 y).foldl (fun product (p : E × E) ↦
          product * (1 + p.1 + p.2)) c), acc.2.map (· ^ 2))) (a, r)).1 =
        a + ∑ k ∈ Finset.range cs.length,
          cs.getD k 0 * LeanVM.Protocol.Verifier.eqEval (r.map (· ^ 2 ^ k)) y
  | [], a, r => by simp
  | c :: cs, a, r => by
    rw [List.foldl_cons]
    simp only []
    rw [ringWeight_fold y cs, foldl_zip_eq_eqEval, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, pow_one, List.map_map]
    have e : ∀ k ∈ Finset.range cs.length,
        cs.getD k 0 * LeanVM.Protocol.Verifier.eqEval
          (List.map ((fun x ↦ x ^ 2 ^ k) ∘ fun x ↦ x ^ 2) r) y =
        cs.getD k 0 * LeanVM.Protocol.Verifier.eqEval (List.map (fun x ↦ x ^ 2 ^ (k + 1)) r) y :=
      fun k _ ↦ by
        have : ((fun x : E ↦ x ^ 2 ^ k) ∘ fun x ↦ x ^ 2) = fun x ↦ x ^ 2 ^ (k + 1) := by
          funext b
          simp only [Function.comp, pow_succ, pow_mul]
          ring
        rw [this]
    rw [Finset.sum_congr rfl e]
    simp only [List.map_id']
    ring

/-- **The program's weight is `Σ_k c_k eq(r^(2^k), ·)`.** -/
theorem ringWeight_eq (r y cs : List E) :
    LeanVM.Protocol.Verifier.ringWeight r y cs =
      ∑ k ∈ Finset.range cs.length,
        cs.getD k 0 * LeanVM.Protocol.Verifier.eqEval (r.map (· ^ 2 ^ k)) y := by
  rw [LeanVM.Protocol.Verifier.ringWeight]
  exact (ringWeight_fold y cs 0 r).trans (zero_add _)

/-! ## The staged map and its coefficients -/

/-- **The program's `Φ` is ArkLib's staged map**: the stages in order, shifts `32, …, 1`. -/
theorem phiMap_eq (a : E) {ch : List E} (h : ch.length = 6) :
    LeanVM.Protocol.Verifier.phiMap a ch = frobMap (Flock.ringStages 5 (toVec 6 ch)) a := by
  match ch, h with
  | [f0, f1, f2, f3, f4, f5], _ =>
    simp [LeanVM.Protocol.Verifier.phiMap, LeanVM.Protocol.Verifier.ringMapShifts,
      Flock.ringShifts, frobMap, Flock.ringStages, List.ofFn_succ, toVec]

set_option maxHeartbeats 4000000 in
/-- The coefficient identity over six named coefficients. -/
theorem ringCoefficients_sum6 (f0 f1 f2 f3 f4 f5 : E) (F : ℕ → E) :
    ∑ k ∈ Finset.range 64,
        (LeanVM.Protocol.Verifier.ringCoefficients [f0, f1, f2, f3, f4, f5]).getD k 0 * F k =
      ((frobTerms (Flock.ringStages 5 (toVec 6 [f0, f1, f2, f3, f4, f5]))).map
        fun t ↦ t.1 * F t.2).sum := by
  simp only [LeanVM.Protocol.Verifier.ringCoefficients, LeanVM.Protocol.Verifier.ringMapShifts,
    Flock.ringShifts, LeanVM.Protocol.Verifier.kBits, Vector.toList_mk, List.zip_cons_cons,
    List.zip_nil_right]
  simp [frobTerms, Flock.ringStages, List.ofFn_succ, toVec, Finset.sum_range_succ, List.filter]
  ring

/-- **The program's coefficients are ArkLib's Frobenius terms'**: for any function of the
exponent, `Σ_{k < 64} c_k F(k)` over the program's closed form is the sum over ArkLib's terms. A
computation over the six coefficients. -/
theorem ringCoefficients_sum {ch : List E} (h : ch.length = 6) (F : ℕ → E) :
    ∑ k ∈ Finset.range 64, (LeanVM.Protocol.Verifier.ringCoefficients ch).getD k 0 * F k =
      ((frobTerms (Flock.ringStages 5 (toVec 6 ch))).map fun t ↦ t.1 * F t.2).sum := by
  match ch, h with
  | [f0, f1, f2, f3, f4, f5], _ => exact ringCoefficients_sum6 f0 f1 f2 f3 f4 f5 F

/-- The program's coefficients are sixty-four. -/
theorem length_ringCoefficients (ch : List E) :
    (LeanVM.Protocol.Verifier.ringCoefficients ch).length = 64 := by
  simp [LeanVM.Protocol.Verifier.ringCoefficients, LeanVM.Protocol.Verifier.kBits]

/-- `GEN` is the generator `g` of `K`, embedded. -/
theorem gen_eq : LeanVM.Protocol.Verifier.gen = algebraMap K E g := rfl

/-- ArkLib's target as a sum over the slices' list. -/
theorem ringTarget_eq_sum (P : Flock.Params E) (fs : Vector E 6) (sv : List E)
    (hsv : sv.length = 2 ^ P.s) :
    Flock.ringTarget P 5 (algebraMap K E) g (toVec (2 ^ P.s) sv) fs =
      ∑ i ∈ Finset.range sv.length,
        algebraMap K E (g ^ i) * frobMap (Flock.ringStages 5 fs) (sv.getD i 0) := by
  unfold Flock.ringTarget
  have h : ∀ i : Fin (2 ^ P.s), (toVec (2 ^ P.s) sv)[i] = sv.getD i 0 := fun i ↦ by
    simp [toVec]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ algebraMap K E (g ^ i) *
    frobMap (Flock.ringStages 5 fs) (sv.getD i 0)), hsv]

/-- **The program's target is ArkLib's**: `poly_eval([Φ(s_i)], GEN) = Σ_i g^i Φ(s_i)`. -/
theorem target_eq {sv ch : List E} (hsv : sv.length = 64) (hch : ch.length = 6)
    (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes) :
    LeanVM.Protocol.Verifier.polyEval (sv.map (LeanVM.Protocol.Verifier.phiMap · ch))
        LeanVM.Protocol.Verifier.gen = arkTarget F prog s sv ch := by
  unfold arkTarget
  rw [ringTarget_eq_sum _ _ _ hsv, polyEval_eq_sum, List.length_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i < sv.length := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, phiMap_eq _ hch, gen_eq, ← map_pow, mul_comm,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

/-! ## The weight -/

/-- Raising a point read off a list is reading the raised list. -/
theorem frobPoint_toVec (n e : ℕ) (pt : List E) :
    frobPoint e (toVec n pt) = toVec n (pt.map (· ^ 2 ^ e)) := by
  apply Vector.ext
  intro i hi
  simp only [frobPoint_getElem, toVec, Vector.getElem_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases pt[i]? with
  | none => simp
  | some a => simp

section Weight

variable (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
  (layout : LeanVM.Protocol.Verifier.Layout)
  (toI : Column layout.stackLog → Column (fI F prog s).μ)

/-- **What ring switching needs of the layout** (bridge A): the program's weight of the `QFLOCK`
placement at a point of the region, `eqAbove · eq(p, ·)`, paired with a candidate, is the
extension of its reading at the point lifted by the instance's layout (`FlockPhase.lift`). -/
def ringLayoutHyp : Prop :=
  ∀ (p : List E), p.length = (fP F prog s).m + (fP F prog s).κ → ∀ q : Column layout.stackLog,
    ∑ x : Fin (2 ^ layout.stackLog),
      ((layout.placements.getD LeanVM.Protocol.Verifier.qflock default).eqAbove
          (boolPoint layout.stackLog x) *
        LeanVM.Protocol.Verifier.eqEval p ((boolPoint layout.stackLog x).take
          (layout.placements.getD LeanVM.Protocol.Verifier.qflock default).vars)) *
        ofK (q.values.getD x 0) =
      eval₂Mle (toI q).values (algebraMap K E) (FlockPhase.lift (fR F prog s) (toVec _ p))

/-- ArkLib's switched weight paired with a stack: the Frobenius terms of the point's lifts. -/
theorem pair_arkWeight (pt ch : List E) (q : Column (fI F prog s).μ) :
    (arkWeight F prog s pt ch).pair (algebraMap K E) q.values =
      ((frobTerms (Flock.ringStages 5 (toVec 6 ch))).map fun t ↦ t.1 *
        eval₂Mle q.values (algebraMap K E) (FlockPhase.lift (fR F prog s)
          (toVec _ (pt.map (· ^ 2 ^ t.2))))).sum := by
  unfold arkWeight Flock.ringWeight
  rw [Weight.pair_combine, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ ↦ ?_)
  simp only [Function.comp, Weight.pair_eqWeight, frobPoint_toVec]
  rfl

/-- **The ring claim's fidelity**, from the layout's reading of the region. -/
theorem ringFaithful (hlay : ringLayoutHyp F prog s layout toI) :
    RingFaithful F prog s layout toI := by
  intro pt sv ch q hpt hsv hch hholds
  unfold StackClaim.Holds LeanVM.Protocol.Verifier.ringSwitchClaim at hholds
  dsimp only at hholds
  rw [← target_eq hsv hch F prog s, ← hholds, pair_arkWeight, ← ringCoefficients_sum hch
    (fun k ↦ eval₂Mle (toI q).values (algebraMap K E)
      (FlockPhase.lift (fR F prog s) (toVec _ (pt.map (· ^ 2 ^ k)))))]
  simp only [ringWeight_eq, length_ringCoefficients, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← hlay (pt.map (· ^ 2 ^ k)) (by rw [List.length_map, hpt]) q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  ring

end Weight

end
end LeanVM.Protocol.EndToEnd.Front
