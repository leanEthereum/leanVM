/-
  LeanVM.Protocol.EndToEnd.Complete.Ring

  The honest run of ring switching: no prover message, six challenges, and the ring-switching
  claim the program opens on the stack is true of the honest stack and has a multilinear weight,
  for the true slices of the Flock region.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Facts
public import LeanVM.Protocol.EndToEnd.Complete.Sumcheck
public import LeanVM.Protocol.ToArkLib.Flock.FrobeniusMap
import LeanVM.Protocol.Flock

/-!
# Completeness of ring switching

About the transcription of `python-verifier/verifier.py:1304-1340` (`_phi`,
`_ring_weight`, `ring_switch`) and `:1405-1406` (the ring claim on the stack) at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d` (`Verifier.ringSwitch`, `Verifier.ringSwitchClaim`).

`ringSwitch point s` reads nothing: it draws the six coefficients `ch` of the staged map
`Φ(a) = a + f · a^(2^shift)`, stage by stage (`phiMap`), and returns the target
`Σ_i g^i Φ(s_i)` and the weight `W(u) = Σ_k c_k Π_n (1 + point_n^(2^k) + u_n)` (`ringWeight`,
with the closed-form coefficients `c_k = ringCoefficients ch`). The program opens
`⟨eqAbove · W(take), q⟩ = target` on the stack.

For the true slices `s_i = ŝ_i(point)` of the Flock region (`FlockGood`), the claim is true and
its weight multilinear:

* `phiMap_eq_sum`: the staged map is the Frobenius sum `Φ(b) = Σ_{k < 64} c_k b^(2^k)` with the
  program's closed-form coefficients (`frobMap_eq_sum`, then a computation over the six
  coefficients, `frobTerms_stagesOf`);
* `ringWeight_eq_sum`: the weight is `Σ_k c_k eq(point^(2^k), ·)`;
* `ringClaim_weight`: with the `QFLOCK` placement's `eqAbove`, the claim's weight is
  `Σ_k c_k eq(P(point^(2^k)), ·)`, `P` the placement of a point of the region on the stack: a
  combination of the weights of 64 true column claims on `QFLOCK` (`TrueClaim`), hence
  multilinear (`ringClaim_multilinear`), and paired with the stack it is
  `Σ_k c_k q̂_flock(point^(2^k))`;
* `sum_gen_slice_frob`: `Σ_i g^i s_i^(2^k) = q̂_flock(point^(2^k))`: the Frobenius is additive,
  fixes the bits, and sends `eq(u, point)` at a cube point `u` to `eq(u, point^(2^k))`; the bits
  of a cell packed by the powers of `g` are the cell (`ofK_eq_sum_cellBit`). Hence the target
  is `Σ_k c_k q̂_flock(point^(2^k))` too (`ringTarget_eq`).

`follows_ringSwitch`: the honest prover, which only receives the challenges, follows the program,
and the claim it returns holds of the stack with a multilinear weight. No mismatch.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Complete
open CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The Frobenius of `E` -/

/-- The Frobenius `b ↦ b^(2^k)` is additive. -/
theorem frob_add (a b : E) (k : ℕ) : (a + b) ^ 2 ^ k = a ^ 2 ^ k + b ^ 2 ^ k :=
  add_pow_char_pow a b 2 k

/-- The Frobenius commutes with finite sums. -/
theorem frob_sum {ι : Type} (s : Finset ι) (f : ι → E) (k : ℕ) :
    (∑ i ∈ s, f i) ^ 2 ^ k = ∑ i ∈ s, f i ^ 2 ^ k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob_add, ih]

/-- The Frobenius fixes `0` and `1`. -/
theorem frob_bool {b : E} (hb : b = 0 ∨ b = 1) (k : ℕ) : b ^ 2 ^ k = b := by
  rcases hb with rfl | rfl <;> simp

/-- The coordinates of a cube point are `0` or `1`. -/
theorem boolPoint_isBool (m u : ℕ) : ∀ x ∈ boolPoint m u, x = 0 ∨ x = 1 := by
  intro x hx
  simp only [boolPoint, List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  split <;> simp

/-- The Frobenius of the equality kernel against a Boolean point raises the other point. -/
theorem eqEval_frob (k : ℕ) : ∀ (a p : List E), (∀ x ∈ a, x = 0 ∨ x = 1) →
    eqEval a p ^ 2 ^ k = eqEval a (p.map (· ^ 2 ^ k))
  | [], p, _ => by simp
  | _ :: _, [], _ => by simp
  | x :: a, z :: p, h => by
    rw [List.map_cons, eqEval_cons, eqEval_cons, mul_pow,
      eqEval_frob k a p fun y hy ↦ h y (List.mem_cons_of_mem x hy), frob_add, frob_add, one_pow,
      frob_bool (h x List.mem_cons_self)]

/-! ## The staged map -/

/-- The stages of the program's map: shift `ringMapShifts[p]`, coefficient `ch[p]`. -/
def stagesOf (ch : List E) : List (ℕ × E) := (List.zip ch ringMapShifts).map fun p ↦ (p.2, p.1)

/-- **The program's `Φ` is the staged map** of its stages. -/
theorem phiMap_eq_frobMap (a : E) (ch : List E) : phiMap a ch = frobMap (stagesOf ch) a := by
  unfold phiMap stagesOf
  generalize List.zip ch ringMapShifts = l
  induction l generalizing a with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨c, sh⟩ := p
    simp only [List.foldl_cons, List.map_cons, frobMap]
    exact ih _

set_option maxHeartbeats 4000000 in
/-- The program's closed-form coefficients are the Frobenius terms' of its stages: a
computation over six named coefficients. -/
theorem frobTerms_stagesOf (f0 f1 f2 f3 f4 f5 : E) (F : ℕ → E) :
    ((frobTerms (stagesOf [f0, f1, f2, f3, f4, f5])).map fun t ↦ t.1 * F t.2).sum =
      ∑ k ∈ Finset.range 64, (ringCoefficients [f0, f1, f2, f3, f4, f5]).getD k 0 * F k := by
  simp only [ringCoefficients, ringMapShifts, Flock.ringShifts, kBits, Vector.toList_mk,
    List.zip_cons_cons, List.zip_nil_right, stagesOf]
  simp [frobTerms, Finset.sum_range_succ, List.filter]
  ring

/-- **The staged map is the Frobenius sum with the program's coefficients**:
`Φ(b) = Σ_{k < 64} c_k b^(2^k)`. -/
theorem phiMap_eq_sum {ch : List E} (h : ch.length = 6) (b : E) :
    phiMap b ch = ∑ k ∈ Finset.range 64, (ringCoefficients ch).getD k 0 * b ^ 2 ^ k := by
  rw [phiMap_eq_frobMap, frobMap_eq_sum]
  match ch, h with
  | [f0, f1, f2, f3, f4, f5], _ => exact frobTerms_stagesOf f0 f1 f2 f3 f4 f5 fun k ↦ b ^ 2 ^ k

/-- The program's coefficients are sixty-four. -/
theorem length_ringCoefficients (ch : List E) : (ringCoefficients ch).length = 64 := by
  simp [ringCoefficients, kBits]

/-! ## The weight -/

/-- A fold multiplying by a function of each entry is the product. -/
theorem foldl_mul_map' {α : Type} (f : α → E) (c : E) (l : List α) :
    l.foldl (fun p a ↦ p * f a) c = c * (l.map f).prod := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- The program's product over a zipped pair of points is the equality kernel. -/
theorem foldl_zip_eqEval (c : E) : ∀ (r y : List E),
    (List.zip r y).foldl (fun product (p : E × E) ↦ product * (1 + p.1 + p.2)) c =
      c * eqEval r y
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: r, b :: y => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_eqEval _ r y, eqEval_cons]
    ring

/-- The weight fold from any start: the start plus `Σ_k c_k eq(r^(2^k), y)`. -/
theorem ringWeight_fold (y : List E) :
    ∀ (cs : List E) (a : E) (r : List E),
      (cs.foldl (fun (acc : E × List E) c ↦
        ((acc.1 + (List.zip acc.2 y).foldl (fun product (p : E × E) ↦
          product * (1 + p.1 + p.2)) c), acc.2.map (· ^ 2))) (a, r)).1 =
        a + ∑ k ∈ Finset.range cs.length, cs.getD k 0 * eqEval (r.map (· ^ 2 ^ k)) y
  | [], a, r => by simp
  | c :: cs, a, r => by
    rw [List.foldl_cons]
    rw [ringWeight_fold y cs, foldl_zip_eqEval, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, pow_one, List.map_map]
    have e : ∀ k ∈ Finset.range cs.length,
        cs.getD k 0 * eqEval (List.map ((fun x ↦ x ^ 2 ^ k) ∘ fun x ↦ x ^ 2) r) y =
          cs.getD k 0 * eqEval (List.map (fun x ↦ x ^ 2 ^ (k + 1)) r) y := fun k _ ↦ by
      have : ((fun x : E ↦ x ^ 2 ^ k) ∘ fun x ↦ x ^ 2) = fun x ↦ x ^ 2 ^ (k + 1) := by
        funext b
        simp only [Function.comp]
        rw [← pow_mul, pow_succ 2 k, mul_comm]
      rw [this]
    rw [Finset.sum_congr rfl e]
    simp only [List.map_id']
    ring

/-- **The program's weight is `Σ_k c_k eq(r^(2^k), ·)`.** -/
theorem ringWeight_eq_sum (r y cs : List E) :
    ringWeight r y cs =
      ∑ k ∈ Finset.range cs.length, cs.getD k 0 * eqEval (r.map (· ^ 2 ^ k)) y := by
  rw [ringWeight]
  exact (ringWeight_fold y cs 0 r).trans (zero_add _)

/-! ## The placement -/

/-- The selector bits above `v` are the bits of the shifted index. -/
theorem selectorPoint_drop (idx n v : ℕ) :
    (selectorPoint idx n).drop v = selectorPoint (idx >>> v) (n - v) := by
  rw [selectorPoint_eq_boolPoint, selectorPoint_eq_boolPoint, drop_boolPoint,
    Nat.shiftRight_eq_div_pow]

/-- An aligned placement's selector times the equality kernel of the window is the equality
kernel of the placed point. -/
theorem eqAbove_mul_eqEval (P : Placement) (hlow : P.low = 0) (p pt : List E)
    (hp : p.length = P.vars) (hv : P.vars ≤ pt.length) :
    P.eqAbove pt * eqEval p (pt.take P.vars) = eqEval (P.stackPoint p pt.length) pt := by
  obtain ⟨v, idx, low⟩ := P
  simp only at hlow hp hv
  subst hlow
  simp only [Placement.eqAbove, Placement.stackPoint, zero_add, Nat.sub_zero, List.take_zero,
    List.nil_append, selectorPoint_drop]
  have e := eqEval_append p (selectorPoint (idx >>> v) (pt.length - v)) (pt.take v)
    (pt.drop v) (by simp; omega)
  rw [List.take_append_drop] at e
  rw [e, mul_comm]

/-- The placement of `QFLOCK`: its log-size, at its block's offset. -/
theorem qflockPlacement_eq (prog : Program) (s : Sizes) :
    (verifierLayout prog s).placements.getD qflock default =
      { vars := kappa prog s flockCol,
        index := (blocks prog s).offset (blockOf flockCol not_isLimb_flockCol) } := by
  rw [← pyCol_flockCol]
  exact placement_committed prog s flockCol not_isLimb_flockCol

/-- The region's coordinates fit in the stack. -/
theorem kappa_flockCol_le (prog : Program) (s : Sizes) :
    kappa prog s flockCol ≤ leanIsaμ prog s := by
  have h := length_stackPoint prog s flockCol (Vector.replicate _ 0)
  rw [pyCol_flockCol, qflockPlacement_eq prog s] at h
  simp only [Placement.stackPoint, selectorPoint, List.length_append, List.length_take,
    List.length_drop, List.length_map, List.length_range, Vector.length_toList] at h
  omega

/-! ## The claim's weight -/

section Claim

variable {prog : Program} {s : Sizes} (q : Column (leanIsaμ prog s))

/-- The point `point^(2^k)` of the region, as a point of `QFLOCK`'s variables. -/
def frobVec (point : List E) (hpt : point.length = 8 + s.τ 5) (k : ℕ) :
    Vector E (kappa prog s flockCol) :=
  ⟨(point.map (· ^ 2 ^ k)).toArray, by rw [List.size_toArray, List.length_map]; exact hpt⟩

theorem toList_frobVec (point : List E) (hpt : point.length = 8 + s.τ 5) (k : ℕ) :
    (frobVec (prog := prog) point hpt k).toList = point.map (· ^ 2 ^ k) := by
  simp [frobVec]

/-- The true claim on `QFLOCK` at `point^(2^k)`. -/
def frobClaim (point : List E) (hpt : point.length = 8 + s.τ 5) (k : ℕ) :
    Verifier.ColumnClaim :=
  ⟨pyCol flockCol, (frobVec (prog := prog) point hpt k).toList,
    colEval prog s q flockCol (frobVec point hpt k)⟩

theorem trueClaim_frobClaim (point : List E) (hpt : point.length = 8 + s.τ 5) (k : ℕ) :
    TrueClaim prog s q (frobClaim q point hpt k) :=
  ⟨flockCol, frobVec point hpt k, rfl⟩

/-- The weight of the true claim on `QFLOCK` at `point^(2^k)`. -/
theorem frobClaim_weight (point : List E) (hpt : point.length = 8 + s.τ 5) (k : ℕ) :
    ((frobClaim q point hpt k).onStack (verifierLayout prog s)).1 =
      fun x ↦ eqEval (((verifierLayout prog s).placements.getD qflock default).stackPoint
        (point.map (· ^ 2 ^ k)) (verifierLayout prog s).stackLog) x := by
  simp only [frobClaim, ColumnClaim.onStack, toList_frobVec, pyCol_flockCol]

/-- **The ring claim's weight** on a point of the stack's length is the combination, with the
program's coefficients, of the weights of the true claims on `QFLOCK` at `point^(2^k)`. -/
theorem ringClaim_weight (point ch : List E) (hpt : point.length = 8 + s.τ 5) (target : E)
    (x : List E) (hx : x.length = leanIsaμ prog s) :
    (ringSwitchClaim (verifierLayout prog s) target
        fun rPrime ↦ ringWeight point rPrime (ringCoefficients ch)).1 x =
      ∑ k ∈ Finset.range 64, (ringCoefficients ch).getD k 0 *
        ((frobClaim q point hpt k).onStack (verifierLayout prog s)).1 x := by
  simp only [ringSwitchClaim, ringWeight_eq_sum, length_ringCoefficients, Finset.mul_sum,
    frobClaim_weight]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hP := qflockPlacement_eq prog s
  rw [mul_left_comm, eqAbove_mul_eqEval _ (by rw [hP]) _ _
      (by rw [hP, List.length_map, hpt]; rfl)
      (by rw [hP, hx]; exact kappa_flockCol_le prog s),
    hx, stackLog_verifierLayout]

/-- A sum over `range n` is the sum of the mapped `List.range n`. -/
theorem sum_range_eq_map_sum (f : ℕ → E) : ∀ n : ℕ,
    ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_eq_map_sum f n, List.range_succ, List.map_append,
      List.sum_append]
    simp

/-- **The ring claim's weight is multilinear** on the stack's cube. -/
theorem ringClaim_multilinear (q : Column (leanIsaμ prog s)) (point ch : List E)
    (hpt : point.length = 8 + s.τ 5) (target : E) :
    IsMultilinearFn (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) target
        fun rPrime ↦ ringWeight point rPrime (ringCoefficients ch)).1 := by
  refine isMultilinearFn_congr ?_ fun x hx ↦ (ringClaim_weight q point ch hpt target x hx).symm
  have h := isMultilinearFn_list_sum (List.range 64) (fun k ↦ (ringCoefficients ch).getD k 0)
    (fun k ↦ ((frobClaim q point hpt k).onStack (verifierLayout prog s)).1)
    fun k _ ↦ (trueClaim_frobClaim q point hpt k).multilinear
  exact isMultilinearFn_congr h fun x _ ↦ (sum_range_eq_map_sum _ 64).symm

/-- The ring claim paired with the stack is `Σ_k c_k q̂_flock(point^(2^k))`. -/
theorem ringClaim_pair (point ch : List E) (hpt : point.length = 8 + s.τ 5) (target : E) :
    ∑ x : Fin (2 ^ leanIsaμ prog s), (ringSwitchClaim (verifierLayout prog s) target
        fun rPrime ↦ ringWeight point rPrime (ringCoefficients ch)).1
        (boolPoint (leanIsaμ prog s) x) * ofK (q.values.getD x 0) =
      ∑ k ∈ Finset.range 64, (ringCoefficients ch).getD k 0 *
        colEval prog s q flockCol (frobVec point hpt k) := by
  simp only [ringClaim_weight q point ch hpt target _ (Whir.Complete.length_boolPoint _ _),
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h := (trueClaim_frobClaim q point hpt k).holds
  unfold StackClaim.Holds at h
  change _ = colEval prog s q flockCol (frobVec point hpt k) at h
  rw [← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-! ## The target -/

/-- An entry of a mapped list below its length. -/
theorem getD_map_of_lt {α : Type} (f : α → E) (l : List α) {u : ℕ} (hu : u < l.length)
    (d : α) : (l.map f).getD u 0 = f (l.getD u d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getD_eq_getElem _ _ hu,
    List.getElem_map]

/-- The extension of a `K`-column at a point of `E`, as a sum over the cube. -/
theorem eval₂Mle_eq_sum {n : ℕ} (c : Vector K (2 ^ n)) (z : Vector E n) :
    eval₂Mle c (algebraMap K E) z =
      ∑ u ∈ Finset.range (2 ^ n), ofK (c.toList.getD u 0) * eqEval (boolPoint n u) z.toList := by
  unfold eval₂Mle
  rw [← multilinearEval_eq_evalMle,
    multilinearEval_eq_sum n _ _ (by simp [CMlPolynomialEval.map]) (by simp)]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' : u < c.toList.length := by simpa using Finset.mem_range.mp hu
  simp only [CMlPolynomialEval.map, Vector.toList_map]
  rw [getD_map_of_lt _ _ hu' 0]
  rfl

/-- **The Frobenius of the slices packs into the region**: `Σ_i g^i s_i^(2^k)` is the region's
extension at `point^(2^k)`. -/
theorem sum_gen_slice_frob (point : List E) (hpt : point.length = 8 + s.τ 5) (k : ℕ) :
    ∑ i ∈ Finset.range 64, gen ^ i * flockSlice prog s q i point ^ 2 ^ k =
      colEval prog s q flockCol (frobVec point hpt k) := by
  set cells := ((inst prog s).column q flockCol).values with hcells
  have hlen : cells.toList.length = 2 ^ (8 + s.τ 5) := by simp; rfl
  have hslice : ∀ i, flockSlice prog s q i point ^ 2 ^ k =
      ∑ u ∈ Finset.range (2 ^ (8 + s.τ 5)), cellBit (cells.toList.getD u 0) i *
        eqEval (boolPoint (8 + s.τ 5) u) (point.map (· ^ 2 ^ k)) := by
    intro i
    rw [flockSlice, ← hcells, multilinearEval_eq_sum (8 + s.τ 5) _ _ (by simpa using hlen) hpt,
      frob_sum]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hu' : u < cells.toList.length := by rw [hlen]; exact Finset.mem_range.mp hu
    rw [getD_map_of_lt _ _ hu' 0, mul_pow, frob_bool (cellBit_isBool _ _),
      eqEval_frob k _ _ (boolPoint_isBool _ _)]
  have hcol : colEval prog s q flockCol (frobVec point hpt k) =
      ∑ u ∈ Finset.range (2 ^ (8 + s.τ 5)), ofK (cells.toList.getD u 0) *
        eqEval (boolPoint (8 + s.τ 5) u) (point.map (· ^ 2 ^ k)) := by
    have h := eval₂Mle_eq_sum (n := 8 + s.τ 5) cells (frobVec (prog := prog) point hpt k)
    erw [toList_frobVec] at h
    exact h
  simp only [hslice, Finset.mul_sum, hcol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [ofK_eq_sum_cellBit, Finset.sum_mul,
    Fin.sum_univ_eq_sum_range (fun i ↦ ofK (g ^ i) * cellBit (cells.toList.getD u 0) i *
      eqEval (boolPoint (8 + s.τ 5) u) (point.map (· ^ 2 ^ k))) (2 ^ Flock.kSkip)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hg : gen ^ i = ofK (g ^ i) := by
    rw [show gen = algebraMap K E g from rfl, ← map_pow]
    rfl
  rw [hg]
  ring

/-- **The program's target is the ring claim's value**: for the true slices,
`Σ_i g^i Φ(s_i) = Σ_k c_k q̂_flock(point^(2^k))`. -/
theorem ringTarget_eq (point ch : List E) (hpt : point.length = 8 + s.τ 5)
    (hch : ch.length = 6) :
    polyEval (((List.range 64).map fun i ↦ flockSlice prog s q i point).map (phiMap · ch)) gen =
      ∑ k ∈ Finset.range 64, (ringCoefficients ch).getD k 0 *
        colEval prog s q flockCol (frobVec point hpt k) := by
  rw [polyEval_eq_sum]
  simp only [List.map_map, List.length_map, List.length_range]
  have e : ∀ i ∈ Finset.range 64,
      ((List.range 64).map ((phiMap · ch) ∘ fun i ↦ flockSlice prog s q i point)).getD i 0 *
        gen ^ i = ∑ k ∈ Finset.range 64, (ringCoefficients ch).getD k 0 *
          (gen ^ i * flockSlice prog s q i point ^ 2 ^ k) := fun i hi ↦ by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
      Function.comp, phiMap_eq_sum hch, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.mul_sum, sum_gen_slice_frob q point hpt k]

end Claim

/-! ## The honest run -/

/-- **The honest prover of ring switching**: it sends nothing; it receives the six coefficients
and returns what the program returns. -/
def hRing (point slices : List E) : Script (E × (List E → E)) := do
  let challenges ← Script.sampleN ringMapShifts.length
  let coefficients := ringCoefficients challenges
  return (polyEval (slices.map (phiMap · challenges)) gen,
    fun rPrime ↦ ringWeight point rPrime coefficients)

/-- **Completeness of ring switching.** For the true slices of the Flock region at a point of
its coordinates (`FlockGood`), the honest prover follows `ringSwitch` for every challenge, and
the claim the program opens on the stack holds of it with a multilinear weight. -/
theorem follows_ringSwitch {prog : Program} {s : Sizes} {q : Column (leanIsaμ prog s)}
    (r : List E × List E) (hr : FlockGood prog s q r) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        StackClaim.Holds (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2) q ∧
        IsMultilinearFn (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2).1)
      (hRing r.1 r.2) (ringSwitch r.1 r.2) cs := by
  obtain ⟨hpt, hsl⟩ := hr
  simp only [hRing, ringSwitch, Script.bind_eq, Prog.bind_eq]
  refine Follows.bind (fun cs' a b h ↦ ?_) _ _ _ (Follows.sampleN_sampleN cs _)
  obtain ⟨rfl, rfl, hl⟩ := h
  have hch : a.length = 6 := hl
  refine ⟨rfl, rfl, ?_, ringClaim_multilinear q r.1 a hpt _⟩
  unfold StackClaim.Holds
  rw [ringClaim_pair q r.1 a hpt, hsl, ringTarget_eq q r.1 a hpt hch]
  rfl

end
end LeanVM.Protocol.EndToEnd.Complete
