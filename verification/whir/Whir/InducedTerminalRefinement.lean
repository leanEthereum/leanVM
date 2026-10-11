import Whir.AdditiveColumn
import Whir.ExecutableOOD

/-! Exact evaluation of the executable query columns and the source terminal
subspace recurrence. All algebraic operations are the certified machine fields. -/
namespace Whir.InducedTerminalRefinement
open Concrete ArrayLayout ExecutableOOD AdditiveCode
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem cubeIndex_last {n : Nat} (u : Cube (n+1)) :
    cubeIndex u = cubeIndex (fun i : Fin n => u i.castSucc) +
      2^n * (if u (Fin.last n) then 1 else 0) := by
  induction n with
  | zero => simp [cubeIndex]
  | succ n ih =>
    rw [cubeIndex, ih (fun i => u i.succ)]
    simp only [cubeIndex, pow_succ, Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
    ring_nf
    rfl

private theorem novel_cube (v : Nat → E) (x : E) {n : Nat} (u : Cube n) :
    (novel v n (cubeIndex u)).eval x =
      ∏ i : Fin n, if u i then (normalized v i.val).eval x else 1 := by
  induction n with
  | zero => simp [novel]
  | succ n ih =>
    rw [cubeIndex_last, Fin.prod_univ_castSucc]
    have hlt := cubeIndex_lt (fun i : Fin n => u i.castSucc)
    cases u (Fin.last n) <;> simp [novel, hlt, ih]

/-- The actual append/scale column kernel, at the actual little-endian cube index. -/
theorem decode_column (n q : Nat) :
    decode n (column n q) = tensorWeight (fun i : Fin n =>
      E.ofK (normalizedSubspaces n (UInt64.ofNat q))[i.val]!) := by
  funext u
  rw [decode, concrete_column, getElem!_tab _ _ _ (cubeIndex_lt u), novel_cube]
  unfold tensorWeight
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  rw [show E.ofK (normalizedSubspaces n (UInt64.ofNat q))[i.val]! =
    (normalized (bitBasis E.ofK) i.val).eval (E.ofK (UInt64.ofNat q)) from
      normalizedSubspaces_map concreteBaseRepresentation n (UInt64.ofNat q) i.val i.isLt]

/-- Weighted column aggregation commutes with the explicit array/cube decoding. -/
theorem decode_induced (n : Nat) (queries : Array Nat) (weights : Array E) :
    decode n (induced n queries weights) = inducedWeight
      (fun i : Fin queries.size => weights[i.val]!)
      (fun i : Fin queries.size => fun k : Fin n =>
        E.ofK (normalizedSubspaces n (UInt64.ofNat queries[i.val]!))[k.val]!) := by
  funext u
  simp only [decode, induced, QueryRefinement.inducedColumns_get _ _ _ _ (cubeIndex_lt u),
    Array.size_map, inducedWeight, batchWeights]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [getElem!_pos (queries.map (column n)) i.val (by simp), Array.getElem_map,
    ← getElem!_pos queries i.val i.isLt]
  exact congrArg (weights[i.val]! * ·) (congrFun (decode_column n queries[i.val]!) u)

private theorem range_mul_fold (n : Nat) (f : Nat → E) (a : E) :
    (List.range n).foldl (fun a i => a * f i) a = a * ∏ i : Fin n, f i.val := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Fin.prod_univ_castSucc, mul_assoc]

private theorem range_add_fold (n : Nat) (f : Nat → E) (a : E) :
    (List.range n).foldl (fun a i => a + f i) a = a + ∑ i : Fin n, f i.val := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Fin.sum_univ_castSucc, add_assoc]

/-- Closed form of the executable loop, including repeated query indices. -/
theorem inducedAt_eq_sum (n : Nat) (queries : Array Nat) (weights point : Array E) :
    inducedAt n queries weights point = ∑ i : Fin queries.size, weights[i.val]! *
      ∏ k : Fin n, (1 + point[k.val]! *
        (1 + E.ofK (normalizedSubspaces n (UInt64.ofNat queries[i.val]!))[k.val]!)) := by
  unfold inducedAt
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind]
  change (List.range queries.size).foldl (fun out i => out +
    (List.range n).foldl (fun p k => p * (1 + point[k]! *
      (1 + E.ofK (normalizedSubspaces n (UInt64.ofNat queries[i]!))[k]!))) weights[i]!) 0 = _
  simp_rw [range_mul_fold]
  rw [range_add_fold, zero_add]
  rfl

/-- Exact executable induced evaluation; no supplied column correctness predicate. -/
theorem inducedAt_eq_mle (n : Nat) (queries : Array Nat) (weights point : Array E)
    (_hw : weights.size = queries.size) (hp : point.size = n) :
    inducedAt n queries weights point = Concrete.mle (induced n queries weights) point := by
  let r : Fin n → E := fun i => point[i.val]!
  have he : point = Array.ofFn r := by
    apply Array.ext
    · simp [hp]
    · intro i hi hj
      simp [r, getElem!_pos, hi]
  rw [he, mle_eq_cube _ r (QueryRefinement.size_induced _ _ _), decode_induced,
    inducedWeight_mle_charTwo, inducedAt_eq_sum]
  simp [r, getElem!_pos]

/-- The source's explicit zero branch, not an assumption about division by zero. -/
def nativeInverse (sigma : K) : K := if sigma = 0 then 0 else kinv sigma

/-- `LevelCtx::basis_at`, verify.rs:181–185. -/
def nativeLinear (n : Nat) (point : Array E) : Array (E × E) :=
  point.mapIdx fun k p => (p + 1, p * E.ofK (nativeInverse (subspaceRoots n)[k]!))

/-- One source iteration. The subspace recurrence takes place before factors
after the first one, and runs in the extension field on `query_point`. -/
def nativeStep (roots : Array K) (lin : Array (E × E)) (state : E × E) (k : Nat) :
    E × E :=
  let s := if k = 0 then state.1 else
    state.1 * state.1 + state.1 * E.ofK roots[k-1]!
  (s, state.2 * (lin[k]!.2 * s + lin[k]!.1))

/-- Exact source fold. Zip truncation is retained on malformed weight arrays;
valid callers prove matching lengths. Query words use the UInt64 embedding. -/
def nativeBasisAt (n : Nat) (queries : Array Nat) (weights point : Array E) : E :=
  let roots := subspaceRoots n
  let lin := nativeLinear n point
  (List.range (min queries.size weights.size)).foldl (fun acc i =>
    let product := ((List.range point.size).foldl (nativeStep roots lin)
      (E.ofK (UInt64.ofNat queries[i]!), 1)).2
    weights[i]! * product + acc) 0

/-- Every sigma actually used by a valid binary-field level is nonzero. -/
theorem subspaceRoots_ne_zero (n k : Nat) (hn : n ≤ 64) (hk : k < n) :
    (subspaceRoots n)[k]! ≠ 0 := by
  intro h
  have hr := subspaceRoots_map concreteBaseRepresentation n k (by omega)
  simp only [concreteBaseRepresentation] at hr
  have hz := root_ne_zero (concrete_bitBasis_independent n hn) hk
  apply hz
  rw [← hr, h]
  exact FieldModel.ofK_zero

theorem nativeInverse_eq_kinv (n k : Nat) (hn : n ≤ 64) (hk : k < n) :
    nativeInverse (subspaceRoots n)[k]! = kinv (subspaceRoots n)[k]! := by
  simp [nativeInverse, subspaceRoots_ne_zero n k hn hk]

private theorem nativeLinear_get (n : Nat) (point : Array E) (k : Nat)
    (hk : k < point.size) :
    (nativeLinear n point)[k]! =
      (point[k]! + 1, point[k]! * E.ofK (nativeInverse (subspaceRoots n)[k]!)) := by
  simp [nativeLinear, getElem!_pos, hk]

private noncomputable def evalSubspace (x : E) (k : Nat) : E :=
  (subspace (bitBasis E.ofK) k).eval x

private theorem evalSubspace_succ (n k : Nat) (x : E) (hk : k < n) :
    evalSubspace x (k+1) =
      evalSubspace x k * evalSubspace x k +
        evalSubspace x k * E.ofK (subspaceRoots n)[k]! := by
  have h := subspaceRoots_map concreteBaseRepresentation n k (by omega)
  simp only [concreteBaseRepresentation] at h
  simp only [evalSubspace, subspace, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C]
  rw [h]
  ring

private theorem native_factor (n k : Nat) (x : K) (point : Array E)
    (hn : n ≤ 64) (hp : point.size = n) (hk : k < n) :
    (nativeLinear n point)[k]!.2 * evalSubspace (E.ofK x) k +
        (nativeLinear n point)[k]!.1 =
      1 + point[k]! * (1 + E.ofK (normalizedSubspaces n x)[k]!) := by
  rw [nativeLinear_get n point k (by omega), nativeInverse_eq_kinv n k hn hk]
  have h := normalizedSubspaces_map concreteBaseRepresentation n x k hk
  simp only [concreteBaseRepresentation] at h
  rw [h]
  simp only [normalized, Polynomial.eval_mul, Polynomial.eval_C,
    FieldModel.ofK_kinv]
  have hr := subspaceRoots_map concreteBaseRepresentation n k (by omega)
  simp only [concreteBaseRepresentation] at hr
  rw [hr]
  unfold evalSubspace
  ring

private theorem native_loop (n : Nat) (x : K) (point : Array E)
    (hn : n ≤ 64) (hp : point.size = n) (k : Nat) (hk : k ≤ n) :
    let state := (List.range k).foldl (nativeStep (subspaceRoots n) (nativeLinear n point))
      (E.ofK x, 1)
    state.1 = evalSubspace (E.ofK x) (k-1) ∧
    state.2 = ∏ i : Fin k,
      (1 + point[i.val]! * (1 + E.ofK (normalizedSubspaces n x)[i.val]!)) := by
  induction k with
  | zero => simp [evalSubspace, subspace]
  | succ k ih =>
    obtain ⟨hs, hprod⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hs' : (if k = 0 then
        ((List.range k).foldl (nativeStep (subspaceRoots n) (nativeLinear n point))
          (E.ofK x, 1)).1
      else
        ((List.range k).foldl (nativeStep (subspaceRoots n) (nativeLinear n point))
          (E.ofK x, 1)).1 *
        ((List.range k).foldl (nativeStep (subspaceRoots n) (nativeLinear n point))
          (E.ofK x, 1)).1 +
        ((List.range k).foldl (nativeStep (subspaceRoots n) (nativeLinear n point))
          (E.ofK x, 1)).1 * E.ofK (subspaceRoots n)[k-1]!) =
        evalSubspace (E.ofK x) k := by
      rw [hs]
      by_cases h : k = 0
      · simp [h]
      · simp only [h, ↓reduceIte]
        rw [← evalSubspace_succ n (k-1) (E.ofK x) (by omega)]
        congr 1
        omega
    constructor
    · simpa only [nativeStep, Nat.add_sub_cancel] using hs'
    · simp only [nativeStep, hs', hprod, native_factor n k x point hn hp (by omega)]
      rw [Fin.prod_univ_castSucc]
      rfl

/-- The source recurrence and the executable normalized-column formula agree;
the zero-sigma fallback is proved unreachable, not silently equated to inversion. -/
theorem nativeBasisAt_eq_inducedAt (n : Nat) (queries : Array Nat)
    (weights point : Array E) (hn : n ≤ 64)
    (hw : weights.size = queries.size) (hp : point.size = n) :
    nativeBasisAt n queries weights point = inducedAt n queries weights point := by
  unfold nativeBasisAt
  simp only [hw, min_self, hp]
  have he : ∀ i : Nat, ((List.range n).foldl (nativeStep (subspaceRoots n) (nativeLinear n point))
      (E.ofK (UInt64.ofNat queries[i]!), 1)).2 =
      ∏ k : Fin n, (1 + point[k.val]! *
        (1 + E.ofK (normalizedSubspaces n (UInt64.ofNat queries[i]!))[k.val]!)) :=
    fun i => (native_loop n (UInt64.ofNat queries[i]!) point hn hp n le_rfl).2
  simp_rw [he, add_comm (_ * _)]
  rw [range_add_fold, zero_add, inducedAt_eq_sum]

theorem nativeBasisAt_eq_mle (n : Nat) (queries : Array Nat)
    (weights point : Array E) (hn : n ≤ 64)
    (hw : weights.size = queries.size) (hp : point.size = n) :
    nativeBasisAt n queries weights point = Concrete.mle (induced n queries weights) point :=
  (nativeBasisAt_eq_inducedAt n queries weights point hn hw hp).trans
    (inducedAt_eq_mle n queries weights point hw hp)

/-- Native `query_point` embeds the actual index word without wrap on every
permitted query domain, including the 64-bit endpoint. -/
theorem queryWord_toNat (depth q : Nat) (hd : depth ≤ 64) (hq : q < 2^depth) :
    (UInt64.ofNat q).toNat = q := by
  have hq64 : q < 2^64 :=
    hq.trans_le (Nat.pow_le_pow_right (by decide) hd)
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hq64]

#print axioms inducedAt_eq_mle
#print axioms subspaceRoots_ne_zero
#print axioms nativeBasisAt_eq_mle
#print axioms queryWord_toNat

end Whir.InducedTerminalRefinement
