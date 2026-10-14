import Whir.AdditiveCode
import Whir.QueryRefinement

/-! Refinement of the actual dense encoder's subspace loops. The remaining
representation obligations are operation preservation, not an RS-code axiom. -/
namespace Whir.AdditiveCode
open Polynomial
open Whir.Concrete
noncomputable section
variable {F : Type*} [Field F]

/-- Exact operations needed from the concrete base-field representation. -/
structure BaseRepresentation (F : Type*) [Field F] where
  map : K → F
  one : map 1 = 1
  add : ∀ x y, map (x ^^^ y) = map x + map y
  mul : ∀ x y, map (kmul x y) = map x * map y
  inv : ∀ x, map (kinv x) = (map x)⁻¹

def bitBasis (f : K → F) (i : ℕ) : F := f ((1 : K) <<< UInt64.ofNat i)

private def rootStep (state : Array K × Array K) (i : Nat) : Array K × Array K :=
  let layer := state.2.map fun x => kmul x (x ^^^ state.1[i]!)
  (state.1.push layer[0]!, layer.extract 1 layer.size)

private def rootState (n k : Nat) : Array K × Array K :=
  (List.range k).foldl rootStep (#[1], tab n fun i => (1 : K) <<< UInt64.ofNat (i+1))

private theorem rootState_succ (n k : Nat) :
    rootState n (k+1) = rootStep (rootState n k) k := by
  simp [rootState, List.range_succ]

private theorem rootState_invariant (f : BaseRepresentation F) (n k : Nat) (hk : k ≤ n) :
    (rootState n k).1.size = k+1 ∧ (rootState n k).2.size = n-k ∧
    (∀ i < k+1, f.map (rootState n k).1[i]! =
      (subspace (bitBasis f.map) i).eval (bitBasis f.map i)) ∧
    (∀ j < n-k, f.map (rootState n k).2[j]! =
      (subspace (bitBasis f.map) k).eval (bitBasis f.map (k+j+1))) := by
  induction k with
  | zero =>
    simp only [rootState, List.range_zero, List.foldl_nil, Nat.zero_add, Nat.sub_zero]
    refine ⟨rfl, by simp, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst i
      simp [subspace, bitBasis]
    · intro j hj
      simp [tab, hj, getElem!_pos, subspace, bitBasis]
  | succ k ih =>
    obtain ⟨hrs, hls, hroot, hlayer⟩ := ih (by omega)
    have hkn : k < n := by omega
    have hks : k < (rootState n k).1.size := by omega
    have h0 : 0 < (rootState n k).2.size := by omega
    rw [rootState_succ]
    have hnew (j : Nat) (hj : j < (rootState n k).2.size) :
        f.map ((rootState n k).2.map (fun x => kmul x (x ^^^ (rootState n k).1[k]!)))[j]! =
          (subspace (bitBasis f.map) (k+1)).eval (bitBasis f.map (k+j+1)) := by
      rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_map, f.mul, f.add,
        ← getElem!_pos (rootState n k).2 j hj, hlayer j (by omega), hroot k (by omega)]
      simp [subspace]
    constructor
    · simp [rootStep, hrs]
    constructor
    · simp [rootStep, hls]; omega
    constructor
    · intro i hi
      by_cases hik : i < k+1
      · have his : i < (rootState n k).1.size := by omega
        simp only [rootStep]
        rw [getElem!_pos _ _ (by simpa using Nat.lt_succ_of_lt his),
          Array.getElem_push_lt his, ← getElem!_pos (rootState n k).1 i his]
        exact hroot i hik
      · have hieq : i = k+1 := by omega
        subst i
        simpa [rootStep, getElem!_pos, ← hrs, Array.getElem_push_eq] using hnew 0 h0
    · intro j hj
      have hj' : j+1 < (rootState n k).2.size := by omega
      have h := hnew (j+1) hj'
      simp only [rootStep]
      rw [getElem!_pos _ _ (by simp [hls]; omega), Array.getElem_extract]
      have hm : j+1 < ((rootState n k).2.map
          (fun x => kmul x (x ^^^ (rootState n k).1[k]!))).size := by simpa using hj'
      simpa only [getElem!_pos ((rootState n k).2.map
        (fun x => kmul x (x ^^^ (rootState n k).1[k]!))) (j+1) hm,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Every diagonal value produced by the actual root-table loop is the
mathematical subspace polynomial at the actual bit-basis vector. -/
theorem subspaceRoots_map (f : BaseRepresentation F) (n i : Nat) (hi : i < n+1) :
    f.map (subspaceRoots n)[i]! =
      (subspace (bitBasis f.map) i).eval (bitBasis f.map i) := by
  have he : subspaceRoots n = (rootState n n).1 := by
    unfold subspaceRoots
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
      List.forIn_pure_yield_eq_foldl, pure_bind]
    rfl
  rw [he]
  exact (rootState_invariant f n n le_rfl).2.2.1 i hi

private def normalizedStep (roots : Array K) (state : Array K × K) (i : Nat) :
    Array K × K :=
  (state.1.push (kmul state.2 (kinv roots[i]!)), kmul state.2 (state.2 ^^^ roots[i]!))

private def normalizedState (n : Nat) (x : K) (k : Nat) : Array K × K :=
  (List.range k).foldl (normalizedStep (subspaceRoots n)) (#[], x)

private theorem normalizedState_invariant (f : BaseRepresentation F) (n : Nat) (x : K)
    (k : Nat) (hk : k ≤ n) :
    (normalizedState n x k).1.size = k ∧
    f.map (normalizedState n x k).2 = (subspace (bitBasis f.map) k).eval (f.map x) ∧
    ∀ i < k, f.map (normalizedState n x k).1[i]! =
      (normalized (bitBasis f.map) i).eval (f.map x) := by
  induction k with
  | zero => simp [normalizedState, subspace]
  | succ k ih =>
    obtain ⟨hs, hx, hout⟩ := ih (by omega)
    have he : normalizedState n x (k+1) =
        normalizedStep (subspaceRoots n) (normalizedState n x k) k := by
      simp [normalizedState, List.range_succ]
    rw [he]
    constructor
    · simp [normalizedStep, hs]
    constructor
    · simp only [normalizedStep, f.mul, f.add, hx, subspaceRoots_map f n k (by omega)]
      simp [subspace]
    · intro i hi
      by_cases hik : i < k
      · simp only [normalizedStep]
        have his : i < (normalizedState n x k).1.size := by omega
        rw [getElem!_pos _ _ (by simpa using Nat.lt_succ_of_lt his),
          Array.getElem_push_lt his, ← getElem!_pos (normalizedState n x k).1 i his]
        exact hout i hik
      · have hieq : i = k := by omega
        subst i
        simp only [normalizedStep]
        rw [getElem!_pos _ _ (by simp [hs])]
        have hp := Array.getElem_push_eq (xs := (normalizedState n x k).1)
          (x := kmul (normalizedState n x k).2 (kinv (subspaceRoots n)[k]!))
        simp only [hs] at hp
        rw [hp, f.mul, f.inv, hx, subspaceRoots_map f n k (by omega)]
        simp [normalized, mul_comm]

/-- Exact scalar-by-scalar refinement of the executable normalization loop. -/
theorem normalizedSubspaces_map (f : BaseRepresentation F) (n : Nat) (x : K)
    (i : Nat) (hi : i < n) :
    f.map (normalizedSubspaces n x)[i]! =
      (normalized (bitBasis f.map) i).eval (f.map x) := by
  have he : normalizedSubspaces n x = (normalizedState n x n).1 := by
    unfold normalizedSubspaces
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
      List.forIn_pure_yield_eq_foldl, pure_bind]
    rfl
  rw [he]
  exact (normalizedState_invariant f n x n le_rfl).2.2 i hi

end
end Whir.AdditiveCode
