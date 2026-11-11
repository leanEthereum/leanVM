/-
  LeanVM.Protocol.Whir.SubspaceAt

  The verifier's subspace-polynomial arithmetic in closed form: `subspaceRoots` and `subspaceAt`.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Protocol.Whir.Subspace

/-!
# The verifier's subspace polynomials

`subspace_roots(n)` and `Subspace::at(x)` (`crates/verifier/src/whir.rs:94-130`,
`LeanVM.Protocol.Verifier.subspaceRoots` and `subspaceAt`) compute the normalizers
`W_i(β_i)` and the normalized subspace polynomials `Ŵ_i(x)` by the recursion
`W_(i+1) = W_i^2 + W_i(β_i) W_i` (`LeanVM.Protocol.Whir.vanishingAt_succ`):

* `verifier_subspaceRoots_eq`: `subspaceRoots n = [W_0(β_0), …, W_n(β_n)]`;
* `subspaceAt_eq`: `subspaceAt n x = [Ŵ_0(x), …, Ŵ_n(x)]`.
-/

namespace LeanVM.Protocol.Whir

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The verifier's `subspaceRoots`: `[W_0(β_0), …, W_n(β_n)]`, `β_c = e_c`. -/
theorem verifier_subspaceRoots_eq (n : ℕ) :
    Verifier.subspaceRoots n = (List.range (n + 1)).map fun i ↦ vanishingAt i (basisVec i) := by
  have hstep : ∀ j c, vanishingAt j (basisVec c) * vanishingAt j (basisVec c) +
      vanishingAt j (basisVec j) * vanishingAt j (basisVec c) = vanishingAt (j + 1) (basisVec c) := by
    intro j c
    rw [vanishingAt_succ, sq]
  have key : ∀ k j, subspaceRootsAux k (vanishingAt j (basisVec j))
      ((List.range' (j + 1) k).map fun c ↦ vanishingAt j (basisVec c)) =
        (List.range' (j + 1) k).map fun i ↦ vanishingAt i (basisVec i) := by
    intro k
    induction k with
    | zero => intro j; simp [subspaceRootsAux]
    | succ k ih =>
      intro j
      simp only [List.range'_succ, List.map_cons, List.map_map, Function.comp_def, hstep,
        subspaceRootsAux]
      rw [← ih (j + 1)]
  have h0 : ∀ a : K, vanishingAt 0 a = a := fun a ↦ by simp [vanishingAt]
  have e1 : vanishingAt 0 (basisVec 0) = 1 := by rw [h0, basisVec_zero]
  have hl : (List.range n).map (fun i ↦ K.ofBits (2 ^ (i + 1))) =
      (List.range' (0 + 1) n).map fun c ↦ vanishingAt 0 (basisVec c) := by
    rw [List.range'_eq_map_range, List.map_map]
    exact List.map_congr_left fun i _ ↦ by simp [h0, basisVec, Nat.add_comm]
  have hr : (List.range n).map ((fun i ↦ vanishingAt i (basisVec i)) ∘ Nat.succ) =
      (List.range' (0 + 1) n).map fun i ↦ vanishingAt i (basisVec i) := by
    rw [List.range'_eq_map_range, List.map_map]
    exact List.map_congr_left fun i _ ↦ by simp [Nat.add_comm]
  rw [Verifier.subspaceRoots, List.range_succ_eq_map, List.map_cons, List.map_map, hl, hr,
    ← key n 0, e1]

/-- The loop of `subspaceAt` from coordinate `s`, the basis at `W_s(x)`. -/
private theorem subspaceAtAux_range' (x : K) : ∀ (k s : ℕ),
    subspaceAtAux ((List.range' s k).map fun i ↦
        (vanishingAt i (basisVec i), (vanishingAt i (basisVec i))⁻¹)) (vanishingAt s x) =
      (List.range' s k).map fun i ↦ normVanishingAt i x
  | 0, _ => by simp [subspaceAtAux]
  | k + 1, s => by
    rw [List.range'_succ, List.map_cons, List.map_cons, subspaceAtAux, ← sq, ← vanishingAt_succ,
      subspaceAtAux_range' x k (s + 1)]
    rfl

/-- **The verifier's `subspaceAt`**: `[Ŵ_0(x), …, Ŵ_n(x)]`. -/
theorem subspaceAt_eq (n : ℕ) (x : K) :
    subspaceAt n x = (List.range (n + 1)).map fun i ↦ normVanishingAt i x := by
  have h0 : vanishingAt 0 x = x := by simp [vanishingAt]
  rw [subspaceAt, verifier_subspaceRoots_eq, List.map_map, List.range_eq_range']
  have := subspaceAtAux_range' x (n + 1) 0
  rw [h0] at this
  exact this

end
end LeanVM.Protocol.Whir
