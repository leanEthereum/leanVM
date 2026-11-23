module

public import NativeVm.Model.Whir
public import NativeRustcVm.Whir.Rep
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `induced_weight` as `whir.rs` computes it

`induced_weight` sums, query by query (`indTot`, `indTot_succ`), the weight times the factors
`1 + (1 ⊕ What_i)·r_i` over the point and the query's `What`s, one at a time (`indProd`,
`indProd_succ`); the factor is the limbs' `kmul` by `1 ⊕ What_i`, `1` added to the low one
(`indFactor_eq`). The pairs of the subspace table in memory read back as themselves
(`pairsOf_of_pairsAt`).
-/

namespace NativeRustcVm.Whir

open NativeVm.Model

@[expose] public section

/-- A factor `1 + (1 ⊕ v)·c`. -/
def indFactor (c : EW) (v : UInt64) : EW := 1 + EW.scale (1 ^^^ v) c

/-- The product of the weight and the first `t` factors. -/
def indProd (point : Array EW) (what : Array UInt64) (w : EW) (t : Nat) : EW :=
  ((point.toList.zip what.toList).take t).foldl (fun p cv ↦ p * indFactor cv.1 cv.2) w

/-- The sum over the first `j` queries. -/
def indTot (mu : Nat) (queries : Array UInt64) (weights point : Array EW) (j : Nat) : EW :=
  ((weights.toList.zip queries.toList).take j).foldl (fun total wq ↦
    total + indProd point (subspaceAt mu wq.2) wq.1 (min point.size (subspaceAt mu wq.2).size)) 0

end

public section

/-- The factor as the code computes it. -/
theorem indFactor_eq (c : EW) (v : UInt64) :
    indFactor c v = ⟨kmul (1 ^^^ v) c.c0 ^^^ 1, kmul (1 ^^^ v) c.c1⟩ := by
  show (⟨1 ^^^ kmul (1 ^^^ v) c.c0, 0 ^^^ kmul (1 ^^^ v) c.c1⟩ : EW) = _
  rw [UInt64.xor_comm 1, UInt64.zero_xor]

theorem indProd_zero (point : Array EW) (what : Array UInt64) (w : EW) :
    indProd point what w 0 = w := by
  simp [indProd]

theorem indProd_succ (point : Array EW) (what : Array UInt64) (w : EW) {t : Nat}
    (h1 : t < point.size) (h2 : t < what.size) :
    indProd point what w (t + 1) = indProd point what w t * indFactor point[t] what[t] := by
  rw [indProd, indProd, List.take_add_one, List.foldl_append]
  simp [h1, h2]

/-- The full product. -/
theorem indProd_full (point : Array EW) (what : Array UInt64) (w : EW) :
    (point.zip what).foldl
        (fun product (challenge, value) ↦ product * (1 + EW.scale (1 ^^^ value) challenge)) w =
      indProd point what w (min point.size what.size) := by
  rw [indProd, List.take_of_length_le (by simp), ← Array.foldl_toList, Array.toList_zip]
  rfl

theorem indTot_zero (mu : Nat) (queries : Array UInt64) (weights point : Array EW) :
    indTot mu queries weights point 0 = 0 := by
  simp [indTot]

theorem indTot_succ (mu : Nat) (queries : Array UInt64) (weights point : Array EW) {j : Nat}
    (h1 : j < weights.size) (h2 : j < queries.size) :
    indTot mu queries weights point (j + 1) = indTot mu queries weights point j +
      indProd point (subspaceAt mu queries[j]) weights[j]
        (min point.size (subspaceAt mu queries[j]).size) := by
  rw [indTot, indTot, List.take_add_one, List.foldl_append]
  simp [h1, h2]

/-- **`inducedWeight`** is the sum over the queries the weights and the queries both have. -/
theorem inducedWeight_eq (mu : Nat) (queries : Array UInt64) (weights point : Array EW) :
    inducedWeight mu queries weights point =
      indTot mu queries weights point (min weights.size queries.size) := by
  rw [inducedWeight, indTot, List.take_of_length_le (by simp), ← Array.foldl_toList,
    Array.toList_zip]
  congr 1
  funext total wq
  rw [← indProd_full]

/-- The pairs of a table read back. -/
theorem pairsOf_of_pairsAt {d : Mem 64} {p : BitVec 64} {ps : List (UInt64 × UInt64)}
    (h : PairsAt d p ps) : pairsOf d p ps.length = ps := by
  have hb : ∀ ps : List (UInt64 × UInt64), (pairWords ps).flatMap wordBytes =
      (ps.map fun q ↦ (⟨q.1, q.2⟩ : EW)).flatMap ewBytes := by
    intro ps
    induction ps with
    | nil => rfl
    | cons q qs ih =>
      simp only [pairWords, List.flatMap_cons, List.map_cons] at ih ⊢
      rw [← ih]
      simp [ewBytes]
  have he : EWsAt d p (ps.map fun q ↦ (⟨q.1, q.2⟩ : EW)) := by
    unfold EWsAt; rw [← hb]; exact h
  have := ewsOf_of_ewsAt he
  rw [List.length_map] at this
  rw [pairsOf, this, List.map_map]
  conv => rhs; rw [← List.map_id ps]
  rfl

end

end NativeRustcVm.Whir
