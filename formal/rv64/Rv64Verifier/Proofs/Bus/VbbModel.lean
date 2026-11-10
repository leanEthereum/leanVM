import Rv64Verifier.Model.Bus

/-!
# `verify_bus_balance`: the compiled loops against the mirror

The GKR loop (`0x8000669c`) is `gkrLoopM` rotated: `layer > 0` is tested before the first
iteration (`0x80006610`) and after each (`0x80006698`); an iteration samples, calls `poly_eval`,
`sumcheck`, three `next_scalars`, folds each child's product in place, compares the claim (in
checked mode), calls `samples` and three `multilinear_eval`s, pushing into the cleared `values`,
then concatenates the point: `gkrStepM`'s operations in its order (`gkrLoopM_pos`). The side loop
(`0x800074e0`) runs over a stack array of the three sides in the mirror's order, and its block
loop (`0x800078f0`) over `min(tables, blocks)` blocks, the mirror's `zip`.

Where the code differs from the mirror:
* `padding_weight` is inlined, its step `(1 + b + r) * pad + (1 + b) * r` (`padLow`,
  `paddingWeightRust_eq_padLow`);
* `E::sum` over the chained selectors is two loops, each adding an element on the left
  (`sumLeft`, `sumE_append`);
* `padding_rows += p` computes `p + padding_rows`, and a side's total is
  `rows + ones + known + tree + 1` (`sideTotal_code`);
* push's framework `pc` is the literal `ONE` (`gpowRust_zero_eq_one`).
-/

namespace Rv64Verifier.Model
open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## The GKR loop -/

theorem gkrLoopM_zero (state : GkrState) : gkrLoopM 0 state = pure state := by
  rw [gkrLoopM]
  simp

theorem gkrLoopM_pos {layer : ℕ} (h : 0 < layer) (state : GkrState) :
    gkrLoopM layer state = gkrStepM (if layer % 2 = 1 then 1 else 2) state >>=
      gkrLoopM (layer - if layer % 2 = 1 then 1 else 2) := by
  rw [gkrLoopM]
  simp [h]

/-! ## `padding_weight`, inlined -/

/-- One iteration of the inlined loop: `pad` after bit `k`, the point's coordinate `r`. -/
def padStepCode (n : BitVec 64) (pad r : E) (k : ℕ) : E :=
  (1 + bitE n k + r) * pad + (1 + bitE n k) * r

/-- The loop's value after `k` coordinates. -/
def padLow (n : BitVec 64) (point : List E) : ℕ → E
  | 0 => 1
  | k + 1 => padStepCode n (padLow n point k) (point.getD k 0) k

theorem padLow_eq (n : BitVec 64) (point : List E) : ∀ k, k ≤ point.length →
    padLow n point k = (point.take k).zipIdx.foldl
      (fun pad (rk : E × ℕ) ↦ (1 + bitE n rk.2) * rk.1 + (1 + bitE n rk.2 + rk.1) * pad) 1
  | 0, _ => by simp [padLow]
  | k + 1, hk => by
    have ih := padLow_eq n point k (by omega)
    have ht : point.take (k + 1) = point.take k ++ [point.getD k 0] := by
      rw [List.take_add_one, List.getD_eq_getElem _ _ (by omega),
        List.getElem?_eq_getElem (by omega)]
      rfl
    have hl : (point.take k).length = k := by rw [List.length_take]; omega
    rw [ht, List.zipIdx_append, List.foldl_append, ← ih, hl]
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      padLow, padStepCode]
    exact add_comm _ _

theorem paddingWeightRust_eq_padLow (point : List E) (n : BitVec 64) :
    paddingWeightRust point n = (1 + bitE n point.length) * padLow n point point.length := by
  rw [paddingWeightRust, padLow_eq n point _ (le_refl _), List.take_length]

/-! ## Sums -/

/-- The inlined `E::sum` loop: each element added on the left. -/
def sumLeft (acc : E) (l : List E) : E := l.foldl (fun acc x ↦ x + acc) acc

theorem sumLeft_eq : ∀ (acc : E) (l : List E), sumLeft acc l = l.foldl (· + ·) acc
  | _, [] => rfl
  | acc, x :: l => by
    simp only [sumLeft, List.foldl_cons] at *
    rw [add_comm x acc]
    exact sumLeft_eq _ l

theorem sumE_append (fs ts : List E) : sumE (fs ++ ts) = sumLeft (sumLeft 0 fs) ts := by
  rw [sumE, List.foldl_append, sumLeft_eq, sumLeft_eq]

theorem sideTotal_code (tree known ones rows : E) :
    tree + known + (ones + 1) + rows = rows + ones + known + tree + 1 := by
  abel

theorem gpowRust_zero_eq_one : gpowRust 0#64 = 1 := pow_zero _

end Rv64Verifier.Model
