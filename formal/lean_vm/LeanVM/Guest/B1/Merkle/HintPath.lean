/-
  LeanVM.Guest.B1.Merkle.HintPath

  A Merkle path's children cells, as `walk_path` holds them, are the honest hint generator's steps (`Hints.climbSteps`, `Hints.stepChildren`).
-/

module

public import LeanVM.Guest.Hints
public import LeanVM.Guest.B1.Merkle.Climb

/-!
# A path's children are the hint generator's

* `climbSteps_fst`: the generator's steps from tree index `idx` are, level `l`, the index `idx / 2^l`, the node `climbD` reaches after `l` levels and the sibling;
* `climbD_mod`: `climbD` reads the position's low bits only;
* `range_four_mul`: a run of `4n` cells, four at a time;
* `pathCells_eq_steps`: the `4 pd` children cells `pathCell` of a path's first `pd` levels, from leaf `q` of a depth-`D` tree, are the first `pd` steps' ordered children.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **The generator's steps**: level `l`'s index, node and sibling. -/
theorem climbSteps_fst : ∀ (ss : List Digest) (idx : ℕ) (node : Digest),
    (Hints.climbSteps idx node ss).1 = (List.range ss.length).map fun l =>
      (idx / 2 ^ l, climbD node idx (ss.take l), ss.getD l (Vector.replicate 4 0))
  | [], _, _ => rfl
  | s :: ss, idx, node => by
    simp only [Hints.climbSteps, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [climbSteps_fst ss]
    simp only [pow_zero, Nat.div_one, List.take_zero, climbD_nil, List.getD_cons_zero, List.cons.injEq,
      true_and]
    refine List.map_congr_left fun l _ => ?_
    simp only [Function.comp_apply, List.take_succ_cons, climbD_cons, List.getD_cons_succ,
      Nat.div_div_eq_div_mul, pow_succ']

/-- **`climbD` reads the position's low bits only.** -/
theorem climbD_mod : ∀ (ss : List Digest) (x : Digest) (q q' : ℕ),
    q % 2 ^ ss.length = q' % 2 ^ ss.length → climbD x q ss = climbD x q' ss
  | [], _, _, _, _ => rfl
  | s :: ss, x, q, q', h => by
    rw [List.length_cons, pow_succ'] at h
    have h2 : q % 2 = q' % 2 := by
      rw [← Nat.mod_mod_of_dvd q (dvd_mul_right 2 (2 ^ ss.length)),
        ← Nat.mod_mod_of_dvd q' (dvd_mul_right 2 (2 ^ ss.length)), h]
    have hd : q / 2 % 2 ^ ss.length = q' / 2 % 2 ^ ss.length := by
      rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, h]
    rw [climbD_cons, climbD_cons, h2]
    exact climbD_mod ss _ _ _ hd

/-- A run of `4n` cells, four at a time. -/
theorem range_four_mul {α : Type} (f : ℕ → α) : ∀ n : ℕ,
    (List.range (4 * n)).map f = (List.range n).flatMap fun l => [f (4 * l), f (4 * l + 1), f (4 * l + 2), f (4 * l + 3)]
  | 0 => rfl
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, List.range_add, List.map_append, range_four_mul f n,
      List.range_succ (n := n), List.flatMap_append]
    simp [List.range_succ]

/-- The bit at level `l < D` of leaf `q`'s tree index `2^D + q` is `q`'s. -/
theorem index_bit {D l q : ℕ} (hl : l < D) : (2 ^ D + q) / 2 ^ l % 2 = q / 2 ^ l % 2 := by
  rw [show 2 ^ D = 2 ^ l * 2 ^ (D - l) by rw [← pow_add]; congr 1; omega,
    Nat.add_comm, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mod,
    show 2 ^ (D - l) = 2 * 2 ^ (D - l - 1) by rw [← pow_succ']; congr 1; omega, Nat.mul_mod_right]
  simp

/-- **A path's children cells are the generator's steps**: the first `pd` levels of the path from
leaf `q` of a depth-`D` tree, `pd ≤ D`. -/
theorem pathCells_eq_steps {D pd q : ℕ} (leaf : Digest) (path : List Digest) (hpd : pd ≤ D)
    (hl : pd ≤ path.length) :
    (List.range (4 * pd)).map (pathCell leaf q (path.take pd)) =
      ((Hints.climbSteps (2 ^ D + q) leaf path).1.take pd).flatMap Hints.stepChildren := by
  rw [climbSteps_fst, ← List.map_take, List.take_range, min_eq_left hl, List.flatMap_map,
    range_four_mul]
  refine List.flatMap_congr fun l hl' => ?_
  have hlp := List.mem_range.mp hl'
  have hb := index_bit (q := q) (show l < D by omega)
  have hc : climbD leaf (2 ^ D + q) (path.take l) = climbD leaf q (path.take l) :=
    climbD_mod _ _ _ _ (by
      rw [List.length_take, min_eq_left (by omega),
        show 2 ^ D = 2 ^ l * 2 ^ (D - l) by rw [← pow_add]; congr 1; omega, Nat.add_comm,
        Nat.add_mul_mod_self_left])
  have hn : climbNode leaf q (path.take pd) l = climbD leaf q (path.take l) := by
    rw [climbNode, List.take_take, min_eq_left (by omega)]
  have hs : (path.take pd)[l]? = path[l]? := by
    rw [List.getElem?_take]; simp [hlp]
  have ht : q.testBit l = decide (q / 2 ^ l % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ l) with h | h <;>
    simp [pathCell, Hints.stepChildren, Hints.digestCells, List.getD_eq_getElem?_getD, hb, hc, hn, hs, ht, h,
      show 4 * l / 4 = l by omega, show (4 * l + 1) / 4 = l by omega,
      show (4 * l + 2) / 4 = l by omega, show (4 * l + 3) / 4 = l by omega, show 4 * l % 2 = 0 by omega,
      show (4 * l + 1) % 4 = 1 by omega, show (4 * l + 2) % 4 = 2 by omega, show (4 * l + 3) % 4 = 3 by omega,
      show (4 * l + 1) % 2 = 1 by omega, show (4 * l + 2) % 2 = 0 by omega, show (4 * l + 3) % 2 = 1 by omega]

end
end LeanVM.Guest.B1
