/-
  LeanVM.Protocol.EndToEnd.Complete.BusDepth

  The bus's push tree is no deeper than the stack: every table pushes at most as many tuples per
  row as it commits columns, and the framework pushes fewer leaves than it commits cells. So the
  bus phase's grind, `busGrindingBits` of the push tree's depth, is at most `25` bits on the
  admissible sizes.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.BusLayout

/-!
# The depth of the bus

The bus phase (`verify_bus_balance`, `crates/verifier/src/bus.rs:130-247` at leanVM `f128`) grinds
`busGrindingBits(D) = grindingBits(2^D)` bits before its fingerprint, `D` the push tree's depth
(`bus_grinding_bits`, `bus.rs:14-18`), and requires `D < 64`.

* `blocks_total_eq_sum`: the stack's blocks total `Σ_c 2^κ_c` over the committed columns, grouped by
  table (`committedCount`).
* `pushTotal_le_blocks`: the push side's leaves, `1 + 2^κ + 2^ℓ + Σ_t (pushes of t)·2^τ_t`, are at
  most the stack's committed cells, `3·2^κ + 2^ℓ + 2^(τ_5 + 6) + Σ_t (committed columns of t)·2^τ_t`:
  each table pushes at most as many tuples per row as it commits columns (`pushes_le_committed`).
* `busDepth_le_leanIsaμ`: so the depth is at most the stack's number of variables, and on
  admissible sizes at most `28` (`busDepth_le`), the grind at most `25` bits
  (`busGrindingBits_le`).
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front Finset

@[expose] public section

/-- The committed columns of table `j` of the instance. -/
def committedCount (j : Fin 9) : ℕ :=
  ((List.finRange (width j)).filter fun i ↦ !decide (IsVirtual ⟨j, i⟩)).length

/-- **The stack's blocks total**: `Σ_j (committed columns of j)·2^(height j)`. -/
theorem blocks_total_eq_sum (prog : LeanIsaProgram) (s : Sizes) :
    (blocks prog s).total = ∑ j : Fin 9, committedCount j * 2 ^ height prog s j := by
  rw [Blocks.total_eq_sum]
  have h1 : ∑ b : Fin (blocks prog s).n, 2 ^ (blocks prog s).size b =
      ((LeanIsa.stackOrder prog s).map fun c ↦ 2 ^ kappa prog s c).sum := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem (by simp [blocks])
    intro i h1 h2
    simp [blocks]
  rw [h1, LeanIsa.stackOrder, ((List.mergeSort_perm _ _).map _).sum_eq, committedColumns, columns,
    List.filter_flatMap, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map,
    ← List.ofFn_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Function.comp_def, List.filter_map, List.map_map, kappa, List.map_const',
    List.sum_replicate, smul_eq_mul, committedCount]

/-- **Each table pushes at most as many tuples per row as it commits columns.** -/
theorem pushes_le_committed :
    ∀ t : Fin 6, (refSide t .push).length ≤ committedCount ⟨t.val + 3, by omega⟩ := by
  decide +kernel

/-- The framework's committed columns: three of the memory, one of the bytecode, one
`QKECCAK`. -/
theorem committedCount_framework :
    committedCount 0 = 3 ∧ committedCount 1 = 1 ∧ committedCount 2 = 1 := by
  decide +kernel

/-- **The push side's leaves are at most the stack's committed cells.** -/
theorem pushTotal_le_blocks (prog : LeanIsaProgram) (s : Sizes) :
    blockTotal (sideSizes (fwLogs prog s) (pushBlocks s)) ≤ (blocks prog s).total := by
  have hsplit : ∑ j : Fin 9, committedCount j * 2 ^ height prog s j =
      3 * 2 ^ s.logMem + (2 ^ prog.logSize + (2 ^ (s.τ 5 + 6) +
        ∑ t : Fin 6, committedCount ⟨t.val + 3, by omega⟩ * 2 ^ s.τ t)) := by
    rw [Fin.sum_univ_succ (n := 8), Fin.sum_univ_succ (n := 7), Fin.sum_univ_succ (n := 6)]
    obtain ⟨c0, c1, c2⟩ := committedCount_framework
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, c0, c1, c2, one_mul]
    rfl
  rw [blockTotal_sideSizes, blocks_total_eq_sum, pushBlocks, sum_flatten_ofFn, hsplit]
  simp only [fwLogs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero,
    List.map_map, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul]
  have ht : ∑ t : Fin 6, (refSide t .push).length * 2 ^ s.τ t ≤
      ∑ t : Fin 6, committedCount ⟨t.val + 3, by omega⟩ * 2 ^ s.τ t :=
    Finset.sum_le_sum fun t _ ↦ Nat.mul_le_mul (pushes_le_committed t) le_rfl
  have hm : 1 ≤ 2 ^ s.logMem := Nat.one_le_two_pow
  linarith [ht, hm, Nat.zero_le (2 ^ (s.τ 5 + 6))]

/-- **The push tree is no deeper than the stack.** -/
theorem busDepth_le_leanIsaμ (prog : LeanIsaProgram) (s : Sizes) :
    busDepth prog s ≤ leanIsaμ prog s := by
  rw [busDepth, log2Ceil_eq_clog]
  exact Nat.clog_le_of_le_pow ((pushTotal_le_blocks prog s).trans (blocks_fits prog s))

/-- On admissible sizes the push tree has depth at most `28`. -/
theorem busDepth_le {prog : LeanIsaProgram} {s : Sizes} (hs : s.Admissible prog) :
    busDepth prog s ≤ 28 :=
  (busDepth_le_leanIsaμ prog s).trans hs.2.2.2

/-- **On admissible sizes the bus grinds at most `25` bits.** -/
theorem busGrindingBits_le {prog : LeanIsaProgram} {s : Sizes} (hs : s.Admissible prog) :
    busGrindingBits (busDepth prog s) ≤ 25 := by
  have hD := busDepth_le hs
  unfold busGrindingBits grindingBits securityBits
  split_ifs with h
  · omega
  · have : Nat.log2 (2 ^ busDepth prog s - 1) < busDepth prog s := by
      rw [Nat.log2_lt (by omega)]
      omega
    omega

end
end LeanVM.Protocol.EndToEnd.Complete
