/-
  LeanVM.Guest.B1.Exact.SharedTables

  `shared_selector_tables` is exact on every valid tree: its six bits are Boolean and their factors rebuild its
  `g`-power.
-/

module

public import LeanVM.Guest.Exact.Ok
public import LeanVM.Guest.B1.Bits.GPowerP
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Common.Find

/-!
# `shared_selector_tables`, exact

`shared_selector_tables` hints the six bits of its `g`-power's exponent, pins each by booleanity and asserts that the
product of the low two's factors times the fourth power of the high four's is the `g`-power. So on every path that
holds, the product of the six factors is the `g`-power (`bitFactor_pow4`): its one computed hint is exact
(`sst_pathExact`). Its callees have no computed hint, so it is in `ExactOk`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `shared_selector_tables`' computed hint: the six bits of its `g`-power's exponent. -/
def sstHint : Atom := .hint (.bitsExp (.n 5) 6 (.stack [.n 6, .n 7, .n 8, .n 9, .n 10, .n 11]))

theorem sst_sites : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ [sstHint])) pinsInverse
    (fn% «shared_selector_tables»).body = true := by
  decide +kernel

/-- **Every path of `shared_selector_tables` that holds is exact.** -/
theorem sst_pathExact : PathExactFn fn% «shared_selector_tables» := by
  refine pathExact_of_sites sst_sites fun rd σ es vs hw hes a ha _ => ?_
  rw [List.mem_singleton.mp ha]
  have w3 := word_gpow_one 0 (by norm_num) 3 (by decide)
  have w5 := word_gpow_one 1 (by norm_num) 5 (by decide)
  have w17 := word_gpow_one 2 (by norm_num) 17 (by decide)
  have w257 := word_gpow_one 3 (by norm_num) 257 (by decide)
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «shared_selector_tables»).body False (fun _ => True) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hes e he, fun _ _ _ _ => trivial⟩, trivial⟩)
  simp only [show (fn% «shared_selector_tables»).body = Fn.«shared_selector_tables».core.body from rfl,
    Fn.«shared_selector_tables».core.body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨m6, m7, m8, m9, m10, m11, c12, c13, h14, h15, c16, c17, h18, h19, h20, c21, c22, h23, h24, c25, c26, h27,
    h28, h29, c30, c31, h32, h33, h34, c35, c36, h37, h38, h39, h40, h41, h42, ha, -⟩ := h
  have hb : ∀ j < 6, σ (.n (6 + j)) * σ (.n (6 + j)) = σ (.n (6 + j)) := by
    intro j hj; interval_cases j
    exacts [m6.symm, m7.symm, m8.symm, m9.symm, m10.symm, m11.symm]
  have rg : σ (.n 20) = ∏ j ∈ Finset.range 2, (1 + σ (.n (6 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h20, h15, h19, c12, h14, c13, c16, h18, c17, w3, w5, word_one]
  have qg : σ (.n 39) = ∏ j ∈ Finset.range 4, (1 + σ (.n (8 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h39, h34, h29, h24, h28, h33, h38, c21, h23, c22, c25, h27, c26, c30, h32, c31, c35, h37, c36, w3, w5, w17,
      w257, word_one]
  have hq4 : σ (.n 41) = ∏ j ∈ Finset.range 4, (1 + σ (.n (6 + (2 + j))) * (gen ^ 2 ^ (2 + j) + 1)) := by
    rw [h41, h40, qg, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have := bitFactor_pow4 (hb (2 + j) (by have := Finset.mem_range.mp hj; omega)) j
    rw [show 6 + (2 + j) = 8 + j by omega, show j + 2 = 2 + j by omega] at this
    rw [show 6 + (2 + j) = 8 + j by omega, ← this]
    ring
  have hv : σ (.n 5) = ∏ j ∈ Finset.range 6, (1 + σ (.n (6 + j)) * (gen ^ 2 ^ j + 1)) := by
    rw [show Finset.range 6 = Finset.range (2 + 4) from rfl, Finset.prod_range_add, ← e_add_eq_zero_iff.mp ha, h42,
      hq4, rg, mul_comm]
  exact bitsExp_exact_of_prod (fun j => σ (.n (6 + j))) rfl hb hv

theorem find_sst : coreProgram.find? "shared_selector_tables" = some fn% «shared_selector_tables» :=
  coreProgram_find?_at (j := idx% «shared_selector_tables») rfl

theorem sst_callees_free : ∀ g ∈ Stmt.blockCallees (fn% «shared_selector_tables»).body, ExactFreeG g := by
  intro g hg
  have hall : (Stmt.blockCallees (fn% «shared_selector_tables»).body).all
      (fun g => exactCallee idx% «shared_selector_tables» g) = true := by
    decide +kernel
  exact exactFreeG_of_callee (List.all_eq_true.mp hall g hg)

/-- **`shared_selector_tables` is exact on every valid tree.** -/
theorem sst_exactOk : ExactOk "shared_selector_tables" :=
  .node find_sst sst_pathExact fun g hg _ => .free (sst_callees_free g hg)

end
end LeanVM.Guest.B1
