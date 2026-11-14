/-
  LeanVM.Guest.B1.Exact.RsEqRun

  `rs_eq_run` and `ring_switch_weight` are exact on every valid tree: `rs_eq_run`'s six bits are Boolean and their
  factors rebuild its `g`-power.
-/

module

public import LeanVM.Guest.Exact.Ok
public import LeanVM.Guest.B1.Eq.RsEqRun

/-!
# `rs_eq_run`, exact

`rs_eq_run` hints the six bits of its `g`-power's exponent, pins each by booleanity and asserts that the product of the
low three's factors times the eighth power of the high three's is the `g`-power (`RsEqRun.lean`). So on every path that
holds, the product of the six factors is the `g`-power (`bitFactor_pow8`): its one computed hint is exact
(`rs_pathExact`, `bitsExp_exact_of_prod`). Its callees have no computed hint, so `rs_eq_run` and its caller
`ring_switch_weight` are in `ExactOk`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `rs_eq_run`'s computed hint: the six bits of its `g`-power's exponent. -/
def rsHint : Atom := .hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))

theorem rs_sites : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ [rsHint])) pinsInverse
    (fn% «rs_eq_run»).body = true := by
  decide +kernel

/-- **Every path of `rs_eq_run` that holds is exact.** -/
theorem rs_pathExact : PathExactFn fn% «rs_eq_run» := by
  refine pathExact_of_sites rs_sites fun rd σ es vs hw hes a ha _ => ?_
  rw [List.mem_singleton.mp ha]
  obtain ⟨w3, w5, w17⟩ := rs_consts
  have h : Stmt.HoldsList (fun _ _ _ => True) rd σ (fn% «rs_eq_run»).body False (fun _ => True) :=
    holdsList_of_walk _ (by rw [hw]; exact ⟨fun e he => ⟨hes e he, fun _ _ _ _ => trivial⟩, trivial⟩)
  rw [rs_eq_run_body, rsBody] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, -⟩ := h
  have hb : ∀ j < 6, σ (.n (4 + j)) * σ (.n (4 + j)) = σ (.n (4 + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm, b3.symm, b4.symm, b5.symm]
  have rg : σ (.n 23) = ∏ j ∈ Finset.range 3, (1 + σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, word_one]
  have qg : σ (.n 37) = ∏ j ∈ Finset.range 3, (1 + σ (.n (7 + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, word_one]
  have hq8 : σ (.n 40) = ∏ j ∈ Finset.range 3, (1 + σ (.n (4 + (3 + j))) * (gen ^ 2 ^ (3 + j) + 1)) := by
    rw [h40, h39, h38, qg, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have := bitFactor_pow8 (hb (3 + j) (by have := Finset.mem_range.mp hj; omega)) j
    rw [show 4 + (3 + j) = 7 + j by omega, show j + 3 = 3 + j by omega] at this
    rw [show 4 + (3 + j) = 7 + j by omega, ← this]
    ring
  have hv : σ (.n 3) = ∏ j ∈ Finset.range 6, (1 + σ (.n (4 + j)) * (gen ^ 2 ^ j + 1)) := by
    rw [show Finset.range 6 = Finset.range (3 + 3) from rfl, Finset.prod_range_add, ← e_add_eq_zero_iff.mp ha, h41,
      hq8, rg, mul_comm]
  exact bitsExp_exact_of_prod (fun j => σ (.n (4 + j))) rfl hb hv

theorem rs_callees_free : ∀ g ∈ Stmt.blockCallees (fn% «rs_eq_run»).body, ExactFreeG g := by
  intro g hg
  have hall : (Stmt.blockCallees (fn% «rs_eq_run»).body).all (fun g => exactCallee idx% «rs_eq_run» g) = true := by
    decide +kernel
  exact exactFreeG_of_callee (List.all_eq_true.mp hall g hg)

/-- **`rs_eq_run` is exact on every valid tree.** -/
theorem rs_exactOk : ExactOk "rs_eq_run" :=
  .node find_rs_eq_run rs_pathExact fun g hg _ => .free (rs_callees_free g hg)

theorem find_rsw : coreProgram.find? "ring_switch_weight" = some fn% «ring_switch_weight» :=
  coreProgram_find?_at (j := idx% «ring_switch_weight») rfl

/-- **`ring_switch_weight` is exact on every valid tree**: its body has no computed hint, its callee is
`rs_eq_run`. -/
theorem rsw_exactOk : ExactOk "ring_switch_weight" := by
  refine .node find_rsw (pathExact_of_sites (sites := []) (by decide +kernel) fun _ _ _ _ _ _ _ ha _ => absurd ha
    List.not_mem_nil) fun g hg _ => ?_
  rw [show Stmt.blockCallees (fn% «ring_switch_weight»).body = ["rs_eq_run"] by decide +kernel,
    List.mem_singleton] at hg
  rw [hg]; exact rs_exactOk

end
end LeanVM.Guest.B1
