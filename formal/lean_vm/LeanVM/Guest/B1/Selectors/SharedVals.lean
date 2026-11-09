/-
  LeanVM.Guest.B1.Selectors.SharedVals

  `shared_selector_tables`' loop end and dispatch selector on every valuation satisfying its body:
  functions of its length argument alone.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables

/-!
# `shared_selector_tables`' loop end

On every valuation satisfying the body's atoms before its loop (`ssA`; any memory, any call
relation), with `len_g = g^n`, `n < 64`: the hinted bits rebuild `q_g = g^(n / 4)` (`σ 39`, the
end `__loop8` runs to) and `r_g = g^(n % 4)` (`σ 20`, the dispatch's selector), the loop's
condition is `1 + g^(n / 4)` and its start `1` (`ss_body_vals`). No load or unpinned hint enters:
the bits are pinned Boolean and their value by `q_g^4·r_g = len_g`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The body's atoms before its loop. -/
def ssA : List Stmt := [
    .atom (.hint (.bitsExp (.n 5) 6 (.stack [.n 6, .n 7, .n 8, .n 9, .n 10, .n 11]))),
    .atom (.mul (.n 6) (.n 6) (.n 6)),
    .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.mul (.n 8) (.n 8) (.n 8)),
    .atom (.mul (.n 9) (.n 9) (.n 9)),
    .atom (.mul (.n 10) (.n 10) (.n 10)),
    .atom (.mul (.n 11) (.n 11) (.n 11)),
    .atom (.const (.n 12) (word 1 0 0)),
    .atom (.const (.n 13) (word (imFactor 0) 0 0)),
    .atom (.mul (.n 14) (.n 6) (.n 13)),
    .atom (.add (.n 15) (.n 12) (.n 14)),
    .atom (.const (.n 16) (word 1 0 0)),
    .atom (.const (.n 17) (word (imFactor 1) 0 0)),
    .atom (.mul (.n 18) (.n 7) (.n 17)),
    .atom (.add (.n 19) (.n 16) (.n 18)),
    .atom (.mul (.n 20) (.n 15) (.n 19)),
    .atom (.const (.n 21) (word 1 0 0)),
    .atom (.const (.n 22) (word (imFactor 0) 0 0)),
    .atom (.mul (.n 23) (.n 8) (.n 22)),
    .atom (.add (.n 24) (.n 21) (.n 23)),
    .atom (.const (.n 25) (word 1 0 0)),
    .atom (.const (.n 26) (word (imFactor 1) 0 0)),
    .atom (.mul (.n 27) (.n 9) (.n 26)),
    .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.mul (.n 29) (.n 24) (.n 28)),
    .atom (.const (.n 30) (word 1 0 0)),
    .atom (.const (.n 31) (word (imFactor 2) 0 0)),
    .atom (.mul (.n 32) (.n 10) (.n 31)),
    .atom (.add (.n 33) (.n 30) (.n 32)),
    .atom (.mul (.n 34) (.n 29) (.n 33)),
    .atom (.const (.n 35) (word 1 0 0)),
    .atom (.const (.n 36) (word (imFactor 3) 0 0)),
    .atom (.mul (.n 37) (.n 11) (.n 36)),
    .atom (.add (.n 38) (.n 35) (.n 37)),
    .atom (.mul (.n 39) (.n 34) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 39)),
    .atom (.mul (.n 41) (.n 40) (.n 40)),
    .atom (.mul (.n 42) (.n 41) (.n 20)),
    .atom (.assertEq (.n 42) (.n 5)),
    .atom (.const (.n 43) (word 1 0 0)),
    .atom (.add (.n 44) (.n 43) (.n 39)),
    .atom (.const (.n 45) (word 1 0 0))]

/-- The body's straight statements, before its dispatch. -/
def ssS : List Stmt := [
    .atom (.hint (.bitsExp (.n 5) 6 (.stack [.n 6, .n 7, .n 8, .n 9, .n 10, .n 11]))),
    .atom (.mul (.n 6) (.n 6) (.n 6)),
    .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.mul (.n 8) (.n 8) (.n 8)),
    .atom (.mul (.n 9) (.n 9) (.n 9)),
    .atom (.mul (.n 10) (.n 10) (.n 10)),
    .atom (.mul (.n 11) (.n 11) (.n 11)),
    .atom (.const (.n 12) (word 1 0 0)),
    .atom (.const (.n 13) (word (imFactor 0) 0 0)),
    .atom (.mul (.n 14) (.n 6) (.n 13)),
    .atom (.add (.n 15) (.n 12) (.n 14)),
    .atom (.const (.n 16) (word 1 0 0)),
    .atom (.const (.n 17) (word (imFactor 1) 0 0)),
    .atom (.mul (.n 18) (.n 7) (.n 17)),
    .atom (.add (.n 19) (.n 16) (.n 18)),
    .atom (.mul (.n 20) (.n 15) (.n 19)),
    .atom (.const (.n 21) (word 1 0 0)),
    .atom (.const (.n 22) (word (imFactor 0) 0 0)),
    .atom (.mul (.n 23) (.n 8) (.n 22)),
    .atom (.add (.n 24) (.n 21) (.n 23)),
    .atom (.const (.n 25) (word 1 0 0)),
    .atom (.const (.n 26) (word (imFactor 1) 0 0)),
    .atom (.mul (.n 27) (.n 9) (.n 26)),
    .atom (.add (.n 28) (.n 25) (.n 27)),
    .atom (.mul (.n 29) (.n 24) (.n 28)),
    .atom (.const (.n 30) (word 1 0 0)),
    .atom (.const (.n 31) (word (imFactor 2) 0 0)),
    .atom (.mul (.n 32) (.n 10) (.n 31)),
    .atom (.add (.n 33) (.n 30) (.n 32)),
    .atom (.mul (.n 34) (.n 29) (.n 33)),
    .atom (.const (.n 35) (word 1 0 0)),
    .atom (.const (.n 36) (word (imFactor 3) 0 0)),
    .atom (.mul (.n 37) (.n 11) (.n 36)),
    .atom (.add (.n 38) (.n 35) (.n 37)),
    .atom (.mul (.n 39) (.n 34) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 39)),
    .atom (.mul (.n 41) (.n 40) (.n 40)),
    .atom (.mul (.n 42) (.n 41) (.n 20)),
    .atom (.assertEq (.n 42) (.n 5)),
    .atom (.const (.n 43) (word 1 0 0)),
    .atom (.add (.n 44) (.n 43) (.n 39)),
    .atom (.const (.n 45) (word 1 0 0)),
    .callIf (.n 44) "__loop8" [.n 45, .n 39, .n 0, .n 2, .n 3, .n 1, .n 4],
    .atom (.mul (.n 46) (.n 41) (.n 41)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.mul (.n 48) (.n 0) (.n 47)),
    .atom (.mul (.n 49) (.n 48) (.n 47)),
    .atom (.mul (.n 50) (.n 1) (.n 47)),
    .atom (.mul (.n 51) (.n 2) (.n 41)),
    .atom (.mul (.n 52) (.n 3) (.n 41)),
    .atom (.mul (.n 53) (.n 4) (.n 41))]

/-- The body's dispatch. -/
def ssDispV : Stmt := .dispatch (.n 20) ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 49, .n 50, .n 51, .n 52, .n 53] [.n 54]

theorem ssPre_eq_disp : ssPre = ssS ++ [ssDispV] := rfl

theorem ssA_eq_take : ssS.take 42 = ssA := rfl

/-- **The loop end and the selector are the length's.** -/
theorem ss_body_vals {C : CallRel} {rd : Reader} {σ : Val} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ ssA next kret) {n : ℕ} (hn : n < 64)
    (h5 : σ (.n 5) = gen ^ n) :
    σ (.n 39) = gen ^ (n / 4) ∧ σ (.n 20) = gen ^ (n % 4) ∧
      σ (.n 44) = 1 + gen ^ (n / 4) ∧ σ (.n 45) = 1 := by
  simp only [ssA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨p6, p7, p8, p9, p10, p11, c12, c13, m14, a15, c16, c17, m18, a19, m20, c21, c22, m23,
    a24, c25, c26, m27, a28, m29, c30, c31, m32, a33, m34, c35, c36, m37, a38, m39, m40, m41, m42,
    e42, c43, a44, c45, -⟩ := h
  let f : ℕ → Bool := fun k ↦ decide (σ (.n (6 + k)) = 1)
  have pin : ∀ k < 6, σ (.n (6 + k)) * σ (.n (6 + k)) = σ (.n (6 + k)) := by
    intro k hk
    interval_cases k
    · exact p6.symm
    · exact p7.symm
    · exact p8.symm
    · exact p9.symm
    · exact p10.symm
    · exact p11.symm
  let r := bitsVal f 2
  let q := bitsVal (fun k ↦ f (k + 2)) 4
  have hr4 : r < 4 := bitsVal_lt f 2
  have hq16 : q < 16 := bitsVal_lt _ 4
  have hrg : σ (.n 20) = gen ^ r := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + j))) (n := 2) (by norm_num)
      (fun j hj => pin j (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m20, a15, a19, c12, c16, m14, m18, c13, c17, tb_word_one, this]
  have hqg : σ (.n 39) = gen ^ q := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + (j + 2)))) (n := 4) le_rfl
      (fun j hj => pin (j + 2) (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m39, m34, m29, a24, a28, a33, a38, c21, c25, c30, c35, m23, m27, m32, m37, c22, c26, c31,
      c36, tb_word_one, this]
  have hq4 : σ (.n 41) = gen ^ (4 * q) := by rw [m41, m40, hqg]; ring
  have hn' : 4 * q + r = n := by
    have e : gen ^ (4 * q + r) = gen ^ n := by
      rw [← h5, ← e_add_eq_zero_iff.mp e42, m42, hq4, hrg, ← pow_add]
    exact gen_pow_inj (by omega) (by omega) e
  have hq : q = n / 4 := by omega
  have hr : r = n % 4 := by omega
  refine ⟨by rw [hqg, hq], by rw [hrg, hr], by rw [a44, c43, tb_word_one, hqg, hq],
    by rw [c45, tb_word_one]⟩

end
end LeanVM.Guest.B1.Tables
