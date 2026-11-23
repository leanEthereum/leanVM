/-
  LeanVM.Guest.B1.Selectors.SharedVals

  `shared_selector_tables`' loop end and dispatch selector on every valuation satisfying its body:
  functions of its length argument alone.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«shared_selector_tables»

/-!
# `shared_selector_tables`' loop end

On every valuation satisfying the body's atoms before its loop (`ssA`; any memory, any call
relation), with `len_g = g^n`, `n < 64`: the hinted bits rebuild `q_g = g^(n / 4)` (`σ 39`, the
end `shared_selector_tables_loop0` runs to) and `r_g = g^(n % 4)` (`σ 20`, the dispatch's selector),
the loop's condition is `1 + g^(n / 4)` and its start `1` (`ss_body_vals`). No load or unpinned hint
enters: the bits are pinned Boolean and their value by `q_g^4·r_g = len_g`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The body's atoms before its loop. -/
def ssA : List Stmt := [
    .atom (.hint (.bitsExp (.n (val% «shared_selector_tables» "len_g")) 6 (.stack [.n (val% «shared_selector_tables» "nb[0]"), .n (val% «shared_selector_tables» "nb[1]"), .n (val% «shared_selector_tables» "nb[2]"), .n (val% «shared_selector_tables» "nb[3]"), .n (val% «shared_selector_tables» "nb[4]"), .n (val% «shared_selector_tables» "nb[5]")]))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[0]")) (.n (val% «shared_selector_tables» "nb[0]")) (.n (val% «shared_selector_tables» "nb[0]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[1]")) (.n (val% «shared_selector_tables» "nb[1]")) (.n (val% «shared_selector_tables» "nb[1]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[2]")) (.n (val% «shared_selector_tables» "nb[2]")) (.n (val% «shared_selector_tables» "nb[2]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[3]")) (.n (val% «shared_selector_tables» "nb[3]")) (.n (val% «shared_selector_tables» "nb[3]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[4]")) (.n (val% «shared_selector_tables» "nb[4]")) (.n (val% «shared_selector_tables» "nb[4]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[5]")) (.n (val% «shared_selector_tables» "nb[5]")) (.n (val% «shared_selector_tables» "nb[5]"))),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~1")) (word (imFactor 0) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "r_g~2")) (.n (val% «shared_selector_tables» "nb[0]")) (.n (val% «shared_selector_tables» "r_g~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "r_g~3")) (.n (val% «shared_selector_tables» "r_g~0")) (.n (val% «shared_selector_tables» "r_g~2"))),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~4")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~5")) (word (imFactor 1) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "r_g~6")) (.n (val% «shared_selector_tables» "nb[1]")) (.n (val% «shared_selector_tables» "r_g~5"))),
    .atom (.add (.n (val% «shared_selector_tables» "r_g~7")) (.n (val% «shared_selector_tables» "r_g~4")) (.n (val% «shared_selector_tables» "r_g~6"))),
    .atom (.mul (.n (val% «shared_selector_tables» "r_g")) (.n (val% «shared_selector_tables» "r_g~3")) (.n (val% «shared_selector_tables» "r_g~7"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@1~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@1~1")) (word (imFactor 0) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@1~2")) (.n (val% «shared_selector_tables» "nb[2]")) (.n (val% «shared_selector_tables» "q_g@1~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@1")) (.n (val% «shared_selector_tables» "q_g@1~0")) (.n (val% «shared_selector_tables» "q_g@1~2"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@2~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@2~1")) (word (imFactor 1) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@2~2")) (.n (val% «shared_selector_tables» "nb[3]")) (.n (val% «shared_selector_tables» "q_g@2~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@2~3")) (.n (val% «shared_selector_tables» "q_g@2~0")) (.n (val% «shared_selector_tables» "q_g@2~2"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@2")) (.n (val% «shared_selector_tables» "q_g@1")) (.n (val% «shared_selector_tables» "q_g@2~3"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@3~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@3~1")) (word (imFactor 2) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@3~2")) (.n (val% «shared_selector_tables» "nb[4]")) (.n (val% «shared_selector_tables» "q_g@3~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@3~3")) (.n (val% «shared_selector_tables» "q_g@3~0")) (.n (val% «shared_selector_tables» "q_g@3~2"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@3")) (.n (val% «shared_selector_tables» "q_g@2")) (.n (val% «shared_selector_tables» "q_g@3~3"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@4~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@4~1")) (word (imFactor 3) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@4~2")) (.n (val% «shared_selector_tables» "nb[5]")) (.n (val% «shared_selector_tables» "q_g@4~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@4~3")) (.n (val% «shared_selector_tables» "q_g@4~0")) (.n (val% «shared_selector_tables» "q_g@4~2"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@4")) (.n (val% «shared_selector_tables» "q_g@3")) (.n (val% «shared_selector_tables» "q_g@4~3"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q4~0")) (.n (val% «shared_selector_tables» "q_g@4")) (.n (val% «shared_selector_tables» "q_g@4"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q4")) (.n (val% «shared_selector_tables» "q4~0")) (.n (val% «shared_selector_tables» "q4~0"))),
    .atom (.mul (.n (val% «shared_selector_tables» "s7#0")) (.n (val% «shared_selector_tables» "q4")) (.n (val% «shared_selector_tables» "r_g"))),
    .atom (.assertEq (.n (val% «shared_selector_tables» "s7#0")) (.n (val% «shared_selector_tables» "len_g"))),
    .atom (.const (.n (val% «shared_selector_tables» "s8#0")) (word 1 0)),
    .atom (.add (.n (val% «shared_selector_tables» "s8#1")) (.n (val% «shared_selector_tables» "s8#0")) (.n (val% «shared_selector_tables» "q_g@4"))),
    .atom (.const (.n (val% «shared_selector_tables» "s8#2")) (word 1 0))]

/-- The body's straight statements, before its dispatch. -/
def ssS : List Stmt := [
    .atom (.hint (.bitsExp (.n (val% «shared_selector_tables» "len_g")) 6 (.stack [.n (val% «shared_selector_tables» "nb[0]"), .n (val% «shared_selector_tables» "nb[1]"), .n (val% «shared_selector_tables» "nb[2]"), .n (val% «shared_selector_tables» "nb[3]"), .n (val% «shared_selector_tables» "nb[4]"), .n (val% «shared_selector_tables» "nb[5]")]))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[0]")) (.n (val% «shared_selector_tables» "nb[0]")) (.n (val% «shared_selector_tables» "nb[0]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[1]")) (.n (val% «shared_selector_tables» "nb[1]")) (.n (val% «shared_selector_tables» "nb[1]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[2]")) (.n (val% «shared_selector_tables» "nb[2]")) (.n (val% «shared_selector_tables» "nb[2]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[3]")) (.n (val% «shared_selector_tables» "nb[3]")) (.n (val% «shared_selector_tables» "nb[3]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[4]")) (.n (val% «shared_selector_tables» "nb[4]")) (.n (val% «shared_selector_tables» "nb[4]"))),
    .atom (.mul (.n (val% «shared_selector_tables» "nb[5]")) (.n (val% «shared_selector_tables» "nb[5]")) (.n (val% «shared_selector_tables» "nb[5]"))),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~1")) (word (imFactor 0) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "r_g~2")) (.n (val% «shared_selector_tables» "nb[0]")) (.n (val% «shared_selector_tables» "r_g~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "r_g~3")) (.n (val% «shared_selector_tables» "r_g~0")) (.n (val% «shared_selector_tables» "r_g~2"))),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~4")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "r_g~5")) (word (imFactor 1) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "r_g~6")) (.n (val% «shared_selector_tables» "nb[1]")) (.n (val% «shared_selector_tables» "r_g~5"))),
    .atom (.add (.n (val% «shared_selector_tables» "r_g~7")) (.n (val% «shared_selector_tables» "r_g~4")) (.n (val% «shared_selector_tables» "r_g~6"))),
    .atom (.mul (.n (val% «shared_selector_tables» "r_g")) (.n (val% «shared_selector_tables» "r_g~3")) (.n (val% «shared_selector_tables» "r_g~7"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@1~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@1~1")) (word (imFactor 0) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@1~2")) (.n (val% «shared_selector_tables» "nb[2]")) (.n (val% «shared_selector_tables» "q_g@1~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@1")) (.n (val% «shared_selector_tables» "q_g@1~0")) (.n (val% «shared_selector_tables» "q_g@1~2"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@2~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@2~1")) (word (imFactor 1) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@2~2")) (.n (val% «shared_selector_tables» "nb[3]")) (.n (val% «shared_selector_tables» "q_g@2~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@2~3")) (.n (val% «shared_selector_tables» "q_g@2~0")) (.n (val% «shared_selector_tables» "q_g@2~2"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@2")) (.n (val% «shared_selector_tables» "q_g@1")) (.n (val% «shared_selector_tables» "q_g@2~3"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@3~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@3~1")) (word (imFactor 2) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@3~2")) (.n (val% «shared_selector_tables» "nb[4]")) (.n (val% «shared_selector_tables» "q_g@3~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@3~3")) (.n (val% «shared_selector_tables» "q_g@3~0")) (.n (val% «shared_selector_tables» "q_g@3~2"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@3")) (.n (val% «shared_selector_tables» "q_g@2")) (.n (val% «shared_selector_tables» "q_g@3~3"))),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@4~0")) (word 1 0)),
    .atom (.const (.n (val% «shared_selector_tables» "q_g@4~1")) (word (imFactor 3) 0)),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@4~2")) (.n (val% «shared_selector_tables» "nb[5]")) (.n (val% «shared_selector_tables» "q_g@4~1"))),
    .atom (.add (.n (val% «shared_selector_tables» "q_g@4~3")) (.n (val% «shared_selector_tables» "q_g@4~0")) (.n (val% «shared_selector_tables» "q_g@4~2"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q_g@4")) (.n (val% «shared_selector_tables» "q_g@3")) (.n (val% «shared_selector_tables» "q_g@4~3"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q4~0")) (.n (val% «shared_selector_tables» "q_g@4")) (.n (val% «shared_selector_tables» "q_g@4"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q4")) (.n (val% «shared_selector_tables» "q4~0")) (.n (val% «shared_selector_tables» "q4~0"))),
    .atom (.mul (.n (val% «shared_selector_tables» "s7#0")) (.n (val% «shared_selector_tables» "q4")) (.n (val% «shared_selector_tables» "r_g"))),
    .atom (.assertEq (.n (val% «shared_selector_tables» "s7#0")) (.n (val% «shared_selector_tables» "len_g"))),
    .atom (.const (.n (val% «shared_selector_tables» "s8#0")) (word 1 0)),
    .atom (.add (.n (val% «shared_selector_tables» "s8#1")) (.n (val% «shared_selector_tables» "s8#0")) (.n (val% «shared_selector_tables» "q_g@4"))),
    .atom (.const (.n (val% «shared_selector_tables» "s8#2")) (word 1 0)),
    .callIf (.n (val% «shared_selector_tables» "s8#1")) name% «shared_selector_tables_loop0» [.n (val% «shared_selector_tables» "s8#2"), .n (val% «shared_selector_tables» "q_g@4"), .n (val% «shared_selector_tables» "eq_tab"), .n (val% «shared_selector_tables» "zeta_hi"), .n (val% «shared_selector_tables» "zeta1_hi"), .n (val% «shared_selector_tables» "g_tab"),
        .n (val% «shared_selector_tables» "gsq_hi")],
    .atom (.mul (.n (val% «shared_selector_tables» "q16~0")) (.n (val% «shared_selector_tables» "q4")) (.n (val% «shared_selector_tables» "q4"))),
    .atom (.mul (.n (val% «shared_selector_tables» "q16")) (.n (val% «shared_selector_tables» "q16~0")) (.n (val% «shared_selector_tables» "q16~0"))),
    .atom (.mul (.n (val% «shared_selector_tables» "done~1")) (.n (val% «shared_selector_tables» "eq_tab")) (.n (val% «shared_selector_tables» "q16"))),
    .atom (.mul (.n (val% «shared_selector_tables» "done~2")) (.n (val% «shared_selector_tables» "done~1")) (.n (val% «shared_selector_tables» "q16"))),
    .atom (.mul (.n (val% «shared_selector_tables» "done~3")) (.n (val% «shared_selector_tables» "g_tab")) (.n (val% «shared_selector_tables» "q16"))),
    .atom (.mul (.n (val% «shared_selector_tables» "done~4")) (.n (val% «shared_selector_tables» "zeta_hi")) (.n (val% «shared_selector_tables» "q4"))),
    .atom (.mul (.n (val% «shared_selector_tables» "done~5")) (.n (val% «shared_selector_tables» "zeta1_hi")) (.n (val% «shared_selector_tables» "q4"))),
    .atom (.mul (.n (val% «shared_selector_tables» "done~6")) (.n (val% «shared_selector_tables» "gsq_hi")) (.n (val% «shared_selector_tables» "q4")))]

/-- The body's dispatch. -/
def ssDispV : Stmt := .dispatch (.n (val% «shared_selector_tables» "r_g")) ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n (val% «shared_selector_tables» "done~2"), .n (val% «shared_selector_tables» "done~3"), .n (val% «shared_selector_tables» "done~4"), .n (val% «shared_selector_tables» "done~5"), .n (val% «shared_selector_tables» "done~6")] [.n (val% «shared_selector_tables» "done")]

theorem ssPre_eq_disp : ssPre = ssS ++ [ssDispV] := rfl

theorem ssA_eq_take : ssS.take 42 = ssA := rfl

/-- **The loop end and the selector are the length's.** -/
theorem ss_body_vals {C : CallRel} {rd : Reader} {σ : Val} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ ssA next kret) {n : ℕ} (hn : n < 64)
    (h5 : σ (.n (val% «shared_selector_tables» "len_g")) = gen ^ n) :
    σ (.n (val% «shared_selector_tables» "q_g@4")) = gen ^ (n / 4) ∧ σ (.n (val% «shared_selector_tables» "r_g")) = gen ^ (n % 4) ∧
      σ (.n (val% «shared_selector_tables» "s8#1")) = 1 + gen ^ (n / 4) ∧ σ (.n (val% «shared_selector_tables» "s8#2")) = 1 := by
  simp only [ssA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨p6, p7, p8, p9, p10, p11, c12, c13, m14, a15, c16, c17, m18, a19, m20, c21, c22, m23,
    a24, c25, c26, m27, a28, m29, c30, c31, m32, a33, m34, c35, c36, m37, a38, m39, m40, m41, m42,
    e42, c43, a44, c45, -⟩ := h
  let f : ℕ → Bool := fun k ↦ decide (σ (.n (6 + k)) = 1)
  have pin : ∀ k < 6, σ (.n ((val% «shared_selector_tables» "nb[0]") + k)) * σ (.n ((val% «shared_selector_tables» "nb[0]") + k)) = σ (.n ((val% «shared_selector_tables» "nb[0]") + k)) := by
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
  have hrg : σ (.n (val% «shared_selector_tables» "r_g")) = gen ^ r := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + j))) (n := 2) (by norm_num)
      (fun j hj => pin j (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m20, a15, a19, c12, c16, m14, m18, c13, c17, word_one, this]
  have hqg : σ (.n (val% «shared_selector_tables» "q_g@4")) = gen ^ q := by
    have := ss_prod (b := fun j ↦ σ (.n (6 + (j + 2)))) (n := 4) le_rfl
      (fun j hj => pin (j + 2) (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m39, m34, m29, a24, a28, a33, a38, c21, c25, c30, c35, m23, m27, m32, m37, c22, c26, c31,
      c36, word_one, this]
  have hq4 : σ (.n (val% «shared_selector_tables» "q4")) = gen ^ (4 * q) := by rw [m41, m40, hqg]; ring
  have hn' : 4 * q + r = n := by
    have e : gen ^ (4 * q + r) = gen ^ n := by
      rw [← h5, ← e_add_eq_zero_iff.mp e42, m42, hq4, hrg, ← pow_add]
    exact gen_pow_inj (by omega) (by omega) e
  have hq : q = n / 4 := by omega
  have hr : r = n % 4 := by omega
  refine ⟨by rw [hqg, hq], by rw [hrg, hr], by rw [a44, c43, word_one, hqg, hq],
    by rw [c45, word_one]⟩

end
end LeanVM.Guest.B1.Tables
