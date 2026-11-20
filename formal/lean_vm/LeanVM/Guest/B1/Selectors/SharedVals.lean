/-
  LeanVM.Guest.B1.Selectors.SharedVals

  `shared_selector_tables`' loop end, dispatch selector and tables' sizes on every valuation
  satisfying its body: functions of its length argument alone.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables
public import LeanVM.Guest.Data.NameStrings

/-!
# `shared_selector_tables`' loop end

On every valuation satisfying the body's atoms before its loop (`ssA`; any memory, any call
relation), with `len_g = g^n`, `n < 64`: the hinted bits rebuild `q_g = g^(n / 4)` (`σ 37`, the
end `shared_selector_tables_loop0` runs to) and `r_g = g^(n % 4)` (`σ 18`, the dispatch's selector),
the tables' sizes are `g^(32 (q + 1))` and `g^(16 (q + 1))` (`σ 47`, `σ 46`), the loop's condition
is `1 + g^(n / 4)` and its start `1` (`ss_body_vals`). No load or unpinned hint enters: the bits are
pinned Boolean and their value by `q_g^4·r_g = len_g`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The body's atoms before its loop. -/
def ssA : List Stmt := [
    .atom (.hint (.bitsExp (.n 3) 6 (.stack [.n 4, .n 5, .n 6, .n 7, .n 8, .n 9]))),
    .atom (.mul (.n 4) (.n 4) (.n 4)), .atom (.mul (.n 5) (.n 5) (.n 5)),
    .atom (.mul (.n 6) (.n 6) (.n 6)), .atom (.mul (.n 7) (.n 7) (.n 7)),
    .atom (.mul (.n 8) (.n 8) (.n 8)), .atom (.mul (.n 9) (.n 9) (.n 9)),
    .atom (.const (.n 10) (word 1 0)), .atom (.const (.n 11) (word (imFactor 0) 0)),
    .atom (.mul (.n 12) (.n 4) (.n 11)), .atom (.add (.n 13) (.n 10) (.n 12)),
    .atom (.const (.n 14) (word 1 0)), .atom (.const (.n 15) (word (imFactor 1) 0)),
    .atom (.mul (.n 16) (.n 5) (.n 15)), .atom (.add (.n 17) (.n 14) (.n 16)),
    .atom (.mul (.n 18) (.n 13) (.n 17)),
    .atom (.const (.n 19) (word 1 0)), .atom (.const (.n 20) (word (imFactor 0) 0)),
    .atom (.mul (.n 21) (.n 6) (.n 20)), .atom (.add (.n 22) (.n 19) (.n 21)),
    .atom (.const (.n 23) (word 1 0)), .atom (.const (.n 24) (word (imFactor 1) 0)),
    .atom (.mul (.n 25) (.n 7) (.n 24)), .atom (.add (.n 26) (.n 23) (.n 25)),
    .atom (.mul (.n 27) (.n 22) (.n 26)),
    .atom (.const (.n 28) (word 1 0)), .atom (.const (.n 29) (word (imFactor 2) 0)),
    .atom (.mul (.n 30) (.n 8) (.n 29)), .atom (.add (.n 31) (.n 28) (.n 30)),
    .atom (.mul (.n 32) (.n 27) (.n 31)),
    .atom (.const (.n 33) (word 1 0)), .atom (.const (.n 34) (word (imFactor 3) 0)),
    .atom (.mul (.n 35) (.n 9) (.n 34)), .atom (.add (.n 36) (.n 33) (.n 35)),
    .atom (.mul (.n 37) (.n 32) (.n 36)),
    .atom (.mul (.n 38) (.n 37) (.n 37)), .atom (.mul (.n 39) (.n 38) (.n 38)),
    .atom (.mul (.n 40) (.n 39) (.n 18)), .atom (.assertEq (.n 40) (.n 3)),
    .atom (.const (.n 41) (word 2 0)), .atom (.mul (.n 42) (.n 37) (.n 41)),
    .atom (.mul (.n 43) (.n 42) (.n 42)), .atom (.mul (.n 44) (.n 43) (.n 43)),
    .atom (.mul (.n 45) (.n 44) (.n 44)), .atom (.mul (.n 46) (.n 45) (.n 45)),
    .atom (.mul (.n 47) (.n 46) (.n 46)),
    .atom (.hint (.allocDyn (.n 48) (.n 47))), .atom (.hint (.allocDyn (.n 49) (.n 46))),
    .atom (.const (.n 50) (word 1 0)), .atom (.add (.n 51) (.n 50) (.n 37)),
    .atom (.const (.n 52) (word 1 0))]

/-- The body's straight statements, before its dispatch. -/
def ssS : List Stmt := ssA ++ [
    .callIf (.n 51) name% «shared_selector_tables_loop0» [.n 52, .n 37, .n 48, .n 0, .n 1, .n 49,
        .n 2],
    .atom (.mul (.n 53) (.n 39) (.n 39)), .atom (.mul (.n 54) (.n 53) (.n 53)),
    .atom (.mul (.n 55) (.n 48) (.n 54)), .atom (.mul (.n 56) (.n 55) (.n 54)),
    .atom (.mul (.n 57) (.n 49) (.n 54)), .atom (.mul (.n 58) (.n 0) (.n 39)),
    .atom (.mul (.n 59) (.n 1) (.n 39)), .atom (.mul (.n 60) (.n 2) (.n 39))]

/-- The body's dispatch. -/
def ssDispV : Stmt := .dispatch (.n 18) ["sel_partial_nibble__L0", "sel_partial_nibble__L1",
  "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 56, .n 57, .n 58, .n 59, .n 60] [.n 61]

/-- The body's copies of its two tables, after its dispatch. -/
def ssTail : List Stmt := [.atom (.copy (.n 62) (.n 48)), .atom (.copy (.n 63) (.n 49))]

theorem ssPre_eq_disp : ssPre = ssS ++ ssDispV :: ssTail := rfl

/-- The tables' sizes: `32 (q + 1)` and `16 (q + 1)` words, `q = n / 4`. -/
def ssEqW (n : ℕ) : ℕ := 32 * (n / 4 + 1)

/-- The `g` table's size. -/
def ssGW (n : ℕ) : ℕ := 16 * (n / 4 + 1)

/-- **The loop end, the selector and the tables' sizes are the length's.** -/
theorem ss_body_vals {C : CallRel} {rd : Reader} {σ : Val} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ ssA next kret) {n : ℕ} (hn : n < 64)
    (h3 : σ (.n 3) = gen ^ n) :
    σ (.n 37) = gen ^ (n / 4) ∧ σ (.n 18) = gen ^ (n % 4) ∧
      σ (.n 51) = 1 + gen ^ (n / 4) ∧ σ (.n 52) = 1 ∧ σ (.n 47) = gen ^ ssEqW n ∧
      σ (.n 46) = gen ^ ssGW n := by
  simp only [ssA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and] at h
  obtain ⟨p4, p5, p6, p7, p8, p9, c10, c11, m12, a13, c14, c15, m16, a17, m18, c19, c20, m21,
    a22, c23, c24, m25, a26, m27, c28, c29, m30, a31, m32, c33, c34, m35, a36, m37, m38, m39, m40,
    e40, c41, m42, m43, m44, m45, m46, m47, c50, a51, c52, -⟩ := h
  let f : ℕ → Bool := fun k ↦ decide (σ (.n (4 + k)) = 1)
  have pin : ∀ k < 6, σ (.n (4 + k)) * σ (.n (4 + k)) = σ (.n (4 + k)) := by
    intro k hk
    interval_cases k
    · exact p4.symm
    · exact p5.symm
    · exact p6.symm
    · exact p7.symm
    · exact p8.symm
    · exact p9.symm
  let r := bitsVal f 2
  let q := bitsVal (fun k ↦ f (k + 2)) 4
  have hr4 : r < 4 := bitsVal_lt f 2
  have hq16 : q < 16 := bitsVal_lt _ 4
  have hrg : σ (.n 18) = gen ^ r := by
    have := ss_prod (b := fun j ↦ σ (.n (4 + j))) (n := 2) (by norm_num)
      (fun j hj => pin j (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m18, a13, a17, c10, c14, m12, m16, c11, c15, tb_word_one, this]
  have hqg : σ (.n 37) = gen ^ q := by
    have := ss_prod (b := fun j ↦ σ (.n (4 + (j + 2)))) (n := 4) le_rfl
      (fun j hj => pin (j + 2) (by omega))
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, Nat.reduceAdd] at this
    rw [m37, m32, m27, a22, a26, a31, a36, c19, c23, c28, c33, m21, m25, m30, m35, c20, c24, c29,
      c34, tb_word_one, this]
  have hq4 : σ (.n 39) = gen ^ (4 * q) := by rw [m39, m38, hqg]; ring
  have hn' : 4 * q + r = n := by
    have e : gen ^ (4 * q + r) = gen ^ n := by
      rw [← h3, ← e_add_eq_zero_iff.mp e40, m40, hq4, hrg, ← pow_add]
    exact gen_pow_inj (by omega) (by omega) e
  have hq : q = n / 4 := by omega
  have hr : r = n % 4 := by omega
  have h42 : σ (.n 42) = gen ^ (n / 4 + 1) := by rw [m42, c41, hqg, hq, tb_word_gen]; ring
  have h46 : σ (.n 46) = gen ^ ssGW n := by
    rw [m46, m45, m44, m43, h42, ssGW]; ring
  refine ⟨by rw [hqg, hq], by rw [hrg, hr], by rw [a51, c50, tb_word_one, hqg, hq],
    by rw [c52, tb_word_one], by rw [m47, h46, ssEqW, ssGW]; ring, h46⟩

end
end LeanVM.Guest.B1.Tables
