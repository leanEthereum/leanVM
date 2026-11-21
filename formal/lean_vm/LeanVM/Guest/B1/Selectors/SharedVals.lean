/-
  LeanVM.Guest.B1.Selectors.SharedVals

  `shared_selector_tables`' loop end and dispatch selector on every valuation satisfying its body:
  functions of its length arguments alone.
-/

module

public import LeanVM.Guest.B1.Selectors.SharedTables
public import LeanVM.Guest.Data.NameStrings

/-!
# `shared_selector_tables`' loop end

On every valuation satisfying the body's atoms before its loop (`ssA`; any memory, any call
relation), with `len_g = g^n`, `n < 64`, and `q_g = g^(n / 4)` (`σ 6`, the end
`shared_selector_tables_loop0` runs to): `r_g = len_g / q_g^4 = g^(n % 4)` (`σ 9`, the dispatch's
selector), the loop's condition is `1 + g^(n / 4)` and its start `1` (`ss_body_vals`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The body's atoms before its loop. -/
def ssA : List Stmt := [
    .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 7)),
    .atom (.mul (.n 5) (.n 9) (.n 8)),
    .atom (.const (.n 10) (word 1 0)),
    .atom (.add (.n 11) (.n 10) (.n 6)),
    .atom (.const (.n 12) (word 1 0))]

/-- The body's straight statements, before its dispatch. -/
def ssS : List Stmt := ssA ++ [
    .callIf (.n 11) name% «shared_selector_tables_loop0» [.n 12, .n 6, .n 0, .n 2, .n 3, .n 1,
        .n 4],
    .atom (.mul (.n 13) (.n 8) (.n 8)),
    .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.const (.n 15) (word 8 0)),
    .atom (.rangeCheck (.n 9) (.n 16) (.n 17) (.n 18) (.n 15)),
    .atom (.mul (.n 19) (.n 0) (.n 14)),
    .atom (.mul (.n 20) (.n 19) (.n 14)),
    .atom (.mul (.n 21) (.n 1) (.n 14)),
    .atom (.mul (.n 22) (.n 2) (.n 8)),
    .atom (.mul (.n 23) (.n 3) (.n 8)),
    .atom (.mul (.n 24) (.n 4) (.n 8))]

/-- The body's dispatch. -/
def ssDispV : Stmt := .dispatch (.n 9) ["sel_partial_nibble__L0", "sel_partial_nibble__L1", "sel_partial_nibble__L2", "sel_partial_nibble__L3"] [.n 20, .n 21, .n 22, .n 23, .n 24] [.n 25]

theorem ssPre_eq_disp : ssPre = ssS ++ [ssDispV] := rfl

theorem ssA_eq_take : ssS.take 6 = ssA := rfl

/-- **The selector and the loop's ends are the lengths'.** -/
theorem ss_body_vals {C : CallRel} {rd : Reader} {σ : Val} {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ ssA next kret) {n : ℕ}
    (h5 : σ (.n 5) = gen ^ n) (h6 : σ (.n 6) = gen ^ (n / 4)) :
    σ (.n 9) = gen ^ (n % 4) ∧ σ (.n 11) = 1 + gen ^ (n / 4) ∧ σ (.n 12) = 1 := by
  simp only [ssA, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨m7, m8, m5, c10, a11, c12, -⟩ := h
  have hq4 : σ (.n 8) = gen ^ (4 * (n / 4)) := by rw [m8, m7, h6]; ring
  refine ⟨?_, by rw [a11, c10, tb_word_one, h6], by rw [c12, tb_word_one]⟩
  refine mul_right_cancel₀ (gen_pow_ne_zero (4 * (n / 4))) ?_
  have e := m5
  rw [h5, hq4] at e
  rw [← e, ← pow_add, show n % 4 + 4 * (n / 4) = n by omega]

end
end LeanVM.Guest.B1.Tables
