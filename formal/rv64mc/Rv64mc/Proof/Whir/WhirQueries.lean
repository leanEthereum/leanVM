/-
  Rv64mc.Proof.Whir.WhirQueries

  `whir_queries` keeps its contract (`Spec.Whir.WhirQueries.spec`), over any program holding its template, with
  `WHIR_QUERIES` at the template's data reference (`Table`): the three range checks give `None`, the last path
  reads the slice header at row `log_inv_rate - 1`, column `log_n - 16`.
-/

import Rv64mc.Spec.Whir.WhirQueries
import Rv64mc.Gen.Tmpl.Verifier.Whir.WhirQueries
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Whir.WhirQueries

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Whir Rv64mc.Spec.Whir.WhirQueries
open Rv64mc.Gen.Verifier.Whir.WhirQueries (Link tmpl)

/-! ## The table's shape -/

theorem table_length : Model.whirQueriesTable.length = 4 := rfl

theorem row_length : ∀ r (h : r < Model.whirQueriesTable.length), (Model.whirQueriesTable[r]).length = 15 := by
  decide

theorem queries_none_rate {n r : Nat} (h : r = 0 ∨ 4 < r) : Model.whirQueriesRust n r = none := by
  unfold Model.whirQueriesRust Model.checkedSub
  rcases h with rfl | h
  · rfl
  · simp only [show 1 ≤ r by omega, ite_true, Option.bind_eq_bind, Option.bind_some]
    rw [List.getElem?_eq_none (by rw [table_length]; omega)]; rfl

theorem queries_none_size {n r : Nat} (hr : 1 ≤ r ∧ r ≤ 4) (h : n < 16 ∨ 30 < n) :
    Model.whirQueriesRust n r = none := by
  unfold Model.whirQueriesRust Model.checkedSub
  simp only [hr.1, ite_true, Option.bind_eq_bind, Option.bind_some]
  rw [List.getElem?_eq_getElem (by rw [table_length]; omega), Option.bind_some]
  rcases h with h | h
  · simp [show ¬ 16 ≤ n by omega]
  · simp only [show 16 ≤ n by omega, ite_true, Option.bind_some]
    rw [List.getElem?_eq_none (by rw [row_length _ (by rw [table_length]; omega)]; omega)]

theorem queries_some {n r : Nat} (h1 : 1 ≤ r) (h2 : r ≤ 4) (h3 : 16 ≤ n) (h4 : n ≤ 30) :
    Model.whirQueriesRust n r = some ((Model.whirQueriesTable[r - 1]'(by rw [table_length]; omega))[n - 16]'(by
      rw [row_length _ (by rw [table_length]; omega)]; omega)) := by
  unfold Model.whirQueriesRust Model.checkedSub
  simp only [h1, h3, ite_true, Option.bind_eq_bind, Option.bind_some]
  rw [List.getElem?_eq_getElem (by rw [table_length]; omega), Option.bind_some, List.getElem?_eq_getElem]

/-! ## The machine's tests and address -/

theorem rate_bad {w : Word} (h : 3#64 < w + 18446744073709551615#64) : w.toNat = 0 ∨ 4 < w.toNat := by
  bv_omega

theorem rate_ok {w : Word} (h : w + 18446744073709551615#64 ≤ 3#64) : 1 ≤ w.toNat ∧ w.toNat ≤ 4 := by
  bv_omega

theorem size_lo {w : Word} (h : w < 16#64) : w.toNat < 16 := by bv_omega

theorem size_hi {w : Word} (h : 14#64 < w + 18446744073709551600#64) (h' : 16#64 ≤ w) : 30 < w.toNat := by
  bv_omega

theorem size_ok {w : Word} (h : w + 18446744073709551600#64 ≤ 14#64) (h' : 16#64 ≤ w) :
    16 ≤ w.toNat ∧ w.toNat ≤ 30 := by
  bv_omega

/-- The header's address the code computes, `rate * 240 + (size - 16) * 16 - 240`, and an offset `k` in it. -/
theorem addr_eq (a w10 w11 c : Word) (k : Nat) (hc : c.toNat = 2 ^ 64 - 240 + k)
    (h10 : 16 ≤ w10.toNat ∧ w10.toNat ≤ 30) (h11 : 1 ≤ w11.toNat ∧ w11.toNat ≤ 4) :
    a + (w11 <<< 8 - w11 <<< 4) + (w10 + 18446744073709551600#64) <<< 4 + c =
      a + BitVec.ofNat 64 (240 * (w11.toNat - 1) + 16 * (w10.toNat - 16)) + BitVec.ofNat 64 k := by
  have e1 : (w11 <<< 8).toNat = 256 * w11.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have e2 : (w11 <<< 4).toNat = 16 * w11.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have e3 : (w10 + 18446744073709551600#64).toNat = w10.toNat - 16 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e4 : ((w10 + 18446744073709551600#64) <<< 4).toNat = 16 * (w10.toNat - 16) := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, e3, Nat.mod_eq_of_lt (by omega)]; omega
  have e5 : (w11 <<< 8 - w11 <<< 4).toNat = 240 * w11.toNat := by
    rw [BitVec.toNat_sub, e1, e2]; omega
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]
  rw [BitVec.add_right_inj]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, e5, e4, hc, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- **`whir_queries` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (htab : Table env L.d_c960_dba1010e.addr) : spec env p i need := by
  rv_auto hp with [hL]
  · rw [queries_none_rate (rate_bad hc)]
  · rw [queries_none_size (rate_ok hc_1) (.inl (size_lo hc))]
  · rw [queries_none_size (rate_ok hc_1) (.inr (size_hi hc hc_2))]
  · have hr := rate_ok hc_1
    have hn := size_ok hc hc_2
    rw [queries_some hr.1 hr.2 hn.1 hn.2]
    obtain ⟨ptr, hptr, hhd, hq⟩ := htab ((regs .x11).toNat - 1) ((regs .x10).toNat - 16)
      (by rw [table_length]; omega) (by rw [row_length _ (by rw [table_length]; omega)]; omega)
    have e0 := hhd.getMem hpre_4 (k := 0) (by simp)
    have e1 := hhd.getMem hpre_4 (k := 1) (by simp)
    rw [hL.d_c960_dba1010e, addr_eq _ _ _ 18446744073709551376#64 0 (by decide) hn hr,
      addr_eq _ _ _ 18446744073709551384#64 8 (by decide) hn hr]
    simp only [Nat.mul_zero, Nat.mul_one, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1
    exact ⟨by rw [Tactic.rf_get_x10, e0]; exact hptr, by rw [Tactic.rf_get_x11, e1],
      by rw [Tactic.rf_get_x10, e0]; exact hq⟩

end Rv64mc.Proof.Whir.WhirQueries
