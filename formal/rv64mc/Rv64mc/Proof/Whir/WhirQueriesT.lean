/-
  Rv64mc.Proof.Whir.WhirQueriesT

  `whir_queries` is total: it returns `WhirQueries.Post`'s slice (`Spec.Whir.WhirQueries`), over any program holding
  its template, given the table `WHIR_QUERIES` (`Table`, words of the static data). The partial proof
  (`WhirQueries.lean`) ported by `rv_autoT`; the header's two loads are static data words, in a window and aligned by
  `Windows.data_ok`.

  ## Main definitions

  * `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Whir.WhirQueries
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Whir.WhirQueriesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Whir Rv64mc.Spec.Whir.WhirQueries
open Rv64mc.Proof.Whir.WhirQueries
open Rv64mc.Gen.Verifier.Whir.WhirQueries (Link tmpl)

/-- **The total contract of `whir_queries`**: `WhirQueries.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) (Post env)

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (htab : Table env L.d_c960_dba1010e.addr) : specT env p i need := by
  rv_autoT hp with [hL]
  · rw [queries_none_rate (rate_bad hc)]
  · rw [queries_none_size (rate_ok hc_1) (.inl (size_lo hc))]
  · rw [queries_none_size (rate_ok hc_1) (.inr (size_hi hc hc_2))]
  all_goals
    have hr := rate_ok hc_1
    have hn := size_ok hc hc_2
    obtain ⟨ptr, hptr, hhd, hq⟩ := htab ((regs .x11).toNat - 1) ((regs .x10).toNat - 16)
      (by rw [table_length]; omega) (by rw [row_length _ (by rw [table_length]; omega)]; omega)
    have hW : Windows env top m := ‹_›
    have d0 := hW.data_ok _ (hhd 0 (by simp))
    have d1 := hW.data_ok _ (hhd 1 (by simp))
    rw [hL.d_c960_dba1010e] at *
    try rw [addr_eq _ _ _ 18446744073709551376#64 0 (by decide) hn hr]
    try rw [addr_eq _ _ _ 18446744073709551384#64 8 (by decide) hn hr]
  · simpa using d0.1
  · simpa using d0.2
  · simpa using d1.1
  · simpa using d1.2
  · rw [queries_some hr.1 hr.2 hn.1 hn.2]
    have e0 := hhd.getMem hpre_4 (k := 0) (by simp)
    have e1 := hhd.getMem hpre_4 (k := 1) (by simp)
    simp only [Nat.mul_zero, Nat.mul_one, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1
    exact ⟨by rw [Tactic.rf_get_x10, e0]; exact hptr, by rw [Tactic.rf_get_x11, e1],
      by rw [Tactic.rf_get_x10, e0]; exact hq⟩

end Rv64mc.Proof.Whir.WhirQueriesT

/-- info: 'Rv64mc.Proof.Whir.WhirQueriesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.WhirQueriesT.total
