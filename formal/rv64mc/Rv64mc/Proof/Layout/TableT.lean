/-
  Rv64mc.Proof.Layout.TableT

  `Table::n_constraints` and `Table::count_columns` are total: `Spec.Layout.Table`'s postconditions, or the run ends
  with the guest's abort (`AbortStop`) past the sixth table, from `panic_bounds_check`'s `Aborts`. The partial proofs
  (`Table.lean`) ported by `rv_autoT`. The table read lies in the static data: each takes its table in `env.data`
  (`DataRef.InData`, an environment fact as `FieldT.ClmulTable` is), whose `Windows.data_ok` puts the loaded words in
  a window and aligned; `count_columns` also takes `CountColumnsData`, which its partial proof takes.

  ## Main definitions

  * `nConstraintsSpecT`, `countColumnsSpecT`

  ## Main results

  * `nConstraints_total`, `countColumns_total`
-/

import Rv64mc.Proof.Layout.Table
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Layout.TableT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout.Table Rv64mc.Proof.Layout.Table
open Rv64mc.Proof.Runtime (Aborts)

/-- **The total contract of `Table::n_constraints`.** -/
def nConstraintsSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) NConstraintsPost (Stop := AbortStop)

/-- **The total contract of `Table::count_columns`.** -/
def countColumnsSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) (CountColumnsPost env) (Stop := AbortStop)

set_option rv_sym.heap true in
theorem nConstraints_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Gen.Verifier.Layout.Table.NConstraints.Link)
    (hp : p[i]? = some (Gen.Verifier.Layout.Table.NConstraints.tmpl L))
    (hdata : DataRef.InData env [(L.d_c48_401b839e, Gen.Verifier.Layout.Table.NConstraints.d_c48_401b839e_words)])
    {need : Nat} (hpanic : Aborts env p L.panicBoundsCheck.idx need) (hL : L.WF p) :
    nConstraintsSpecT env p i need := by
  have hw := hdata.words (List.mem_singleton_self _)
  have hl : Gen.Verifier.Layout.Table.NConstraints.d_c48_401b839e_words.length = 6 := rfl
  rv_autoT hp with [hL] using [hpanic]
  all_goals
    obtain ⟨e, hk⟩ := shl_small hc 3
    rw [e, show 2 ^ 3 * (regs .x10).toNat = 8 * (regs .x10).toNat from rfl]
  · exact (hpre_7.data_ok _ (hdata _ (List.mem_singleton_self _) (regs .x10).toNat (by rw [hl]; omega))).1
  · exact (hpre_7.data_ok _ (hdata _ (List.mem_singleton_self _) (regs .x10).toNat (by rw [hl]; omega))).2
  · rw [hw.get hpre_4 _ (by rw [hl]; omega)]
    simp only [Model.nConstraintsRust, Gen.Verifier.Layout.Table.NConstraints.d_c48_401b839e_words]
    rcases (by omega : (regs .x10).toNat = 0 ∨ (regs .x10).toNat = 1 ∨ (regs .x10).toNat = 2 ∨
      (regs .x10).toNat = 3 ∨ (regs .x10).toNat = 4 ∨ (regs .x10).toNat = 5) with h | h | h | h | h | h <;>
      simp [h]

set_option rv_sym.heap true in
theorem countColumns_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Gen.Verifier.Layout.Table.CountColumns.Link)
    (hp : p[i]? = some (Gen.Verifier.Layout.Table.CountColumns.tmpl L))
    (hin : DataRef.InData env [(L.d_c96_da3654e1, Gen.Verifier.Layout.Table.CountColumns.d_c96_da3654e1_words L)])
    (hdata : CountColumnsData env L.d_c96_da3654e1)
    {need : Nat} (hpanic : Aborts env p L.panicBoundsCheck.idx need) (hL : L.WF p) :
    countColumnsSpecT env p i need := by
  rv_autoT hp with [hL] using [hpanic]
  all_goals
    obtain ⟨e, hk⟩ := shl_small hc 4
    have e8 : L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (16 * (regs .x10).toNat) + 8#64 =
        L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (8 * (2 * (regs .x10).toNat + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    have e0 : L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (16 * (regs .x10).toNat) =
        L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (8 * (2 * (regs .x10).toNat)) := by
      congr 2; omega
    have hlen : (Gen.Verifier.Layout.Table.CountColumns.d_c96_da3654e1_words L).length = 12 := rfl
    have d0 := hpre_7.data_ok _ (hin _ (List.mem_singleton_self _) (2 * (regs .x10).toNat) (by rw [hlen]; omega))
    have d1 := hpre_7.data_ok _ (hin _ (List.mem_singleton_self _) (2 * (regs .x10).toNat + 1)
      (by rw [hlen]; omega))
    rw [e, show 2 ^ 4 * (regs .x10).toNat = 16 * (regs .x10).toNat from rfl]
  · rw [e0]; exact d0.1
  · rw [e0]; exact d0.2
  · rw [e8]; exact d1.1
  · rw [e8]; exact d1.2
  · obtain ⟨q, hq⟩ := hdata (regs .x10).toNat (by omega)
    intro M hM
    obtain ⟨h1, h2, -⟩ := hq m hpre_4
    obtain ⟨-, -, h3⟩ := hq M hM
    have e8' : L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (16 * (regs .x10).toNat) + 8#64 =
        L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (16 * (regs .x10).toNat + 8) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
    rw [e8', h1, h2]
    exact ⟨by simp, h3⟩

end Rv64mc.Proof.Layout.TableT

/-- info: 'Rv64mc.Proof.Layout.TableT.nConstraints_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.TableT.nConstraints_total

/-- info: 'Rv64mc.Proof.Layout.TableT.countColumns_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.TableT.countColumns_total
