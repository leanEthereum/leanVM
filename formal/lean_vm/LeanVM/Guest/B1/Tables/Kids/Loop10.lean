/-
  LeanVM.Guest.B1.Tables.Kids.Loop10

  `verify_tables_loop0` (the table sumcheck's rounds) loads from any region holding the rounds'
  records, the challenges, the running products and the round polynomials at the records' cursors.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.B1.Tables.Vt.Loop10
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables_loop0»

/-!
# `verify_tables_loop0`, loading from a region

Iteration `k < K` of `verify_tables_loop0` (`x = g^k`, the end `g^K`) reads record `k` at
`rounds·g^(7k)` (offsets `5`, `6`, `12`, `13`; `sumcheck_round4` its first `12` words and the `3` words
at its cursor, not `tabs`), writes the challenge at `rk·g^k` and the running product at `cprod·g^k`
(offsets `0`, `1`). `loop10_relIn`: by induction on the derivation's depth, every iteration loads from
`R` when the runs `rounds` (`7(K+1)`), `rk` (`K`), `cprod` (`K+1`) lie in `R` and every record's cursor
word points at `3` words in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `verify_tables_loop0`'s statements before its `ret`. -/
def l10Pre : List Stmt := l10Body.dropLast

theorem l10Body_eq : l10Body = l10Pre ++ [.ret []] := by simp [l10Pre, l10Body]

theorem l10_flat : l10Pre.all Stmt.flat = true := by decide +kernel

theorem l10_noDisp : l10Pre.all noDispB = true := by decide +kernel

/-- The pointers `verify_tables_loop0` loads through, and their runs. -/
def l10Tbl : List (ℕ × ℕ) := [(10, 14), (16, 1), (17, 1), (20, 2)]

theorem l10_loads : l10Pre.all (loadsViaB l10Tbl) = true := by decide +kernel

theorem l10_calls : l10Pre.filterMap Main.Stmt.callS =
    [(none, "sumcheck_round4", [.n (val% «verify_tables_loop0» "rd"), .n (val% «verify_tables_loop0» "ncur~3"), .n (val% «verify_tables_loop0» "ncur~4"), .n (val% «verify_tables_loop0» "tabs")], [.n (val% «verify_tables_loop0» "ncur"), .n (val% «verify_tables_loop0» "nclaim"), .n (val% «verify_tables_loop0» "rk")]),
      (some (.n (val% «verify_tables_loop0» "s8#2")), name% «verify_tables_loop0», [.n (val% «verify_tables_loop0» "s8#4"), .n (val% «verify_tables_loop0» "bound"), .n (val% «verify_tables_loop0» "zc_rounds"), .n (val% «verify_tables_loop0» "tabs"), .n (val% «verify_tables_loop0» "zc_rk"), .n (val% «verify_tables_loop0» "zc_cprod")], [])] := by
  decide +kernel

theorem gen_pow_pred_inv {K : ℕ} (hK : 0 < K) : gen ^ K * vtWInvGen = gen ^ (K - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  rw [pow_succ, mul_assoc, mul_comm gen, vtWInvGen_mul, mul_one, Nat.add_sub_cancel]

/-- **`verify_tables_loop0` loads from `R`**, every iteration `k < K`. -/
theorem loop10_relIn {rd : Reader} {R : ℕ → Prop} {K : ℕ}
    {rounds tabs rkb cprod : E} (hr : PtrIn R rounds (7 * (K + 1))) (hc : PtrIn R rkb K)
    (hp : PtrIn R cprod (K + 1))
    (hcur : ∀ k < K, ∀ c, LoadHolds rd (rounds * gen ^ (7 * k)) 5 c → PtrIn R c 3) :
    ∀ d k, k < K →
      coreProgram.relN rd d name% «verify_tables_loop0» [gen ^ k, gen ^ K, rounds, tabs, rkb, cprod] [] →
      coreProgram.RelIn rd R name% «verify_tables_loop0» [gen ^ k, gen ^ K, rounds, tabs, rkb, cprod] [] := by
  intro d
  induction d with
  | zero => intro k _ h; exact h.elim
  | succ d ih =>
    intro k hk h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hpm, hb⟩ := l10Found
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb, l10Body_eq]) l10_flat hsem fun σ hpar hh ↦ ?_
    rw [hpm] at hpar
    simp only [List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
      List.cons_append, List.cons.injEq, and_true] at hpar
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hpar
    rw [hb] at hh
    simp only [l10Body, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hh
    obtain ⟨m6, m7, m8, m9, m10, l11, l12, hcall, m16, l15, l13, l14, m17, l18, m19, m20, l19, c21,
      m22, a23, c24, m25, ⟨-, hnext, -⟩⟩ := hh
    simp only [Atom.Holds] at m6 m7 m8 m9 m10 l11 l12 m16 l15 l13 l14 m17 l18 m19 m20 l19 c21 m22
    simp only [Atom.Holds] at a23 c24 m25
    rw [tb_word_gen] at c21 c24
    have e10 : σ (.n (val% «verify_tables_loop0» "rd")) = rounds * gen ^ (7 * k) := by
      rw [m10, m9, m8, m7, m6, p0, p2]; ring
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp l10_noDisp s hs),
      loads_via l10_loads fun pb hpb ↦ ?_, fun c hc' ht ↦ ?_⟩
    · simp only [l10Tbl, List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl | rfl | rfl
      · rw [e10]; exact ptrIn_mul (ptrIn_mono hr (by omega))
      · rw [m16, p4, p0]; exact ptrIn_mul (ptrIn_mono hc (by omega))
      · rw [m17, p5, p0]; exact ptrIn_mul (ptrIn_mono hp (by omega))
      · rw [m20, p5, p0]; exact ptrIn_mul (ptrIn_mono hp (by omega))
    · rw [filterMap_callSF l10_noDisp, l10_calls] at hc'
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl
      · -- the round
        simp only [Main.mkCall, List.map_cons, List.map_nil]
        refine sumcheck_round4_relIn ?_ ?_ (relN_le_rel coreProgram d _ _ _ hcall)
        · rw [e10]; exact ptrIn_mul (ptrIn_mono hr (by omega))
        · exact hcur k hk _ (by rw [← e10]; exact l11)
      · -- the next iteration
        simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
        have e25 : σ (.n (val% «verify_tables_loop0» "s8#4")) = gen ^ (k + 1) := by rw [m25, c24, p0, pow_succ]
        have e23 : σ (.n (val% «verify_tables_loop0» "s8#2")) = gen ^ (k + 1) + gen ^ K := by rw [a23, m22, c21, p0, p1, pow_succ]
        have hk1 : k + 1 < K := by
          rcases Nat.lt_or_ge (k + 1) K with h' | h'
          · exact h'
          · exfalso
            apply ht
            rw [e23, show k + 1 = K by omega, e_add_eq_zero_iff]
        have hrel := hnext ht
        simp only [List.map_cons, List.map_nil, e25, p1, p2, p3, p4, p5] at hrel ⊢
        exact ih (k + 1) hk1 hrel

end
end LeanVM.Guest.B1.Tables
