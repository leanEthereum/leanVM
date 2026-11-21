/-
  LeanVM.Guest.B1.Tables.Vt.Loop10

  `verify_tables`' table sumcheck loop `verify_tables_loop0`: one `sumcheck_round4` a record, its
  challenge stored in round order, and the running product of the challenges.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.ZcCert
public import LeanVM.Guest.B1.Sumcheck.Round4
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.B1.Common.Vc
import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.Data.ValNames.«verify_tables_loop0»

/-!
# The table sumcheck's rounds (`verify_tables_loop0`)

`verify_tables_loop0(x, g^n, rounds, tabs, rk, cprod)` at `x = g^j`: the record `rounds·x^7`
(capacity cells `0 .. 4`, cursor `5`, claim `6`) runs `sumcheck_round4`, whose cursor and claim go
to the next record; its challenge `r_j` is stored at `rk[x]`, and `cprod[x·g] = cprod[x]·r_j`. `l10_step`: an iteration's facts (`L10B`) and the next iteration's call.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtWInvGen_mul : vtWInvGen * gen = 1 := by
  rw [vtWInvGen, tb_word_eOfNat, eOfNat, ← tb_word_gen, tb_word_eOfNat, eOfNat, ← ofK_mul,
    show K.ofBits 9223372036854775821 * K.ofBits 2 = 1 by decide +kernel, ofK_one]

/-- `verify_tables_loop0`'s body. -/
def l10Body : List Stmt :=
  [.atom (.mul (.n (val% «verify_tables_loop0» "rd~0")) (.n (val% «verify_tables_loop0» "xk")) (.n (val% «verify_tables_loop0» "xk"))), .atom (.mul (.n (val% «verify_tables_loop0» "rd~1")) (.n (val% «verify_tables_loop0» "rd~0")) (.n (val% «verify_tables_loop0» "xk"))),
    .atom (.mul (.n (val% «verify_tables_loop0» "rd~2")) (.n (val% «verify_tables_loop0» "rd~1")) (.n (val% «verify_tables_loop0» "rd~1"))), .atom (.mul (.n (val% «verify_tables_loop0» "rd~3")) (.n (val% «verify_tables_loop0» "rd~2")) (.n (val% «verify_tables_loop0» "xk"))),
    .atom (.mul (.n (val% «verify_tables_loop0» "rd")) (.n (val% «verify_tables_loop0» "zc_rounds")) (.n (val% «verify_tables_loop0» "rd~3"))), .atom (.load (.n (val% «verify_tables_loop0» "ncur~3")) (.n (val% «verify_tables_loop0» "rd")) 5),
    .atom (.load (.n (val% «verify_tables_loop0» "ncur~4")) (.n (val% «verify_tables_loop0» "rd")) 6),
    .call "sumcheck_round4" [.n (val% «verify_tables_loop0» "rd"), .n (val% «verify_tables_loop0» "ncur~3"), .n (val% «verify_tables_loop0» "ncur~4"), .n (val% «verify_tables_loop0» "tabs")] [.n (val% «verify_tables_loop0» "ncur"), .n (val% «verify_tables_loop0» "nclaim"), .n (val% «verify_tables_loop0» "rk")],
    .atom (.mul (.n (val% «verify_tables_loop0» "s2#0")) (.n (val% «verify_tables_loop0» "zc_rk")) (.n (val% «verify_tables_loop0» "xk"))), .atom (.load (.n (val% «verify_tables_loop0» "rk")) (.n (val% «verify_tables_loop0» "s2#0")) 0),
    .atom (.load (.n (val% «verify_tables_loop0» "ncur")) (.n (val% «verify_tables_loop0» "rd")) 12), .atom (.load (.n (val% «verify_tables_loop0» "nclaim")) (.n (val% «verify_tables_loop0» "rd")) 13),
    .atom (.mul (.n (val% «verify_tables_loop0» "s6#0")) (.n (val% «verify_tables_loop0» "zc_cprod")) (.n (val% «verify_tables_loop0» "xk"))), .atom (.load (.n (val% «verify_tables_loop0» "s6#1")) (.n (val% «verify_tables_loop0» "s6#0")) 0),
    .atom (.mul (.n (val% «verify_tables_loop0» "s6#2")) (.n (val% «verify_tables_loop0» "s6#1")) (.n (val% «verify_tables_loop0» "rk"))), .atom (.mul (.n (val% «verify_tables_loop0» "s6#3")) (.n (val% «verify_tables_loop0» "zc_cprod")) (.n (val% «verify_tables_loop0» "xk"))),
    .atom (.load (.n (val% «verify_tables_loop0» "s6#2")) (.n (val% «verify_tables_loop0» "s6#3")) 1), .atom (.const (.n (val% «verify_tables_loop0» "s8#0")) (word 2 0)),
    .atom (.mul (.n (val% «verify_tables_loop0» "s8#1")) (.n (val% «verify_tables_loop0» "xk")) (.n (val% «verify_tables_loop0» "s8#0"))), .atom (.add (.n (val% «verify_tables_loop0» "s8#2")) (.n (val% «verify_tables_loop0» "s8#1")) (.n (val% «verify_tables_loop0» "bound"))),
    .atom (.const (.n (val% «verify_tables_loop0» "s8#3")) (word 2 0)), .atom (.mul (.n (val% «verify_tables_loop0» "s8#4")) (.n (val% «verify_tables_loop0» "xk")) (.n (val% «verify_tables_loop0» "s8#3"))),
    .callIf (.n (val% «verify_tables_loop0» "s8#2")) name% «verify_tables_loop0» [.n (val% «verify_tables_loop0» "s8#4"), .n (val% «verify_tables_loop0» "bound"), .n (val% «verify_tables_loop0» "zc_rounds"), .n (val% «verify_tables_loop0» "tabs"), .n (val% «verify_tables_loop0» "zc_rk"), .n (val% «verify_tables_loop0» "zc_cprod")],
        .ret []]

noncomputable def l10Check : Bool :=
  match coreProgram.find? name% «verify_tables_loop0» with
  | some fn => decide (fn.params = (List.range 6).map V.n) && tbStmtsEqb fn.body l10Body
  | none => false

theorem l10Check_eq : l10Check = true := by decide +kernel

theorem l10Found : ∃ fn : Fn, coreProgram.find? name% «verify_tables_loop0» = some fn ∧
    fn.params = (List.range 6).map V.n ∧ fn.body = l10Body := by
  have h := l10Check_eq
  unfold l10Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- What an iteration at `x` gives: the round on the record `rounds·x^7`, the next record's cursor
and claim, the challenge at `rk·x`, the running product. -/
def L10B (rd : Reader) (rounds tabs rkb cprod x : E) : Prop :=
  ∃ cur claim ncur nclaim rk : E, LoadHolds rd (rounds * x ^ 7) 5 cur ∧
    LoadHolds rd (rounds * x ^ 7) 6 claim ∧
    coreProgram.Rel rd "sumcheck_round4" [rounds * x ^ 7, cur, claim, tabs] [ncur, nclaim, rk] ∧
    LoadHolds rd (rounds * x ^ 7) 12 ncur ∧ LoadHolds rd (rounds * x ^ 7) 13 nclaim ∧
    LoadHolds rd (rkb * x) 0 rk ∧
    ∃ cp, LoadHolds rd (cprod * x) 0 cp ∧ LoadHolds rd (cprod * x) 1 (cp * rk)

/-- **An iteration of `verify_tables_loop0`.** -/
theorem l10_step {rd : Reader} {N rounds tabs rkb cprod : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «verify_tables_loop0» (x :: [N, rounds, tabs, rkb,
        cprod]) []) :
    L10B rd rounds tabs rkb cprod x ∧
      (x * gen + N ≠ 0 →
        coreProgram.relN rd d name% «verify_tables_loop0» (x * gen :: [N, rounds, tabs, rkb,
            cprod]) []) := by
  revert h
  rw [B1.relN_succ_iff_fnSem (coreProgram_find?_at (j := idx% «verify_tables_loop0») rfl)]
  vc [B1.word_gen]
  simp only [show x * x * x * (x * x * x) * x = x ^ 7 by ring]
  rintro ⟨cur, l11, claim, l12, ncur, nclaim, rk, hc, lrk, l13, l14, cp, lcp, lcp1, -, hn, -⟩
  exact ⟨⟨cur, claim, ncur, nclaim, rk, l11, l12, relN_le_rel coreProgram d _ _ _ hc, l13, l14, lrk,
    cp, lcp, lcp1⟩, hn⟩

end
end LeanVM.Guest.B1.Tables
