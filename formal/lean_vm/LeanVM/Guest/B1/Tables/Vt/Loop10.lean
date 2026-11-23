/-
  LeanVM.Guest.B1.Tables.Vt.Loop10

  `verify_tables`' table sumcheck loop `verify_tables_loop0`: one inlined `sumcheck_round4` a record, its
  challenge stored in round order, and the running product of the challenges.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.ZcCert
public import LeanVM.Guest.B1.Sumcheck.Round4
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.B1.Common.Atoms
import LeanVM.Guest.ValRef
import LeanVM.Guest.B1.Common.Vc
import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.Data.ValNames.«verify_tables_loop0»

/-!
# The table sumcheck's rounds (`verify_tables_loop0`)

`verify_tables_loop0(x, g^n, rounds, tabs, rk, cprod)` at `x = g^j`: the record `rounds·x^7`
(capacity cells `0 .. 4`, cursor `5`, claim `6`) runs the inlined `sumcheck_round4` (`MeaningSumcheckRound4`), whose cursor and claim go
to the next record; its challenge `r_j` is stored at `rk[x]`, and `cprod[x·g] = cprod[x]·r_j`. `l10_step`: an iteration's facts (`L10B`) and the next iteration's call.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtWInvGen_mul : vtWInvGen * gen = 1 := by
  rw [vtWInvGen, tb_word_eOfNat, eOfNat, ← tb_word_gen, tb_word_eOfNat, eOfNat, ← ofK_mul,
    show K.ofBits 9223372036854775821 * K.ofBits 2 = 1 by decide +kernel, ofK_one]

/-- `verify_tables_loop0`'s atoms, `sumcheck_round4` inlined on the record `rounds·x^7` (value `10`). -/
def l10Atoms : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)), .atom (.mul (.n 7) (.n 6) (.n 0)), .atom (.mul (.n 8) (.n 7) (.n 7)),
    .atom (.mul (.n 9) (.n 8) (.n 0)), .atom (.mul (.n 10) (.n 2) (.n 9)),
    .atom (.load (.n 11) (.n 10) 5), .atom (.load (.n 12) (.n 10) 6),
    .atom (.load (.n 13) (.n 10) 0), .atom (.load (.n 14) (.n 10) 1), .atom (.load (.n 15) (.n 10) 2),
    .atom (.load (.n 16) (.n 10) 3), .atom (.load (.n 17) (.n 10) 4),
    .atom (.load (.n 18) (.n 11) 0), .atom (.copy (.n 19) (.n 18)), .atom (.const (.n 20) (word 0 1)),
    .atom (.load (.n 21) (.n 11) 1), .atom (.copy (.n 22) (.n 21)), .atom (.const (.n 23) (word 0 1)),
    .atom (.load (.n 24) (.n 11) 2), .atom (.copy (.n 25) (.n 24)), .atom (.const (.n 26) (word 0 1)),
    .atom (.const (.n 27) (word 0 0)), .atom (.const (.n 28) (word 0 0)),
    .atom (.keccak [.n 19, .n 20, .n 22, .n 23, .n 25, .n 26, .n 27, .n 28, .n 13, .n 14, .n 15, .n 16, .n 17]
      [.n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36, .n 37, .n 38, .n 39, .n 40, .n 41] false false),
    .atom (.load (.n 37) (.n 10) 7), .atom (.load (.n 38) (.n 10) 8), .atom (.load (.n 39) (.n 10) 9),
    .atom (.load (.n 40) (.n 10) 10), .atom (.load (.n 41) (.n 10) 11),
    .atom (.const (.n 42) (word 1 0)), .atom (.add (.n 43) (.n 42) (.n 29)), .atom (.mul (.n 44) (.n 43) (.n 24)),
    .atom (.add (.n 45) (.n 21) (.n 44)), .atom (.mul (.n 46) (.n 43) (.n 45)), .atom (.add (.n 47) (.n 12) (.n 46)),
    .atom (.mul (.n 48) (.n 29) (.n 47)), .atom (.add (.n 49) (.n 18) (.n 48)),
    .atom (.mul (.n 50) (.n 4) (.n 0)), .atom (.load (.n 29) (.n 50) 0),
    .atom (.const (.n 51) (word 8 0)), .atom (.mul (.n 52) (.n 11) (.n 51)),
    .atom (.load (.n 52) (.n 10) 12), .atom (.load (.n 49) (.n 10) 13),
    .atom (.mul (.n 53) (.n 5) (.n 0)), .atom (.load (.n 54) (.n 53) 0), .atom (.mul (.n 55) (.n 54) (.n 29)),
    .atom (.mul (.n 56) (.n 5) (.n 0)), .atom (.load (.n 55) (.n 56) 1),
    .atom (.const (.n 57) (word 2 0)), .atom (.mul (.n 58) (.n 0) (.n 57)), .atom (.add (.n 59) (.n 58) (.n 1)),
    .atom (.const (.n 60) (word 2 0)), .atom (.mul (.n 61) (.n 0) (.n 60))]

/-- `verify_tables_loop0`'s body: its atoms, the next iteration, the return. -/
def l10Body : List Stmt :=
  l10Atoms ++ [.callIf (.n 59) name% «verify_tables_loop0» [.n 61, .n 1, .n 2, .n 3, .n 4, .n 5], .ret []]

theorem l10_atomsB : l10Atoms.all (fun s ↦ match s with | .atom _ => true | _ => false) = true := by
  decide +kernel

theorem l10_atoms : AllAtoms l10Atoms := fun s hs ↦ by
  have := List.all_eq_true.mp l10_atomsB s hs
  cases s <;> simp_all

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
    MeaningSumcheckRound4 rd [rounds * x ^ 7, cur, claim, tabs] [ncur, nclaim, rk] ∧
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
  vc [B1.word_gen, keccakF_cells, word_zero, word_one, word_eight]
  simp only [show x * x * x * (x * x * x) * x = x ^ 7 by ring]
  rintro ⟨x11, l11, x12, l12, x13, l13, x14, l14, x15, l15, x16, l16, x17, l17, x18, l18, x21, l21,
    x24, l24, n7, n8, n9, n10, n11, lrk, lnc, lncl, x54, lcp, lcp1, -, hn, -⟩
  refine ⟨⟨x11, x12, _, _, _, l11, l12, ?_, lnc, lncl, lrk, x54, lcp, lcp1⟩, hn⟩
  simp only [MeaningSumcheckRound4, exists_and_left, exists_capAt]
  simp only [capAt5, ReadsAt, round4_sponge, Fs.squeeze, capOf, perm_eq_cells, pendCells,
    List.flatMap_cons, List.flatMap_nil, List.replicate, scalarCells_eq, word_dsObserve,
    Keccak.challengeOf_cells, loadHolds_mul_gen_pow, List.length_cons, List.length_nil,
    Nat.forall_lt_succ_left', Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
    List.getElem_cons_zero, List.getElem_cons_succ, and_true, Nat.zero_add, Nat.mul_one,
    Nat.add_zero, List.cons_append, List.nil_append, exists_and_left, and_assoc,
    ← round4_eval, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLeDiff]
  exact ⟨x13, l13, x14, l14, x15, l15, x16, l16, x17, l17, x18, l18, x21, l21, x24, l24, n7, n8, n9,
    n10, n11, rfl⟩

end
end LeanVM.Guest.B1.Tables
