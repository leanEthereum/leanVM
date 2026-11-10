/-
  LeanVM.Guest.B1.Tables.Vt.Loop10

  `verify_tables`' table sumcheck loop `__loop9`: one `sumcheck_round4` a record, its challenge
  stored at its variable's place in `chi`, and the running product of the challenges.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.ZcCert
public import LeanVM.Guest.B1.Sumcheck.Round4

/-!
# The table sumcheck's rounds (`__loop9`, G:2396-2406)

`__loop9(x, g^n, rounds, tabs, chi, g^n, cprod)` at `x = g^j`: the record `rounds·x^7` (capacity
cells `0 .. 4`, cursor `5`, claim `6`) runs `sumcheck_round4`, whose cursor and claim go to the next
record; its challenge `r_j` is stored at `chi[g^(n-1)/x]`, and `cprod[x·g] = cprod[x]·r_j`.
`l10_step`: an iteration's facts (`L10B`) and the next iteration's call.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vtWInvGen_mul : vtWInvGen * gen = 1 := by
  rw [vtWInvGen, tb_word_eOfNat, eOfNat, ← tb_word_gen, tb_word_eOfNat, eOfNat, ← ofK_mul,
    show K.ofBits 9223372036854775821 * K.ofBits 2 = 1 by decide +kernel, ofK_one]

/-- `__loop9`'s body. -/
def l10Body : List Stmt :=
  [.atom (.mul (.n 7) (.n 0) (.n 0)), .atom (.mul (.n 8) (.n 7) (.n 0)),
    .atom (.mul (.n 9) (.n 8) (.n 8)), .atom (.mul (.n 10) (.n 9) (.n 0)),
    .atom (.mul (.n 11) (.n 2) (.n 10)), .atom (.load (.n 12) (.n 11) 5),
    .atom (.load (.n 13) (.n 11) 6),
    .call "sumcheck_round4" [.n 11, .n 12, .n 13, .n 3] [.n 14, .n 15, .n 16],
    .atom (.const (.n 17) vtWInvGen), .atom (.mul (.n 18) (.n 5) (.n 17)),
    .atom (.mul (.n 18) (.n 19) (.n 0)), .atom (.mul (.n 20) (.n 4) (.n 19)),
    .atom (.load (.n 16) (.n 20) 0), .atom (.load (.n 14) (.n 11) 12),
    .atom (.load (.n 15) (.n 11) 13), .atom (.mul (.n 21) (.n 6) (.n 0)),
    .atom (.load (.n 22) (.n 21) 0), .atom (.mul (.n 23) (.n 22) (.n 16)),
    .atom (.mul (.n 24) (.n 6) (.n 0)), .atom (.load (.n 23) (.n 24) 1),
    .atom (.const (.n 25) (word 2 0)), .atom (.mul (.n 26) (.n 0) (.n 25)),
    .atom (.add (.n 27) (.n 26) (.n 1)), .atom (.const (.n 28) (word 2 0)),
    .atom (.mul (.n 29) (.n 0) (.n 28)),
    .callIf (.n 27) "__loop9" [.n 29, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], .ret []]

noncomputable def l10Check : Bool :=
  match coreProgram.find? "__loop9" with
  | some fn => decide (fn.params = (List.range 7).map V.n) && tbStmtsEqb fn.body l10Body
  | none => false

theorem l10Check_eq : l10Check = true := by decide +kernel

theorem l10Found : ∃ fn : Fn, coreProgram.find? "__loop9" = some fn ∧
    fn.params = (List.range 7).map V.n ∧ fn.body = l10Body := by
  have h := l10Check_eq
  unfold l10Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- What an iteration at `x` gives: the round on the record `rounds·x^7`, the next record's cursor
and claim, the challenge at `chi·y` with `g^n·g⁻¹ = y·x`, the running product. -/
def L10B (rd : Reader) (rounds tabs chi gn cprod x : E) : Prop :=
  ∃ cur claim ncur nclaim rk : E, LoadHolds rd (rounds * x ^ 7) 5 cur ∧
    LoadHolds rd (rounds * x ^ 7) 6 claim ∧
    coreProgram.Rel rd "sumcheck_round4" [rounds * x ^ 7, cur, claim, tabs] [ncur, nclaim, rk] ∧
    LoadHolds rd (rounds * x ^ 7) 12 ncur ∧ LoadHolds rd (rounds * x ^ 7) 13 nclaim ∧
    (∃ y, gn * vtWInvGen = y * x ∧ LoadHolds rd (chi * y) 0 rk) ∧
    ∃ cp, LoadHolds rd (cprod * x) 0 cp ∧ LoadHolds rd (cprod * x) 1 (cp * rk)

/-- **An iteration of `__loop9`.** -/
theorem l10_step {rd : Reader} {N rounds tabs chi gn cprod : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) "__loop9" (x :: [N, rounds, tabs, chi, gn, cprod]) []) :
    L10B rd rounds tabs chi gn cprod x ∧
      (x * gen + N ≠ 0 →
        coreProgram.relN rd d "__loop9" (x * gen :: [N, rounds, tabs, chi, gn, cprod]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := l10Found
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb] at hbody
  simp only [l10Body, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hbody
  obtain ⟨m7, m8, m9, m10, m11, l12, l13, hcall, c17, m18, m18', m20, l16, l14, l15, m21, l22, m23,
    m24, l23, c25, m26, a27, c28, m29, ⟨-, hnext, -⟩⟩ := hbody
  simp only [Atom.Holds] at m7 m8 m9 m10 m11 l12 l13 c17 m18 m18' m20 l16 l14 l15 m21 l22 m23 m24
  simp only [Atom.Holds] at l23 c25 m26 a27 c28 m29
  have e11 : σ (.n 11) = σ (.n 2) * σ (.n 0) ^ 7 := by rw [m11, m10, m9, m8, m7]; ring
  refine ⟨⟨σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15), σ (.n 16), by rw [← e11]; exact l12,
    by rw [← e11]; exact l13, by rw [← e11]; exact relN_le_rel coreProgram d _ _ _ hcall,
    by rw [← e11]; exact l14, by rw [← e11]; exact l15,
    ⟨σ (.n 19), by rw [← m18', m18, c17], by rw [← m20]; exact l16⟩,
    σ (.n 22), by rw [← m21]; exact l22, by rw [← m24, ← m23]; exact l23⟩, fun hne => ?_⟩
  rw [tb_word_gen] at c25 c28
  have := hnext (by rw [a27, m26, c25]; exact hne)
  rw [m29, c28] at this
  exact this

end
end LeanVM.Guest.B1.Tables
