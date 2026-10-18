/-
  LeanVM.Guest.B1.Tables

  B1 for `exponent_tables`: the two read-only tables over the exponent domain.
-/

module

public import LeanVM.Guest.B1.Grind

/-!
# `exponent_tables` (TRIAGE #13)

`exponent_tables()` (G:572-587) fills two fresh `HeapBuf(34)` tables: `g_logs_pow2[g^j] = E(2^j)`
and `g_squares[g^j] = g^(2^j)`, the second's constants folded by the compiler
(`Value.Tables.gSquaresBits`, checked against the squares of `g`). Its relation holds exactly
when the two returned pointers hold them; the pointers themselves are the allocator's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `g_logs_pow2[g^j] = 2^j`. -/
def etBlk1 (j : ℕ) : List Stmt :=
  [.atom (.const (.n (1 + j)) (word (2 ^ j) 0 0)), .atom (.load (.n (1 + j)) (.n 0) j)]

/-- `g_squares[g^j] = g^(2^j)`, folded. -/
def etBlk2 (j : ℕ) : List Stmt :=
  [.atom (.const (.n (36 + j)) (word (gSquaresBits.getD j 0) 0 0)),
    .atom (.load (.n (36 + j)) (.n 35) j)]

/-- The expansion of `exponent_tables`. -/
def etBody : List Stmt :=
  [.atom (.hint (.alloc (.n 0) 34))] ++ ((List.range 34).map etBlk1).flatten ++
  [.atom (.hint (.alloc (.n 35) 34))] ++ ((List.range 34).map etBlk2).flatten ++
  [.atom (.copy (.n 70) (.n 0)), .atom (.copy (.n 71) (.n 35)), .ret [.n 70, .n 71]]

theorem core2_body : Fn.body Data.core2 = etBody := stmtsEqb_sound (by decide +kernel)

/-- The two exponent tables at `p`, `q`: `p[g^j] = E(2^j)`, `q[g^j] = g^(2^j)`, `j < 34`. -/
def ExpTables (rd : Reader) (p q : E) : Prop :=
  ∀ j < sizeBits, LoadHolds rd p j (eOfNat (2 ^ j)) ∧ LoadHolds rd q j (gen ^ 2 ^ j)

/-- **`exponent_tables()`** (G:572-587; TRIAGE #13): the function returns two pointers holding
the exponent tables. -/
def MeaningExponentTables (rd : Reader) : List E → List E → Prop
  | [], [p, q] => ExpTables rd p q
  | _, _ => False

theorem find_exponent_tables : coreProgram.find? "exponent_tables" = some Data.core2 :=
  Program.find?_of_indexOf? (j := 2) (by decide +kernel) rfl

theorem exponent_tables_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "exponent_tables" args rets ↔ MeaningExponentTables rd args rets := by
  rw [rel_iff_sem find_exponent_tables, core2_body, show Fn.params Data.core2 = [] from rfl, etBody]
  simp only [holdsList_append, Stmt.HoldsList]
  simp only [holdsList_range_flatten 34 etBlk1 (fun _ => rfl),
    holdsList_range_flatten 34 etBlk2 (fun _ => rfl), etBlk1, etBlk2]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, true_and,
    and_true]
  constructor
  · rintro ⟨σ, hp, ht1, ht2, h70, h71, hret⟩
    subst hp hret
    intro j hj
    obtain ⟨c1, l1⟩ := ht1 j hj
    obtain ⟨c2, l2⟩ := ht2 j hj
    rw [h70, h71]
    rw [c1, word_eOfNat] at l1
    rw [c2, word_eOfNat, eOfNat_gSquaresBits j hj] at l2
    exact ⟨l1, l2⟩
  · intro hm
    obtain ⟨rfl, p, q, rfl, ht⟩ : args = [] ∧ ∃ p q, rets = [p, q] ∧ ExpTables rd p q := by
      match args, rets, hm with
      | [], [p, q], h => exact ⟨rfl, p, q, rfl, h⟩
    refine ⟨setl (setv (setl (setv (setl (Val.ofArgs []) 0 [p]) 1 34 fun j => word (2 ^ j) 0 0) 35
      [q]) 36 34 fun j => word (gSquaresBits.getD j 0) 0 0) 70 [p, q], rfl, fun j hj => ?_,
      fun j hj => ?_, ?_, ?_, ?_⟩
    all_goals (try b1_look)
    · rw [word_eOfNat]; exact ⟨trivial, (ht j hj).1⟩
    · rw [word_eOfNat, eOfNat_gSquaresBits j hj]; exact ⟨trivial, (ht j hj).2⟩

end
end LeanVM.Guest.B1
