/-
  LeanVM.Guest.ExpandLemmas

  The structural lemmas of the expansion: an `unroll` emits its iterations' blocks in order, and
  an `if` whose condition folds is its taken branch.
-/

module

public import LeanVM.Guest.Expand
public import LeanVM.Guest.CoreLemmas

/-!
# Lemmas about the expansion

* `appendBlocks_out`: an `unroll` expands each iteration, the counter substituted, into a block
  of its own (`capture`, in `stmtKind`), and emits the blocks in order; with
  `Core.holdsList_flatten` its semantics is the conjunction of the iterations' when they do not
  return;
* `lowerIf_fold`: an `if` whose two sides have integer readings below `2^32` (and agreeing field
  readings, unless it is `if const(...)`) expands to its taken branch, in the enclosing scope.
-/

namespace LeanVM.Guest.Expand

open LeanVM.Guest.Source

@[expose] public section

/-- Emitting captured blocks appends them, in order. -/
theorem appendBlocks_out (bs : List (Bool × List Core.Stmt)) (st : St) :
    ∃ st', (appendBlocks bs).run st = .ok ((), st') ∧
      st'.out.toList = st.out.toList ++ (bs.map Prod.snd).flatten ∧ st'.names = st.names := by
  induction bs generalizing st with
  | nil => exact ⟨st, rfl, by simp, rfl⟩
  | cons b bs ih =>
      let pd := if b.2.isEmpty then st.pending else b.1
      obtain ⟨st', h, hout, hn⟩ := ih { st with out := st.out ++ b.2.toArray, pending := pd }
      refine ⟨st', ?_, by simp [hout], hn⟩
      have e : (appendBlocks (b :: bs)).run st =
          (appendBlocks bs).run { st with out := st.out ++ b.2.toArray, pending := pd } := rfl
      rw [e, h]

/-- An `if` whose condition folds expands to its taken branch, in the enclosing scope. -/
theorem lowerIf_fold (n : Nat) (eq : Bool) (lhs rhs : Expr) (thn els : List Source.Stmt)
    (fc : Bool) (st : St) (a b : Known) (ai bi : Nat)
    (ha : (eval evalFuel lhs).run st = .ok (a, st)) (hb : (eval evalFuel rhs).run st = .ok (b, st))
    (hai : a.int = some ai) (hbi : b.int = some bi) (hai' : ai < u32Bound) (hbi' : bi < u32Bound)
    (hdiv : fc = true ∨ (a.diverging = none ∧ b.diverging = none)) :
    (lowerIf (n + 1) eq lhs rhs thn els fc).run st =
      (withSeg (if (ai == bi) == eq then .t else .e)
        (stmts n (if (ai == bi) == eq then thn else els))).run st := by
  simp only [StateT.run] at ha hb ⊢
  rcases hdiv with hfc | ⟨hda, hdb⟩
  · subst hfc
    simp [lowerIf, bind, StateT.bind, Except.bind, ha, hb, hai, hbi, hai', hbi']
  · simp [lowerIf, bind, StateT.bind, Except.bind, ha, hb, hai, hbi, hai', hbi', hda, hdb, pure,
      forIn, ForIn.forIn]
    split <;> rfl

end
end LeanVM.Guest.Expand
