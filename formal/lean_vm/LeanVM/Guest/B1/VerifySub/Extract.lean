/-
  LeanVM.Guest.B1.VerifySub.Extract

  `verify_sub`'s body as facts: its relation is a valuation satisfying every statement before its
  final `ret`, and any run of them, found at its position by kernel evaluation, holds.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface

/-!
# Reading `verify_sub`'s body

`verify_sub`'s body (`Data.core15`, 2137 statements) is straight-line: atoms, calls, a guarded
loop call, one fused dispatch, then `ret []`. Its relation is a valuation satisfying every
statement of `vsPre`, the statements before the `ret` (`verify_sub_holds`). A run of statements
`blk` at position `n` of `vsPre`, checked by `decide +kernel` on `stmtsEqb`, then holds on its own
(`VsHolds.slice`), and each fact the proof needs is read off a run.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem find_verify_sub : coreProgram.find? "verify_sub" = some Data.core15 :=
  Program.find?_of_indexOf? (j := 15) (by decide +kernel) rfl

/-- `verify_sub`'s statements before its final `ret []`. -/
noncomputable def vsPre : List Stmt := (Fn.body Data.core15).take 2136

theorem core15_body : Fn.body Data.core15 = vsPre ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

theorem vsPre_noRet : Stmt.noRetList vsPre = true := by decide +kernel

theorem core15_params : Fn.params Data.core15 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := rfl

/-- The valuation `σ` satisfies every statement of `verify_sub` before its `ret`. -/
def VsHolds (rd : Reader) (σ : Val) : Prop :=
  Stmt.HoldsList (coreProgram.Rel rd) rd σ vsPre True fun rs => rs = []

theorem verify_sub_holds {rd : Reader} {args : List E}
    (h : coreProgram.Rel rd "verify_sub" args []) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] = args ∧
      VsHolds rd σ := by
  rw [rel_iff_sem find_verify_sub, core15_body, core15_params] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsList_append, holdsList_noRet _ vsPre_noRet] at hb
  exact ⟨σ, hp, hb.1⟩

theorem noRetList_append (a b : List Stmt) :
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b) := by
  induction a with
  | nil => simp [Stmt.noRetList]
  | cons s a ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

/-- **A run of statements of the body holds**: `blk`, equal to the statements at position `n`. -/
theorem VsHolds.slice {rd : Reader} {σ : Val} (h : VsHolds rd σ) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((vsPre.drop n).take blk.length) = true) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ blk True fun rs => rs = [] := by
  have hsplit : vsPre = vsPre.take n ++ (((vsPre.drop n).take blk.length) ++
      (vsPre.drop n).drop blk.length) := by simp
  have hnr := vsPre_noRet
  unfold VsHolds at h
  rw [hsplit] at h hnr
  rw [noRetList_append, noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsList_append, holdsList_noRet _ hnr.1, holdsList_append,
    holdsList_noRet _ hnr.2.1] at h
  rw [stmtsEqb_sound heq]
  exact h.2.1

/-- One atom of the body holds. -/
theorem VsHolds.atom {rd : Reader} {σ : Val} (h : VsHolds rd σ) (n : ℕ) (a : Atom)
    (heq : stmtsEqb [.atom a] ((vsPre.drop n).take 1) = true) : a.Holds rd σ := by
  have := h.slice n [.atom a] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One call of the body holds. -/
theorem VsHolds.call {rd : Reader} {σ : Val} (h : VsHolds rd σ) (n : ℕ) (f : String)
    (args rets : List V) (heq : stmtsEqb [.call f args rets] ((vsPre.drop n).take 1) = true) :
    coreProgram.Rel rd f (args.map σ) (rets.map σ) := by
  have := h.slice n [.call f args rets] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

end
end LeanVM.Guest.B1.VerifySub
