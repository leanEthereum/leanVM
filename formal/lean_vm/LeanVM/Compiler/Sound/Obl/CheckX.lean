/-
  LeanVM.Compiler.Sound.Obl.CheckX

  The analysis with calls of `ext` functions: at named statements, a call, conditional call or
  dispatch whose callees' `ext` preconditions are shown outside the analysis.
-/

module

public import LeanVM.Compiler.Sound.Obl.Check

/-!
# Calls of `ext` functions

`callOk` never accepts a call of a function marked `ext`: its precondition (`X` in `UOf`) is not
of the table's form. `chkTX` takes a list `xs` of statement indices of a block; at those it checks
a call, a conditional call or a dispatch as `chkS` does but for the callees' `ext` part, which the
soundness theorem (`Obl.CheckXSound`) takes as a hypothesis on the statements before the site.
-/

namespace LeanVM.Compiler.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Look

variable (T : Tab)

/-- A call of `f` on `args` meets the table part of `f`'s precondition, `ext` aside. -/
def callOkX (ctx : List Hyp) (f : String) (args : List V) : Bool :=
  let s := T.sig f
  s.pre.all (fun p => p.1 < args.length && bndLe T ctx (args.getD p.1 default) p.2) &&
    s.mem.all (fun m => m.1 < args.length && memLe ctx (args.getD m.1 default) m.2.1 m.2.2) &&
    s.xpre.all (fun p => p.1 < args.length && xLe ctx (args.getD p.1 default) p.2)

/-- The analysis of a statement at an `ext` site: a call, a conditional call or a dispatch whose
selector is bounded and whose callees' table preconditions hold. -/
def chkX (ctx : List Hyp) : Stmt → Bool
  | .call f args _ => callOkX T ctx f args
  | .callIf _ f args => callOkX T ctx f args
  | .dispatch x fs args _ => bndLe T ctx x fs.length && fs.all (callOkX T ctx · args)
  | _ => false

/-- **The analysis of a block with facts and `ext` sites**: each fact `(i, h)` joins the
hypotheses at statement `i`, and a statement whose index is in `xs` is checked by `chkX`. -/
def chkTX (post : Want) (facts : List (Nat × Hyp)) (xs : List Nat) :
    Nat → List Hyp → List Stmt → Bool
  | _, _, [] => true
  | i, ctx, s :: ss =>
      (if xs.contains i then chkX T (factsAt facts i ++ ctx) s
        else chkS T post (factsAt facts i ++ ctx) s) &&
        chkTX post facts xs (i + 1) (after T (factsAt facts i ++ ctx) s) ss

/-- The analysis of a function with facts and `ext` sites. -/
def chkFnX (facts : List (Nat × Hyp)) (xs : List Nat) (f : Fn) : Bool :=
  chkTX T ⟨f.params, (T.sig f.name).post⟩ facts xs 0 (entry f.params (T.sig f.name)) f.body

end Look

end
end LeanVM.Compiler.Obl
