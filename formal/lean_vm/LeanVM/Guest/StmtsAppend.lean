/-
  LeanVM.Guest.StmtsAppend

  `a ⧺ b`: `a ++ b` on statement lists, elaborated with its type given.
-/

module

public import LeanVM.Guest.Core

/-!
# Appending statement lists

A template written `[.atom …, …] ++ t ++ …` goes through `binop%`, which elaborates each operand
first with no expected type. A list of dot-constructor statements (`.atom …`, `.call …`) does not
elaborate without one, so the elaborator fails on it and elaborates it again once the type is
known. `a ⧺ b` is the same term, `@HAppend.hAppend (List Stmt) (List Stmt) (List Stmt) _ a b`,
with the type given, so each operand is elaborated once against `List Stmt`.
-/

namespace LeanVM.Guest.Core

/-- `a ++ b` on statement lists, with the type given to the elaborator: the same term. -/
scoped infixl:65 " ⧺ " => @HAppend.hAppend (List Stmt) (List Stmt) (List Stmt) _

end LeanVM.Guest.Core
