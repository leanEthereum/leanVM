/-
  LeanVM.Guest.B1.Link.Arith.Std

  The guest's inputs as variables (`stdIn`), the valuation reading them from given inputs
  (`envOf`), the Statement's lists in the forms the variables give, and the guest's functions as
  evaluations of their expressions.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Norm
public import LeanVM.Guest.B1.Link.ArithTac
import Mathlib.Tactic.IntervalCases

/-!
# The standard variables

`stdIn`: the guest's inputs as variables, field `f`'s entry `k` the variable `1000·f + k`, the
scalars from `10000`; `envOf v` reads them back from `v`. Each guest function at `v` is its
expression at `stdIn` evaluated at `envOf v` (`gProgram_eval`, …), by the kernel: the generic
definition unfolds to one term at both.

`list_canon`: a list of length at least `n` is its first `n` entries, as a map over `List.range n`,
then the rest: the form in which the Statement's slices of it reduce.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Protocol.Verifier

@[expose] public section

/-- The guest's inputs as variables. -/
def stdIn : LinkIn Ex where
  chal k := .v k
  slot k := .v (1000 + k)
  sent k := .v (2000 + k)
  splitv k := .v (3000 + k)
  eqQ k := .v (4000 + k)
  omega k := .v (5000 + k)
  act k := .v (6000 + k)
  eqTau k := .v (7000 + k)
  corner k := .v (8000 + k)
  jump k := .v (9000 + k)
  e0 := .v 10000
  ec := .v 10001
  idx := .v 10002
  eqzr := .v 10003
  shz := .v 10004
  belowMem := .v 10005
  belowBc := .v 10006
  eq0R := .v 10007
  m1 := .v 10008
  cert := .v 10009
  xBc := .v 10010
  pFp := .v 10011
  yMem := .v 10012

/-- The valuation of `stdIn`'s variables at the inputs `v`. -/
def envOf (v : LinkIn E) (i : ℕ) : E :=
  if i < 1000 then v.chal i
  else if i < 2000 then v.slot (i - 1000)
  else if i < 3000 then v.sent (i - 2000)
  else if i < 4000 then v.splitv (i - 3000)
  else if i < 5000 then v.eqQ (i - 4000)
  else if i < 6000 then v.omega (i - 5000)
  else if i < 7000 then v.act (i - 6000)
  else if i < 8000 then v.eqTau (i - 7000)
  else if i < 9000 then v.corner (i - 8000)
  else if i < 10000 then v.jump (i - 9000)
  else if i = 10000 then v.e0
  else if i = 10001 then v.ec
  else if i = 10002 then v.idx
  else if i = 10003 then v.eqzr
  else if i = 10004 then v.shz
  else if i = 10005 then v.belowMem
  else if i = 10006 then v.belowBc
  else if i = 10007 then v.eq0R
  else if i = 10008 then v.m1
  else if i = 10009 then v.cert
  else if i = 10010 then v.xBc
  else if i = 10011 then v.pFp
  else v.yMem

/-- The access weights `mu`, per table, from the challenges (`ACC_START`). -/
def muOf {α : Type} (chal : ℕ → α) : List (List α) :=
  (List.range nTab).map fun t ↦ (runOf Data.arr_ACC_START t).map fun a ↦ chal (oMu + a)

/-! ## The guest's functions, evaluated -/

theorem gClaim_eval (v : LinkIn E) : gClaim v = (gClaim stdIn).eval (envOf v) := by kernel_eq

theorem gProgram_eval1 (v : LinkIn E) : (gProgram v).1 = (gProgram stdIn).1.eval (envOf v) := by
  kernel_eq

theorem gProgram_eval2 (v : LinkIn E) : (gProgram v).2 = (gProgram stdIn).2.eval (envOf v) := by
  kernel_eq

theorem gYMem_eval (v : LinkIn E) : gYMem v = (gYMem stdIn).eval (envOf v) := by kernel_eq

theorem gXBc_eval (v : LinkIn E) : gXBc v = (gXBc stdIn).eval (envOf v) := by kernel_eq

theorem gPFp_eval (v : LinkIn E) : gPFp v = (gPFp stdIn).eval (envOf v) := by kernel_eq

theorem gCoef_eval (v : LinkIn E) : gCoef v = (gCoef stdIn).eval (envOf v) := by kernel_eq

theorem gShift_eval (v : LinkIn E) (s : ℕ) (hs : s < nShift) :
    gShift v s = (gShift stdIn s).eval (envOf v) := by
  have : ∀ s < nShift, gShift v s = (gShift stdIn s).eval (envOf v) := by
    intro s hs
    interval_cases s <;> kernel_eq
  exact this s hs

theorem gCertW_eval (v : LinkIn E) : gCertW v = (gCertW stdIn).eval (envOf v) := by kernel_eq

theorem gBase_eval (v : LinkIn E) : gBase v = (gBase stdIn).eval (envOf v) := by kernel_eq

/-! ## Lists in the variables' form -/

/-- The first `n` entries of a list, then the rest. -/
theorem list_canon (l : List E) (n : ℕ) (h : n ≤ l.length) :
    l = (List.range n).map (l.getD · 0) ++ l.drop n := by
  conv_lhs => rw [← List.take_append_drop n l]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_take] at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]

/-- A list of length `n`, as a map over `List.range n`. -/
theorem list_canon_eq (l : List E) (n : ℕ) (h : l.length = n) : l = (List.range n).map (l.getD · 0) := by
  have := list_canon l n h.ge
  rwa [List.drop_of_length_le h.le, List.append_nil] at this

end

end LeanVM.Guest.B1.Link.Arith
