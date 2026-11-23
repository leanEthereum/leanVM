/-
  LeanVM.Guest.CoreMode.Fam.LinkDefs

  The checks behind a callee's table reads: its entries and bound parameters linked to its
  caller's frame, and the residual a read inside that table leaves.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.B1.Digest.Chain
public import LeanVM.Guest.Memory.StaticCut
public import LeanVM.Guest.Memory.Family

/-!
# Linking a callee's parameters to its caller's frame

A callee reads `[pE]·[x]^4`, `x` range-checked against its parameter `pL`, and the residual asks
that this lie inside its caller's table: the run of four cells from `[[1]·g^2]·g^(4j)`, `j` below the
exponent of `[[1]·g^5]`, header cell `1` naming the caller's frame. A `Link` names the
callees (`fams`: name, the indices of `pE` and `pL` among its parameters) and their caller `o`,
whose cell `2` holds its entries parameter `uE` and cell `5` its bound `uL = w · c`, `c = g`; the
callees get `uE` and `w`. A loop callee passes them on along its tail calls.

The checks: `originB` (the caller: its cells, the bound's atoms on every path, its call sites of the
callees passing `uE` and `w`, each a site of its plumbing); `calleeB` (each callee: `pE` and `pL` no
loop counter, a loop not calling itself before its tail); `callersB` (a function calling a callee
is the caller, or the callee itself, a loop); `callersG`, `callersM` the same against `(callee, caller)` and
`(callee, callers)` pairs.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-- **Callees linked to a caller's frame.** -/
structure Link where
  /-- The callees: name, the indices of the entries and bound parameters. -/
  fams : List (String × ℕ × ℕ)
  /-- The caller's compiled index and name. -/
  o : ℕ
  oName : String
  /-- The caller's entries and bound parameters, the bound's quotient by `c`, and `c = g`. -/
  uE : V
  uL : V
  w : V
  c : V

/-- The arguments and returns of a call site of compiled function `o`'s plumbing. -/
noncomputable def siteB (o : ℕ) (args rets : List V) : Bool :=
  ((B2C.plumbOf o).sites.find? fun s => s.args == args.map (·.idx) && s.rets == rets.map (·.idx)).isSome

/-- `d = a · b`. -/
def isMulAt (d a b : V) : Atom → Bool
  | .mul d' a' b' => decide (d' = d) && decide (a' = a) && decide (b' = b)
  | _ => false

/-- **The caller's check.** -/
noncomputable def originB (L : Link) : Bool :=
  (coreOf L.o).name == L.oName && !(coreOf L.o).loop && decide (L.uE ∈ (coreOf L.o).params) &&
  decide (L.uL ∈ (coreOf L.o).params) && cellJ L.o L.uE == 2 && cellJ L.o L.uL == 5 &&
  Nat.blt 5 (fsN L.o) && scanAt (isMulAt L.uL L.w L.c) (coreOf L.o).body &&
  scanAt (B1.Digest.isConstAt L.c 2 0) (coreOf L.o).body &&
  sitesB (fun f args rets => L.fams.all fun F => F.1 != f ||
    (args[F.2.1]? == some L.uE && args[F.2.2]? == some L.w && siteB L.o args rets)) (coreOf L.o).body

/-- **A callee's check.** -/
noncomputable def calleeB (F : String × ℕ × ℕ) : Bool :=
  match coreProgram.find? F.1 with
  | some fn => Nat.ble 1 F.2.1 && Nat.ble 1 F.2.2 && Nat.blt F.2.1 fn.params.length &&
      Nat.blt F.2.2 fn.params.length && (!fn.loop || !(Stmt.blockCallees (loopBody fn)).contains F.1)
  | none => false

/-- **The callers' check of one function**: a call of a callee is the caller's, or the callee's, a
loop. -/
noncomputable def callersB (L : Link) (fn : Fn) : Bool :=
  sitesB (fun f _ _ => !(L.fams.any (·.1 == f)) || fn.name == L.oName || (fn.name == f && fn.loop)) fn.body

/-- **The callers' check of one function** against `(callee, caller)` pairs: a call of a listed
callee is its caller's, or its own, a loop. -/
noncomputable def callersG (R : List (String × String)) (fn : Fn) : Bool :=
  sitesB (fun f _ _ => R.all fun p => p.1 != f || fn.name == p.2 || (fn.name == f && fn.loop)) fn.body

/-- **The callers' check of one function** against `(callee, callers)` pairs: a call of a listed callee is one of
its callers', or its own, a loop. -/
noncomputable def callersM (R : List (String × List String)) (fn : Fn) : Bool :=
  sitesB (fun f _ _ => R.all fun p => p.1 != f || p.2.contains fn.name || (fn.name == f && fn.loop)) fn.body

theorem walkOk_const {α : Type} (c : α → Bool) : ∀ (j : ℕ) (l : List α), walkOk (fun _ x => c x) j l = l.all c
  | _, [] => rfl
  | j, x :: xs => by simp only [walkOk, List.all_cons, walkOk_const c (j + 1) xs]

/-- **A check of every function, by ranges.** -/
theorem rangeOk_all {c : Fn → Bool} (h : RangeOk (fun _ fn => c fn) 0 coreProgram.length) :
    ∀ fn ∈ coreProgram, c fn = true := by
  unfold RangeOk at h
  rw [List.drop_zero, List.take_length, walkOk_const] at h
  exact List.all_eq_true.mp h

end

end LeanVM.Guest.Res
