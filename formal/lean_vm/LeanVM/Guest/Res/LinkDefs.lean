/-
  LeanVM.Guest.Res.LinkDefs

  The checks behind a callee's table reads: its entries and bound parameters linked to its
  caller's frame, and the residual a read inside that table leaves.
-/

module

public import LeanVM.Guest.Res.Down
public import LeanVM.Guest.B1.Digest.Chain
public import LeanVM.Guest.Memory.StaticCut
public import LeanVM.Guest.Memory.Family

/-!
# Linking a callee's parameters to its caller's frame

A callee reads `[pE]·[x]^4`, `x` range-checked against its parameter `pL`, and the residual asks
that this lie inside its caller's table: the run of four cells from `[[1]·g^2]·g^(4j)`, `j` below the
exponent of `[[1]·g^5]` (`anyTab`), header cell `1` naming the caller's frame. A `Link` names the
callees (`fams`: name, the indices of `pE` and `pL` among its parameters) and their caller `o`,
whose cell `2` holds its entries parameter `uE` and cell `5` its bound `uL = w · c`, `c = g`; the
callees get `uE` and `w`. A loop callee passes them on along its tail calls.

The checks: `originB` (the caller: its cells, the bound's atoms on every path, its call sites of the
callees passing `uE` and `w`, each a site of its plumbing); `calleeB` (each callee: `pE` and `pL` no
loop counter, a loop not calling itself before its tail); `callersB` (a function calling a callee
is the caller, or the callee itself, a loop). `anyResB L j x`: residual `x` of function `j` is such
a read, its cells and range check checked against the body.
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

/-- A range check of a value of cell `o` against `pL`. -/
noncomputable def rcAt (j : ℕ) (pL : V) (o : ℕ) : Atom → Bool
  | .rangeCheck x _ _ _ k => decide (k = pL) && cellJ j x == o
  | _ => false

/-- **The caller's table**: four runs of stride 4, from `[[1]·g^2]` up to the exponent of `[[1]·g^5]`. -/
def anyTab : List Mode.Rng :=
  (List.range 4).map fun d => ⟨⟨0, 0, [(.hp 1 2, 1)]⟩, .num 0, .ex (.hp 1 5) 0, 4, d⟩

/-- The shape of a read: four cells from `[cE]·[cO]^4`. -/
def anyRead (cE cO : ℕ) : Mode.Rng := ⟨⟨0, 0, [(.fr cE, 1), (.fr cO, 4)]⟩, .num 0, .num 4, 1, 0⟩

/-- **A read of function `j` inside its caller's table**: `[pE]·[x]^4` for a callee of `L`, `x`
range-checked against `pL` on every path, both cells inside the frame. -/
noncomputable def anyResB (L : Link) (j : ℕ) : Mode.Res → Bool
  | .sub a bs => decide (bs = anyTab) && L.fams.any fun F => (coreOf j).name == F.1 &&
      match (coreOf j).params[F.2.1]?, (coreOf j).params[F.2.2]?, a.q.bs with
      | some pE, some pL, [(.fr cE, 1), (.fr cO, 4)] => decide (a = anyRead cE cO) &&
          cellJ j pE == cE && Nat.ble 2 cE && Nat.blt cE (fsN j) && Nat.ble 2 cO && Nat.blt cO (fsN j) &&
          scanAt (rcAt j pL cO) (coreOf j).body
      | _, _, _ => false
  | _ => false

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
