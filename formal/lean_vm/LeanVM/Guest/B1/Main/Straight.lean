/-
  LeanVM.Guest.B1.Main.Straight

  The path of a straight-line body (atoms, calls, conditional calls, then a return): its events,
  `HeapBuf` hints, `frameAddr`s and frames, read off the statements, for `relAt_of_walk`.
-/

module

public import LeanVM.Guest.Memory.Placed
public import LeanVM.Guest.B1.Main.Basic

/-!
# Straight-line bodies

A body with no branch, `match` or dispatch walks every statement in turn
(`walk_straight`), so the `HeapBuf` hints, `frameAddr`s and frames of its path are those of its
statements (`allocDsts_straight`, `allocs_straight`, `addrs_straight`, `calls_straight`), each a
`filterMap` over the statements that the kernel evaluates on a concrete body; only a conditional
call's `taken` and a dynamic size's exponent depend on the valuation.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A statement of a straight-line body. -/
def Stmt.straight : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf .. => true
  | _ => false

/-- The events of a straight-line statement. -/
noncomputable def slEvs (σ : Val) : Stmt → List Ev
  | .atom a => [.atom a]
  | .call f args rets => [.call f args rets]
  | .callIf c f args => [.inK c, if σ c = 0 then .skip f args else .call f args []]
  | _ => []

theorem walk1_straight (σ : Val) : ∀ s : Stmt, Stmt.straight s = true → walk1 σ s = .fall (slEvs σ s)
  | .atom _, _ => rfl
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .ite .., h => by simp [Stmt.straight] at h
  | .match_ .., h => by simp [Stmt.straight] at h
  | .dispatch .., h => by simp [Stmt.straight] at h
  | .ret _, h => by simp [Stmt.straight] at h

/-- **A straight-line body walks every statement.** -/
theorem walk_straight (σ : Val) (vs : List V) : ∀ pre : List Stmt, pre.all Stmt.straight = true →
    walk σ (pre ++ [.ret vs]) = .ret (pre.flatMap (slEvs σ)) vs
  | [], _ => by simp [walk, walk1, Out.seq]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_straight σ vs pre h.2, walk1_straight σ s h.1, Out.seq,
      Out.pre, List.flatMap_cons]

/-- A `HeapBuf` hint: its pointer, and its size or the value whose exponent it is. -/
def Stmt.allocSz : Stmt → Option (V × (ℕ ⊕ V))
  | .atom (.hint (.alloc d n)) => some (d, .inl n)
  | .atom (.hint (.allocDyn d s)) => some (d, .inr s)
  | _ => none

/-- A `frameAddr`: its pointer and its run's first value. -/
def Stmt.addrS : Stmt → Option (V × V)
  | .atom (.frameAddr p (r :: _)) => some (p, r)
  | _ => none

/-- A frame a statement sets up: its condition, callee, arguments, returns. -/
def Stmt.callS : Stmt → Option (Option V × String × List V × List V)
  | .call f args rets => some (none, f, args, rets)
  | .callIf c f args => some (some c, f, args, [])
  | _ => none

/-- The frame of `Stmt.callS` under `σ`. -/
noncomputable def mkCall (σ : Val) : Option V × String × List V × List V → Call
  | (none, f, args, rets) => ⟨f, args, rets, true⟩
  | (some c, f, args, rets) => ⟨f, args, rets, decide (σ c ≠ 0)⟩

theorem slEvs_atom_alloc (σ : Val) (a : Atom) :
    (slEvs σ (.atom a)).filterMap Ev.allocDst? = ((Stmt.allocSz (.atom a)).map Prod.fst).toList ∧
    (slEvs σ (.atom a)).filterMap (Ev.alloc? σ) =
      ((Stmt.allocSz (.atom a)).map fun x => x.2.elim id fun s => logG (σ s)).toList ∧
    (slEvs σ (.atom a)).filterMap Ev.addr? = (Stmt.addrS (.atom a)).toList ∧
    (slEvs σ (.atom a)).filterMap Ev.call? = [] := by
  simp only [slEvs, List.filterMap_cons, List.filterMap_nil]
  cases a with
  | frameAddr p run =>
    cases run <;> simp [Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz, Stmt.addrS]
  | hint h => cases h <;> simp [Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz, Stmt.addrS]
  | _ => simp [Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz, Stmt.addrS]

theorem straight_parts (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.straight = true →
    allocDsts (pre.flatMap (slEvs σ)) = (pre.filterMap Stmt.allocSz).map Prod.fst ∧
    allocs σ (pre.flatMap (slEvs σ)) =
      (pre.filterMap Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) ∧
    addrs (pre.flatMap (slEvs σ)) = pre.filterMap Stmt.addrS ∧
    calls (pre.flatMap (slEvs σ)) = (pre.filterMap Stmt.callS).map (mkCall σ)
  | [], _ => by simp [allocDsts, allocs, addrs, calls]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨i1, i2, i3, i4⟩ := straight_parts σ pre h.2
    simp only [allocDsts, allocs, addrs, calls, List.flatMap_cons, List.filterMap_append] at i1 i2 i3 i4 ⊢
    rw [i1, i2, i3, i4]
    match s, h.1 with
    | .atom a, _ =>
      obtain ⟨e1, e2, e3, e4⟩ := slEvs_atom_alloc σ a
      rw [e1, e2, e3, e4]
      cases hs : Stmt.allocSz (.atom a) <;> cases ha : Stmt.addrS (.atom a) <;>
        simp [List.filterMap_cons, hs, ha, Stmt.callS]
    | .call f args rets, _ =>
      simp [slEvs, List.filterMap_cons, Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Stmt.allocSz,
        Stmt.addrS, Stmt.callS, mkCall]
    | .callIf c f args, _ =>
      by_cases hc : σ c = 0 <;>
        simp [slEvs, hc, List.filterMap_cons, Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?,
          Stmt.allocSz, Stmt.addrS, Stmt.callS, mkCall]

end
end LeanVM.Guest.B1.Main
