/-
  LeanVM.Guest.B1.Opening.QueriesFlatC

  Blocks of atoms, `match`es of atom arms and calls: their relation, statement by statement, and
  `mul_range` loops whose body calls.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesFlat
public import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.Value.FieldBits

/-!
# Flat blocks with calls

`opening_queries`' blocks are atoms, `match`es of atom arms (a query, `walk_path` inline) and calls (its
loops). `FlatC ss`: every statement is an atom, a `match` of atom arms or
a call. `holdsList_flatC`: such a block holds exactly when every statement does (`StmtOkC C`: a call
holds in the call relation `C`), then `next`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Every statement is an atom, a `match` of atom arms, or a call. -/
def FlatC (ss : List Stmt) : Prop :=
  ∀ s ∈ ss, (∃ a, s = .atom a) ∨ (∃ x arms, s = .match_ x arms ∧ ∀ arm ∈ arms, AllAtoms arm) ∨
    ∃ f args rets, s = .call f args rets

/-- What a statement of a flat block with calls asks of a valuation. -/
def StmtOkC (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .atom a => a.Holds rd σ
  | .match_ x arms => StmtOk rd σ (.match_ x arms)
  | .call f args rets => C f (args.map σ) (rets.map σ)
  | _ => False

/-- The statements of a block hold, statement by statement, calls in `C`. -/
def BlockOkC (C : CallRel) (rd : Reader) (σ : Val) (ss : List Stmt) : Prop := ∀ s ∈ ss, StmtOkC C rd σ s

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem flatC_of_flat {ss : List Stmt} (h : Flat ss) : FlatC ss := fun s hs ↦
  (h s hs).elim Or.inl fun h' ↦ Or.inr (Or.inl h')

theorem flatC_append {ss ts : List Stmt} (h1 : FlatC ss) (h2 : FlatC ts) : FlatC (ss ++ ts) :=
  fun s hs ↦ (List.mem_append.mp hs).elim (h1 s) (h2 s)

theorem flatC_cons {s : Stmt} {ss : List Stmt} (h : FlatC (s :: ss)) : FlatC ss :=
  fun t ht ↦ h t (List.mem_cons_of_mem _ ht)

theorem blockOkC_cons {s : Stmt} {ss : List Stmt} :
    BlockOkC C rd σ (s :: ss) ↔ StmtOkC C rd σ s ∧ BlockOkC C rd σ ss := by
  simp [BlockOkC]

/-- **A flat block with calls holds exactly when each of its statements does.** -/
theorem holdsList_flatC : ∀ {ss : List Stmt}, FlatC ss →
    ∀ (next : Prop) (kret : List E → Prop),
      (Stmt.HoldsList C rd σ ss next kret ↔ BlockOkC C rd σ ss ∧ next)
  | [], _, _, _ => by simp [Stmt.HoldsList, BlockOkC]
  | s :: ss, h, next, kret => by
    have ih : Stmt.HoldsList C rd σ ss next kret ↔ BlockOkC C rd σ ss ∧ next :=
      holdsList_flatC (flatC_cons h) next kret
    rw [blockOkC_cons]
    rcases h s (by simp) with ⟨a, rfl⟩ | ⟨x, arms, rfl, harms⟩ | ⟨f, args, rets, rfl⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, ih, StmtOkC]
      tauto
    · simp only [Stmt.HoldsList, Stmt.Holds, holdsArms_iff, Nat.zero_add, StmtOkC, StmtOk]
      constructor
      · rintro ⟨j, hj, hx, ha⟩
        rw [holdsList_atoms (harms _ (List.getElem_mem hj)), ih] at ha
        exact ⟨⟨⟨j, hj, hx, ha.1⟩, ha.2.1⟩, ha.2.2⟩
      · rintro ⟨⟨⟨j, hj, hx, ha⟩, hss⟩, hn⟩
        refine ⟨j, hj, hx, ?_⟩
        rw [holdsList_atoms (harms _ (List.getElem_mem hj)), ih]
        exact ⟨ha, hss, hn⟩
    · simp only [Stmt.HoldsList, Stmt.Holds, ih, StmtOkC]
      tauto

theorem blockOkC_of_blockOk {ss : List Stmt} (h : BlockOk rd σ ss) : BlockOkC C rd σ ss :=
  fun s hs ↦ by
    have := h s hs
    match s, this with
    | .atom _, h => exact h
    | .match_ _ _, h => exact h

theorem BlockOkC.blockOk {ss : List Stmt} (h : BlockOkC C rd σ ss) (hF : Flat ss) : BlockOk rd σ ss :=
  fun s hs ↦ by
    have := h s hs
    rcases hF s hs with ⟨a, rfl⟩ | ⟨x, arms, rfl, -⟩
    · exact this
    · exact this

theorem BlockOkC.mono {ss ts : List Stmt} (h : BlockOkC C rd σ ts) (hs : ∀ s ∈ ss, s ∈ ts) :
    BlockOkC C rd σ ss := fun s hs' ↦ h s (hs s hs')

theorem BlockOkC.atom {ss : List Stmt} (h : BlockOkC C rd σ ss) {a : Atom} (ha : Stmt.atom a ∈ ss) :
    a.Holds rd σ := h _ ha

theorem BlockOkC.call {ss : List Stmt} (h : BlockOkC C rd σ ss) {f : String} {args rets : List V}
    (ha : Stmt.call f args rets ∈ ss) : C f (args.map σ) (rets.map σ) := h _ ha

theorem blockOkC_append {ss ts : List Stmt} :
    BlockOkC C rd σ (ss ++ ts) ↔ BlockOkC C rd σ ss ∧ BlockOkC C rd σ ts := by
  simp only [BlockOkC, List.mem_append]
  exact ⟨fun h ↦ ⟨fun s hs ↦ h s (Or.inl hs), fun s hs ↦ h s (Or.inr hs)⟩,
    fun h s hs ↦ hs.elim (h.1 s) (h.2 s)⟩

theorem stmtOkC_mono {C C' : CallRel} (hC : CallRel.Le C C') :
    ∀ s : Stmt, StmtOkC C rd σ s → StmtOkC C' rd σ s
  | .atom _, h => h
  | .match_ _ _, h => h
  | .call _ _ _, h => hC _ _ _ h

theorem BlockOkC.monoC {C C' : CallRel} (hC : CallRel.Le C C') {ss : List Stmt}
    (h : BlockOkC C rd σ ss) : BlockOkC C' rd σ ss := fun s hs ↦ stmtOkC_mono hC s (h s hs)

/-- The meaning of a flat loop body with calls at the arguments `args`. -/
def FlatBodyC (C : CallRel) (rd : Reader) (params : List V) (A : List Stmt) (args : List E) : Prop :=
  ∃ σ : Val, params.map σ = args ∧ BlockOkC C rd σ A

theorem FlatBodyC.monoC {C C' : CallRel} (hC : CallRel.Le C C') {params : List V} {A : List Stmt}
    {args : List E} (h : FlatBodyC C rd params A args) : FlatBodyC C' rd params A args :=
  let ⟨σ, hp, hA⟩ := h; ⟨σ, hp, hA.monoC hC⟩

end
end LeanVM.Guest.B1
