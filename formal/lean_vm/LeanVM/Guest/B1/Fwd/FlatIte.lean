/-
  LeanVM.Guest.B1.Fwd.FlatIte

  A body as the forward evaluator walks it (each top-level `ite`'s branches in order, an
  `assertNe` as the product it checks), statements holding one by one, loads inside buffers:
  the generic part of `verify_tables`' completeness (`Tables/VtC`), shared by every flat
  function's.
-/

module

public import LeanVM.Guest.B1.Fwd.Canon

/-!
# Flat bodies

`flatIte`: a block with each top-level `ite`'s branches in order (both are numbered in order, so
the evaluator defines each branch's values; only the taken branch must hold). `fixNe`: an
`assertNe x i p` after a hint `i = 1/x` defines `p` as `x·i`, the product it checks.
`VSH C rd σ s`: the statement holds, its continuation aside; an `ite` by its taken branch
(`holdsList_of_vsh`). `mem_flatIte_of`, `mem_flatIte_ite`: a statement, an `ite`'s branches, are in
the list. `InBuf`, `LoadsInBuf`: loads inside buffers.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A block with each top-level `ite`'s branches in order. -/
def flatIte : List Stmt → List Stmt
  | [] => []
  | .ite _ z n :: ss => z ++ n ++ flatIte ss
  | s :: ss => s :: flatIte ss

/-- An `assertNe` read as the product it checks. -/
def fixNe : Stmt → Stmt
  | .atom (.assertNe x i p) => .atom (.mul p x i)
  | s => s

/-- A straight statement: an atom, a call, a conditional call or a dispatch. -/
def straightB : Stmt → Bool
  | .atom _ | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- A straight statement, or an `ite` of straight branches. -/
def iteOk : Stmt → Bool
  | .ite _ z n => z.all straightB && n.all straightB
  | s => straightB s

/-- A statement holds, its continuation aside; an `ite` by its taken branch. -/
def VSH (C : CallRel) (rd : Reader) (σ : Val) : Stmt → Prop
  | .ite c z n => IsInK (σ c) ∧ (σ c = 0 → ∀ s ∈ z, SHolds C rd σ s) ∧
      (σ c ≠ 0 → ∀ s ∈ n, SHolds C rd σ s)
  | s => SHolds C rd σ s

theorem holdsList_straightN {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) {next : Prop}, ss.all straightB = true → (∀ s ∈ ss, SHolds C rd σ s) →
      next → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, hn => hn
  | s :: ss, next, hst, hs, hn => by
    simp only [List.all_cons, Bool.and_eq_true] at hst
    have ih := holdsList_straightN (kret := kret) ss (next := next) hst.2
      (fun t ht => hs t (List.mem_cons_of_mem _ ht)) hn
    have h0 := hs s List.mem_cons_self
    simp only [Stmt.HoldsList]
    cases s with
    | atom a => exact ⟨h0, ih⟩
    | call f args rets => exact ⟨h0, ih⟩
    | callIf c f args => exact ⟨h0.1, h0.2, ih⟩
    | dispatch x fs args rets => exact ⟨h0, ih⟩
    | _ => simp [straightB] at hst

/-- **A block of straight statements and `ite`s of straight branches holds** when each does. -/
theorem holdsList_of_vsh {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) {next : Prop}, ss.all iteOk = true → (∀ s ∈ ss, VSH C rd σ s) →
      next → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, hn => hn
  | s :: ss, next, hok, hs, hn => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have ih := holdsList_of_vsh (kret := kret) ss (next := next) hok.2
      (fun t ht => hs t (List.mem_cons_of_mem _ ht)) hn
    have h0 := hs s List.mem_cons_self
    simp only [Stmt.HoldsList]
    cases s with
    | atom a => exact ⟨h0, ih⟩
    | call f args rets => exact ⟨h0, ih⟩
    | callIf c f args => exact ⟨h0.1, h0.2, ih⟩
    | dispatch x fs args rets => exact ⟨h0, ih⟩
    | ite c z n =>
      simp only [iteOk, Bool.and_eq_true] at hok
      obtain ⟨hk, hz, hn'⟩ := h0
      exact ⟨hk, fun h => holdsList_straightN z hok.1.1 (hz h) ih,
        fun h => holdsList_straightN n hok.1.2 (hn' h) ih⟩
    | _ => simp [iteOk, straightB] at hok

/-- An `assertNe` read as the product it checks (`fixNe` on atoms). -/
def fixA : Atom → Atom
  | .assertNe x i p => .mul p x i
  | a => a

theorem fixNe_atom (a : Atom) : fixNe (.atom a) = .atom (fixA a) := by
  cases a <;> rfl

/-- A hint. -/
def hintB : Atom → Bool
  | .hint _ => true
  | _ => false

/-- What holds by evaluation alone: constants, sums, copies, products of older values, hints. -/
def autoB : Stmt → Bool
  | .atom a => pureB a || hintB a
  | _ => false

theorem mem_flatIte_of {s : Stmt} (hni : ∀ c z n, s ≠ .ite c z n) :
    ∀ {ss : List Stmt}, s ∈ ss → s ∈ flatIte ss
  | [], h => absurd h (by simp)
  | t :: ss, h => by
    rcases List.mem_cons.mp h with rfl | h
    · cases s with
      | ite c z n => exact absurd rfl (hni c z n)
      | _ => simp [flatIte]
    · have ih := mem_flatIte_of hni h
      cases t with
      | ite c z n => simp [flatIte, ih]
      | _ => simp [flatIte, ih]

theorem mem_flatIte_ite {c : V} {z n : List Stmt} :
    ∀ {ss : List Stmt}, Stmt.ite c z n ∈ ss → ∀ t ∈ z ++ n, t ∈ flatIte ss
  | [], h => absurd h (by simp)
  | u :: ss, h => by
    intro t ht
    rcases List.mem_cons.mp h with rfl | h
    · simp only [flatIte, List.mem_append]
      rcases List.mem_append.mp ht with ht | ht
      · exact Or.inl (Or.inl ht)
      · exact Or.inl (Or.inr ht)
    · have ih := mem_flatIte_ite h t ht
      cases u with
      | ite c' z' n' => simp [flatIte, ih]
      | _ => simp [flatIte, ih]

/-- A load through `p` at `off` lands in one of the buffers `bufs` (pointer, length). -/
def InBuf (σ : Val) (bufs : List (E × ℕ)) (p : V) (off : ℕ) : Prop :=
  ∃ q ∈ bufs, ∃ j : ℕ, σ p = q.1 * gen ^ j ∧ j + off < q.2

/-- Every load atom of a block lands in one of the buffers. -/
def LoadsInBuf (σ : Val) (bufs : List (E × ℕ)) (blk : List Stmt) : Prop :=
  ∀ d p off, Stmt.atom (.load d p off) ∈ blk → InBuf σ bufs p off

end
end LeanVM.Guest.B1.Tables
