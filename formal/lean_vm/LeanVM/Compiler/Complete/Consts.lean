/-
  LeanVM.Compiler.Complete.Consts

  A right table of constant parameters (`ConstsOk`) holds of every call a body makes: what
  completeness reads of an honest run.
-/

module

public import LeanVM.Compiler.Sound.Consts

/-!
# The constant parameters on an honest run

`withConstsC C T` is the call relation `C` at calls whose arguments the table `T` names hold their
words. Where `T` is right of a block (`blockOk`), the block's semantics under `C` is its semantics
under `withConstsC C T` (`holdsList_consts`), what the statements before each call teach
supplying the words; so a function's relation, called with its own entries' words, makes only
such calls (`fnSem_consts`). The twin, for the obligations, is `Sound/Consts.lean`.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The call relation at calls whose arguments `T` names hold their words. -/
def withConstsC (C : CallRel) (T : Consts) : CallRel :=
  fun f a r => C f a r ∧ ∀ x ∈ T.at f, a[x.1]? = some x.2

section

variable {T : Consts} {C : CallRel} {rd : Reader} {σ : Val}

mutual
/-- **A statement's semantics makes only calls with the table's words.** -/
theorem holds_consts : ∀ (s : Stmt) {kn : Known} {A B : Prop} {kret : List E → Prop},
    KnownHolds σ kn → stmtOk T kn s = true → (A → B) → Stmt.Holds C rd σ s A kret →
      Stmt.Holds (withConstsC C T) rd σ s B kret
  | .atom _, _, _, _, _, _, _, hAB, h => ⟨h.1, hAB h.2⟩
  | .ite _ z n, _, _, _, _, hk, hs, hAB, h => by
      simp only [stmtOk, Bool.and_eq_true] at hs
      exact ⟨h.1, fun h0 => holdsList_consts z hk hs.1 hAB (h.2.1 h0),
        fun h0 => holdsList_consts n hk hs.2 hAB (h.2.2 h0)⟩
  | .match_ x arms, _, _, _, _, hk, hs, hAB, h => holdsArms_consts x arms 0 hk hs hAB h
  | .call _ _ _, _, _, _, _, hk, hs, hAB, h => ⟨⟨h.1, argsOk_words hk hs⟩, hAB h.2⟩
  | .callIf _ _ _, _, _, _, _, hk, hs, hAB, h =>
      ⟨h.1, fun h0 => ⟨h.2.1 h0, argsOk_words hk hs⟩, hAB h.2.2⟩
  | .dispatch _ fs _ _, _, _, _, _, hk, hs, hAB, h => by
      obtain ⟨⟨j, hj, hx, hc⟩, hn⟩ := h
      exact ⟨⟨j, hj, hx, hc, argsOk_words hk (List.all_eq_true.mp hs _ (List.getElem_mem hj))⟩,
        hAB hn⟩
  | .ret _, _, _, _, _, _, _, _, h => h

/-- **A block's semantics makes only calls with the table's words**, each statement knowing what
the ones before it taught. -/
theorem holdsList_consts : ∀ (ss : List Stmt) {kn : Known} {A B : Prop} {kret : List E → Prop},
    KnownHolds σ kn → blockOk T kn ss = true → (A → B) → Stmt.HoldsList C rd σ ss A kret →
      Stmt.HoldsList (withConstsC C T) rd σ ss B kret
  | [], _, _, _, _, _, _, hAB, h => hAB h
  | .atom a :: ss, _, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact ⟨h.1, holdsList_consts ss (learn_holds hk h.1) hs.2 hAB h.2⟩
  | .ite c z n :: ss, _, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact holds_consts (.ite c z n) hk hs.1 (holdsList_consts ss hk hs.2 hAB) h
  | .match_ x arms :: ss, _, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact holds_consts (.match_ x arms) hk hs.1 (holdsList_consts ss hk hs.2 hAB) h
  | .call f args rets :: ss, _, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact holds_consts (.call f args rets) hk hs.1 (holdsList_consts ss hk hs.2 hAB) h
  | .callIf c f args :: ss, _, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact holds_consts (.callIf c f args) hk hs.1 (holdsList_consts ss hk hs.2 hAB) h
  | .dispatch x fs args rets :: ss, _, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact holds_consts (.dispatch x fs args rets) hk hs.1 (holdsList_consts ss hk hs.2 hAB) h
  | .ret vs :: ss, _, _, _, _, hk, hs, hAB, h => by
      simp only [blockOk, Bool.and_eq_true] at hs
      exact holds_consts (.ret vs) hk hs.1 (holdsList_consts ss hk hs.2 hAB) h

/-- **The arms' semantics makes only calls with the table's words.** -/
theorem holdsArms_consts (x : V) : ∀ (arms : List (List Stmt)) (j : Nat) {kn : Known} {A B : Prop}
    {kret : List E → Prop}, KnownHolds σ kn → armsOk T kn arms = true → (A → B) →
      Stmt.HoldsArms C rd σ x j arms A kret → Stmt.HoldsArms (withConstsC C T) rd σ x j arms B kret
  | [], _, _, _, _, _, _, _, _, h => h
  | a :: as, j, _, _, _, _, hk, hs, hAB, h => by
      simp only [armsOk, Bool.and_eq_true] at hs
      rcases h with ⟨hx, ha⟩ | ha
      · exact Or.inl ⟨hx, holdsList_consts a hk hs.1 hAB ha⟩
      · exact Or.inr (holdsArms_consts x as (j + 1) hk hs.2 hAB ha)
end

/-- **A function's relation, called with its entries' words, makes only calls with the table's
words**, for a table right of a program holding the function. -/
theorem fnSem_consts {p : Program} (hT : ConstsOk T p = true) {f : Fn} (hf : f ∈ p)
    {args rets : List E} (ha : ∀ x ∈ T.at f.name, args[x.1]? = some x.2)
    (h : f.Sem C rd args rets) : f.Sem (withConstsC C T) rd args rets := by
  obtain ⟨σ, hp, hb⟩ := h
  exact ⟨σ, hp, holdsList_consts f.body (entryKnown_holds hp ha)
    (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hT).2 f hf) id hb⟩

end

end
end LeanVM.Compiler
