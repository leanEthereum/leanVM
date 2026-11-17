/-
  LeanVM.Compiler.Sound.Obl.Post

  The postconditions the analysis checks hold of a program's located call relation.
-/

module

public import LeanVM.Compiler.Sound.Obl.CheckSound

/-!
# Postconditions of the located call relation

`post_relL`: in a program whose every function with a postcondition the analysis accepts, a call
in the located relation (`Program.RelL`) meets its callee's postcondition, its frames meeting the
preconditions (`A`). The callee's body holds at some frame with a `return`; `holdsList_post`
bounds what it returns from the callee's own hypotheses, by induction on the depth of calls. The
relations a signature's `xpost` names are not the analysis': they come from a fact about the
unlocated relation (`hxp`).
-/

namespace LeanVM.Compiler.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Reach

variable {C : CallRel} {rd : Reader} {σ : Val}

mutual
/-- A statement that holds goes on or returns. -/
theorem reach_s : ∀ (s : Stmt) {next : Prop} {kret : List E → Prop},
    Stmt.Holds C rd σ s next kret → next ∨ ∃ rs, kret rs
  | .atom _, _, _, h => .inl h.2
  | .ite c z n, _, _, h => by
      by_cases hc : σ c = 0
      · exact reach_l z (h.2.1 hc)
      · exact reach_l n (h.2.2 hc)
  | .match_ x arms, _, _, h => reach_a x arms 0 h
  | .call .., _, _, h => .inl h.2
  | .callIf .., _, _, h => .inl h.2.2
  | .dispatch .., _, _, h => .inl h.2
  | .ret _, _, _, h => .inr ⟨_, h⟩

/-- A block that holds goes on or returns. -/
theorem reach_l : ∀ (ss : List Stmt) {next : Prop} {kret : List E → Prop},
    Stmt.HoldsList C rd σ ss next kret → next ∨ ∃ rs, kret rs
  | [], _, _, h => .inl h
  | s :: ss, _, _, h => (reach_s s h).elim (fun h' => reach_l ss h') .inr

/-- Arms that hold go on or return. -/
theorem reach_a (x : V) : ∀ (arms : List (List Stmt)) (j : Nat) {next : Prop}
    {kret : List E → Prop}, Stmt.HoldsArms C rd σ x j arms next kret → next ∨ ∃ rs, kret rs
  | [], _, _, _, h => h.elim
  | a :: as, j, _, _, h => h.elim (fun h' => reach_l a h'.2) (fun h' => reach_a x as (j + 1) h')
end

end Reach

variable {R : Nat → Reader → E → Prop} {T : Tab} {κ : ℕ} {L : MemoryImage κ}

/-- **Calls of the located relation of depth `n` meet their callees' postconditions.** -/
theorem post_locN (hT : PowsOk T) (hκ : κ ≤ 32) {P : Program} {vf : String → K → Val}
    {A : String → K → List E → List E → Prop}
    (hP : ∀ fn ∈ P, (T.sig fn.name).post ≠ [] → chkFn T fn = true)
    (hA : ∀ f fp a r, A f fp a r → SigPre R L.read (T.sig f) a)
    (hxp : ∀ f a r, P.Rel L.read f a r → XPost R L.read (T.sig f) (a ++ r)) :
    ∀ (n : Nat) (f : String) (a r : List E), P.locN L.read vf A n f a r →
      SigPost (T.sig f) (a ++ r)
  | 0, _, _, _, h => h.elim
  | n + 1, f, a, r, ⟨fn, fp, hf, hAf, hp, hb⟩ => by
      by_cases hpost : (T.sig f).post = []
      · intro p hp'
        rw [hpost] at hp'
        exact absurd hp' List.not_mem_nil
      have hname : fn.name = f := by
        have := List.find?_some hf
        simpa using this
      have hchk := hP fn (List.mem_of_find?_eq_some hf) (by rwa [hname])
      unfold chkFn at hchk
      rw [hname] at hchk
      have hpre : SigPre R L.read (T.sig f) (fn.params.map (vf f fp)) := hp ▸ hA f fp a r hAf
      have hh := holdsList_post hT hκ (fun f' a' r' h' => ⟨post_locN hT hκ hP hA hxp n f' a' r' h',
          hxp f' a' r' (relN_le_rel P n f' a' r' (locN_le_relN P n f' a' r' h'))⟩)
        ⟨fn.params, (T.sig f).post⟩ fn.body _ False False _ (entry_holds hpre) hchk id hb
      rcases reach_l fn.body hh with hF | ⟨rs, rfl, hpo⟩
      · exact hF.elim
      · intro p hp' hl
        have := hpo p hp' (by simpa [hp] using hl)
        simpa [hp] using this

/-- **Calls of the located relation meet their callees' postconditions**, those the analysis
checks and, from the unlocated relation, the relations `xpost` says. -/
theorem post_relL (hT : PowsOk T) (hκ : κ ≤ 32) {P : Program} {vf : String → K → Val}
    {A : String → K → List E → List E → Prop}
    (hP : ∀ fn ∈ P, (T.sig fn.name).post ≠ [] → chkFn T fn = true)
    (hA : ∀ f fp a r, A f fp a r → SigPre R L.read (T.sig f) a)
    (hxp : ∀ f a r, P.Rel L.read f a r → XPost R L.read (T.sig f) (a ++ r)) (f : String)
    (a r : List E) (h : P.RelL L.read vf A f a r) :
    SigPost (T.sig f) (a ++ r) ∧ XPost R L.read (T.sig f) (a ++ r) :=
  let ⟨n, hn⟩ := h
  ⟨post_locN hT hκ hP hA hxp n f a r hn, hxp f a r (relL_le_rel P f a r ⟨n, hn⟩)⟩

end
end LeanVM.Compiler.Obl
