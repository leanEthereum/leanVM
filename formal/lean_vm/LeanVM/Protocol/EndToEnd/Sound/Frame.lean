/-
  LeanVM.Protocol.EndToEnd.Sound.Frame

  Rules of the specification calculus the end-to-end assembly needs beyond the core ones: an
  invariant carried along a sub-program without commitments (a frame rule), a return invariant
  added to a postcondition, the stack's commitment with any postcondition, and facts on returns
  of sequenced programs.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.Compile.Prover
public import LeanVM.Protocol.Verifier

/-!
# Frame rules for the end-to-end assembly

* `Spec.frame`: an invariant `J` of the history that the sub-program's runs keep (for instance
  "the commitments so far are exactly the stack's", along a phase without commitments) is
  carried from the precondition to the postcondition. The doom is `J h₀ ∧ D`; the potential is
  `1` where `J h₀` fails.
* `Spec.retInv`: a property of every value the program can return is added to the
  postcondition.
* `commitSpec`: the stack's commitment (`commitStack`), from no doom to any postcondition `Post`
  created at the root, and `commitSpec_D`, its doom right after the root.
* `retSplit_eq_none_of_after`, `after_bind_ret`: where a program is defined and not returned it
  has not returned before, and a return of a sequence splits at a return of its first part.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type} {p : Prog α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

/-! ## The frame rule -/

open Classical in
/-- **The frame rule**: an invariant `J` of the history that every run of `p` keeps is carried
from the precondition to the postcondition. -/
noncomputable def Spec.frame (S : Spec p Pre Post εmax L T) (J : List Ev → Prop)
    (hJ : ∀ h₀ l, p.Reach h₀ l → J h₀ → J (h₀ ++ l)) :
    Spec p (fun h ↦ Pre h ∧ J h) (fun a h ↦ Post a h ∧ J h) εmax L T where
  D h₀ l := J h₀ ∧ S.D h₀ l
  V h₀ l := if J h₀ then S.V h₀ l else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one _ _, le_rfl]
  start_D h₀ h := ⟨h.2, S.start_D h₀ h.1⟩
  start_V h₀ h := by simp only [h.2, ↓reduceIte]; exact S.start_V h₀ h.1
  read x hl ha hD := ⟨hD.1, S.read x hl ha hD.2⟩
  grind hl ha hD := ⟨hD.1, S.grind hl ha hD.2⟩
  commit word hl ha hw hD := ⟨hD.1, S.commit word hl ha hw hD.2⟩
  sample {h₀ _ _} hl ha := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.sample hl ha
    · simp only [hJ0, ↓reduceIte]; exact avg_le_one _ fun _ ↦ le_rfl
  query {h₀ _ _ _ _ _} hl ha hans := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.query hl ha hans
    · simp [hJ0]
  moveEnd {h₀ _ _} hl ha hm hD := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.moveEnd hl ha hm fun h ↦ hD ⟨hJ0, h⟩
    · simp [hJ0]
  retEnd {h₀ _ _} hl ha hD := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.retEnd hl ha fun h ↦ hD ⟨hJ0, h⟩
    · simp [hJ0]
  retDoom hl ha hD := by simp only [hD.1, ↓reduceIte]; exact S.retDoom hl ha hD.2
  post hl ha hD := ⟨S.post hl ha hD.2, hJ _ _ hl hD.1⟩
  bound hl hne hm hD := by simp only [hD.1, ↓reduceIte]; exact S.bound hl hne hm hD.2

/-- The doom of a framed specification. -/
theorem Spec.frame_D (S : Spec p Pre Post εmax L T) (J : List Ev → Prop)
    (hJ : ∀ h₀ l, p.Reach h₀ l → J h₀ → J (h₀ ++ l)) (h₀ l : List Ev) :
    (Spec.frame S J hJ).D h₀ l ↔ J h₀ ∧ S.D h₀ l := Iff.rfl

/-- **A return invariant**: a property of every value `p` returns is added to the
postcondition. -/
def Spec.retInv (S : Spec p Pre Post εmax L T) (Q : α → Prop)
    (hQ : ∀ l a, p.after l = some (.ret a) → Q a) :
    Spec p Pre (fun a h ↦ Post a h ∧ Q a) εmax L T where
  D := S.D
  V := S.V
  le_one := S.le_one
  start_D := S.start_D
  start_V := S.start_V
  read := S.read
  grind := S.grind
  commit := S.commit
  sample := S.sample
  query := S.query
  moveEnd := S.moveEnd
  retEnd := S.retEnd
  retDoom := S.retDoom
  post hl ha hD := ⟨S.post hl ha hD, hQ _ _ ha⟩
  bound := S.bound

/-- The doom of a specification transported along an equality of programs is unchanged. -/
theorem Spec.congr_D {p' : Prog α} (h : p = p') (S : Spec p Pre Post εmax L T) :
    (S.congr h).D = S.D := by
  subst h; rfl

/-! ## Returns -/

/-- Where a program is defined at a node that is not a return, it has not returned before. -/
theorem retSplit_eq_none_of_after {p : Prog α} {l : List Ev} {q : Prog α}
    (ha : p.after l = some q) (hq : ∀ a, q ≠ .ret a) : p.retSplit l = none := by
  rcases hs : p.retSplit l with _ | ⟨a, l₁, l₂⟩
  · rfl
  · obtain ⟨rfl, h1⟩ := Prog.retSplit_eq_some_iff.1 hs
    rw [Prog.after_append, h1, Option.bind_some] at ha
    cases l₂ with
    | nil => simp only [Prog.after, Option.some.injEq] at ha; exact absurd ha.symm (hq a)
    | cons e es => cases e <;> simp [Prog.after] at ha

/-- A sequence equal to a return starts with a return. -/
theorem bind_eq_ret_iff {p : Prog α} {f : α → Prog β} {b : β} (h : p.bind f = .ret b) :
    ∃ a, p = .ret a ∧ f a = .ret b := by
  cases p <;> simp_all [Prog.bind]

/-- **A return of a sequence** is a return of its first part followed by a return of the
second. -/
theorem after_bind_ret {p : Prog α} {f : α → Prog β} {l : List Ev} {b : β}
    (h : (p.bind f).after l = some (.ret b)) :
    ∃ a l₁ l₂, l = l₁ ++ l₂ ∧ p.after l₁ = some (.ret a) ∧ (f a).after l₂ = some (.ret b) := by
  rcases Prog.after_bind_cases f h with ⟨q, hq, hr⟩ | ⟨a, l₁, l₂, rfl, h1, -, h3⟩
  · obtain ⟨a, rfl, hfa⟩ := bind_eq_ret_iff hr.symm
    exact ⟨a, l, [], by simp, hq, by simp [Prog.after, hfa]⟩
  · exact ⟨a, l₁, l₂, rfl, h1, h3⟩

/-- A return of a program at a history, and at an extension of it, are at the same history. -/
theorem eq_of_after_ret {p : Prog α} {l l' : List Ev} {a : α}
    (h : p.after l = some (.ret a)) (h' : (p.after (l ++ l')).isSome) : l' = [] := by
  rw [Prog.after_append, h, Option.bind_some] at h'
  cases l' with
  | nil => rfl
  | cons e es => cases e <;> simp [Prog.after] at h'

/-! ## The stack's commitment with any postcondition -/

/-- **The stack's root with any postcondition**: from no doom, the doom after the root is
`Post ()`, created by the commitment (the same specification as `commitStackSpec`, with the
postcondition a parameter). The boundary after the root carries the follower's lead `T`. -/
noncomputable def commitSpec (Post : Unit → List Ev → Prop) (logN logInvRate : ℕ)
    (hT : T ≤ εmax) : Spec (commitStack logN logInvRate) (fun _ ↦ False) Post εmax 0 T :=
  Spec.bind (Spec.dead : Spec _ _ (fun _ _ ↦ False) εmax 0 0) fun config ↦ by
    cases config with
    | nil => exact Spec.fail
    | cons level _ =>
      exact Spec.commitP _ _ (fun _ _ h _ ↦ h.elim) hT

/-- The doom of the stack's root, right after it: the postcondition. -/
theorem commitSpec_D (Post : Unit → List Ev → Prop) {logN logInvRate : ℕ} (hT : T ≤ εmax)
    {level : Whir.Level} {rest : List Whir.Level}
    (hc : deriveConfig logN logInvRate = some (level :: rest)) (h₀ : List Ev) (e : Ev) :
    (commitSpec Post logN logInvRate hT).D h₀ [e] ↔ Post () (h₀ ++ [e]) := by
  have hs : (liftOption (deriveConfig logN logInvRate)).retSplit [e] =
      some (level :: rest, [], [e]) := by
    rw [hc]
    exact Prog.retSplit_of_after (Prog.ret (level :: rest)) [] [e] rfl
  rw [commitSpec, Spec.bind_D, Spec.bindD_after hs (List.cons_ne_nil _ _)]
  simp only [List.append_nil]
  rfl

end
end LeanVM.Protocol.EndToEnd.Sound
