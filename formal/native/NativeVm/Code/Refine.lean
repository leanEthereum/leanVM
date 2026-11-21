module

public import NativeVm.Code.Rel

/-!
# Code refining the model

`Refines P c m Q E`: from a machine state and a model state related by `P`, the code `c` runs to
its end; normally exactly when the model's `m` returns, the result and the states then related by
`Q`, and at the failure exit exactly when `m` rejects, in a state satisfying `E`. `E` is the
invariant the failure exit needs (the context pointer, the saved registers); it holds of every
failure of a phase, so it is one predicate throughout, not a relation to the start.

The rules follow the model's program: `Refines.seq`/`blk_cons` (`>>=`, the analogue of
`Equiv.Sim.bind`), `pure`, `require`, `liftOpt`, `reject`, `ite`, code with no model step
(`pre`, `post`), and the loop `foldlM` (a `.loop` against `List.foldlM`, one pass per element).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model

/-- **`c` refines `m`** from `P`: it ends normally exactly when `m` returns, in `Q` of the result
and the states, and fails exactly when `m` rejects, in `E`. -/
def Refines {α : Type} (P : TState → QState → Prop) (c : Stmt) (m : VM α)
    (Q : α → TState → QState → Prop) (E : QState → Prop) : Prop :=
  ∀ t s, P t s → WP c s (fun s' ↦ ∃ x t', m.run t = some (x, t') ∧ Q x t' s')
    (fun s' ↦ m.run t = none ∧ E s')

namespace Refines

variable {α β γ : Type} {P P' : TState → QState → Prop} {c c₁ c₂ : Stmt} {m : VM α}
  {Q Q' : α → TState → QState → Prop} {E E' : QState → Prop}

theorem mono (h : Refines P c m Q E) (hP : ∀ t s, P' t s → P t s)
    (hQ : ∀ x t s, Q x t s → Q' x t s) (hE : ∀ s, E s → E' s) : Refines P' c m Q' E' :=
  fun t s hts ↦ WP.mono (h t s (hP t s hts))
    (fun _ ⟨x, t', hr, hq⟩ ↦ ⟨x, t', hr, hQ _ _ _ hq⟩) (fun _ ⟨hr, he⟩ ↦ ⟨hr, hE _ he⟩)

/-- A precondition that is a fact of the start: assume it. -/
theorem intro {R : Prop} (h : R → Refines P c m Q E) : Refines (fun t s ↦ R ∧ P t s) c m Q E :=
  fun t s ⟨hr, hts⟩ ↦ h hr t s hts

/-- The run of `m >>= f` after `m` returned. -/
theorem run_bind_some {f : α → VM β} {t t' : TState} {x : α} (h : m.run t = some (x, t')) :
    (m >>= f).run t = (f x).run t' := by
  rw [StateT.run_bind, h]
  rfl

theorem run_bind_none {f : α → VM β} {t : TState} (h : m.run t = none) : (m >>= f).run t = none := by
  rw [StateT.run_bind, h]
  rfl

/-- **Sequence** (`Equiv.Sim.bind`): `c₁; c₂` refines `m₁ >>= m₂` when `c₁` refines `m₁` and
`c₂` refines `m₂ x` from what `c₁` leaves. -/
theorem seq {m₁ : VM α} {m₂ : α → VM β} {Q₁ : α → TState → QState → Prop}
    {Q₂ : β → TState → QState → Prop} (h₁ : Refines P c₁ m₁ Q₁ E)
    (h₂ : ∀ x, Refines (Q₁ x) c₂ (m₂ x) Q₂ E) : Refines P (.seq c₁ c₂) (m₁ >>= m₂) Q₂ E := by
  intro t s hts
  refine WP.seq (WP.mono (h₁ t s hts) (fun s₁ ⟨x, t₁, hr, hq⟩ ↦ ?_) (fun _ ⟨hr, he⟩ ↦
    ⟨run_bind_none hr, he⟩))
  rw [run_bind_some hr]
  exact h₂ x t₁ s₁ hq

theorem blk_cons {cs : List Stmt} {m₁ : VM α} {m₂ : α → VM β} {Q₁ : α → TState → QState → Prop}
    {Q₂ : β → TState → QState → Prop} (h₁ : Refines P c₁ m₁ Q₁ E)
    (h₂ : ∀ x, Refines (Q₁ x) (blk cs) (m₂ x) Q₂ E) :
    Refines P (blk (c₁ :: cs)) (m₁ >>= m₂) Q₂ E := by
  intro t s hts
  refine WP.blk_cons (WP.mono (h₁ t s hts) (fun s₁ ⟨x, t₁, hr, hq⟩ ↦ ?_) (fun _ ⟨hr, he⟩ ↦
    ⟨run_bind_none hr, he⟩))
  rw [run_bind_some hr]
  exact h₂ x t₁ s₁ hq

/-- Code with no model step before `c`: it runs from `P` to `P'` and does not fail. -/
theorem pre (h₁ : ∀ t s, P t s → WP c₁ s (P' t) fun _ ↦ False) (h₂ : Refines P' c₂ m Q E) :
    Refines P (.seq c₁ c₂) m Q E :=
  fun t s hts ↦ WP.seq (WP.mono (h₁ t s hts) (fun s₁ h ↦ h₂ t s₁ h) (fun _ h ↦ h.elim))

theorem pre_blk {cs : List Stmt} (h₁ : ∀ t s, P t s → WP c₁ s (P' t) fun _ ↦ False)
    (h₂ : Refines P' (blk cs) m Q E) : Refines P (blk (c₁ :: cs)) m Q E :=
  fun t s hts ↦ WP.blk_cons (WP.mono (h₁ t s hts) (fun s₁ h ↦ h₂ t s₁ h) (fun _ h ↦ h.elim))

/-- Code with no model step after `c`: it runs from `Q` to `Q'` and does not fail. -/
theorem post (h₁ : Refines P c₁ m Q E)
    (h₂ : ∀ x t s, Q x t s → WP c₂ s (Q' x t) fun _ ↦ False) : Refines P (.seq c₁ c₂) m Q' E :=
  fun t s hts ↦ WP.seq (WP.mono (h₁ t s hts)
    (fun _ ⟨x, t', hr, hq⟩ ↦ WP.mono (h₂ x t' _ hq) (fun _ h ↦ ⟨x, t', hr, h⟩) (fun _ h ↦ h.elim))
    (fun _ h ↦ h))

/-- **Pure**: code that computes `a` and does not fail. -/
theorem pure {a : α} {Q : α → TState → QState → Prop}
    (h : ∀ t s, P t s → WP c s (Q a t) fun _ ↦ False) : Refines P c (Pure.pure a : VM α) Q E :=
  fun t s hts ↦ WP.mono (h t s hts) (fun _ hq ↦ ⟨a, t, rfl, hq⟩) (fun _ h ↦ h.elim)

theorem skip {a : α} {Q : α → TState → QState → Prop} (h : ∀ t s, P t s → Q a t s) :
    Refines P .skip (Pure.pure a : VM α) Q E :=
  pure fun t s hts ↦ WP.skip (h t s hts)

/-- **Reject**: code that fails in `E`. -/
theorem reject {Q : α → TState → QState → Prop} (h : ∀ t s, P t s → WP c s (fun _ ↦ False) E) :
    Refines P c (Model.reject : VM α) Q E :=
  fun t s hts ↦ WP.mono (h t s hts) (fun _ h ↦ h.elim) (fun _ he ↦ ⟨rfl, he⟩)

theorem require_run (b : Bool) (t : TState) :
    (Model.require b).run t = if b then some ((), t) else none := by
  unfold Model.require
  cases b <;> rfl

/-- **Require**: code that fails exactly when the check does. -/
theorem require {b : Bool} {Q : Unit → TState → QState → Prop}
    (h : ∀ t s, P t s → WP c s (fun s' ↦ b = true ∧ Q () t s') fun s' ↦ b = false ∧ E s') :
    Refines P c (Model.require b) Q E := by
  intro t s hts
  refine WP.mono (h t s hts) (fun _ ⟨hb, hq⟩ ↦ ⟨(), t, by rw [require_run, hb]; rfl, hq⟩)
    (fun _ ⟨hb, he⟩ ↦ ⟨by rw [require_run, hb]; rfl, he⟩)

theorem liftOpt_run (o : Option α) (t : TState) :
    (Model.liftOpt o).run t = o.map fun a ↦ (a, t) := by
  cases o <;> rfl

/-- **`liftOpt`**: code that fails exactly on `none`. -/
theorem liftOpt {o : Option α}
    (h : ∀ t s, P t s → WP c s (fun s' ↦ ∃ a, o = some a ∧ Q a t s') fun s' ↦ o = none ∧ E s') :
    Refines P c (Model.liftOpt o) Q E := by
  intro t s hts
  refine WP.mono (h t s hts) (fun _ ⟨a, ho, hq⟩ ↦ ⟨a, t, by rw [liftOpt_run, ho]; rfl, hq⟩)
    (fun _ ⟨ho, he⟩ ↦ ⟨by rw [liftOpt_run, ho]; rfl, he⟩)

/-- **Branch**: the code's condition is the model's. -/
theorem ite {b : Bool} {cond : Cond} {m₁ m₂ : VM α}
    (hc : ∀ t s, P t s → cond.eval s = b) (h₁ : b = true → Refines P c₁ m₁ Q E)
    (h₂ : b = false → Refines P c₂ m₂ Q E) :
    Refines P (.ite cond c₁ c₂) (if b then m₁ else m₂) Q E := by
  intro t s hts
  refine WP.ite ?_
  rw [hc t s hts]
  cases b
  · exact h₂ rfl t s hts
  · exact h₁ rfl t s hts

/-- A model program with the same runs (a program normalized by the monad laws, a `match`
unfolded). -/
theorem of_run {m' : VM α} (he : ∀ t, m.run t = m'.run t) (h : Refines P c m Q E) :
    Refines P c m' Q E := by
  intro t s hts
  rw [← he t]
  exact h t s hts

/-- **The loop** over a list, against `List.foldlM`: `Inv k acc` after `k` passes with accumulator
`acc`; the condition holds while elements remain, and each pass refines the fold's step on the
next element. -/
theorem foldlM {δ : Type} {l : List δ} {f : β → δ → VM β} {cond : Cond} {body : Stmt}
    {Inv : Nat → β → TState → QState → Prop}
    (hcond : ∀ k acc t s, Inv k acc t s → (cond.eval s = true ↔ k < l.length))
    (hbody : ∀ k (hk : k < l.length) acc,
      Refines (Inv k acc) body (f acc l[k]) (fun acc' t' s' ↦ Inv (k + 1) acc' t' s') E)
    {init : β} : Refines (Inv 0 init) (.loop cond body) (l.foldlM f init)
      (fun acc t s ↦ Inv l.length acc t s) E := by
  suffices H : ∀ n k acc t s, l.length - k = n → k ≤ l.length → Inv k acc t s →
      WP (.loop cond body) s
        (fun s' ↦ ∃ x t', ((l.drop k).foldlM f acc).run t = some (x, t') ∧ Inv l.length x t' s')
        (fun s' ↦ ((l.drop k).foldlM f acc).run t = none ∧ E s') by
    intro t s hts
    exact H _ 0 init t s rfl (Nat.zero_le _) hts
  intro n
  induction n with
  | zero =>
    intro k acc t s hn hk hinv
    have hkl : k = l.length := by omega
    subst hkl
    have hc : cond.eval s = false := by
      rw [Bool.eq_false_iff, ne_eq, hcond _ _ _ _ hinv]
      exact Nat.lt_irrefl _
    rw [List.drop_length]
    exact ⟨_, .loopFalse hc, acc, t, rfl, hinv⟩
  | succ n ih =>
    intro k acc t s hn hk hinv
    have hkl : k < l.length := by omega
    have hc : cond.eval s = true := (hcond _ _ _ _ hinv).mpr hkl
    rw [List.drop_eq_getElem_cons hkl, List.foldlM_cons]
    obtain ⟨o, hx, ho⟩ := hbody k hkl acc t s hinv
    cases o with
    | ok s₁ =>
      obtain ⟨x, t₁, hr, hq⟩ := ho
      obtain ⟨o', hx', ho'⟩ := ih (k + 1) x t₁ s₁ (by omega) hkl hq
      refine ⟨o', .loopTrue hc hx hx', ?_⟩
      rw [run_bind_some hr]
      exact ho'
    | err s₁ =>
      obtain ⟨hr, he⟩ := ho
      exact ⟨_, .loopErr hc hx, run_bind_none hr, he⟩

end Refines

end NativeVm.Code
