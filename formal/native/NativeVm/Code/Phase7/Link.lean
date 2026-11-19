module

public import NativeVm.Code.Phase7.Adapt

/-!
# Chaining a level's pieces

The chains of `levelC` and `finalC` carry one memory fact `X` (with its `Dep`) in the shape
`Base ∧ X ∧ I`. `m0_step`: a transcript piece adding a memory fact `Y x` and a fact `R x` of its
result; `req_then`: a piece that fails exactly when a check does (`require`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model

variable {p : Par} {X X' : (UInt64 → Option UInt64) → Prop} {D : Nat → Prop}
/-- WHIR's state after the non-final levels `0 .. k - 1`: two glued claims a level, the levels'
folds as `α`s, every glued claim folding from at most the `α`s there are, every induced one over
at most `30` variables. -/
def WOk (L : List LeanVM.Parameters.Whir.Level) (k : Nat) (sW : WhirStateW) : Prop :=
  sW.glued.size = 2 * k ∧ sW.alphas.size = ((L.take k).map (·.fold)).sum ∧
    ∀ g ∈ sW.glued, g.foldStart ≤ sW.alphas.size ∧
      ∀ mu qs ws, g.weight = .induced mu qs ws → mu ≤ 30


/-- **A transcript piece adding `Y x`** (and `R x`, a fact of its result), then the rest. -/
theorem m0_step {α β : Type} {c : Stmt} {cs : List Stmt} {mc : VM α} {m₂ : α → VM β}
    {Q : β → TState → QState → Prop} {I : TState → Prop}
    {Y : α → (UInt64 → Option UInt64) → Prop} {R : α → Prop} {Wc : Nat → Prop}
    (hX : Dep p.env X D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd) (hDW : ∀ j, D j → ¬ Wc j)
    (hc : ∀ m0, Refines (fun t s ↦ Base p t s ∧ s.mem = m0 ∧ X s.mem ∧ I t) c mc
      (fun x t s ↦ Base p t s ∧ (Y x s.mem ∧ R x) ∧ Only p.env Wc m0 s.mem) (Err p))
    (h : ∀ x, R x → Refines (fun t s ↦ Base p t s ∧ (X s.mem ∧ Y x s.mem) ∧ True) (blk cs) (m₂ x)
      Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ I t) (blk (c :: cs)) (mc >>= m₂) Q (Err p) :=
  m0_then (X' := X) (Post := fun x _ s ↦ Y x s.mem ∧ R x) hX hD hDW (fun _ h ↦ h)
    (fun m0 ↦ (hc m0).mono (fun _ _ h ↦ h) (fun _ _ _ ⟨hb, hy, ho⟩ ↦ ⟨hb, hy, ho⟩) (fun _ h ↦ h))
    fun x t s ⟨hb, hx, hy, hr⟩ ↦ h x hr t s ⟨hb, ⟨hx, hy⟩, trivial⟩

/-- **A check**: a piece failing exactly when `b` is false, then the rest. -/
theorem req_then {β : Type} {c : Stmt} {cs : List Stmt} {b : Bool} {m : Unit → VM β}
    {Q : β → TState → QState → Prop} {I : TState → Prop} {R : QState → Prop} {Wc : Nat → Prop}
    (hX : Dep p.env X' D) (hD : ∀ j, D j → mineLo ≤ j ∧ j < dataEnd)
    (hDW : ∀ j, D j → ¬ Wc j) (hXX : ∀ m, X m → X' m)
    (hc : ∀ t s, Base p t s → X s.mem → I t →
      WP c s (fun s' ↦ b = true ∧ R s' ∧ FrM p.env s s' ∧ Only p.env Wc s.mem s'.mem)
        (fun s' ↦ b = false ∧ FrM p.env s s'))
    (h : Refines (fun t s ↦ Base p t s ∧ (X' s.mem ∧ R s) ∧ I t) (blk cs) (m ()) Q (Err p)) :
    Refines (fun t s ↦ Base p t s ∧ X s.mem ∧ I t) (blk (c :: cs)) (Model.require b >>= m) Q
      (Err p) := by
  refine Refines.blk_cons (Q₁ := fun _ t s ↦ Base p t s ∧ (X' s.mem ∧ R s) ∧ I t) ?_ fun x ↦ h
  refine Refines.require fun t s ⟨hb, hx, hi⟩ ↦ WP.mono (hc t s hb hx hi)
    (fun _ ⟨hb', hr, hf, ho⟩ ↦ ⟨hb', hb.frM hf, ⟨keepX hX hD hDW ho (hXX _ hx), hr⟩, hi⟩)
    fun _ ⟨hb', hf⟩ ↦ ⟨hb', hb.fr.trans hf.fr⟩

end NativeVm.Code.P7
