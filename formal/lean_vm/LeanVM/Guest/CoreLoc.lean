/-
  LeanVM.Guest.CoreLoc

  The located call relation of the core IR: a callee runs at a frame, and its values are the ones
  that frame gives.
-/

module

public import LeanVM.Guest.CoreLemmas

/-!
# The located call relation

`Program.Rel` relates a callee's argument and return words when *some* valuation of its values
satisfies its body. The located relation `Program.RelL rd vf A` asks instead for the valuation
`vf f fp` of a frame `fp` with `A f fp args rets`. That is what the walk of the guest's run gives
(`Check.frameVal`: each value is the word of its certificate cell), so whatever a proof reads off
a callee's valuation is a function of the memory and of the callee's frame.

* `relL_le_rel`: the located relation implies the relation;
* `relL_iff`: it is a fixed point, a call holding exactly when the callee's body does at some
  frame, its own calls located.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The located call relation of depth `n`: calls nested at most `n` deep, each callee `f` on the
words `args`, `rets` at a frame `fp` with `A f fp args rets` under the valuation `vf f fp`. -/
def Program.locN (P : Program) (rd : Reader) (vf : String → K → Val) (A : String → K → List E → List E → Prop) :
    Nat → CallRel
  | 0 => fun _ _ _ => False
  | n + 1 => fun f args rets => ∃ fn fp, P.find? f = some fn ∧ A f fp args rets ∧
      fn.params.map (vf f fp) = args ∧
      Stmt.HoldsList (P.locN rd vf A n) rd (vf f fp) fn.body False (fun rs => rs = rets)

/-- **The located call relation**: every finite depth. -/
def Program.RelL (P : Program) (rd : Reader) (vf : String → K → Val) (A : String → K → List E → List E → Prop) : CallRel :=
  fun f args rets => ∃ n, P.locN rd vf A n f args rets

variable {vf : String → K → Val} {A : String → K → List E → List E → Prop}

theorem locN_succ (P : Program) : ∀ n, CallRel.Le (P.locN rd vf A n) (P.locN rd vf A (n + 1))
  | 0 => fun _ _ _ h => h.elim
  | n + 1 => fun _ _ _ ⟨fn, fp, hf, hA, hp, h⟩ =>
      ⟨fn, fp, hf, hA, hp, holdsList_mono (locN_succ P n) fn.body id (fun _ h => h) h⟩

theorem locN_mono (P : Program) {m n : Nat} (h : m ≤ n) :
    CallRel.Le (P.locN rd vf A m) (P.locN rd vf A n) := by
  induction h with
  | refl => exact fun _ _ _ h => h
  | step _ ih => exact fun f a r h => locN_succ P _ f a r (ih f a r h)

theorem locN_le_relL (P : Program) (n : Nat) : CallRel.Le (P.locN rd vf A n) (P.RelL rd vf A) :=
  fun _ _ _ h => ⟨n, h⟩

theorem locN_le_relN (P : Program) : ∀ n, CallRel.Le (P.locN rd vf A n) (P.relN rd n)
  | 0 => fun _ _ _ h => h
  | n + 1 => fun f _ _ ⟨fn, fp, hf, _, hp, h⟩ =>
      ⟨fn, hf, vf f fp, hp, holdsList_mono (locN_le_relN P n) fn.body id (fun _ h => h) h⟩

/-- The located relation implies the relation. -/
theorem relL_le_rel (P : Program) : CallRel.Le (P.RelL rd vf A) (P.Rel rd) :=
  fun _ _ _ ⟨n, h⟩ => ⟨n, locN_le_relN P n _ _ _ h⟩

/-! ## The fixed point -/

/-- A family of continuations, monotone in the call relation and reached at a finite depth of
the located relation. -/
structure FinitaryL (P : Program) (rd : Reader) (vf : String → K → Val) (A : String → K → List E → List E → Prop)
    (F : CallRel → Prop) : Prop where
  mono : ∀ C C', CallRel.Le C C' → F C → F C'
  finite : F (P.RelL rd vf A) → ∃ n, F (P.locN rd vf A n)

mutual
theorem holds_finiteL (P : Program) :
    ∀ (s : Stmt) (F : CallRel → Prop) (kret : List E → Prop), FinitaryL P rd vf A F →
      Stmt.Holds (P.RelL rd vf A) rd σ s (F (P.RelL rd vf A)) kret →
        ∃ n, Stmt.Holds (P.locN rd vf A n) rd σ s (F (P.locN rd vf A n)) kret
  | .atom _, F, _, hF, h => (hF.finite h.2).imp fun _ hn => ⟨h.1, hn⟩
  | .ite c z n', F, kret, hF, h => by
      by_cases hc : σ c = 0
      · obtain ⟨n, hn⟩ := holdsList_finiteL P z F kret hF (h.2.1 hc)
        exact ⟨n, h.1, fun _ => hn, fun hc' => absurd hc hc'⟩
      · obtain ⟨n, hn⟩ := holdsList_finiteL P n' F kret hF (h.2.2 hc)
        exact ⟨n, h.1, fun hc' => absurd hc' hc, fun _ => hn⟩
  | .match_ x arms, F, kret, hF, h => holdsArms_finiteL P x arms 0 F kret hF h
  | .call f args rets, F, _, hF, h => by
      obtain ⟨n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, locN_mono P (le_max_left _ _) _ _ _ h1,
        hF.mono _ _ (locN_mono P (le_max_right _ _)) h2⟩
  | .callIf c f args, F, _, hF, h => by
      obtain ⟨n2, h2⟩ := hF.finite h.2.2
      by_cases hc : σ c ≠ 0
      · obtain ⟨n1, h1⟩ := h.2.1 hc
        exact ⟨max n1 n2, h.1, fun _ => locN_mono P (le_max_left _ _) _ _ _ h1,
          hF.mono _ _ (locN_mono P (le_max_right _ _)) h2⟩
      · exact ⟨n2, h.1, fun hc' => absurd hc' hc, h2⟩
  | .dispatch x fs args rets, F, _, hF, h => by
      obtain ⟨j, hj, hx, n1, h1⟩ := h.1
      obtain ⟨n2, h2⟩ := hF.finite h.2
      exact ⟨max n1 n2, ⟨j, hj, hx, locN_mono P (le_max_left _ _) _ _ _ h1⟩,
        hF.mono _ _ (locN_mono P (le_max_right _ _)) h2⟩
  | .ret _, _, _, _, h => ⟨0, h⟩

theorem holdsList_finiteL (P : Program) :
    ∀ (ss : List Stmt) (F : CallRel → Prop) (kret : List E → Prop), FinitaryL P rd vf A F →
      Stmt.HoldsList (P.RelL rd vf A) rd σ ss (F (P.RelL rd vf A)) kret →
        ∃ n, Stmt.HoldsList (P.locN rd vf A n) rd σ ss (F (P.locN rd vf A n)) kret
  | [], _, _, hF, h => hF.finite h
  | s :: ss, F, kret, hF, h =>
      holds_finiteL P s (fun C => Stmt.HoldsList C rd σ ss (F C) kret) kret
        ⟨fun C C' hC h => holdsList_mono hC ss (hF.mono C C' hC) (fun _ h => h) h,
          holdsList_finiteL P ss F kret hF⟩ h

theorem holdsArms_finiteL (P : Program) (x : V) :
    ∀ (arms : List (List Stmt)) (j : Nat) (F : CallRel → Prop) (kret : List E → Prop),
      FinitaryL P rd vf A F → Stmt.HoldsArms (P.RelL rd vf A) rd σ x j arms (F (P.RelL rd vf A)) kret →
        ∃ n, Stmt.HoldsArms (P.locN rd vf A n) rd σ x j arms (F (P.locN rd vf A n)) kret
  | [], _, _, _, _, h => h.elim
  | a :: as, j, F, kret, hF, h => by
      rcases h with ⟨hx, ha⟩ | ha
      · exact (holdsList_finiteL P a F kret hF ha).imp fun _ hn => Or.inl ⟨hx, hn⟩
      · exact (holdsArms_finiteL P x as (j + 1) F kret hF ha).imp fun _ hn => Or.inr hn
end

/-- **`Program.RelL` is a fixed point**: a call holds exactly when the callee's body does at some
frame `fp` with `A f fp args rets`, under that frame's valuation, its own calls located. -/
theorem relL_iff (P : Program) (f : String) (args rets : List E) :
    P.RelL rd vf A f args rets ↔ ∃ fn fp, P.find? f = some fn ∧ A f fp args rets ∧
      fn.params.map (vf f fp) = args ∧
      Stmt.HoldsList (P.RelL rd vf A) rd (vf f fp) fn.body False (fun rs => rs = rets) := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact hn.elim
    | succ n =>
        obtain ⟨fn, fp, hf, hA, hp, h⟩ := hn
        exact ⟨fn, fp, hf, hA, hp, holdsList_mono (locN_le_relL P n) fn.body id (fun _ h => h) h⟩
  · rintro ⟨fn, fp, hf, hA, hp, h⟩
    obtain ⟨n, hn⟩ := holdsList_finiteL (σ := vf f fp) P fn.body (fun _ => False)
      (fun rs => rs = rets) ⟨fun _ _ _ h => h, fun h => h.elim⟩ h
    exact ⟨n + 1, fn, fp, hf, hA, hp, hn⟩

end
end LeanVM.Guest.Core
