import Rv64Verifier.Model.Whir

/-!
# Mirrors that keep the proof, the roots and the opening offset

The transcript's methods but `commit` and `merkle` change only the sponge and the stream offset:
`Keeps m` says so of `m`, so a level loop's invariant can carry the proof and the roots across them.
-/

namespace Rv64Verifier.Model.Pcs
open LeanVM.Parameters LeanVM.Protocol

/-- `m` keeps the proof, the roots and the opening offset. -/
def Keeps {α : Type} (m : TM α) : Prop :=
  ∀ t a t', m.run t = some (a, t') →
    t'.proof = t.proof ∧ t'.roots = t.roots ∧ t'.openingOffset = t.openingOffset

theorem Keeps.pure {α : Type} (a : α) : Keeps (Pure.pure a : TM α) := by
  intro t b t' h
  cases (Option.some.inj h : ((a, t) : α × TState) = (b, t'))
  exact ⟨rfl, rfl, rfl⟩

theorem Keeps.bind {α β : Type} {m : TM α} {k : α → TM β} (hm : Keeps m)
    (hk : ∀ a, Keeps (k a)) : Keeps (m >>= k) := by
  intro t b t' h
  rw [StateT.run_bind] at h
  cases hmt : m.run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨a, t₁⟩ := p
    rw [hmt] at h
    obtain ⟨e1, e2, e3⟩ := hm t a t₁ hmt
    obtain ⟨f1, f2, f3⟩ := hk a t₁ b t' h
    exact ⟨f1.trans e1, f2.trans e2, f3.trans e3⟩

theorem Keeps.nextScalar : Keeps TM.nextScalar := by
  intro t a t' h
  simp only [StateT.run, TM.nextScalar] at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem Keeps.sample : Keeps TM.sample := by
  intro t a t' h
  simp only [StateT.run, TM.sample] at h
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem Keeps.nextScalars : ∀ n, Keeps (TM.nextScalars n)
  | 0 => Keeps.pure _
  | n + 1 => Keeps.bind Keeps.nextScalar fun _ ↦ Keeps.bind (Keeps.nextScalars n) fun _ ↦
      Keeps.pure _

theorem nextScalars_len : ∀ (n : ℕ) (t : TState) (xs : List E) (t' : TState),
    (TM.nextScalars n).run t = some (xs, t') → xs.length = n
  | 0, t, xs, t', h => by
    cases (Option.some.inj h : (([] : List E), t) = (xs, t'))
    rfl
  | n + 1, t, xs, t', h => by
    simp only [TM.nextScalars] at h
    rw [StateT.run_bind] at h
    cases h1 : TM.nextScalar.run t with
    | none => rw [h1] at h; cases h
    | some p =>
      obtain ⟨x, t1⟩ := p
      rw [h1] at h
      change (TM.nextScalars n >>= fun ys ↦ (Pure.pure (x :: ys) : TM (List E))).run t1 =
        some (xs, t') at h
      rw [StateT.run_bind] at h
      cases h2 : (TM.nextScalars n).run t1 with
      | none => rw [h2] at h; cases h
      | some p2 =>
        obtain ⟨ys, t2⟩ := p2
        rw [h2] at h
        cases (Option.some.inj h : ((x :: ys), t2) = (xs, t'))
        simp [nextScalars_len n t1 ys _ h2]

theorem Keeps.samples : ∀ n, Keeps (TM.samples n)
  | 0 => Keeps.pure _
  | n + 1 => Keeps.bind Keeps.sample fun _ ↦ Keeps.bind (Keeps.samples n) fun _ ↦ Keeps.pure _

theorem Keeps.roundPoly (count : ℕ) (claim : E) (e : Option E) :
    Keeps (TM.sumcheckRoundPoly count claim e) := by
  cases e with
  | none => exact Keeps.bind Keeps.nextScalar fun _ ↦ Keeps.bind (Keeps.nextScalars _) fun _ ↦
      Keeps.pure _
  | some f => exact Keeps.bind (Keeps.nextScalars _) fun _ ↦ Keeps.pure _

theorem Keeps.grind (bits : ℕ) : Keeps (TM.grind bits) := by
  intro t a t' h
  simp only [StateT.run, TM.grind] at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · cases h

theorem Keeps.foldRound (st : WhirLocals × List E) : Keeps (foldRoundRust st) :=
  Keeps.bind Keeps.sample fun _ ↦ Keeps.bind (Keeps.roundPoly _ _ _) fun _ ↦ Keeps.pure _

theorem Keeps.loopN {σ : Type} {f : σ → TM σ} (hf : ∀ x, Keeps (f x)) :
    ∀ n x, Keeps (TM.loopN f n x)
  | 0, _ => Keeps.pure _
  | n + 1, x => Keeps.bind (hf x) fun y ↦ Keeps.loopN hf n y

end Rv64Verifier.Model.Pcs
