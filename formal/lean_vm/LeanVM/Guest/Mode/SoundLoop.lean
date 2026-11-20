module

public import LeanVM.Guest.Mode.SoundEntry

/-!
# Accumulated runs

A loop helper's signature states, at its outermost return, the runs it writes over its counter's range
(`Sig.postL`): `RW.cons`, `RW.last`, `PW.cons`, `PW.last` build them iteration by iteration, and
`loop_step` gives an iteration's run from the next one's and its own point.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Accumulated runs -/

/-- An empty run. -/
theorem RW.nil {s : St} {r : Rng} {vq : E} {y z : ℕ} (hq : MonoVal s r.q vq) (hy : IdxVal s r.lo y)
    (hz : IdxVal s r.hi z) (hle : z ≤ y) : RW s r :=
  ⟨vq, y, z, hq, hy, hz, fun _ h1 h2 ↦ absurd (lt_of_le_of_lt h1 h2) (by omega)⟩

/-- A run from one further, and the point at its start. -/
theorem RW.cons {s : St} {r : Rng} (hn : RW s ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩) (hp : HW s r.first) :
    RW s r := by
  obtain ⟨vq, x1, xhi, h1, h2, h3, h4⟩ := hn
  obtain ⟨y, hy, rfl⟩ := Idx.succ_val h2
  refine ⟨vq, y, xhi, h1, hy, h3, fun j hj1 hj2 ↦ ?_⟩
  rcases Nat.eq_or_lt_of_le hj1 with rfl | hj1
  · obtain ⟨v, x, hv, hx, hw⟩ := hp
    rw [hv.unique (Rng.first_val hy h1)] at hx
    exact ⟨x, hx, hw⟩
  · exact h4 j hj1 hj2

/-- **The exiting iteration's run**: its point, the bound one past the counter. -/
theorem RW.last {s : St} {r : Rng} {y : ℕ} (hy : IdxVal s r.lo y) (hz : IdxVal s r.hi (y + 1))
    (hp : HW s r.first) : RW s r := by
  obtain ⟨v, -, hv, -⟩ := id hp
  obtain ⟨vq, hq⟩ := Rng.first_q hv
  exact RW.cons (RW.nil hq (Idx.succ_val' hy) hz le_rfl) hp

theorem PW.nil {s : St} {r : Rng} {os : List ℕ} {vq : E} {y z : ℕ} (hq : MonoVal s r.q vq)
    (hy : IdxVal s r.lo y) (hz : IdxVal s r.hi z) (hle : z ≤ y) : PW s r os :=
  ⟨vq, y, z, hq, hy, hz, fun _ h1 h2 ↦ absurd (lt_of_le_of_lt h1 h2) (by omega)⟩

/-- A run of pointers from one further, and the pointer at its start. -/
theorem PW.cons {s : St} {r : Rng} {os : List ℕ} (hn : PW s ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩ os)
    (hp : HP s r.first os) : PW s r os := by
  obtain ⟨vq, x1, xhi, h1, h2, h3, h4⟩ := hn
  obtain ⟨y, hy, rfl⟩ := Idx.succ_val h2
  refine ⟨vq, y, xhi, h1, hy, h3, fun j hj1 hj2 ↦ ?_⟩
  rcases Nat.eq_or_lt_of_le hj1 with rfl | hj1
  · obtain ⟨v, x, hv, hx, hw⟩ := hp
    rw [hv.unique (Rng.first_val hy h1)] at hx
    exact ⟨x, hx, hw⟩
  · exact h4 j hj1 hj2

/-- **The exiting iteration's run of pointers.** -/
theorem PW.last {s : St} {r : Rng} {os : List ℕ} {y : ℕ} (hy : IdxVal s r.lo y)
    (hz : IdxVal s r.hi (y + 1)) (hp : HP s r.first os) : PW s r os := by
  obtain ⟨v, -, hv, -⟩ := id hp
  obtain ⟨vq, hq⟩ := Rng.first_q hv
  exact PW.cons (PW.nil hq (Idx.succ_val' hy) hz le_rfl) hp

/-- **A loop's accumulated run, one iteration**: at a tail call the walk accepts,
the next iteration's run (its frame `fp·g^e`) and this iteration's point give this iteration's run. -/
theorem loop_step {s sN : St} {A : Abs} {e : ℕ} (hA : Holds s A) (F : Frames s sN (.own e))
    {r : Rng} (hst : trRngUp A (.own e) r = some ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩) (hn : RW sN r)
    (hp : HW s r.first) : RW s r :=
  RW.cons (RW.trUp F hA hst hn) hp

end

end LeanVM.Guest.Mode
