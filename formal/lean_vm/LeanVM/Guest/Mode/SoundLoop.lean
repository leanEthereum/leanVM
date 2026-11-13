module

public import LeanVM.Guest.Mode.SoundEntry

/-!
# Loops: termination facts and accumulated runs

A loop helper's signature states, at each iteration's entry, its counter's exponent below its
bound's (`Sig.term`), and, at its outermost return, the runs it writes over the counter's range
(`Sig.postL`).

`termStep_sound`: at a tail call the walk accepts, the next iteration's counter is this one's times
a positive power of `g`, its bound the same word. `term_holds`: the counters' exponents increasing,
the last one's naming the bound (the loop exits), every iteration's entry has its termination facts.

`loop_step`: at a tail call the walk accepts, the next iteration's run and this iteration's point
(written on every path, `loopOk`) give this iteration's run; `RW.last`, the exiting iteration's.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Termination -/

/-- **A tail call's counters**: the next iteration's counter is this one's times `g^t`, `t > 0`, its
bound the same word. -/
theorem termStep_sound {s sN : St} {A : Abs} {e : ℕ} {G : Sig} (hA : Holds s A)
    (F : Frames s sN (.own e)) (h : termStep A e G = true) :
    ∀ p ∈ G.term, ∃ a b t, p = (.ex a 0, .ex b 0) ∧ 0 < t ∧
      (∀ u, BaseVal sN a u ↔ ∃ u', BaseVal s a u' ∧ u = ofK (g ^ t) * u') ∧
      ∀ u, BaseVal sN b u ↔ BaseVal s b u := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  rcases p with ⟨_ | ⟨a, _ | _⟩, _ | ⟨b, _ | _⟩⟩ <;> try (simp at this; done)
  simp only [Bool.and_eq_true] at this
  obtain ⟨h1, h2⟩ := this
  split at h1
  · rename_i a' ha'
    split at h1
    · rename_i t ht
      obtain ⟨k, hk, -⟩ := idxUp_some ha'
      rcases trIdxK_ex hk with ⟨-, k', -, -, rfl⟩ | ⟨-, y, hb, rfl⟩
      · simp [Idx.off] at ht
      simp only [Idx.off, Bool.and_eq_true, decide_eq_true_eq] at ht
      split_ifs at ht with hc
      cases ht
      obtain rfl := Base.beq_eq hc.1
      simp only [decide_eq_true_eq] at h1
      split at h2
      · rename_i b' hb'
        obtain rfl := Idx.beq_eq h2
        obtain ⟨k2, hk2, -⟩ := idxUp_some hb'
        rcases trIdxK_ex hk2 with ⟨-, k', -, -, he⟩ | ⟨-, y2, hb2, he⟩
        · cases he
        · simp only [Idx.ex.injEq] at he
          obtain ⟨rfl, he⟩ := he
          obtain rfl : k2 = 0 := by omega
          refine ⟨a, b, k, rfl, by omega, fun u ↦ ?_, fun u ↦ ?_⟩
          · rw [trBase_iff F hA hb u, MonoVal.base1]
          · rw [trBase_iff F hA hb2 u, MonoVal.single]
      · cases h2
    · cases h1
  · cases h1

/-- The counters' exponents increasing, the last one's naming the bound: every earlier one is below
it. -/
theorem lt_of_exit {c : ℕ → ℕ} {J en : ℕ} (hinc : ∀ j < J, c j < c (j + 1)) (hJ : c J < 2 ^ 63)
    (hen : en < 2 ^ 62) (hexit : g ^ c J = g ^ en) : ∀ j < J, c j < en := by
  have heq : c J = en := gpow_inj hJ (by omega) hexit
  have key : ∀ d j, j + d ≤ J → c j + d ≤ c (j + d) := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hj
      have h1 := ih j (by omega)
      have h2 := hinc (j + d) (by omega)
      show c j + (d + 1) ≤ c (j + d + 1)
      omega
  intro j hj
  have := key (J - j) j (by omega)
  rw [show j + (J - j) = J by omega] at this
  omega

/-- **Termination gives the entry inequalities**: iterations `j < J`, iteration `j`'s counter the
word `g^(c j)` and its bound `g^en`, the counters increasing and the loop exiting when the counter
names the bound: each iteration's entry has its termination fact. -/
theorem term_holds {s : ℕ → St} {a b : Base} {c : ℕ → ℕ} {J en : ℕ}
    (hinc : ∀ j < J, c j < c (j + 1)) (hJ : c J < 2 ^ 63) (hen : en < 2 ^ 62)
    (hexit : g ^ c J = g ^ en) (ha : ∀ j < J, BaseVal (s j) a (ofK (g ^ c j)))
    (hb : ∀ j < J, BaseVal (s j) b (ofK (g ^ en))) : ∀ j < J, LTF (s j) (.ex a 0) (.ex b 0) := by
  intro j hj
  have hlt := lt_of_exit hinc hJ hen hexit j hj
  exact ⟨c j, en, ⟨_, c j, ha j hj, rfl, by omega, rfl⟩, ⟨_, en, hb j hj, rfl, hen, rfl⟩, hlt⟩

/-! ## Accumulated runs -/

/-- A run's point at its counter's start names its cell at the counter's exponent. -/
theorem Rng.first_val {s : St} {r : Rng} {y : ℕ} (hy : IdxVal s r.lo y) {vq : E}
    (hq : MonoVal s r.q vq) : MonoVal s r.first (vq * ofK (g ^ (r.S * y + r.d))) := by
  unfold Rng.first
  split
  · rename_i c hc
    rw [hc] at hy
    rw [show y = c from hy]
    exact hq.shift _
  · rename_i x c hc
    rw [hc] at hy
    obtain ⟨u, e, hu, rfl, -, rfl⟩ := hy
    have hx : MonoVal s ⟨0, 0, [(x, r.S)]⟩ (ofK (g ^ e) ^ r.S) :=
      ⟨_, ⟨_, 1, hu, rfl, rfl⟩, by simp⟩
    have := (hq.mul hx).shift (r.S * c + r.d)
    rw [show r.S * (e + c) + r.d = e * r.S + (r.S * c + r.d) by ring, pow_add, ofK_mul, pow_mul,
      ofK_pow]
    rw [← mul_assoc]
    exact this

theorem Rng.first_q {s : St} {r : Rng} {v : E} (h : MonoVal s r.first v) : ∃ vq, MonoVal s r.q vq := by
  unfold Rng.first at h
  split at h
  · obtain ⟨u, hu, -⟩ := h.unshift
    exact ⟨u, hu⟩
  · obtain ⟨u, hu, -⟩ := h.unshift
    obtain ⟨va, -, ha, -, -⟩ := MonoVal.mul_inv hu
    exact ⟨va, ha⟩

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

/-- **A loop's accumulated run, one iteration**: at a tail call the walk accepts (`tailOk_sound`),
the next iteration's run (its frame `fp·g^e`) and this iteration's point give this iteration's run. -/
theorem loop_step {s sN : St} {A : Abs} {e : ℕ} (hA : Holds s A) (F : Frames s sN (.own e))
    {r : Rng} (hst : trRngUp A (.own e) r = some ⟨r.q, r.lo.succ, r.hi, r.S, r.d⟩) (hn : RW sN r)
    (hp : HW s r.first) : RW s r :=
  RW.cons (RW.trUp F hA hst hn) hp

end

end LeanVM.Guest.Mode
