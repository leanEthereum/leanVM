/-
  LeanVM.Guest.Backend.Complete.FrameAtoms

  The atoms on a path: every instruction an atom's placement emits holds on the frame words, and
  the atom's values get their words (`AtomFAt`).
-/

module

public import LeanVM.Guest.Backend.Complete.FramePrims

/-!
# The atoms on the path

An atom's placement reads its operands' cells (`cellOf`, `cellAt`, `factor`, `pointer`), whose
words are the valuation's by `VW`, and emits instructions whose relation on those words is the
atom's event: a written cell, a check against a cell already written, or a back-solved one are all
the same relation on the words, which every value's cell holds from its run on. A pooled result
is placed in a cell holding its word, read from the pool or fresh.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Operands

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

theorem VW.step {ok : V → Prop} {C' : (ℕ → E) → Prop} {st' : St} (h : VW I C st ok)
    (hs : Stronger C' C) (hn : st.next ≤ st'.next) (hl : st'.locs = st.locs) : VW I C' st' ok :=
  h.grow hs hn (by rw [hl]; exact LocsLe.refl _) (fun _ _ h _ => h)
    fun v l _ hl' h0 => by rw [hl, h0] at hl'; cases hl'

/-- **An operand's cell** holds its word. -/
theorem cellOf_fat (v : V) {ok : V → Prop} (hok : I.Ok) (hv : VW I C st ok) (hkv : ok v) :
    FAt ctx I C st (cellOf v) (fun c C' st' => 2 ≤ c ∧ c < st'.next ∧ st'.locs = st.locs ∧
      st'.rest = st.rest ∧ ∀ Ψ, C' Ψ → Ψ c = I.σ v) := by
  unfold cellOf
  refine FAt.get_bind ?_
  split
  · next n hn =>
    obtain ⟨a, b, c⟩ := hv v _ hkv hn
    exact FAt.pure ⟨a, b, rfl, rfl, c⟩
  · next n e hn =>
    obtain ⟨a, b, c⟩ := hv v _ hkv hn
    exact FAt.mono (materialize_fat n e hok a b) fun _ C' st' hs _ _ ⟨h1, h2, h3, h4, h5, _⟩ =>
      ⟨h1, h2, h3, h4, fun Ψ hΨ => (h5 Ψ hΨ).trans (c Ψ (hs Ψ hΨ))⟩
  · exact FAt.fail

/-- **A value's cell**, as it is: the value placed in a cell. -/
theorem cellAt_fat (v : V) :
    FAt ctx I C st (cellAt v) (fun c C' st' => C' = C ∧ st' = st ∧
      st.locs[v]? = some (.cell c)) := by
  unfold cellAt
  refine FAt.get_bind ?_
  split
  · next n hn => exact FAt.pure ⟨rfl, rfl, hn⟩
  · exact FAt.fail

/-- **A factor**: a cell and the shift still to apply, whose product is the value's word. -/
theorem factor_fat (v : V) {ok : V → Prop} (hok : I.Ok) (hv : VW I C st ok) (hkv : ok v) :
    FAt ctx I C st (factor v) (fun r C' st' => 2 ≤ r.1 ∧ r.1 < st'.next ∧ st'.locs = st.locs ∧
      st'.rest = st.rest ∧ ∀ Ψ, C' Ψ → Ψ r.1 * ofK (addressOfIndex r.2) = I.σ v) := by
  unfold factor
  refine FAt.get_bind ?_
  split
  · next n e hn =>
    obtain ⟨a, b, c⟩ := hv v _ hkv hn
    split
    · exact FAt.bind (materialize_fat n e hok a b) fun o st₁ C₁ hs _ _ ⟨h1, h2, h3, h4, h5, _⟩ =>
        FAt.pure ⟨h1, h2, h3, h4, fun Ψ hΨ => by
          rw [ofK_gpow_zero, mul_one, h5 Ψ hΨ]
          exact c Ψ (hs Ψ hΨ)⟩
    · exact FAt.pure ⟨a, b, rfl, rfl, c⟩
  · exact FAt.bind (cellOf_fat v hok hv hkv) fun o st₁ C₁ _ _ _ ⟨h1, h2, h3, h4, h5⟩ =>
      FAt.pure ⟨h1, h2, h3, h4, fun Ψ hΨ => by rw [ofK_gpow_zero, mul_one, h5 Ψ hΨ]⟩

/-- **A `DEREF`'s pointer**: a cell and an immediate `e + off`, the cell's word times `g^e` the
pointer's word. -/
theorem pointer_fat (p : V) (off : ℕ) {ok : V → Prop} (hok : I.Ok) (hv : VW I C st ok)
    (hkp : ok p) :
    FAt ctx I C st (pointer p off) (fun r C' st' => 2 ≤ r.1 ∧ r.1 < st'.next ∧
      st'.locs = st.locs ∧ st'.rest = st.rest ∧ ∃ e, r.2 = e + off ∧
        ∀ Ψ, C' Ψ → Ψ r.1 * ofK (addressOfIndex e) = I.σ p) := by
  unfold pointer
  refine FAt.bind (factor_fat p hok hv hkp) fun r st₁ C₁ _ _ _ ⟨h1, h2, h3, h4, h5⟩ => ?_
  obtain ⟨c, e⟩ := r
  dsimp only
  exact FAt.guard fun _ => FAt.pure ⟨h1, h2, h3, h4, e, rfl, h5⟩

/-! ## Words in `K` -/

theorem isInK_of_mul_ofK {x : E} {y : K} (h : IsInK (x * ofK y)) (hy : y ≠ 0) : IsInK x := by
  obtain ⟨z, hz⟩ := (isInK_iff _).mp h
  have hy' : ofK y ≠ 0 := by
    intro h0
    have h1 : (algebraMap K E) y = 0 := h0
    exact hy ((map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective).mp h1)
  refine (isInK_iff _).mpr ⟨z * y⁻¹, mul_right_cancel₀ hy' ?_⟩
  rw [hz, ← ofK_mul, mul_assoc, inv_mul_cancel₀ hy, mul_one]

theorem addressOfIndex_ne_zero (e : ℕ) : addressOfIndex e ≠ 0 := by
  rw [addressOfIndex]
  exact pow_ne_zero _ (by decide)

/-- A load through `x · g^e` at `off` is a load through `x` at `e + off`. -/
theorem load_shift {x : E} {e off : ℕ} {rd : Reader} {d : E}
    (h : LoadHolds rd (x * ofK (addressOfIndex e)) off d) :
    IsInK x ∧ rd (x.limb 0 * addressOfIndex (e + off)) = some d := by
  have hx := isInK_of_mul_ofK h.1 (addressOfIndex_ne_zero e)
  refine ⟨hx, ?_⟩
  have := h.2
  rw [limb_mul_ofK hx, mul_assoc, addressOfIndex, addressOfIndex, ← pow_add] at this
  rw [addressOfIndex]
  exact this

end Operands

end
end LeanVM.Guest.Backend.Complete
