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

section Atoms

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

theorem FAt.and_wp {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    {Q : α → St → Prop} (h : FAt ctx I C st m R) (hw : wpP m ctx st Q) :
    FAt ctx I C st m (fun a C' st' => R a C' st' ∧ Q a st') := fun hc a st' he => by
  obtain ⟨C', h1, h2, h3, h4, h5, h6⟩ := h hc a st' he
  exact ⟨C', h1, h2, h3, h4, h5, h6, hw a st' he⟩

theorem isLazy_fat (v : V) (k : Kind) :
    FAt ctx I C st (isLazy v k) (fun _ C' st' => C' = C ∧ st' = st) := by
  unfold isLazy
  exact FAt.get_bind (FAt.pure ⟨rfl, rfl⟩)

/-- The atom's values known before are known after. -/
theorem vw_same {ok : V → Prop} {L : List V} {C' : (ℕ → E) → Prop} {st' : St}
    (hv : VW I C st ok) (hL : ∀ v ∈ L, ok v) (hs : Stronger C' C) (hn : st.next ≤ st'.next)
    (hl : st'.locs = st.locs) : VW I C' st' (fun v => ok v ∨ v ∈ L) :=
  (hv.anti fun v h => h.elim id (hL v)).step hs hn hl

/-- A value placed by the atom, with its word. -/
theorem vw_bind {ok : V → Prop} {L : List V} {C' : (ℕ → E) → Prop} {st' : St} {d : V} {l : Loc}
    (hv : VW I C st ok) (hL : ∀ v ∈ L, v ≠ d → ok v) (hs : Stronger C' C)
    (hn : st.next ≤ st'.next) (hl : st'.locs = st.locs.insert d l) (hd0 : st.locs[d]? = none)
    (hw : 2 ≤ locBase l ∧ locBase l < st'.next ∧ ∀ Ψ, C' Ψ → locW Ψ l = I.σ d) :
    VW I C' st' (fun v => ok v ∨ v ∈ L) := by
  refine hv.grow hs hn (fun v x hx => ?_) (fun v l' h hl' => ?_) (fun v l' _ hl' h0 => ?_)
  · rw [hl, KMap.getElem?_insert]
    split
    · next he =>
      subst he
      rw [hd0] at hx
      cases hx
    · exact hx
  · rcases h with h | h
    · exact h
    · by_cases hvd : v = d
      · subst hvd
        rw [hd0] at hl'
        cases hl'
      · exact hL v h hvd
  · rw [hl, KMap.getElem?_insert] at hl'
    split at hl'
    · next he =>
      subst he
      cases hl'
      exact hw
    · rw [h0] at hl'
      cases hl'

theorem pooledCell_alias {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} :
    wpP (pooledCell find learn mk) ctx st fun _ st' => st'.aliasRun = st.aliasRun := by
  unfold pooledCell fresh emitOp takeHints push
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_pure.mpr rfl
  · simp only [wp_bind, wp_modifyGet, wp_modify, wp_pure]

theorem materialize_alias (c e : Cell) :
    wpP (materialize c e) ctx st fun _ st' => st'.aliasRun = st.aliasRun := by
  unfold materialize
  dsimp only
  split
  · exact wp_pure.mpr rfl
  · split
    · exact wp_bind.mpr wp_failP
    · refine wp_bind.mpr (wp_get.mpr ?_)
      split
      · exact wp_pure.mpr rfl
      · generalize matStart _ _ _ _ = pr
        obtain ⟨src, dist⟩ := pr
        dsimp only
        simp only [constCell_eq, mulCell_eq]
        exact wp_bind.mpr (wp_mono pooledCell_alias fun _ st₁ h₁ => wp_bind.mpr
          (wp_mono pooledCell_alias fun _ st₂ h₂ => wp_bind.mpr (wp_modify.mpr
            (wp_pure.mpr (h₂.trans h₁)))))

theorem cellOf_alias (v : V) :
    wpP (cellOf v) ctx st fun _ st' => st'.aliasRun = st.aliasRun := by
  unfold cellOf
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_pure.mpr rfl
  · exact materialize_alias _ _
  · exact wp_failP

/-- The values of an atom, known (a copy into a message run read in place apart). -/
theorem atom_ok {a : Atom} {ok : V → Prop}
    (hops : ∀ v ∈ Memory.atomUses a ++ Memory.atomTmps a, ok v ∨
      ∃ s, a = .copy v s ∧ st.aliasRun.any (·.contains v) = true)
    (hnc : ∀ v s, a ≠ .copy v s) : ∀ v ∈ Memory.atomUses a ++ Memory.atomTmps a, ok v :=
  fun v hv => (hops v hv).resolve_right fun ⟨s, h, _⟩ => hnc v s h

/-- **`SET` of a constant**: a pooled constant's cell, or the value's cell holding it. -/
theorem place_const_fat (d : V) (c : E) : AtomFAt (.const d c) := by
  intro ctx I C st ok hok _ _ hh _ _ _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hev : I.σ d = c := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  have hkd : ok d := hL d (by simp [Memory.atomUses])
  have hwk : Guest.word (limbsOf c).1 (limbsOf c).2 = I.σ d := by rw [word_limbsOf, hev]
  unfold placeAtom
  dsimp only
  refine FAt.bind (FAt.modify rfl rfl rfl id) fun _ st₁ C₁ _ _ _ ⟨hC₁, hst₁⟩ => ?_
  subst C₁ st₁
  refine FAt.bind (isLazy_fat d .pooled) fun z st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => ?_
  subst C₃ st₃
  split
  · unfold pooled
    refine FAt.bind (constCell_eq (limbsOf c) ▸ constCell_fatB (st := { st with
        constOf := st.constOf.insert d (limbsOf c) }) (limbsOf c) (hok.kconst _ _) h2)
      fun o st₄ C₄ hs₄ hn₄ _ ⟨o2, o1, hlo₄, hr₄, how, _⟩ => ?_
    have hv₄ : VW I C₄ st₄ ok := hv.step hs₄ hn₄ hlo₄
    refine FAt.mono (bindTo_fat d (.cell o)) fun _ C' st' _ _ _ ⟨hC, hst, hd0⟩ => ?_
    subst C' st'
    exact ⟨fun _ => vw_bind hv₄ (fun v hv' _ => hL v hv') (Stronger.refl _) le_rfl rfl hd0
      ⟨o2, o1, fun Ψ hΨ => (how Ψ hΨ).trans hwk⟩, hr₄⟩
  · refine FAt.bind (cellAt_fat d) fun ld st₄ C₄ _ _ _ ⟨hC₄, hst₄, hld⟩ => ?_
    subst C₄ st₄
    obtain ⟨d2, d1, hwd⟩ := hv d _ hkd hld
    refine FAt.bind (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ st₅ C₅ _ _ _ ⟨hC₅, hst₅⟩ => ?_
    · show fw I Ψ ld = I.kw (.const (limbsOf c).1 (limbsOf c).2)
      rw [hok.kconst, fw_of_two (n := ld) d2, hwk]
      exact hwd Ψ hΨ
    subst C₅ st₅
    refine FAt.get_bind ?_
    split
    · refine FAt.mono (FAt.modify rfl rfl rfl fun hc => hc.withScope
        (fun Ψ hΨ hp => hp.insertConstIfNew ((show Ψ ld = I.σ d from hwd Ψ hΨ).trans hwk.symm))
        fun hs => { hs with consts := pmap_insertIfNew_imp hs.consts ⟨d2, d1⟩ })
        fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
      subst C' st'
      exact ⟨fun _ => vw_same hv hL (Stronger.refl _) le_rfl rfl, rfl⟩
    · exact FAt.pure ⟨fun _ => vw_same hv hL (Stronger.refl _) le_rfl rfl, rfl⟩

end Atoms

end
end LeanVM.Guest.Backend.Complete
