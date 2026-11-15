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

/-- **`XOR`**: a pooled sum's cell, or the value's cell holding the sum. -/
theorem place_add_fat (d a b : V) : AtomFAt (.add d a b) := by
  intro ctx I C st ok hok _ _ hh _ _ _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hev : I.σ d = I.σ a + I.σ b := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  unfold placeAtom
  dsimp only
  refine FAt.bind (cellOf_fat a hok hv (hL a (by simp [Memory.atomUses])))
    fun la st₁ C₁ hs₁ hn₁ _ ⟨la2, la1, hlo₁, hr₁, hwa⟩ => ?_
  have hv₁ := hv.step hs₁ hn₁ hlo₁
  refine FAt.bind (cellOf_fat b hok hv₁ (hL b (by simp [Memory.atomUses])))
    fun lb st₂ C₂ hs₂ hn₂ _ ⟨lb2, lb1, hlo₂, hr₂, hwb⟩ => ?_
  have hv₂ := hv₁.step hs₂ hn₂ hlo₂
  have hwa₂ : ∀ Ψ, C₂ Ψ → Ψ la = I.σ a := fun Ψ hΨ => hwa Ψ (hs₂ Ψ hΨ)
  have h2' : 2 ≤ st₂.next := le_trans h2 (le_trans hn₁ hn₂)
  refine FAt.bind (isLazy_fat d .pooled) fun z st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => ?_
  subst C₃ st₃
  split
  · unfold pooled
    refine FAt.bind (pooledCell_fat (fun _ => True) (fun Ψ => Ψ la + Ψ lb)
      (wblind_add (wblind_cell (lt_of_lt_of_le la1 hn₂)) (wblind_cell lb1)) h2'
      (fun o ho Ψ _ hp _ => by rw [hp.xors _ o ho, add_sorted]) (fun o ho hs => hs.xors _ o ho)
      (fun _ _ Ψ _ h => ?_) (fun Ψ _ h hp => hp.insertXor (by rw [h, add_sorted]))
      (fun hs => { hs with xors := pmap_insert_imp hs.xors ⟨h2', Nat.lt_succ_self _⟩ }))
      fun o st₄ C₄ hs₄ hn₄ _ ⟨o2, o1, hlo₄, hr₄, how, _⟩ => ?_
    · show fw I Ψ st₂.next = fw I Ψ la + fw I Ψ lb
      rw [fw_of_two la2, fw_of_two lb2, fw_of_two h2', h]
    have hv₄ := hv₂.step hs₄ hn₄ hlo₄
    refine FAt.mono (bindTo_fat d (.cell o)) fun _ C' st' _ _ _ ⟨hC, hst, hd0⟩ => ?_
    subst C' st'
    exact ⟨fun _ => vw_bind hv₄ (fun v hv' _ => hL v hv') (Stronger.refl _) le_rfl rfl hd0
      ⟨o2, o1, fun Ψ hΨ => by
        show Ψ o = I.σ d
        rw [how Ψ hΨ trivial, hwa₂ Ψ (hs₄ Ψ hΨ), hwb Ψ (hs₄ Ψ hΨ), hev]⟩,
      hr₄.trans (hr₂.trans hr₁)⟩
  · refine FAt.bind (cellAt_fat d) fun ld st₄ C₄ _ _ _ ⟨hC₄, hst₄, hld⟩ => ?_
    subst C₄ st₄
    obtain ⟨d2, _, hwd⟩ := hv₂ d _ (hL d (by simp [Memory.atomUses])) hld
    refine FAt.mono (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
    · show fw I Ψ ld = fw I Ψ la + fw I Ψ lb
      rw [fw_of_two (n := ld) d2, fw_of_two la2, fw_of_two lb2, show Ψ ld = I.σ d from hwd Ψ hΨ,
        hwa₂ Ψ hΨ, hwb Ψ hΨ, hev]
    · subst C' st'
      exact ⟨fun _ => vw_same hv₂ hL (Stronger.refl _) le_rfl rfl, hr₂.trans hr₁⟩

/-- **`MUL`**: a pooled product of the factors (an address's shift kept), or the value's cell
holding the product (a store, a check, a back-solved quotient). -/
theorem place_mul_fat (d a b : V) : AtomFAt (.mul d a b) := by
  intro ctx I C st ok hok _ _ hh _ _ _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hev : I.σ d = I.σ a * I.σ b := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  unfold placeAtom
  dsimp only
  refine FAt.bind (isLazy_fat d .pooled) fun z st₀ C₀ _ _ _ ⟨hC₀, hst₀⟩ => ?_
  subst C₀ st₀
  split
  · refine FAt.bind (factor_fat a hok hv (hL a (by simp [Memory.atomUses])))
      fun ra st₁ C₁ hs₁ hn₁ _ ⟨la2, la1, hlo₁, hr₁, hwa⟩ => ?_
    have hv₁ := hv.step hs₁ hn₁ hlo₁
    refine FAt.bind (factor_fat b hok hv₁ (hL b (by simp [Memory.atomUses])))
      fun rb st₂ C₂ hs₂ hn₂ _ ⟨lb2, lb1, hlo₂, hr₂, hwb⟩ => ?_
    have hv₂ := hv₁.step hs₂ hn₂ hlo₂
    have h2' : 2 ≤ st₂.next := le_trans h2 (le_trans hn₁ hn₂)
    obtain ⟨la, ea⟩ := ra
    obtain ⟨lb, eb⟩ := rb
    dsimp only at *
    refine FAt.bind (pooledCell_fat (fun _ => True) (fun Ψ => Ψ la * Ψ lb)
      (wblind_mul (wblind_cell (lt_of_lt_of_le la1 hn₂)) (wblind_cell lb1)) h2'
      (fun o ho Ψ _ hp _ => by rw [hp.muls _ o ho, mul_sorted]) (fun o ho hs => hs.muls _ o ho)
      (fun _ _ Ψ _ h => ?_) (fun Ψ _ h hp => hp.insertMul (by rw [h, mul_sorted]))
      (fun hs => { hs with muls := pmap_insert_imp hs.muls ⟨h2', Nat.lt_succ_self _⟩ }))
      fun o st₄ C₄ hs₄ hn₄ _ ⟨o2, o1, hlo₄, hr₄, how, _⟩ => ?_
    · show fw I Ψ st₂.next = fw I Ψ la * fw I Ψ lb
      rw [fw_of_two la2, fw_of_two lb2, fw_of_two h2', h]
    have hv₄ := hv₂.step hs₄ hn₄ hlo₄
    have hw : ∀ Ψ, C₄ Ψ → Ψ o * ofK (addressOfIndex (ea + eb)) = I.σ d := fun Ψ hΨ => by
      rw [how Ψ hΨ trivial, hev, ← hwa Ψ (hs₂ Ψ (hs₄ Ψ hΨ)), ← hwb Ψ (hs₄ Ψ hΨ),
        ← ofK_gpow_add]
      ring
    refine FAt.mono (bindTo_fat d _) fun _ C' st' _ _ _ ⟨hC, hst, hd0⟩ => ?_
    subst C' st'
    refine ⟨fun _ => vw_bind hv₄ (fun v hv' _ => hL v hv') (Stronger.refl _) le_rfl rfl hd0 ?_,
      hr₄.trans (hr₂.trans hr₁)⟩
    split
    · next he =>
      have he' : ea + eb = 0 := by simpa using he
      exact ⟨o2, o1, fun Ψ hΨ => by
        have := hw Ψ hΨ
        rw [he', ofK_gpow_zero, mul_one] at this
        exact this⟩
    · exact ⟨o2, o1, hw⟩
  · refine FAt.bind (cellOf_fat a hok hv (hL a (by simp [Memory.atomUses])))
      fun la st₁ C₁ hs₁ hn₁ _ ⟨la2, la1, hlo₁, hr₁, hwa⟩ => ?_
    have hv₁ := hv.step hs₁ hn₁ hlo₁
    refine FAt.bind (cellOf_fat b hok hv₁ (hL b (by simp [Memory.atomUses])))
      fun lb st₂ C₂ hs₂ hn₂ _ ⟨lb2, lb1, hlo₂, hr₂, hwb⟩ => ?_
    have hv₂ := hv₁.step hs₂ hn₂ hlo₂
    refine FAt.bind (cellAt_fat d) fun ld st₄ C₄ _ _ _ ⟨hC₄, hst₄, hld⟩ => ?_
    subst C₄ st₄
    obtain ⟨d2, _, hwd⟩ := hv₂ d _ (hL d (by simp [Memory.atomUses])) hld
    refine FAt.mono (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
    · show fw I Ψ ld = fw I Ψ la * fw I Ψ lb
      rw [fw_of_two (n := ld) d2, fw_of_two la2, fw_of_two lb2, show Ψ ld = I.σ d from hwd Ψ hΨ,
        hwa Ψ (hs₂ Ψ hΨ), hwb Ψ hΨ, hev]
    · subst C' st'
      exact ⟨fun _ => vw_same hv₂ hL (Stronger.refl _) le_rfl rfl, hr₂.trans hr₁⟩

/-- **`assert a == b`**: `MUL` by the pooled `1`, the two words equal in characteristic `2`. -/
theorem place_assertEq_fat (a b : V) : AtomFAt (.assertEq a b) := by
  intro ctx I C st ok hok _ _ hh _ _ _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hev : I.σ b = I.σ a := by
    have h : I.σ a + I.σ b = 0 := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact h.symm
  unfold placeAtom
  dsimp only
  refine FAt.bind (cellOf_fat a hok hv (hL a (by simp [Memory.atomUses])))
    fun la st₁ C₁ hs₁ hn₁ _ ⟨la2, la1, hlo₁, hr₁, hwa⟩ => ?_
  have hv₁ := hv.step hs₁ hn₁ hlo₁
  refine FAt.bind (cellOf_fat b hok hv₁ (hL b (by simp [Memory.atomUses])))
    fun lb st₂ C₂ hs₂ hn₂ _ ⟨lb2, lb1, hlo₂, hr₂, hwb⟩ => ?_
  have hv₂ := hv₁.step hs₂ hn₂ hlo₂
  refine FAt.bind (constCell_fatB (1, 0) (hok.kconst _ _) (le_trans h2 (le_trans hn₁ hn₂)))
    fun one st₃ C₃ hs₃ hn₃ _ ⟨o2, _, hlo₃, hr₃, how, _⟩ => ?_
  refine FAt.mono (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
  · show fw I Ψ lb = fw I Ψ la * fw I Ψ one
    rw [fw_of_two la2, fw_of_two lb2, fw_of_two o2, how Ψ hΨ, word_one, mul_one,
      hwb Ψ (hs₃ Ψ hΨ), hwa Ψ (hs₂ Ψ (hs₃ Ψ hΨ)), hev]
  · subst C' st'
    exact ⟨fun _ => vw_same (hv₂.step hs₃ hn₃ hlo₃) hL (Stronger.refl _) le_rfl rfl,
      hr₃.trans (hr₂.trans hr₁)⟩

/-- **`assert a != b`**: `p = x · inv` and `p = 1`. -/
theorem place_assertNe_fat (x inv p : V) : AtomFAt (.assertNe x inv p) := by
  intro ctx I C st ok hok _ _ hh _ _ _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hev : I.σ p = I.σ x * I.σ inv ∧ I.σ p = 1 := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  unfold placeAtom
  dsimp only
  refine FAt.bind (cellOf_fat x hok hv (hL x (by simp [Memory.atomUses])))
    fun lx st₁ C₁ hs₁ hn₁ _ ⟨lx2, lx1, hlo₁, hr₁, hwx⟩ => ?_
  have hv₁ := hv.step hs₁ hn₁ hlo₁
  refine FAt.bind (cellOf_fat inv hok hv₁ (hL inv (by simp [Memory.atomUses])))
    fun li st₂ C₂ hs₂ hn₂ _ ⟨li2, li1, hlo₂, hr₂, hwi⟩ => ?_
  have hv₂ := hv₁.step hs₂ hn₂ hlo₂
  refine FAt.bind (cellAt_fat p) fun lp st₄ C₄ _ _ _ ⟨hC₄, hst₄, hlp⟩ => ?_
  subst C₄ st₄
  obtain ⟨p2, _, hwp⟩ := hv₂ p _ (hL p (by simp [Memory.atomUses])) hlp
  refine FAt.bind (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ st₅ C₅ _ _ _ ⟨hC₅, hst₅⟩ => ?_
  · show fw I Ψ lp = fw I Ψ lx * fw I Ψ li
    rw [fw_of_two (n := lp) p2, fw_of_two lx2, fw_of_two li2, show Ψ lp = I.σ p from hwp Ψ hΨ,
      hwx Ψ (hs₂ Ψ hΨ), hwi Ψ hΨ, hev.1]
  subst C₅ st₅
  refine FAt.mono (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
  · show fw I Ψ lp = I.kw (.const 1 0)
    rw [fw_of_two (n := lp) p2, hok.kconst, word_one, show Ψ lp = I.σ p from hwp Ψ hΨ, hev.2]
  · subst C' st'
    exact ⟨fun _ => vw_same hv₂ hL (Stronger.refl _) le_rfl rfl, hr₂.trans hr₁⟩

/-- **`assert_in_k`**: a `JUMP` on the pooled `0`. -/
theorem place_assertInK_fat (a b : V) : AtomFAt (.assertInK a b) := by
  intro ctx I C st ok hok _ _ hh _ _ _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hev : IsInK (I.σ a) ∧ IsInK (I.σ b) := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  unfold placeAtom
  dsimp only
  refine FAt.bind (cellOf_fat a hok hv (hL a (by simp [Memory.atomUses])))
    fun la st₁ C₁ hs₁ hn₁ _ ⟨la2, la1, hlo₁, hr₁, hwa⟩ => ?_
  have hv₁ := hv.step hs₁ hn₁ hlo₁
  refine FAt.bind (cellOf_fat b hok hv₁ (hL b (by simp [Memory.atomUses])))
    fun lb st₂ C₂ hs₂ hn₂ _ ⟨lb2, lb1, hlo₂, hr₂, hwb⟩ => ?_
  have hv₂ := hv₁.step hs₂ hn₂ hlo₂
  refine FAt.bind (constCell_fatB (0, 0) (hok.kconst _ _) (le_trans h2 (le_trans hn₁ hn₂)))
    fun z st₃ C₃ hs₃ hn₃ _ ⟨z2, _, hlo₃, hr₃, hwz, _⟩ => ?_
  refine FAt.mono (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
  · show fw I Ψ z = 0 ∧ IsInK (fw I Ψ la) ∧ IsInK (fw I Ψ lb)
    rw [fw_of_two z2, fw_of_two la2, fw_of_two lb2, hwz Ψ hΨ, word_zero,
      hwb Ψ (hs₃ Ψ hΨ), hwa Ψ (hs₂ Ψ (hs₃ Ψ hΨ))]
    exact ⟨rfl, hev⟩
  · subst C' st'
    exact ⟨fun _ => vw_same (hv₂.step hs₃ hn₃ hlo₃) hL (Stronger.refl _) le_rfl rfl,
      hr₃.trans (hr₂.trans hr₁)⟩

/-- **A temporary's load**: the `DEREF` through `lp` into the temporary's cell, its word read on
every valuation the instance's off the temporaries. -/
theorem tmpDeref_fat {t pv : V} {lp dst : Cell} {a : Atom} (hes : Memory.Ev.atom a ∈ I.es)
    (hload : ∀ (σ' : Val) (rd : Reader), (Memory.Ev.atom a).Holds rd σ' →
      LoadHolds rd (σ' pv) 0 (σ' t))
    (htt : t ∈ Memory.atomTmps a) (htm : t ∈ I.tmps) (hpv : pv ∉ I.tmps)
    (hld : st.locs[t]? = some (.cell dst)) (hd2 : 2 ≤ dst) (hd : dst < st.next) (hp2 : 2 ≤ lp)
    (hwp : ∀ Ψ, C Ψ → Ψ lp = I.σ pv) (hK : IsInK (I.σ pv)) :
    FAt ctx I C st (emitDeref lp 0 dst) (fun _ C' st' => C' = C ∧ st'.next = st.next ∧
      st'.locs = st.locs ∧ st'.rest = st.rest) := by
  have hc : cellP st.locs t = some dst := by unfold cellP; rw [hld]
  refine emitDeref_fat hp2 hd2 hd (fun Ψ hΨ => by rw [hwp Ψ hΨ]; exact hK)
    (fun Ψ hΨ h => ?_) (fun hz _ Ψ hΨ _ => ?_)
  · exfalso
    rcases h with ⟨hz, hnt⟩ | h
    · exact hnt ⟨t, htm, cellP_mono hz.2 hc⟩
    · exact h t htm hc
  · refine ⟨t, List.mem_flatMap.mpr ⟨_, hes, htt⟩, cellP_mono hz.2 hc, rfl,
      by rw [hwp Ψ hΨ]; exact hK, fun σ' rd hsame hall => ?_⟩
    have := (hload σ' rd (hall _ hes)).2
    rw [hsame pv hpv, ← hwp Ψ hΨ] at this
    exact this

/-- **`assert_gpow`**: a load into the touch cell. -/
theorem place_touch_fat (t p : V) : AtomFAt (.touch t p) := by
  intro ctx I C st ok hok _ hes hh hus hts _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hK : IsInK (I.σ p) := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  unfold placeAtom
  dsimp only
  refine FAt.bind (cellOf_fat p hok hv (hL p (by simp [Memory.atomUses])))
    fun lp st₁ C₁ hs₁ hn₁ _ ⟨lp2, lp1, hlo₁, hr₁, hwp⟩ => ?_
  have hv₁ := hv.step hs₁ hn₁ hlo₁
  refine FAt.bind (cellAt_fat t) fun dt st₂ C₂ _ _ _ ⟨hC₂, hst₂, hld⟩ => ?_
  subst C₂ st₂
  obtain ⟨t2, t1, _⟩ := hv₁ t _ (hL t (by simp [Memory.atomTmps])) hld
  refine FAt.mono (tmpDeref_fat hes (fun σ' rd h => h) (by simp [Memory.atomTmps])
    (hts t (by simp [Memory.atomTmps])) (hus p (by simp [Memory.atomUses])) hld t2 t1 lp2 hwp hK)
    fun _ C' st' _ _ _ ⟨hC, hn, hl, hr⟩ => ?_
  subst C'
  exact ⟨fun _ => vw_same hv₁ hL (Stronger.refl _) (le_of_eq hn.symm) hl, hr.trans hr₁⟩

/-- **A range check**: two loads into its temporaries and `k = x · y`. -/
theorem place_rangeCheck_fat (x y t1 t2 k : V) : AtomFAt (.rangeCheck x y t1 t2 k) := by
  intro ctx I C st ok hok _ hes hh hus hts _ h2 hv hops
  have hL := atom_ok hops fun _ _ h => by cases h
  have hev : IsInK (I.σ x) ∧ I.σ k = I.σ x * I.σ y ∧ IsInK (I.σ y) :=
    let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  unfold placeAtom
  dsimp only
  refine FAt.bind (cellOf_fat k hok hv (hL k (by simp [Memory.atomUses])))
    fun lk st₁ C₁ hs₁ hn₁ _ ⟨lk2, lk1, hlo₁, hr₁, hwk⟩ => ?_
  have hv₁ := hv.step hs₁ hn₁ hlo₁
  refine FAt.bind (cellOf_fat x hok hv₁ (hL x (by simp [Memory.atomUses])))
    fun lx st₂ C₂ hs₂ hn₂ _ ⟨lx2, lx1, hlo₂, hr₂, hwx⟩ => ?_
  have hv₂ := hv₁.step hs₂ hn₂ hlo₂
  refine FAt.bind (cellAt_fat y) fun ly st₃ C₃ _ _ _ ⟨hC₃, hst₃, hly⟩ => ?_
  subst C₃ st₃
  obtain ⟨y2, y1, hwy⟩ := hv₂ y _ (hL y (by simp [Memory.atomUses])) hly
  refine FAt.bind (cellAt_fat t1) fun d1 st₃ C₃ _ _ _ ⟨hC₃, hst₃, hl1⟩ => ?_
  subst C₃ st₃
  obtain ⟨d12, d11, _⟩ := hv₂ t1 _ (hL t1 (by simp [Memory.atomTmps])) hl1
  refine FAt.bind (tmpDeref_fat hes (fun σ' rd h => h.1) (by simp [Memory.atomTmps])
    (hts t1 (by simp [Memory.atomTmps])) (hus x (by simp [Memory.atomUses])) hl1 d12 d11 lx2 hwx
    hev.1) fun _ st₄ C₄ _ _ _ ⟨hC₄, hn₄, hl₄, hr₄⟩ => ?_
  subst C₄
  refine FAt.bind (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ st₅ C₅ _ _ _ ⟨hC₅, hst₅⟩ => ?_
  · show fw I Ψ lk = fw I Ψ lx * fw I Ψ ly
    rw [fw_of_two lk2, fw_of_two lx2, fw_of_two (n := ly) y2, hwk Ψ (hs₂ Ψ hΨ), hwx Ψ hΨ,
      show Ψ ly = I.σ y from hwy Ψ hΨ, hev.2.1]
  subst C₅ st₅
  refine FAt.bind (cellAt_fat t2) fun d2 st₆ C₆ _ _ _ ⟨hC₆, hst₆, hl2⟩ => ?_
  subst C₆ st₆
  have hv₄ : VW I C₂ st₄ ok := hv₂.step (Stronger.refl _) (le_of_eq hn₄.symm) hl₄
  obtain ⟨d22, d21, _⟩ := hv₄ t2 _ (hL t2 (by simp [Memory.atomTmps])) hl2
  refine FAt.mono (tmpDeref_fat hes (fun σ' rd h => h.2.2) (by simp [Memory.atomTmps])
    (hts t2 (by simp [Memory.atomTmps])) (hus y (by simp [Memory.atomUses])) hl2 d22 d21 y2
    (fun Ψ hΨ => hwy Ψ hΨ) hev.2.2) fun _ C' st' _ _ _ ⟨hC, hn, hl, hr⟩ => ?_
  subst C'
  exact ⟨fun _ => vw_same hv₄ hL (Stronger.refl _) (le_of_eq hn.symm) hl,
    hr.trans (hr₄.trans (hr₂.trans hr₁))⟩

/-- **A copy**: `MUL` by the pooled `1`, or dropped when both values are one cell of a message run
read in place (the copy's event giving the destination its word). -/
theorem place_copy_fat (d s : V) (hds : d ≠ s) : AtomFAt (.copy d s) := by
  intro ctx I C st ok hok _ _ hh _ _ _ h2 hv hops
  have hev : I.σ d = I.σ s := let ⟨rd, hrd⟩ := hok.rd; hh rd hrd
  have hks : ok s := (hops s (by simp [Memory.atomUses])).resolve_right fun ⟨_, h, _⟩ => by
    cases h
    exact hds rfl
  unfold placeAtom
  dsimp only
  refine FAt.bind (FAt.and_wp (cellOf_fat s hok hv hks) (cellOf_alias s))
    fun ls st₁ C₁ hs₁ hn₁ _ ⟨⟨l2, l1, hlo₁, hr₁, hws⟩, hal⟩ => ?_
  have hv₁ := hv.step hs₁ hn₁ hlo₁
  refine FAt.get_bind ?_
  split
  · refine FAt.bind (cellAt_fat d) fun c st₂ C₂ _ _ _ ⟨hC₂, hst₂, hlc⟩ => ?_
    subst C₂ st₂
    split
    · exact FAt.fail_bind
    · next hne =>
      have hc : c = ls := by simpa using hne
      subst hc
      refine FAt.pure ⟨fun _ v l hv' hl' => ?_, hr₁⟩
      by_cases hvd : v = d
      · subst hvd
        rw [hlc] at hl'
        cases hl'
        exact ⟨l2, l1, fun Ψ hΨ => (hws Ψ hΨ).trans hev.symm⟩
      · rcases hv' with h | h
        · exact hv₁ v l h hl'
        · have hvs : v = s := by simp [Memory.atomUses, Memory.atomTmps, hvd] at h; exact h
          subst hvs
          exact hv₁ _ l hks hl'
  · next hna =>
    have hkd : ok d := (hops d (by simp [Memory.atomUses])).resolve_right fun ⟨_, _, h⟩ => by
      rw [← hal] at h
      exact hna h
    have hL : ∀ v ∈ Memory.atomUses (.copy d s) ++ Memory.atomTmps (.copy d s), ok v := by
      intro v hv'
      simp [Memory.atomUses, Memory.atomTmps] at hv'
      rcases hv' with rfl | rfl
      · exact hkd
      · exact hks
    refine FAt.bind (constCell_fatB (1, 0) (hok.kconst _ _) (le_trans h2 hn₁))
      fun one st₂ C₂ hs₂ hn₂ _ ⟨o2, _, hlo₂, hr₂, how, _⟩ => ?_
    have hv₂ := hv₁.step hs₂ hn₂ hlo₂
    refine FAt.bind (cellAt_fat d) fun ld st₃ C₃ _ _ _ ⟨hC₃, hst₃, hld⟩ => ?_
    subst C₃ st₃
    obtain ⟨d2, _, hwd⟩ := hv₂ d _ hkd hld
    refine FAt.mono (emitOp_fat _ fun _ _ Ψ hΨ => ?_) fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
    · show fw I Ψ ld = fw I Ψ ls * fw I Ψ one
      rw [fw_of_two (n := ld) d2, fw_of_two l2, fw_of_two o2, how Ψ hΨ, word_one, mul_one,
        show Ψ ld = I.σ d from hwd Ψ hΨ, hws Ψ (hs₂ Ψ hΨ), hev]
    · subst C' st'
      exact ⟨fun _ => vw_same hv₂ hL (Stronger.refl _) le_rfl rfl, hr₂.trans hr₁⟩

end Atoms

end
end LeanVM.Guest.Backend.Complete
