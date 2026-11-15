/-
  LeanVM.Guest.Backend.Complete.FramePrims

  The placement primitives on a path, as `FAt` lemmas: fresh cells, emission, pools, places and
  runs.
-/

module

public import LeanVM.Guest.Backend.Complete.Frame

/-!
# The primitives on the path

Each lemma mirrors a `*_grows` lemma of `InFrame.lean` with the stronger invariant of `FAt`: a
fresh cell gets the word its instruction writes (`fresh_fat`), an instruction emitted holds on the
frame words the constraint allows (`emitOp_fat`), a pool answers with a cell holding the pooled
word, and a run of values taken gets the valuation's words.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

section Prims

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

/-! ## Combinators -/

theorem FAt.mono {α : Type} {m : P α} {R R' : α → ((ℕ → E) → Prop) → St → Prop}
    (h : FAt ctx I C st m R)
    (hr : ∀ a C' st', Stronger C' C → st.next ≤ st'.next → LocsLe st.locs st'.locs →
      R a C' st' → R' a C' st') : FAt ctx I C st m R' :=
  fun hc => wp_mono (h hc) fun a st' ⟨C', h1, h2, h3, h4, h5, h6⟩ =>
    ⟨C', h1, h2, h3, h4, h5, hr a C' st' h2 h3 h4 h6⟩

/-- The invariant at the start, for the proof of an action. -/
theorem FAt.withCOk {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : COk I C st.next st.scope → FAt ctx I C st m R) : FAt ctx I C st m R :=
  fun hc => h hc hc

theorem FAt.pureC {α : Type} {a : α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : COk I C st.next st.scope → R a C st) : FAt ctx I C st (Pure.pure a) R :=
  fun hc => wp_pure.mpr ⟨C, hc, Stronger.refl C, le_rfl, LocsLe.refl _, EmitsW.refl st, h hc⟩

theorem FAt.fail {α : Type} {msg : String} {R : α → ((ℕ → E) → Prop) → St → Prop} :
    FAt ctx I C st (failP msg : P α) R := fun _ => wp_failP

theorem FAt.fail_bind {α β : Type} {msg : String} {f : α → P β}
    {R : β → ((ℕ → E) → Prop) → St → Prop} : FAt ctx I C st ((failP msg : P α) >>= f) R :=
  fun _ => wp_bind.mpr wp_failP

theorem FAt.guard {β : Type} {c : Prop} [Decidable c] {msg : String} {f : PUnit → P β}
    {R : β → ((ℕ → E) → Prop) → St → Prop} (h : ¬c → FAt ctx I C st (f PUnit.unit) R) :
    FAt ctx I C st (if c then failP msg >>= f else f PUnit.unit) R := by
  split
  · exact FAt.fail_bind
  · next hc => exact h hc

theorem FAt.read_bind {β : Type} {f : Ctx → P β} {R : β → ((ℕ → E) → Prop) → St → Prop}
    (h : FAt ctx I C st (f ctx) R) : FAt ctx I C st (read >>= f) R :=
  fun hc => wp_bind.mpr (wp_read.mpr (h hc))

/-- A step that keeps the next free cell, the output and the places, the pools kept. -/
theorem FAt.modify {g : St → St} (hn : (g st).next = st.next) (ho : (g st).out = st.out)
    (hl : (g st).locs = st.locs)
    (hc : COk I C st.next st.scope → COk I C st.next (g st).scope) :
    FAt ctx I C st (modify g) (fun _ C' st' => C' = C ∧ st' = g st) := fun hc' =>
  wp_modify.mpr ⟨C, by rw [hn]; exact hc hc', Stronger.refl C, le_of_eq hn.symm,
    by rw [hl]; exact LocsLe.refl _, ⟨[], by rw [ho]; simp, fun _ _ h => nomatch h⟩, rfl, rfl⟩

/-- An action that keeps the next free cell, the pools, the output and grows the places. -/
theorem FAt.ofSame {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : wpP m ctx st fun a st' => st'.next = st.next ∧ st'.scope = st.scope ∧
      st'.out = st.out ∧ LocsLe st.locs st'.locs ∧ R a C st') : FAt ctx I C st m R :=
  fun hc => wp_mono h fun a st' ⟨hn, hs, ho, hl, hr⟩ =>
    ⟨C, by rw [hn, hs]; exact hc, Stronger.refl C, le_of_eq hn.symm, hl,
      ⟨[], by rw [ho]; simp, fun _ _ h => nomatch h⟩, hr⟩

theorem COk.withScope {n : ℕ} {sc sc' : Scope} (h : COk I C n sc)
    (hp : ∀ Ψ, C Ψ → PoolW I Ψ sc → PoolW I Ψ sc') (hs : ScopeGood n sc → ScopeGood n sc') :
    COk I C n sc' :=
  ⟨h.sat, h.blind, fun Ψ hΨ => hp Ψ hΨ (h.pools Ψ hΨ), hs h.cells⟩

/-- A fresh cell gets a word computed from the cells below it. -/
theorem COk.assign {n : ℕ} {sc : Scope} {w : (ℕ → E) → E} (h : COk I C n sc) (hw : WBlind w n) :
    COk I (fun Ψ => C Ψ ∧ Ψ n = w Ψ) (n + 1) sc :=
  ⟨assign_sat h.blind hw le_rfl h.sat, assign_blind h.blind hw le_rfl,
    fun Ψ hΨ => h.pools Ψ hΨ.1, h.cells.mono (Nat.le_succ n)⟩

theorem fw_of_two {Ψ : ℕ → E} {n : ℕ} (h : 2 ≤ n) : fw I Ψ n = Ψ n := by
  simp [fw, show n ≠ 0 by omega, show n ≠ 1 by omega]

theorem mul_sorted (Ψ : ℕ → E) (a b : ℕ) : Ψ (sorted a b).1 * Ψ (sorted a b).2 = Ψ a * Ψ b := by
  rcases le_total a b with h | h
  · simp [sorted, min_eq_left h, max_eq_right h]
  · simp [sorted, min_eq_right h, max_eq_left h, mul_comm]

theorem add_sorted (Ψ : ℕ → E) (a b : ℕ) : Ψ (sorted a b).1 + Ψ (sorted a b).2 = Ψ a + Ψ b := by
  rcases le_total a b with h | h
  · simp [sorted, min_eq_left h, max_eq_right h]
  · simp [sorted, min_eq_right h, max_eq_left h, add_comm]

/-! ## Cells and instructions -/

/-- **A fresh cell** gets the word `w`, computed from the cells below it. -/
theorem fresh_fat (w : (ℕ → E) → E) (hw : WBlind w st.next) :
    FAt ctx I C st fresh (fun o C' st' => o = st.next ∧ st' = { st with next := st.next + 1 } ∧
      C' = fun Ψ => C Ψ ∧ Ψ st.next = w Ψ) := fun hc =>
  wp_modifyGet.mpr ⟨_, hc.assign hw, fun _ h => h.1, Nat.le_succ _, LocsLe.refl _,
    ⟨[], by simp, fun _ _ h => nomatch h⟩, rfl, rfl, rfl⟩

/-- **An instruction emitted** holds on the frame words, once the final placement extends the
state. -/
theorem emitOp_fat (o : LOp) (h : Fits I st → ∀ Ψ, C Ψ → OpW I Ψ o) :
    FAt ctx I C st (emitOp o) (fun _ C' st' => C' = C ∧
      st' = { st with pending := #[], out := st.out.push (.op st.pending.toList o) }) := by
  intro hc
  unfold emitOp takeHints push
  refine wp_bind.mpr (wp_modifyGet.mpr (wp_modify.mpr ?_))
  refine ⟨C, hc, Stronger.refl C, le_rfl, LocsLe.refl _,
    ⟨[.op st.pending.toList o], by simp, fun hz s hs => ?_⟩, rfl, rfl⟩
  rw [List.mem_singleton] at hs
  subst hs
  exact ⟨_, _, rfl, h hz⟩

/-- **A pooled result**: the pool's cell, or a fresh one, given the word `w`, which the
instruction writes and the pool learns. -/
theorem pooledCell_fat {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (w : (ℕ → E) → E) (hw : WBlind w st.next) (h2 : 2 ≤ st.next)
    (hfind : ∀ o, find st.scope = some o → ∀ Ψ, C Ψ → PoolW I Ψ st.scope → Ψ o = w Ψ)
    (hfc : ∀ o, find st.scope = some o → ScopeGood st.next st.scope → 2 ≤ o ∧ o < st.next)
    (hmk : Fits I { st with next := st.next + 1 } → ∀ Ψ, C Ψ → Ψ st.next = w Ψ →
      OpW I Ψ (mk st.next))
    (hlearn : ∀ Ψ, C Ψ → Ψ st.next = w Ψ → PoolW I Ψ st.scope →
      PoolW I Ψ (learn st.next st.scope))
    (hcells : ScopeGood (st.next + 1) st.scope →
      ScopeGood (st.next + 1) (learn st.next st.scope)) :
    FAt ctx I C st (pooledCell find learn mk) (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧
      st'.locs = st.locs ∧ st'.rest = st.rest ∧ ∀ Ψ, C' Ψ → Ψ o = w Ψ) := by
  unfold pooledCell
  refine FAt.get_bind ?_
  split
  · next o ho =>
    exact FAt.pureC fun hc => ⟨(hfc o ho hc.cells).1, (hfc o ho hc.cells).2, rfl, rfl,
      fun Ψ hΨ => hfind o ho Ψ hΨ (hc.pools Ψ hΨ)⟩
  · refine FAt.bind (fresh_fat w hw) fun o st₁ C₁ _ _ _ ⟨ho, hst₁, hC₁⟩ => ?_
    subst ho hst₁ hC₁
    refine FAt.bind (emitOp_fat (mk st.next) fun hz Ψ hΨ => hmk hz Ψ hΨ.1 hΨ.2)
      fun _ st₂ C₂ _ _ _ ⟨hC₂, hst₂⟩ => ?_
    subst hC₂ hst₂
    refine FAt.bind (FAt.modify rfl rfl rfl fun hc => hc.withScope
      (fun Ψ hΨ hp => hlearn Ψ hΨ.1 hΨ.2 hp) hcells) fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => ?_
    subst hC₃ hst₃
    exact FAt.pure ⟨h2, Nat.lt_succ_self _, rfl, rfl, fun Ψ h => h.2⟩

theorem mulCell_eq (a b : Cell) : mulCell a b = pooledCell (·.muls.get? (sorted a b))
    (fun o sc => { sc with muls := sc.muls.insert (sorted a b) o }) (fun o => .mul a b o) := rfl

/-- **A pooled product** of two good cells below the next free one. -/
theorem mulCell_fat {a b : Cell} (ha2 : 2 ≤ a) (ha : a < st.next) (hb2 : 2 ≤ b)
    (hb : b < st.next) :
    FAt ctx I C st (mulCell a b) (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧ st'.locs = st.locs ∧
      st'.rest = st.rest ∧ ∀ Ψ, C' Ψ → Ψ o = Ψ a * Ψ b) := by
  have h2 : 2 ≤ st.next := le_trans ha2 ha.le
  rw [mulCell_eq]
  refine pooledCell_fat (fun Ψ => Ψ a * Ψ b) (wblind_mul (wblind_cell ha) (wblind_cell hb))
    h2 (fun o ho Ψ _ hp => by rw [hp.muls _ o ho, mul_sorted])
    (fun o ho hs => hs.muls _ o ho) (fun _ Ψ _ h => ?_)
    (fun Ψ _ h hp => hp.insertMul (by rw [h, mul_sorted]))
    (fun hs => { hs with muls := pmap_insert_imp hs.muls ⟨h2, Nat.lt_succ_self _⟩ })
  show fw I Ψ st.next = fw I Ψ a * fw I Ψ b
  rw [fw_of_two ha2, fw_of_two hb2, fw_of_two h2, h]

/-! ## Places -/

/-- **A value placed**: its place is new. -/
theorem bindTo_fat (v : V) (l : Loc) :
    FAt ctx I C st (bindTo v l) (fun _ C' st' => C' = C ∧
      st' = { st with locs := st.locs.insert v l } ∧ st.locs[v]? = none) := by
  unfold bindTo
  refine FAt.get_bind ?_
  split
  · exact FAt.fail_bind
  · next h =>
    refine FAt.ofSame (wp_modify.mpr ⟨rfl, rfl, rfl, fun w x hx => ?_, rfl, rfl,
      KMap.getElem?_eq_none_of_contains_eq_false (by simpa using h)⟩)
    show (st.locs.insert v l)[w]? = some x
    rw [KMap.getElem?_insert]
    split
    · next he =>
      subst he
      rw [KMap.getElem?_eq_none_of_contains_eq_false (by simpa using h)] at hx
      cases hx
    · exact hx

theorem bindRun_wp (base : Cell) : ∀ (vs : List V) (n : ℕ) (st : St),
    wpP ((vs.zipIdx n).forM fun (v, k) => bindTo v (.cell (base + k))) ctx st fun _ st' =>
      st' = { st with locs := st'.locs } ∧ LocsLe st.locs st'.locs ∧
      (∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨ v ∈ vs) ∧
      ∀ k (hk : k < vs.length), st'.locs[vs[k]]? = some (.cell (base + n + k))
  | [], n, st => by
      show wpP (Pure.pure PUnit.unit) ctx st _
      exact wp_pure.mpr ⟨rfl, LocsLe.refl _, fun _ _ h => Or.inl h,
        fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | v :: vs, n, st => by
      rw [List.zipIdx_cons]
      show wpP (bindTo v (.cell (base + n)) >>= fun _ =>
        (vs.zipIdx (n + 1)).forM fun (v, k) => bindTo v (.cell (base + k))) ctx st _
      refine wp_bind.mpr ?_
      unfold bindTo
      refine wp_bind.mpr (wp_get.mpr ?_)
      split
      · exact wp_bind.mpr wp_failP
      · next hcont =>
        have hnone : st.locs[v]? = none :=
          KMap.getElem?_eq_none_of_contains_eq_false (by simpa using hcont)
        refine wp_modify.mpr (wp_mono (bindRun_wp base vs (n + 1) _)
          fun _ st' ⟨he, hg, hnew, hk⟩ => ?_)
        have hle : LocsLe st.locs (st.locs.insert v (.cell (base + n))) := fun w x hx => by
          rw [KMap.getElem?_insert]
          split
          · next he =>
            subst he
            rw [hnone] at hx
            cases hx
          · exact hx
        refine ⟨he, hle.trans hg, fun w l hw => ?_, fun k hk' => ?_⟩
        · rcases hnew w l hw with h | h
          · rw [KMap.getElem?_insert] at h
            split at h
            · next he' => exact Or.inr (he' ▸ List.mem_cons_self)
            · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
        · cases k with
          | zero =>
            refine hg v _ ?_
            simp
          | succ k =>
            have := hk k (Nat.lt_of_succ_lt_succ hk')
            rw [show base + (n + 1) + k = base + n + (k + 1) by ac_rfl] at this
            simpa using this

/-- The values of a run placed in the cells from `base`, the words unchanged. -/
theorem bindRun_fat (vs : List V) (base : Cell) :
    FAt ctx I C st (bindRun vs base) (fun _ C' st' => C' = C ∧
      st' = { st with locs := st'.locs } ∧
      (∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨ v ∈ vs) ∧
      ∀ k (hk : k < vs.length), st'.locs[vs[k]]? = some (.cell (base + k))) := by
  unfold bindRun
  refine FAt.ofSame (wp_mono (bindRun_wp base vs 0 st) fun _ st' ⟨he, hg, hnew, hk⟩ => ?_)
  refine ⟨by rw [he], by rw [he], by rw [he], hg, rfl, he, hnew, fun k hk' => ?_⟩
  simpa using hk k hk'

/-- Words for the cells `base + k`, `k < m`, each of which the constraint is blind to. -/
theorem run_sat {base len : ℕ} (hbl : ∀ Ψ k w, k < len → C Ψ → C (Function.update Ψ (base + k) w))
    (hs : ∃ Ψ, C Ψ) (f : ℕ → E) : ∀ m ≤ len, ∃ Ψ, C Ψ ∧ ∀ k < m, Ψ (base + k) = f k
  | 0, _ => let ⟨Ψ, h⟩ := hs; ⟨Ψ, h, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | m + 1, hm => by
      obtain ⟨Ψ, h, hk⟩ := run_sat hbl hs f m (by omega)
      refine ⟨Function.update Ψ (base + m) (f m), hbl Ψ m _ (by omega) h, fun k hk' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hk k hk'
      · rw [Function.update_self]

/-- The constraint giving the run's cells from `base` the valuation's words. -/
def RunC (I : Inst) (C : (ℕ → E) → Prop) (vs : List V) (base : ℕ) (Ψ : ℕ → E) : Prop :=
  C Ψ ∧ ∀ k (hk : k < vs.length), Ψ (base + k) = I.σ vs[k]

theorem runC_sat {vs : List V} {base : ℕ}
    (hbl : ∀ Ψ k w, k < vs.length → C Ψ → C (Function.update Ψ (base + k) w))
    (hs : ∃ Ψ, C Ψ) : ∃ Ψ, RunC I C vs base Ψ := by
  obtain ⟨Ψ, h, hk⟩ := run_sat hbl hs (fun k => if h : k < vs.length then I.σ vs[k] else 0)
    vs.length le_rfl
  exact ⟨Ψ, h, fun k hk' => by rw [hk k hk']; simp [hk']⟩

/-- `RunC` is blind from `n` on when `C` is and the run is below `n`. -/
theorem runC_blind {vs : List V} {base n : ℕ} (hC : Blind C n) (hb : base + vs.length ≤ n) :
    Blind (RunC I C vs base) n := fun Ψ c w hc ⟨h1, h2⟩ =>
  ⟨hC Ψ c w hc h1, fun k hk => by rw [Function.update_of_ne (by omega)]; exact h2 k hk⟩

/-- **A run of values taken** from the next free cell: each cell gets its value's word. -/
theorem takeRun_fat (vs : List V) :
    FAt ctx I C st (takeRun vs) (fun _ C' st' => st'.next = st.next + vs.length ∧
      st'.rest = st.rest ∧ st'.scope = st.scope ∧
      (∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨ v ∈ vs) ∧
      (∀ k (hk : k < vs.length), st'.locs[vs[k]]? = some (.cell (st.next + k))) ∧
      ∀ Ψ, C' Ψ → ∀ k (hk : k < vs.length), Ψ (st.next + k) = I.σ vs[k]) := by
  intro hc
  unfold takeRun bindRun
  refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_mono (bindRun_wp (ctx := ctx) st.next vs 0 st)
    fun _ st₁ ⟨he, hg, hnew, hk⟩ => wp_modify.mpr ?_)))
  have hs : st₁.scope = st.scope := (congrArg St.scope he).trans rfl
  have hr : st₁.rest = st.rest := (congrArg St.rest he).trans rfl
  have ho : st₁.out = st.out := (congrArg St.out he).trans rfl
  refine ⟨RunC I C vs st.next, ⟨runC_sat (fun Ψ k w _ h => hc.blind Ψ _ w (by omega) h) hc.sat,
    runC_blind (hc.blind.mono (Nat.le_add_right _ _)) le_rfl,
    fun Ψ hΨ => by rw [hs]; exact hc.pools Ψ hΨ.1, by rw [hs]; exact hc.cells.mono (Nat.le_add_right _ _)⟩,
    fun _ h => h.1, Nat.le_add_right _ _, hg, ⟨[], by simp [ho], fun _ _ h => nomatch h⟩, rfl, hr, hs, hnew,
    fun k hk' => by simpa using hk k hk', fun Ψ h => h.2⟩

end Prims

end
end LeanVM.Guest.Backend.Complete
