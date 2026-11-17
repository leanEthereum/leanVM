/-
  LeanVM.Compiler.Complete.FramePrims

  The placement primitives on a path, as `FAt` lemmas: fresh cells, emission, pools, places and
  runs.
-/

module

public import LeanVM.Compiler.Complete.Frame

/-!
# The primitives on the path

Each lemma mirrors a `*_grows` lemma of `InFrame.lean` with the stronger invariant of `FAt`: a
fresh cell gets the word its instruction writes (`fresh_fat`), an instruction emitted holds on the
frame words the constraint allows (`emitOp_fat`), a pool answers with a cell holding the pooled
word, and a run of values taken gets the valuation's words.
-/

namespace LeanVM.Compiler.Complete

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
    (h : COk I C st.next st.scope st.locs → FAt ctx I C st m R) : FAt ctx I C st m R :=
  fun hc => h hc hc

theorem FAt.pureC {α : Type} {a : α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : COk I C st.next st.scope st.locs → R a C st) : FAt ctx I C st (Pure.pure a) R :=
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
    (hc : COk I C st.next st.scope st.locs → COk I C st.next (g st).scope st.locs) :
    FAt ctx I C st (modify g) (fun _ C' st' => C' = C ∧ st' = g st) := fun hc' =>
  wp_modify.mpr ⟨C, by rw [hn, hl]; exact hc hc', Stronger.refl C, le_of_eq hn.symm,
    by rw [hl]; exact LocsLe.refl _, ⟨[], by rw [ho]; simp, fun _ _ _ h => nomatch h⟩, rfl, rfl⟩

/-- An action that keeps the next free cell, the pools, the output and grows the places. -/
theorem FAt.ofSame {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : wpP m ctx st fun a st' => st'.next = st.next ∧ st'.scope = st.scope ∧
      st'.out = st.out ∧ LocsLe st.locs st'.locs ∧ R a C st') : FAt ctx I C st m R :=
  fun hc => wp_mono h fun a st' ⟨hn, hs, ho, hl, hr⟩ =>
    ⟨C, by rw [hn, hs]; exact ⟨hc.sat, hc.blind, fun Ψ hΨ => (hc.pools Ψ hΨ).grow hl, hc.cells⟩, Stronger.refl C, le_of_eq hn.symm, hl,
      ⟨[], by rw [ho]; simp, fun _ _ _ h => nomatch h⟩, hr⟩

theorem COk.withScope {n : ℕ} {sc sc' : Scope} {locs : VMap Loc} (h : COk I C n sc locs)
    (hp : ∀ Ψ, C Ψ → PoolW I Ψ locs sc → PoolW I Ψ locs sc')
    (hs : ScopeGood n sc → ScopeGood n sc') : COk I C n sc' locs :=
  ⟨h.sat, h.blind, fun Ψ hΨ => hp Ψ hΨ (h.pools Ψ hΨ), hs h.cells⟩

/-- A fresh cell gets a word computed from the cells below it. -/
theorem COk.assign {n : ℕ} {sc : Scope} {locs : VMap Loc} {w : (ℕ → E) → E}
    (h : COk I C n sc locs) (hw : WBlind w n) : COk I (fun Ψ => C Ψ ∧ Ψ n = w Ψ) (n + 1) sc locs :=
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

/-- A constraint that leaves the word of cell `c` free. -/
def BlindAt (C : (ℕ → E) → Prop) (c : ℕ) : Prop := ∀ Ψ w, C Ψ → C (Function.update Ψ c w)

/-- A cell whose word a satisfiable constraint fixes is none it leaves free. -/
theorem fixed_ne {c x : ℕ} {a : E} (hs : ∃ Ψ, C Ψ) (hb : BlindAt C c)
    (hx : ∀ Ψ, C Ψ → Ψ x = a) : x ≠ c := by
  rintro rfl
  obtain ⟨Ψ, h⟩ := hs
  have h1 := hx _ (hb Ψ (a + 1) h)
  rw [Function.update_self] at h1
  exact one_ne_zero (by linear_combination h1 : (1 : E) = 0)

/-- The cells below `n` the constraint `C` leaves free, `C'` leaves free. -/
def KeepB (C C' : (ℕ → E) → Prop) (n : ℕ) : Prop := ∀ c, c < n → BlindAt C c → BlindAt C' c

theorem KeepB.refl (C : (ℕ → E) → Prop) (n : ℕ) : KeepB C C n := fun _ _ h => h

theorem KeepB.trans {C₁ C₂ : (ℕ → E) → Prop} {n n₁ : ℕ} (h₁ : KeepB C C₁ n)
    (h₂ : KeepB C₁ C₂ n₁) (hn : n ≤ n₁) : KeepB C C₂ n :=
  fun c hc hb => h₂ c (lt_of_lt_of_le hc hn) (h₁ c hc hb)

/-- A word the constraint fixes stays when a cell it leaves free changes. -/
theorem fixed_upd {c x : ℕ} {a : E} (hb : BlindAt C c) (hx : ∀ Ψ, C Ψ → Ψ x = a) {Ψ : ℕ → E}
    (hΨ : C Ψ) (w : E) : Function.update Ψ c w x = Ψ x := by
  rw [hx _ (hb Ψ w hΨ), hx Ψ hΨ]

/-! ## Cells and instructions -/

/-- **A fresh cell** gets the word `w`, computed from the cells below it. -/
theorem fresh_fat (w : (ℕ → E) → E) (hw : WBlind w st.next) :
    FAt ctx I C st fresh (fun o C' st' => o = st.next ∧ st' = { st with next := st.next + 1 } ∧
      C' = fun Ψ => C Ψ ∧ Ψ st.next = w Ψ) := fun hc =>
  wp_modifyGet.mpr ⟨_, hc.assign hw, fun _ h => h.1, Nat.le_succ _, LocsLe.refl _,
    ⟨[], by simp, fun _ _ _ h => nomatch h⟩, rfl, rfl, rfl⟩

/-- **An instruction emitted** holds on the frame words, once the final placement extends the
state. -/
theorem emitOp_fat (o : LOp) (h : Fits I st → o ∈ I.ops → ∀ Ψ, C Ψ → OpW I Ψ o) :
    FAt ctx I C st (emitOp o) (fun _ C' st' => C' = C ∧
      st' = { st with pending := #[], out := st.out.push (.op st.pending.toList o) }) := by
  intro hc
  unfold emitOp takeHints push
  refine wp_bind.mpr (wp_modifyGet.mpr (wp_modify.mpr ?_))
  refine ⟨C, hc, Stronger.refl C, le_rfl, LocsLe.refl _,
    EmitsW.of_ops (ops := [.op st.pending.toList o]) (by simp) fun hz hops s hs => ?_, rfl, rfl⟩
  rw [List.mem_singleton] at hs
  subst hs
  exact ⟨_, _, rfl, h hz (hops _ _ List.mem_cons_self)⟩

/-- The state once `o` is emitted. -/
def emitted (st : St) (o : LOp) : St :=
  { st with pending := #[], out := st.out.push (.op st.pending.toList o) }

/-- **An instruction emitted**, its relation given once the final placement has the block's
straight-line instructions up to it. -/
theorem emitOp_fatO (o : LOp) (h : Fits I st → OutOps I (emitted st o) → ∀ Ψ, C Ψ → OpW I Ψ o) :
    FAt ctx I C st (emitOp o) (fun _ C' st' => C' = C ∧
      st' = { st with pending := #[], out := st.out.push (.op st.pending.toList o) }) := by
  intro hc
  unfold emitOp takeHints push
  refine wp_bind.mpr (wp_modifyGet.mpr (wp_modify.mpr ?_))
  refine ⟨C, hc, Stronger.refl C, le_rfl, LocsLe.refl _,
    ⟨[.op st.pending.toList o], by simp, fun hz hout s hs => ?_⟩, rfl, rfl⟩
  rw [List.mem_singleton] at hs
  subst hs
  exact ⟨_, _, rfl, h hz hout⟩

/-- The straight-line instructions of a later output. -/
theorem OutOps.sub {s s' : St} (h : OutOps I s) (hsub : ∀ x ∈ s'.out.toList, x ∈ s.out.toList) :
    OutOps I s' := fun h' o hm => h h' o (hsub _ hm)

/-- **A pooled result**: the pool's cell, or a fresh one, given the word `w`, which the
instruction writes and the pool learns. -/
theorem pooledCell_fat {find : Scope → Option Cell} {learn : Cell → Scope → Scope}
    {mk : Cell → LOp} (Q : Cell → Prop) (w : (ℕ → E) → E) (hw : WBlind w st.next)
    (h2 : 2 ≤ st.next)
    (hfind : ∀ o, find st.scope = some o → ∀ Ψ, C Ψ → PoolW I Ψ st.locs st.scope → Q o →
      Ψ o = w Ψ)
    (hfc : ∀ o, find st.scope = some o → ScopeGood st.next st.scope → 2 ≤ o ∧ o < st.next)
    (hmk : Fits I { st with next := st.next + 1 } → mk st.next ∈ I.ops → ∀ Ψ, C Ψ →
      Ψ st.next = w Ψ → OpW I Ψ (mk st.next))
    (hlearn : ∀ Ψ, C Ψ → Ψ st.next = w Ψ → PoolW I Ψ st.locs st.scope →
      PoolW I Ψ st.locs (learn st.next st.scope))
    (hcells : ScopeGood (st.next + 1) st.scope →
      ScopeGood (st.next + 1) (learn st.next st.scope)) :
    FAt ctx I C st (pooledCell find learn mk) (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧
      st'.locs = st.locs ∧ st'.rest = st.rest ∧ (∀ Ψ, C' Ψ → Q o → Ψ o = w Ψ) ∧
      ∀ c, c < st.next → BlindAt C c → (∀ Ψ x, C Ψ → w (Function.update Ψ c x) = w Ψ) →
        BlindAt C' c) := by
  unfold pooledCell
  refine FAt.get_bind ?_
  split
  · next o ho =>
    exact FAt.pureC fun hc => ⟨(hfc o ho hc.cells).1, (hfc o ho hc.cells).2, rfl, rfl,
      fun Ψ hΨ => hfind o ho Ψ hΨ (hc.pools Ψ hΨ), fun _ _ hb _ => hb⟩
  · refine FAt.bind (fresh_fat w hw) fun o st₁ C₁ _ _ _ ⟨ho, hst₁, hC₁⟩ => ?_
    subst ho hst₁ hC₁
    refine FAt.bind (emitOp_fat (mk st.next) fun hz hm Ψ hΨ => hmk hz hm Ψ hΨ.1 hΨ.2)
      fun _ st₂ C₂ _ _ _ ⟨hC₂, hst₂⟩ => ?_
    subst hC₂ hst₂
    refine FAt.bind (FAt.modify rfl rfl rfl fun hc => hc.withScope
      (fun Ψ hΨ hp => hlearn Ψ hΨ.1 hΨ.2 hp) hcells) fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => ?_
    subst hC₃ hst₃
    exact FAt.pure ⟨h2, Nat.lt_succ_self _, rfl, rfl, fun Ψ h _ => h.2,
      fun c hc hb hwc Ψ x h => ⟨hb Ψ x h.1, by
        rw [Function.update_of_ne (Nat.ne_of_gt hc), hwc Ψ x h.1]
        exact h.2⟩⟩

theorem mulCell_eq (a b : Cell) : mulCell a b = pooledCell (·.muls.get? (sorted a b))
    (fun o sc => { sc with muls := sc.muls.insert (sorted a b) o }) (fun o => .mul a b o) := rfl

/-- **A pooled product** of two good cells below the next free one. -/
theorem mulCell_fat {a b : Cell} (ha2 : 2 ≤ a) (ha : a < st.next) (hb2 : 2 ≤ b)
    (hb : b < st.next) :
    FAt ctx I C st (mulCell a b) (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧ st'.locs = st.locs ∧
      st'.rest = st.rest ∧ (∀ Ψ, C' Ψ → Ψ o = Ψ a * Ψ b) ∧
      ∀ c, c < st.next → c ≠ a → c ≠ b → BlindAt C c → BlindAt C' c) := by
  have h2 : 2 ≤ st.next := le_trans ha2 ha.le
  rw [mulCell_eq]
  refine FAt.mono (pooledCell_fat (fun _ => True) (fun Ψ => Ψ a * Ψ b)
    (wblind_mul (wblind_cell ha) (wblind_cell hb))
    h2 (fun o ho Ψ _ hp _ => by rw [hp.muls _ o ho, mul_sorted])
    (fun o ho hs => hs.muls _ o ho) (fun _ _ Ψ _ h => ?_)
    (fun Ψ _ h hp => hp.insertMul (by rw [h, mul_sorted]))
    (fun hs => { hs with muls := pmap_insert_imp hs.muls ⟨h2, Nat.lt_succ_self _⟩ }))
    fun o C' st' _ _ _ ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, fun Ψ hΨ => h5 Ψ hΨ trivial,
      fun c hc hca hcb hb => h6 c hc hb fun Ψ x _ => by
        show Function.update Ψ c x a * Function.update Ψ c x b = Ψ a * Ψ b
        rw [Function.update_of_ne hca.symm, Function.update_of_ne hcb.symm]⟩
  show fw I Ψ st.next = fw I Ψ a * fw I Ψ b
  rw [fw_of_two ha2, fw_of_two hb2, fw_of_two h2, h]

theorem constCell_eq (k : ℕ × ℕ) : constCell k = pooledCell (·.consts.get? k)
    (fun o sc => { sc with consts := sc.consts.insert k o }) (fun o => .set o (.const k.1 k.2)) :=
  rfl

/-- **A pooled constant**, keeping the cells the constraint leaves free. -/
theorem constCell_fatB (k : ℕ × ℕ) (hkw : I.kw (.const k.1 k.2) = Guest.word k.1 k.2)
    (h2 : 2 ≤ st.next) :
    FAt ctx I C st (constCell k) (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧ st'.locs = st.locs ∧
      st'.rest = st.rest ∧ (∀ Ψ, C' Ψ → Ψ o = Guest.word k.1 k.2) ∧
      ∀ c, c < st.next → BlindAt C c → BlindAt C' c) := by
  rw [constCell_eq]
  refine FAt.mono (pooledCell_fat (fun _ => True) (fun _ => Guest.word k.1 k.2)
    (wblind_const _ _) h2 (fun o ho Ψ _ hp _ => hp.consts k o ho) (fun o ho hs => hs.consts k o ho) (fun _ _ Ψ _ h => ?_)
    (fun Ψ _ h hp => hp.insertConst h)
    (fun hs => { hs with consts := pmap_insert_imp hs.consts ⟨h2, Nat.lt_succ_self _⟩ }))
    fun o C' st' _ _ _ ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, fun Ψ hΨ => e Ψ hΨ trivial,
      fun c' hc hb => f c' hc hb
      fun _ _ _ => rfl⟩
  show fw I Ψ st.next = I.kw (.const k.1 k.2)
  rw [hkw, fw_of_two h2, h]

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
      (∀ Ψ, C' Ψ → ∀ k (hk : k < vs.length), Ψ (st.next + k) = I.σ vs[k]) ∧
      ∀ c, c < st.next → BlindAt C c → BlindAt C' c) := by
  intro hc
  unfold takeRun bindRun
  refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_mono (bindRun_wp (ctx := ctx) st.next vs 0 st)
    fun _ st₁ ⟨he, hg, hnew, hk⟩ => wp_modify.mpr ?_)))
  have hs : st₁.scope = st.scope := (congrArg St.scope he).trans rfl
  have hr : st₁.rest = st.rest := (congrArg St.rest he).trans rfl
  have ho : st₁.out = st.out := (congrArg St.out he).trans rfl
  refine ⟨RunC I C vs st.next, ⟨runC_sat (fun Ψ k w _ h => hc.blind Ψ _ w (by omega) h) hc.sat,
    runC_blind (hc.blind.mono (Nat.le_add_right _ _)) le_rfl,
    fun Ψ hΨ => by rw [hs]; exact (hc.pools Ψ hΨ.1).grow hg, by rw [hs]; exact hc.cells.mono (Nat.le_add_right _ _)⟩,
    fun _ h => h.1, Nat.le_add_right _ _, hg, ⟨[], by simp [ho], fun _ _ _ h => nomatch h⟩, rfl, hr, hs, hnew,
    fun k hk' => by simpa using hk k hk', fun Ψ h => h.2,
    fun c hc hb Ψ x h => ⟨hb Ψ x h.1, fun k hk => by
      rw [Function.update_of_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hc (Nat.le_add_right _ _)))]
      exact h.2 k hk⟩⟩

/-! ## Shifted pointers -/

theorem ofK_gpow_zero : ofK (addressOfIndex 0) = 1 := by
  rw [addressOfIndex, pow_zero, ofK_one]

/-- **A shifted pointer made a value**: its cell holds the pointer's word times `g^exp`. -/
theorem materialize_fat (c : Cell) (exp : ℕ) (hok : I.Ok) (hc2 : 2 ≤ c) (hc : c < st.next) :
    FAt ctx I C st (materialize c exp) (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧
      st'.locs = st.locs ∧ st'.rest = st.rest ∧
      (∀ Ψ, C' Ψ → Ψ o = Ψ c * ofK (addressOfIndex exp)) ∧
      ((∃ a, ∀ Ψ, C Ψ → Ψ c = a) → ∀ c', c' < st.next → BlindAt C c' → BlindAt C' c')) := by
  have h2 : 2 ≤ st.next := le_trans hc2 hc.le
  unfold materialize
  dsimp only
  split
  · next h0 =>
    exact FAt.pureC fun _ => ⟨hc2, hc, rfl, rfl, fun Ψ _ => by rw [h0, ofK_gpow_zero, mul_one],
      fun _ _ _ hb => hb⟩
  · refine FAt.guard fun hlt => ?_
    refine FAt.get_bind (FAt.withCOk fun hc0 => ?_)
    have hmats : ∀ p ∈ (st.scope.mats.get? c).getD [], (2 ≤ p.2 ∧ p.2 < st.next) ∧
        ∀ Ψ, C Ψ → Ψ p.2 = Ψ c * ofK (addressOfIndex p.1) := by
      intro p hp
      cases hm : st.scope.mats.get? c with
      | none => rw [hm] at hp; simp at hp
      | some l =>
        rw [hm] at hp
        exact ⟨hc0.cells.mats c l hm p hp, fun Ψ hΨ => (hc0.pools Ψ hΨ).mats c l hm p hp⟩
    split
    · next e o hfind =>
      have hp := hmats (e, o) (List.mem_of_find?_eq_some hfind)
      have he : e = exp := by simpa using List.find?_some hfind
      subst he
      exact FAt.pureC fun _ => ⟨hp.1.1, hp.1.2, rfl, rfl, hp.2, fun _ _ _ hb => hb⟩
    · generalize hpair : matStart st.scope c exp ((st.scope.mats.get? c).getD []) = pr
      obtain ⟨src, dist⟩ := pr
      dsimp only
      obtain ⟨e, hed, hsrc⟩ := matStart_spec hpair
      have hsrc' : (2 ≤ src ∧ src < st.next) ∧
          ∀ Ψ, C Ψ → Ψ src = Ψ c * ofK (addressOfIndex e) := by
        rcases hsrc with h0 | hm
        · cases h0
          exact ⟨⟨hc2, hc⟩, fun Ψ _ => by rw [ofK_gpow_zero, mul_one]⟩
        · exact hmats (e, src) hm
      have hdist : dist < 2 ^ 128 := by omega
      refine FAt.bind (constCell_fatB (gpowLimbs dist) (hok.kconst _ _) h2)
        fun k st₁ C₁ hs₁ hn₁ _ ⟨hk2, hk, hlo₁, hr₁, hkw, hkb⟩ => FAt.withCOk fun hc1 => ?_
      refine FAt.bind (mulCell_fat hsrc'.1.1 (lt_of_lt_of_le hsrc'.1.2 hn₁) hk2 hk)
        fun o st₂ C₂ hs₂ _ _ ⟨ho2, ho, hlo₂, hr₂, how, hmb⟩ => ?_
      have hw : ∀ Ψ, C₂ Ψ → Ψ o = Ψ c * ofK (addressOfIndex exp) := fun Ψ hΨ => by
        rw [how Ψ hΨ, hsrc'.2 Ψ (hs₁ Ψ (hs₂ Ψ hΨ)), hkw Ψ (hs₂ Ψ hΨ), word_gpow hdist, mul_assoc,
          ofK_gpow_add, hed]
      refine FAt.bind (FAt.modify rfl rfl rfl fun hc' => hc'.withScope
        (fun Ψ hΨ hp => hp.insertMats fun p hp' => ?_)
        (fun hs => { hs with mats := nmap_insert_imp hs.mats fun p hp' => ?_ }))
        fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => ?_
      · rcases List.mem_append.mp hp' with hp' | hp'
        · exact (hmats p hp').2 Ψ (hs₁ Ψ (hs₂ Ψ hΨ))
        · obtain rfl := List.mem_singleton.mp hp'
          exact hw Ψ hΨ
      · rcases List.mem_append.mp hp' with hp' | hp'
        · exact ⟨(hmats p hp').1.1, lt_of_lt_of_le (hmats p hp').1.2 (le_trans hn₁ ‹_›)⟩
        · obtain rfl := List.mem_singleton.mp hp'
          exact ⟨ho2, ho⟩
      · subst hC₃ hst₃
        refine FAt.pure ⟨ho2, ho, hlo₂.trans hlo₁, hr₂.trans hr₁, hw, fun ⟨a, ha⟩ c' hc' hb =>
          hmb c' (lt_of_lt_of_le hc' hn₁) ?_ ?_ (hkb c' hc' hb)⟩
        · exact (fixed_ne hc0.sat hb (a := a * ofK (addressOfIndex e))
            fun Ψ hΨ => by rw [hsrc'.2 Ψ hΨ, ha Ψ hΨ]).symm
        · exact (fixed_ne hc1.sat (hkb c' hc' hb) hkw).symm

/-- A pooled constant keeps the products and only extends the output. -/
theorem constCell_muls (k : ℕ × ℕ) : wpP (constCell k) ctx st fun _ st' =>
    st'.scope.muls = st.scope.muls ∧ ∀ x ∈ st.out.toList, x ∈ st'.out.toList := by
  rw [constCell_eq]
  unfold pooledCell fresh emitOp takeHints push
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_pure.mpr ⟨rfl, fun _ h => h⟩
  · simp only [wp_bind, wp_modifyGet, wp_modify, wp_pure]
    exact ⟨by simp, fun _ h => by simp [h]⟩

/-- **A shifted pointer made a value is no temporary's cell**: a cell of the pools of products
and shifted pointers, or a fresh one a `MUL` writes. -/
theorem materialize_nt (c : Cell) (exp : ℕ) (hok : I.Ok) :
    wpP (materialize c exp) ctx st fun o st' => exp ≠ 0 → ∀ s : St,
      (∀ x ∈ st'.out.toList, x ∈ s.out.toList) → OutOps I s →
      (OutOps I st → PoolNT I st.scope) → ¬ I.tc o := by
  by_cases he : exp = 0
  · exact fun _ _ _ h => absurd he h
  unfold materialize
  dsimp only
  simp only [he, ↓reduceIte]
  split
  · exact wp_bind.mpr wp_failP
  · refine wp_bind.mpr (wp_get.mpr ?_)
    split
    · next e o hfind =>
      refine wp_pure.mpr fun _ s hsub hout hp => ?_
      have hm := List.mem_of_find?_eq_some hfind
      cases hmc : st.scope.mats.get? c with
      | none => rw [hmc] at hm; simp at hm
      | some l =>
        rw [hmc] at hm
        exact (hp (hout.sub hsub)).2 c l hmc _ hm
    · generalize matStart _ _ _ _ = pr
      obtain ⟨src, dist⟩ := pr
      dsimp only
      refine wp_bind.mpr (wp_mono (constCell_muls _) fun k s₁ ⟨hm₁, hs₁⟩ => ?_)
      rw [mulCell_eq]
      unfold pooledCell
      refine wp_bind.mpr (wp_bind.mpr (wp_get.mpr ?_))
      split
      · next o ho =>
        refine wp_pure.mpr (wp_bind.mpr (wp_modify.mpr (wp_pure.mpr fun _ s hsub hout hp => ?_)))
        have hs' : ∀ x ∈ st.out.toList, x ∈ s.out.toList := fun x hx => hsub x (hs₁ x hx)
        have ho' : s₁.scope.muls.get? (sorted src k) = some o := ho
        rw [hm₁] at ho'
        exact (hp (hout.sub hs')).1 _ o ho'
      · unfold fresh emitOp takeHints push
        simp only [wp_bind, wp_modifyGet, wp_modify, wp_pure]
        intro _ s hsub hout _ htc
        have hmem := hout s₁.pending.toList (LOp.mul src k s₁.next) (hsub _ (by simp))
        obtain ⟨p, hp, _⟩ := hok.tops _ htc _ hmem (by simp [opCells])
        cases hp

/-! ## Return areas -/

/-- **A return area placed**: the cells from `base`, below the next free one and blind to the
constraint, get the values' words. -/
theorem bindRunAssign_fat (vs : List V) (base : Cell) (hb : base + vs.length ≤ st.next)
    (hbl : ∀ Ψ k w, k < vs.length → C Ψ → C (Function.update Ψ (base + k) w)) :
    FAt ctx I C st (bindRun vs base) (fun _ C' st' => st'.next = st.next ∧ st'.rest = st.rest ∧
      st'.scope = st.scope ∧
      (∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨ v ∈ vs) ∧
      (∀ k (hk : k < vs.length), st'.locs[vs[k]]? = some (.cell (base + k))) ∧
      ∀ Ψ, C' Ψ → ∀ k (hk : k < vs.length), Ψ (base + k) = I.σ vs[k]) := by
  intro hc
  unfold bindRun
  refine wp_mono (bindRun_wp (ctx := ctx) base vs 0 st) fun _ st₁ ⟨he, hg, hnew, hk⟩ => ?_
  have hs : st₁.scope = st.scope := (congrArg St.scope he).trans rfl
  have hr : st₁.rest = st.rest := (congrArg St.rest he).trans rfl
  have ho : st₁.out = st.out := (congrArg St.out he).trans rfl
  have hn : st₁.next = st.next := (congrArg St.next he).trans rfl
  refine ⟨RunC I C vs base, ⟨runC_sat hbl hc.sat, by rw [hn]; exact runC_blind hc.blind hb,
    fun Ψ hΨ => by rw [hs]; exact (hc.pools Ψ hΨ.1).grow hg, by rw [hs, hn]; exact hc.cells⟩,
    fun _ h => h.1, by rw [hn], hg, ⟨[], by simp [ho], fun _ _ _ h => nomatch h⟩, hn, hr, hs, hnew,
    fun k hk' => by simpa using hk k hk', fun Ψ h => h.2⟩

/-! ## Message runs read in place -/

theorem filterMap_full {α β : Type} (f : α → Option β) : ∀ (l : List α),
    (l.filterMap f).length = l.length → ∀ k (hk : k < l.length), f l[k] = (l.filterMap f)[k]?
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: l, h, k, hk => by
      cases ha : f a with
      | none =>
        simp only [List.filterMap_cons, ha, List.length_cons] at h
        have := List.length_filterMap_le f l
        omega
      | some b =>
        simp only [List.filterMap_cons, ha, List.length_cons, Nat.add_right_cancel_iff] at h
        cases k with
        | zero => simp [ha]
        | succ k =>
          simp only [List.filterMap_cons, ha, List.getElem_cons_succ,
            List.getElem?_cons_succ]
          exact filterMap_full f l h k (by simpa using hk)

/-- **A message run read in place**: each value of the run is the destination of the copy at its
index among the next statements, whose source is in the cell `base + k`. -/
theorem spongeInPlace_spec {vs : List V} {up : List Stmt} :
    wpP (spongeInPlace vs up) ctx st fun r st' => st' = st ∧ ∀ base, r = some base →
      ∀ k (hk : k < vs.length), ∃ s, up[k]? = some (.atom (.copy vs[k] s)) ∧
        st.locs[s]? = some (.cell (base + k)) := by
  unfold spongeInPlace
  refine wp_bind.mpr (wp_get.mpr ?_)
  dsimp only
  split
  · exact wp_pure.mpr ⟨rfl, fun _ h => nomatch h⟩
  · next base rest hsrcs =>
    refine wp_pure.mpr ⟨rfl, fun b hb k hk => ?_⟩
    split at hb
    · next hc =>
      cases hb
      rw [hsrcs] at hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      obtain ⟨⟨_, hlen⟩, hcons⟩ := hc
      have hlen' := hlen
      rw [← hsrcs] at hlen'
      have hl : ((up.take vs.length).zipIdx).length = vs.length := by
        have := hlen'.symm.trans_le (List.length_filterMap_le _ _)
        simp only [List.length_zipIdx, List.length_take] at this ⊢
        omega
      have hfull := filterMap_full _ _ (hlen'.trans hl.symm) k (by rw [hl]; exact hk)
      rw [hsrcs] at hfull
      have hk' : k < (base :: rest).length := by rw [hlen]; exact hk
      rw [List.getElem?_eq_getElem hk', consecutiveFrom_getElem hcons k hk'] at hfull
      have hku : k < up.length := by
        simp only [List.length_zipIdx, List.length_take] at hl
        omega
      simp only [List.getElem_zipIdx, List.getElem_take, Nat.zero_add] at hfull
      split at hfull
      · next d s k' heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hst, rfl⟩ := heq
        split at hfull
        · next hd =>
          split at hfull
          · next n hn =>
            cases hfull
            refine ⟨s, ?_, hn⟩
            rw [List.getElem?_eq_getElem hku, hst]
            have : vs[k]? = some d := by simpa using hd
            rw [List.getElem?_eq_getElem hk] at this
            cases this
            rfl
          · cases hfull
        · cases hfull
      · cases hfull
    · cases hb

/-! ## Loads and the frame's own pointer -/

/-- **A load emitted** into a good cell below the next free one: the `DEREF` holds and the pool
learns the load, given the pointer in `K` and the word read (a temporary's load in its cell). -/
theorem emitDeref_fat {ptr off dst : Cell} (hp2 : 2 ≤ ptr) (hd2 : 2 ≤ dst) (hd : dst < st.next)
    (hk : ∀ Ψ, C Ψ → IsInK (Ψ ptr))
    (hrd : ∀ Ψ, C Ψ → ((Fits I st ∧ ¬ I.tc dst) ∨ ∀ t ∈ I.tmps, cellP st.locs t ≠ some dst) →
      ∀ rd, I.Rd rd → rd ((Ψ ptr).limb 0 * addressOfIndex off) = some (Ψ dst))
    (htl : Fits I st → OutOps I (emitted st (.deref ptr off dst .cell)) →
      ∀ Ψ, C Ψ → I.tc dst → I.TL (Ψ ptr) off dst) :
    FAt ctx I C st (emitDeref ptr off dst) (fun _ C' st' => C' = C ∧ st'.next = st.next ∧
      st'.locs = st.locs ∧ st'.rest = st.rest) := by
  unfold emitDeref
  refine FAt.bind (emitOp_fatO _ fun hz hm Ψ hΨ => ?_) fun _ st₁ C₁ _ _ _ ⟨hC₁, hst₁⟩ => ?_
  · show IsInK (fw I Ψ ptr) ∧ (I.tc dst → I.TL (fw I Ψ ptr) off dst) ∧
      (¬ I.tc dst → ∀ rd, FrameRd I Ψ rd → I.Rd rd →
        rd ((fw I Ψ ptr).limb 0 * addressOfIndex off) = some (fw I Ψ dst))
    rw [fw_of_two hp2, fw_of_two hd2]
    exact ⟨hk Ψ hΨ, htl hz hm Ψ hΨ, fun ht rd _ hr => hrd Ψ hΨ (Or.inl ⟨hz, ht⟩) rd hr⟩
  · subst hC₁ hst₁
    refine FAt.mono (FAt.modify rfl rfl rfl fun hc => hc.withScope
      (fun Ψ hΨ hp => hp.insertLoad ⟨hk Ψ hΨ, fun ht => hrd Ψ hΨ (Or.inr ht)⟩)
      (fun hs => { hs with loads := pmap_insertIfNew_imp hs.loads ⟨hd2, hd⟩ }))
      fun _ C' st' _ _ _ ⟨h1, h2⟩ => ?_
    subst h1 h2
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The frame's own pointer**: in `main` the pooled `1`, else the cell read back from a one-cell
buffer whose word is the address of that cell, `g^(fp + o)`. -/
theorem selfFp_fat (hok : I.Ok) (hmain : ctx.isMain = true → I.fp = 0) (h2 : 2 ≤ st.next) :
    FAt ctx I C st selfFp (fun o C' st' => 2 ≤ o ∧ o < st'.next ∧ st'.locs = st.locs ∧
      st'.rest = st.rest ∧ (∀ Ψ, C' Ψ → Ψ o = I.fpw) ∧ KeepB C C' st.next) := by
  unfold selfFp
  refine FAt.read_bind ?_
  by_cases hm : ctx.isMain = true
  · simp only [hm, ↓reduceIte]
    refine FAt.mono (constCell_fatB (1, 0) (hok.kconst _ _) h2)
      fun o C' st' _ _ _ ⟨ha, hb, hc, hd, he, hf⟩ => ⟨ha, hb, hc, hd, fun Ψ h => ?_, hf⟩
    rw [he Ψ h, word_one, Inst.fpw, hmain hm, ofK_gpow_zero]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    refine FAt.get_bind ?_
    split
    · next o ho =>
      exact FAt.pureC fun hc => ⟨(hc.cells.selfFp o ho).1, (hc.cells.selfFp o ho).2, rfl, rfl,
        fun Ψ hΨ => (hc.pools Ψ hΨ).selfFp o ho, KeepB.refl C _⟩
    · intro hc
      simp only [fresh, pushHint, emitOp, takeHints, push, wp_bind, wp_modifyGet, wp_modify,
        wp_pure]
      have hq : WBlind (fun _ => ofK (addressOfIndex (I.fp + (st.next + 1)))) st.next :=
        wblind_const _ _
      have hc₂ := ((hc.assign hq).assign (wblind_const I.fpw _)).withScope
        (fun Ψ hΨ hp => hp.setSelfFp (o := st.next + 1) hΨ.2)
        (fun hs => { hs with selfFp := fun o' h => by cases h; exact ⟨le_trans h2 (Nat.le_succ _), Nat.lt_succ_self _⟩ })
      refine ⟨_, hc₂, fun _ h => h.1.1, ?_, LocsLe.refl _,
        EmitsW.of_ops (ops := [.op (st.pending.push (.resolved (.alloc st.next 1))).toList
          (.deref st.next 0 0 .fp), .op (#[] : Array LHint).toList
          (.deref st.next 0 (st.next + 1) .cell)]) (by simp) fun hz hops s hs => ?_, ?_⟩
      · exact le_trans (Nat.le_succ _) (Nat.le_succ _)
      swap
      · refine ⟨le_trans h2 (Nat.le_succ _), Nat.lt_succ_self _, ?_⟩
        simp only [true_and]
        exact ⟨fun Ψ h => h.2, fun c hc hb Ψ x h => ⟨⟨hb Ψ x h.1.1, by
          rw [Function.update_of_ne (Nat.ne_of_gt hc)]; exact h.1.2⟩, by
          rw [Function.update_of_ne (by omega)]; exact h.2⟩⟩
      have hsf : ¬ I.tc (st.next + 1) := fun ht => by
        obtain ⟨p, hp, hq⟩ := hok.tops _ ht _ (hops _ _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (by simp [opCells])
        cases hp
        exact hq _ _ _ (hops _ _ List.mem_cons_self) rfl
      have hfr : ∀ Ψ, ((C Ψ ∧ Ψ st.next = ofK (addressOfIndex (I.fp + (st.next + 1)))) ∧
          Ψ (st.next + 1) = I.fpw) → IsInK (fw I Ψ st.next) ∧ ∀ rd, FrameRd I Ψ rd →
          rd ((fw I Ψ st.next).limb 0 * addressOfIndex 0) = some (fw I Ψ (st.next + 1)) := by
        intro Ψ hΨ
        rw [fw_of_two h2, fw_of_two (le_trans h2 (Nat.le_succ _)), hΨ.1.2]
        refine ⟨isInK_ofK _, fun rd hr => ?_⟩
        have hlimb : (ofK (addressOfIndex (I.fp + (st.next + 1)))).limb 0 * addressOfIndex 0 =
            addressOfIndex (I.fp + (st.next + 1)) := by simp [addressOfIndex]
        rw [hlimb]
        have hsz : st.next + 1 + 1 ≤ I.size := hz.1
        exact hr.2.2 _ (le_trans h2 (Nat.le_succ _)) hsz hsf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · refine ⟨_, _, rfl, fun Ψ hΨ => ?_⟩
        obtain ⟨hk, hr⟩ := hfr Ψ hΨ
        refine ⟨hk, fun rd hrd _ => ?_⟩
        rw [hr rd hrd, fw_of_two (le_trans h2 (Nat.le_succ _)), hΨ.2]
      · refine ⟨_, _, rfl, fun Ψ hΨ => ?_⟩
        obtain ⟨hk, hr⟩ := hfr Ψ hΨ
        exact ⟨hk, fun h => absurd h hsf, fun _ rd hrd _ => hr rd hrd⟩

/-! ## Known values through a flush -/

theorem VW.grow {ok ok' : V → Prop} {C' : (ℕ → E) → Prop} {st' : St} (h : VW I C st ok)
    (hs : Stronger C' C) (hn : st.next ≤ st'.next) (hl : LocsLe st.locs st'.locs)
    (hok : ∀ v l, ok' v → st.locs[v]? = some l → ok v)
    (hnew : ∀ v l, ok' v → st'.locs[v]? = some l → st.locs[v]? = none →
      2 ≤ locBase l ∧ locBase l < st'.next ∧ ∀ Ψ, C' Ψ → locW Ψ l = I.σ v) :
    VW I C' st' ok' := fun v l hv hl' => by
  cases hv0 : st.locs[v]? with
  | none => exact hnew v l hv hl' hv0
  | some l0 =>
    have e := hl v l0 hv0
    rw [hl'] at e
    cases e
    obtain ⟨a, b, c⟩ := h v l (hok v l hv hv0) hv0
    exact ⟨a, lt_of_lt_of_le b hn, fun Ψ hΨ => c Ψ (hs Ψ hΨ)⟩

theorem VW.anti {ok ok' : V → Prop} (h : VW I C st ok) (hok : ∀ v, ok' v → ok v) :
    VW I C st ok' := fun v l hv hl => h v l (hok v hv) hl

/-- What a flush keeps of the known values: the places it adds are cells, and the values placed
before and known, or placed by it, have their words. -/
def FlushR (I : Inst) (C' : (ℕ → E) → Prop) (st st' : St) (ok : V → Prop) : Prop :=
  (∀ (v : V) (l : Loc), st'.locs[v]? = some l → st.locs[v]? = some l ∨ ∃ c, l = Loc.cell c) ∧
    VW I C' st' (fun v => ok v ∨ st.locs[v]? = none)

theorem FlushR.refl {ok : V → Prop} (h : VW I C st ok) : FlushR I C st st ok :=
  ⟨fun _ _ hl => Or.inl hl, fun v l hv hl => hv.elim (fun h' => h v l h' hl) fun h0 => by
    rw [h0] at hl
    cases hl⟩

theorem FlushR.same {ok : V → Prop} {st' : St} (h : VW I C st ok) (hl : st'.locs = st.locs)
    (hn : st'.next = st.next) : FlushR I C st st' ok := by
  have := FlushR.refl h
  unfold FlushR VW at this ⊢
  rw [hl, hn]
  exact this

theorem FlushR.right {ok : V → Prop} {C' : (ℕ → E) → Prop} {st₁ st₂ : St}
    (h : FlushR I C' st st₁ ok) (hl : st₂.locs = st₁.locs) (hn : st₂.next = st₁.next) :
    FlushR I C' st st₂ ok := by
  unfold FlushR VW at h ⊢
  rw [hl, hn]
  exact h

theorem FlushR.trans {ok : V → Prop} {C₁ C₂ : (ℕ → E) → Prop} {st₁ st₂ : St}
    (h₁ : FlushR I C₁ st st₁ ok) (h₂ : FlushR I C₂ st₁ st₂ (fun v => ok v ∨ st.locs[v]? = none)) :
    FlushR I C₂ st st₂ ok :=
  ⟨fun v l hl => (h₂.1 v l hl).elim (h₁.1 v l) Or.inr,
    h₂.2.anti fun _ hv => Or.inl hv⟩

theorem FlushR.of_locs {ok : V → Prop} {C' : (ℕ → E) → Prop} {st₁ st' : St}
    (h : FlushR I C' st₁ st' ok) (he : st₁.locs = st.locs) : FlushR I C' st st' ok := by
  unfold FlushR at h ⊢
  rw [← he]
  exact h

/-- The places a run adds have their words. -/
theorem run_new {vs : List V} {base : ℕ} {C' : (ℕ → E) → Prop} {st' : St}
    (hbk : ∀ k < vs.length, 2 ≤ base + k ∧ base + k < st'.next)
    (hnew : ∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨ v ∈ vs)
    (hk : ∀ k (hk : k < vs.length), st'.locs[vs[k]]? = some (.cell (base + k)))
    (hw : ∀ Ψ, C' Ψ → ∀ k (hk : k < vs.length), Ψ (base + k) = I.σ vs[k]) {ok : V → Prop}
    (h : VW I C st ok) (hs : Stronger C' C) (hn : st.next ≤ st'.next)
    (hl : LocsLe st.locs st'.locs) :
    FlushR I C' st st' ok := by
  have hc : ∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨
      ∃ k, ∃ hk : k < vs.length, vs[k] = v ∧ l = Loc.cell (base + k) := by
    intro v l hl'
    rcases hnew v l hl' with h' | h'
    · exact Or.inl h'
    · obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem h'
      rw [hk k hk'] at hl'
      cases hl'
      exact Or.inr ⟨k, hk', rfl, rfl⟩
  refine ⟨fun v l hl' => (hc v l hl').imp_right fun ⟨k, _, _, e⟩ => ⟨_, e⟩,
    h.grow hs hn hl (fun v l hv h' => hv.resolve_right (by rw [h']; simp))
      fun v l _ hl' h0 => ?_⟩
  rcases hc v l hl' with h' | ⟨k, hk', rfl, rfl⟩
  · rw [h0] at h'
    cases h'
  · exact ⟨(hbk k hk').1, (hbk k hk').2, fun Ψ hΨ => hw Ψ hΨ k hk'⟩

theorem FAt.discard {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : FAt ctx I C st m R) :
    FAt ctx I C st (Functor.discard m) (fun _ C' st' => ∃ a, R a C' st') := by
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact FAt.bind h fun a _ _ _ _ _ hr => FAt.pure ⟨a, hr⟩

theorem FAt.peek_bind {β : Type} {f : Option Event → P β} {R : β → ((ℕ → E) → Prop) → St → Prop}
    (h : FAt ctx I C st (f st.rest.head?) R) : FAt ctx I C st (peek >>= f) R :=
  fun hc => wp_bind.mpr (wp_peek.mpr (h hc))

theorem advance_fat :
    FAt ctx I C st advance (fun _ C' st' => C' = C ∧ st' = { st with rest := st.rest.tail }) :=
  FAt.modify rfl rfl rfl id

/-- The return cells the constraint leaves free (before the path's return area). -/
def RetBlind (ctx : Ctx) (C : (ℕ → E) → Prop) : Prop :=
  ∀ k, k < ctx.retCells → BlindAt C (2 + ctx.argCells + k)

theorem ofK_addr_ne_zero (e : ℕ) : ofK (addressOfIndex e) ≠ 0 := by
  intro h0
  have h1 : (algebraMap K E) (addressOfIndex e) = 0 := h0
  have h2 := (map_eq_zero_iff (algebraMap K E) (algebraMap K E).injective).mp h1
  rw [addressOfIndex] at h2
  exact pow_ne_zero _ (by decide) h2

theorem newOf {st st' : St} {vs : List V}
    (hnew : ∀ v l, st'.locs[v]? = some l → st.locs[v]? = some l ∨ v ∈ vs) :
    ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ vs := fun v hv => by
  cases h : st'.locs[v]? with
  | none => exact absurd h hv
  | some l => exact (hnew v l h).imp (fun h' => by rw [h']; simp) id

theorem allocsOf_mono {l l' : List Event} (hsub : ∀ x, x ∈ l → x ∈ l') :
    ∀ v, v ∈ allocsOf l → v ∈ allocsOf l' := by
  intro v hv
  simp only [allocsOf, List.mem_flatMap] at hv ⊢
  obtain ⟨x, hx, h⟩ := hv
  exact ⟨x, hsub x hx, h⟩

theorem allocsOf_left {vs : List V} {k : Kind} {es : List Event} :
    ∀ v, v ∈ vs → v ∈ allocsOf (flushSeg (.alloc vs k :: es)) := fun v h => by
  show v ∈ List.flatMap _ (Event.alloc vs k :: flushSeg es)
  rw [List.flatMap_cons]
  exact List.mem_append_left _ h

theorem allocsOf_right {vs : List V} {k : Kind} {es : List Event} :
    ∀ v, v ∈ allocsOf (flushSeg es) → v ∈ allocsOf (flushSeg (.alloc vs k :: es)) := fun v h => by
  show v ∈ List.flatMap _ (Event.alloc vs k :: flushSeg es)
  rw [List.flatMap_cons]
  exact List.mem_append_right _ h

/-- **A value made**: its run's cells and words (`.cell`, `.padRun`, a message run not read in
place), a return area in return cells the constraint leaves free, a message run read in place
whose copies' events give each alias its word, or nothing placed (`.pooled`, `.addr`, `.site`).
Apart from a return area, the cells the constraint leaves free stay free. -/
theorem onAlloc_fat (vs : List V) (kind : Kind) (up : List Stmt) {ok : V → Prop}
    (hcp : ∀ (k : ℕ) (d s : V), (∀ j < k, ∃ a, up[j]? = some (Stmt.atom a)) →
      up[k]? = some (Stmt.atom (.copy d s)) → ok s ∧ I.σ d = I.σ s)
    (hret : kind = .ret → 2 + ctx.argCells + vs.length ≤ st.next ∧
      ∀ k, k < vs.length → BlindAt C (2 + ctx.argCells + k))
    (h2 : 2 ≤ st.next) (hv : VW I C st ok) :
    FAt ctx I C st (onAlloc vs kind up) (fun _ C' st' => st'.rest = st.rest ∧
      FlushR I C' st st' ok ∧ (kind ≠ .ret → ∀ c, c < st.next → BlindAt C c → BlindAt C' c) ∧
      ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ vs) := by
  have hrun : FAt ctx I C st (takeRun vs) (fun _ C' st' => st'.rest = st.rest ∧
      FlushR I C' st st' ok ∧ (kind ≠ .ret → ∀ c, c < st.next → BlindAt C c → BlindAt C' c) ∧
      ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ vs) :=
    FAt.mono (takeRun_fat vs) fun _ C' st' hs hn hl ⟨hnx, hr, _, hnew, hk, hw, hwb⟩ =>
      ⟨hr, run_new (fun k hk => ⟨by simp only [Cell] at *; omega, by simp only [Cell] at *; omega⟩)
        hnew hk hw hv hs hn hl, fun _ => hwb, newOf hnew⟩
  unfold onAlloc
  cases kind with
  | cell => exact hrun
  | pooled =>
    exact FAt.quiet rfl rfl rfl rfl ⟨rfl, FlushR.same hv rfl rfl, fun _ _ _ hb => hb,
      fun _ h => Or.inl h⟩
  | addr =>
    exact FAt.quiet rfl rfl rfl rfl ⟨rfl, FlushR.same hv rfl rfl, fun _ _ _ hb => hb,
      fun _ h => Or.inl h⟩
  | site => exact FAt.pure ⟨rfl, FlushR.refl hv, fun _ _ _ hb => hb, fun _ h => Or.inl h⟩
  | ret =>
    obtain ⟨hb, hbl⟩ := hret rfl
    refine FAt.read_bind (FAt.mono (bindRunAssign_fat vs _ hb fun Ψ k w hk h => hbl k hk Ψ w h)
      fun _ C' st' hs hn hl ⟨_, hr, _, hnew, hk, hw⟩ => ⟨hr, ?_, fun h => absurd rfl h, newOf hnew⟩)
    exact run_new (fun k hk => ⟨by simp only [Cell] at *; omega, by simp only [Cell] at *; omega⟩)
      hnew hk hw hv hs hn hl
  | padRun =>
    exact FAt.bind hrun fun _ st₁ C₁ _ _ _ hr =>
      FAt.quiet rfl rfl rfl rfl ⟨hr.1, hr.2.1.right rfl rfl, hr.2.2.1, hr.2.2.2⟩
  | spongeRun =>
    refine FAt.bind (FAt.ofSame (R := fun r C' st' => C' = C ∧ st = st' ∧ ∀ base, r = some base →
        ∀ k (hk : k < vs.length), ∃ s, up[k]? = some (.atom (.copy vs[k] s)) ∧
          st.locs[s]? = some (.cell (base + k)))
      (wp_mono spongeInPlace_spec fun r st' ⟨he, h⟩ => ⟨by rw [he], by rw [he], by rw [he],
        by rw [he]; exact LocsLe.refl _, rfl, he.symm, h⟩))
      fun r st₁ C₁ hs₁ _ _ ⟨hC₁, he₁, hal⟩ => ?_
    subst hC₁ he₁
    cases r with
    | none => exact hrun
    | some base =>
      refine FAt.bind (bindRun_fat vs base) fun _ st₂ C₂ hs₂ hn₂ hl₂ ⟨hC, he, hnew, hk⟩ => ?_
      subst hC
      refine FAt.quiet rfl rfl rfl rfl ⟨(congrArg St.rest he).trans rfl, ?_,
        fun _ _ _ hb => hb, newOf hnew⟩
      have hal' := hal base rfl
      have hn₂' : st₂.next = st.next := (congrArg St.next he).trans rfl
      refine run_new (base := base) (vs := vs) (fun k hk => ?_) hnew hk
        (fun Ψ hΨ k hk => ?_) hv hs₁ hn₂ hl₂
      · obtain ⟨s, hu, hs⟩ := hal' k hk
        obtain ⟨hok, _⟩ := hcp k vs[k] s (fun j hj => let ⟨_, h, _⟩ := hal' j (by omega); ⟨_, h⟩) hu
        obtain ⟨a, b, _⟩ := hv s _ hok hs
        exact ⟨a, by rw [hn₂']; exact b⟩
      · obtain ⟨s, hu, hs⟩ := hal' k hk
        obtain ⟨hok, he'⟩ := hcp k vs[k] s
          (fun j hj => let ⟨_, h, _⟩ := hal' j (by omega); ⟨_, h⟩) hu
        obtain ⟨_, _, c⟩ := hv s _ hok hs
        exact (c Ψ (hs₁ Ψ hΨ)).trans he'.symm

/-! ## A flush, in lockstep with the scope walk -/

theorem RetBlind.keep {C' : (ℕ → E) → Prop} (h : RetBlind ctx C)
    (hab : 2 + ctx.argCells + ctx.retCells ≤ st.next)
    (hk : ∀ c, c < st.next → BlindAt C c → BlindAt C' c) : RetBlind ctx C' :=
  fun k hk' => hk _ (by simp only [Cell] at *; omega) (h k hk')

/-- A cell whose word times a nonzero shift is fixed is fixed. -/
theorem fixed_of_shift {x : ℕ} {e : ℕ} {a : E}
    (h : ∀ Ψ, C Ψ → Ψ x * ofK (addressOfIndex e) = a) :
    ∃ b, ∀ Ψ, C Ψ → Ψ x = b :=
  ⟨a * (ofK (addressOfIndex e))⁻¹, fun Ψ hΨ => by
    rw [← h Ψ hΨ, mul_assoc, mul_inv_cancel₀ (ofK_addr_ne_zero e), mul_one]⟩

/-- **A flush, step by step with `flushS`**: its trace is the scope walk's, the runs it places
have their words (`FlushR`), and the return cells stay free until the path's return area. -/
theorem flushN_lock (up : List Stmt) (hok : I.Ok) : ∀ (fuel : ℕ) (rs : List Event)
    (live : VMap Unit) (r : Bool) (s₁ : SSt) (ok : V → Prop) (st : St) (C : (ℕ → E) → Prop),
    flushS ctx.retCells rs live r = .ok s₁ → st.rest = rs → rs.length ≤ fuel →
    (∀ (k : ℕ) (d s : V), (∀ j < k, ∃ a, up[j]? = some (Stmt.atom a)) →
      up[k]? = some (Stmt.atom (.copy d s)) → ok s ∧ I.σ d = I.σ s) →
    (∀ v n e, Event.use v ∈ flushSeg rs → st.locs[v]? = some (.shifted n e) → ok v) →
    2 + ctx.argCells + ctx.retCells ≤ st.next → 2 ≤ st.next → VW I C st ok →
    (r = false → RetBlind ctx C) →
    FAt ctx I C st (flushN up fuel) (fun _ C' st' => st'.rest = s₁.rest ∧
      FlushR I C' st st' ok ∧ (s₁.retDone = false → RetBlind ctx C') ∧
      ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg rs))
  | fuel, [], live, r, s₁, ok, st, C, hfl, hst, _, _, _, _, _, hv, hb => by
      simp only [flushS] at hfl
      cases hfl
      cases fuel with
      | zero => exact FAt.pure ⟨hst, FlushR.refl hv, hb, fun _ h => Or.inl h⟩
      | succ fuel =>
        unfold flushN
        refine FAt.peek_bind ?_
        rw [hst]
        exact FAt.pure ⟨hst, FlushR.refl hv, hb, fun _ h => Or.inl h⟩
  | 0, e :: es, _, _, _, _, _, _, _, _, hlen, _, _, _, _, _, _ => absurd hlen (by simp)
  | fuel + 1, e :: es, live, r, s₁, ok, st, C, hfl, hst, hlen, hcp, huse, hab, h2, hv, hb => by
      have hlen' : es.length ≤ fuel := by simpa using hlen
      have hcp' : ∀ (k : ℕ) (d s : V), (∀ j < k, ∃ a, up[j]? = some (Stmt.atom a)) →
          up[k]? = some (Stmt.atom (.copy d s)) →
          (ok s ∨ st.locs[s]? = none) ∧ I.σ d = I.σ s :=
        fun k d s hl hu => let ⟨a, b⟩ := hcp k d s hl hu; ⟨Or.inl a, b⟩
      -- The rest of the flush after a step that keeps the places and the trace's tail.
      have hkeep : (∀ x, x ∈ flushSeg es → x ∈ flushSeg (e :: es)) →
          ∀ (r' : Bool) (st₂ : St) (C₂ : (ℕ → E) → Prop),
          flushS ctx.retCells es live r' = .ok s₁ → (r' = false → RetBlind ctx C₂) →
          Stronger C₂ C → st.next ≤ st₂.next → st₂.locs = st.locs → st₂.rest = st.rest.tail →
          FAt ctx I C₂ st₂ (flushN up fuel) (fun _ C' st' => st'.rest = s₁.rest ∧
            FlushR I C' st st' ok ∧ (s₁.retDone = false → RetBlind ctx C') ∧
            ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg (e :: es))) :=
        fun hsub r' st₂ C₂ hfl' hb' hs₂ hn₂ hlo₂ hr₂ => by
          refine FAt.mono (flushN_lock up hok fuel es live r' s₁ ok st₂ C₂ hfl'
            (by rw [hr₂, hst]; rfl) hlen' hcp
            (fun v n e hu hl => huse v n e (hsub _ hu) (by rw [← hlo₂]; exact hl))
            (le_trans hab hn₂) (le_trans h2 hn₂)
            (hv.grow hs₂ hn₂ (by rw [hlo₂]; exact LocsLe.refl _) (fun _ _ h _ => h)
              fun v l _ hl h0 => by rw [hlo₂, h0] at hl; cases hl) hb')
            fun _ C' st' _ _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2.of_locs hlo₂, h3, fun v hv' =>
              (h4 v hv').imp (fun h => by rw [← hlo₂]; exact h) (allocsOf_mono hsub v)⟩
      unfold flushN
      refine FAt.peek_bind ?_
      rw [hst]
      cases e with
      | alloc vs kind =>
        show FAt ctx I C st (advance >>= fun _ => onAlloc vs kind up >>= fun _ => flushN up fuel) _
        refine FAt.bind advance_fat fun _ st₁ C₁ _ _ _ ⟨hC₁, hst₁⟩ => ?_
        subst C₁ st₁
        have hret : r = false → kind = .ret → vs.length ≤ ctx.retCells ∧
            flushS ctx.retCells es (addLive live vs) true = .ok s₁ := by
          intro hr hk
          subst hr hk
          simp only [flushS, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true] at hfl
          split at hfl
          · cases hfl
          · exact ⟨by omega, hfl⟩
        have hnret : kind ≠ .ret → flushS ctx.retCells es (addLive live vs) r = .ok s₁ := by
          intro hk
          simp only [flushS] at hfl
          split at hfl
          · next h => exact absurd (by simpa using h) hk
          · exact hfl
        by_cases hk : kind = .ret
        · cases r with
          | true =>
            subst hk
            simp [flushS] at hfl
          | false =>
          obtain ⟨hlr, hfl'⟩ := hret rfl hk
          refine FAt.bind (onAlloc_fat (st := { st with rest := st.rest.tail }) vs kind up hcp
            (fun _ => ⟨by simp only [Cell] at *; omega, fun k hk' => hb rfl k (by omega)⟩) h2
            hv)
            fun _ st₂ C₂ hs₂ hn₂ _ ⟨hr₂, hf₂, _, hnw⟩ => ?_
          refine FAt.mono (flushN_lock up hok fuel es (addLive live vs) true s₁
            (fun v => ok v ∨ st.locs[v]? = none) st₂ C₂ hfl' (by rw [hr₂, hst]; rfl) hlen' hcp'
            (fun v n e hu hl => ?_) (le_trans hab hn₂) (le_trans h2 hn₂) hf₂.2 (by simp))
            fun _ C' st' _ _ _ ⟨h1, h3, h4, h5⟩ => ⟨h1, hf₂.trans h3, h4, fun v hv' =>
              (h5 v hv').elim (fun h => (hnw v h).imp id (allocsOf_left v))
                fun h => Or.inr (allocsOf_right v h)⟩
          rcases hf₂.1 v _ hl with h | ⟨c, hc⟩
          · exact Or.inl (huse v n e (List.mem_cons_of_mem _ hu) h)
          · cases hc
        · have hfl' := hnret hk
          refine FAt.bind (onAlloc_fat (st := { st with rest := st.rest.tail }) vs kind up hcp
            (fun h => absurd h hk) h2 hv)
            fun _ st₂ C₂ hs₂ hn₂ _ ⟨hr₂, hf₂, hkb, hnw⟩ => ?_
          refine FAt.mono (flushN_lock up hok fuel es (addLive live vs) r s₁
            (fun v => ok v ∨ st.locs[v]? = none) st₂ C₂ hfl' (by rw [hr₂, hst]; rfl) hlen' hcp'
            (fun v n e hu hl => ?_) (le_trans hab hn₂) (le_trans h2 hn₂) hf₂.2
            fun hr => (hb hr).keep hab (hkb hk))
            fun _ C' st' _ _ _ ⟨h1, h3, h4, h5⟩ => ⟨h1, hf₂.trans h3, h4, fun v hv' =>
              (h5 v hv').elim (fun h => (hnw v h).imp id (allocsOf_left v))
                fun h => Or.inr (allocsOf_right v h)⟩
          rcases hf₂.1 v _ hl with h | ⟨c, hc⟩
          · exact Or.inl (huse v n e (List.mem_cons_of_mem _ hu) h)
          · cases hc
      | use v =>
        have hfl' : flushS ctx.retCells es live r = .ok s₁ := by
          simp only [flushS] at hfl
          split at hfl
          · exact hfl
          · cases hfl
        refine FAt.bind advance_fat fun _ st₁ C₁ _ _ _ ⟨hC₁, hst₁⟩ => ?_
        subst C₁ st₁
        refine FAt.get_bind ?_
        split
        · next c e hc =>
          obtain ⟨a, b, hw⟩ := hv v _ (huse v c e List.mem_cons_self hc) hc
          refine FAt.bind (FAt.discard (materialize_fat (st := { st with rest := st.rest.tail })
            c e hok a b)) fun _ st₂ C₂ hs₂ hn₂ _ ⟨_, _, _, hlo₂, hr₂, _, hmb⟩ => ?_
          refine FAt.bind (FAt.modify rfl rfl rfl id) fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => ?_
          subst C₃ st₃
          exact hkeep (fun _ hx => List.mem_cons_of_mem _ hx) r _ C₂ hfl' (fun hr => (hb hr).keep hab
            (hmb (fixed_of_shift hw))) hs₂ hn₂ hlo₂ hr₂
        · exact FAt.bind (FAt.modify rfl rfl rfl id) fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => by
            subst C₃ st₃
            exact hkeep (fun _ hx => List.mem_cons_of_mem _ hx) r _ C hfl' hb (Stronger.refl C) le_rfl rfl rfl
      | shift v x =>
        have hfl' : flushS ctx.retCells es live r = .ok s₁ := by
          simp only [flushS] at hfl
          split at hfl
          · exact hfl
          · cases hfl
        refine FAt.bind advance_fat fun _ st₁ C₁ _ _ _ ⟨hC₁, hst₁⟩ => ?_
        subst C₁ st₁
        exact FAt.bind (FAt.modify rfl rfl rfl id) fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => by
          subst C₃ st₃
          exact hkeep (fun _ hx => List.mem_cons_of_mem _ hx) r _ C hfl' hb (Stronger.refl C) le_rfl rfl rfl
      | chain =>
        refine FAt.bind advance_fat fun _ st₁ C₁ _ _ _ ⟨hC₁, hst₁⟩ => ?_
        subst C₁ st₁
        exact FAt.bind (FAt.modify rfl rfl rfl id) fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => by
          subst C₃ st₃
          exact hkeep (fun _ hx => List.mem_cons_of_mem _ hx) r _ C hfl hb (Stronger.refl C) le_rfl rfl rfl
      | note n =>
        refine FAt.bind advance_fat fun _ st₁ C₁ _ _ _ ⟨hC₁, hst₁⟩ => ?_
        subst C₁ st₁
        exact FAt.bind (FAt.modify rfl rfl rfl id) fun _ st₃ C₃ _ _ _ ⟨hC₃, hst₃⟩ => by
          subst C₃ st₃
          exact hkeep (fun _ hx => List.mem_cons_of_mem _ hx) r _ C hfl hb (Stronger.refl C) le_rfl rfl rfl
      | emit =>
        simp only [flushS] at hfl
        cases hfl
        exact FAt.pure ⟨hst, FlushR.refl hv, hb, fun _ h => Or.inl h⟩
      | enter =>
        simp only [flushS] at hfl
        cases hfl
        exact FAt.pure ⟨hst, FlushR.refl hv, hb, fun _ h => Or.inl h⟩
      | leave =>
        simp only [flushS] at hfl
        cases hfl
        exact FAt.pure ⟨hst, FlushR.refl hv, hb, fun _ h => Or.inl h⟩

/-- `flushN` to the next statement, in lockstep with `flushS`. -/
theorem flush_lock (up : List Stmt) (hok : I.Ok) {live : VMap Unit} {r : Bool} {s₁ : SSt}
    {ok : V → Prop} (hfl : flushS ctx.retCells st.rest live r = .ok s₁)
    (hlen : st.rest.length ≤ ctx.fuel)
    (hcp : ∀ (k : ℕ) (d s : V), (∀ j < k, ∃ a, up[j]? = some (Stmt.atom a)) →
      up[k]? = some (Stmt.atom (.copy d s)) → ok s ∧ I.σ d = I.σ s)
    (huse : ∀ v n e, Event.use v ∈ flushSeg st.rest → st.locs[v]? = some (.shifted n e) → ok v)
    (hab : 2 + ctx.argCells + ctx.retCells ≤ st.next) (h2 : 2 ≤ st.next) (hv : VW I C st ok)
    (hb : r = false → RetBlind ctx C) :
    FAt ctx I C st (flush up) (fun _ C' st' => st'.rest = s₁.rest ∧
      FlushR I C' st st' ok ∧ (s₁.retDone = false → RetBlind ctx C') ∧
      ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest)) :=
  FAt.read_bind (flushN_lock up hok ctx.fuel st.rest live r s₁ ok st C hfl rfl hlen hcp huse hab
    h2 hv hb)

end Prims

end
end LeanVM.Compiler.Complete
