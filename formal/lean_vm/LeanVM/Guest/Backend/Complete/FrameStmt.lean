/-
  LeanVM.Guest.Backend.Complete.FrameStmt

  The walk's statements on the path, construct by construct: what the scope walk says of the
  flush before a statement, and the atom.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameBlock
public import LeanVM.Guest.Backend.Complete.FramePrims

/-!
# Statements on the path

A statement begins with a flush (`flush_lock`), which asks of the state that the source of every
copy among the next atoms is known or not placed yet, and that every shifted value a flushed `use`
names is known. The scope walk gives both: a value in scope at a later statement is in scope now or
made by the rest of the trace, and the rest of the trace makes values not placed yet (`WInv.fresh`).
`stmtW_atom` is `StmtW` for an atom.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The values a trace makes -/

theorem allocsOf_append (a b : List Event) : allocsOf (a ++ b) = allocsOf a ++ allocsOf b := by
  simp [allocsOf, List.flatMap_append]

theorem allocsOf_alloc (vs : List V) (k : Kind) (rs : List Event) :
    allocsOf (.alloc vs k :: rs) = vs ++ allocsOf rs := by
  simp [allocsOf]

theorem allocsOf_other {e : Event} (he : ∀ vs k, e ≠ .alloc vs k) (rs : List Event) :
    allocsOf (e :: rs) = allocsOf rs := by
  cases e <;> simp_all [allocsOf]

theorem addLive_contains : ∀ (vs : List V) (live : VMap Unit) (v : V),
    (addLive live vs).contains v = true → live.contains v = true ∨ v ∈ vs
  | [], _, _, h => Or.inl h
  | w :: ws, live, v, h => by
    rcases addLive_contains ws (live.insert w ()) v h with h' | h'
    · rw [KMap.contains_eq_isSome, KMap.getElem?_insert] at h'
      split at h'
      · next he => subst he; exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl (by rw [KMap.contains_eq_isSome]; exact h')
    · exact Or.inr (List.mem_cons_of_mem _ h')

/-! ## The scope walk -/

/-- **A flush of the scope walk** passes `flushSeg`; what is in scope after it, or is used in it,
was in scope before or is made by it. -/
theorem flushS_seg (rc : ℕ) : ∀ (rs : List Event) (live : VMap Unit) (r : Bool) (s₁ : SSt),
    flushS rc rs live r = .ok s₁ →
    rs = flushSeg rs ++ s₁.rest ∧
    (∀ v, s₁.live.contains v = true → live.contains v = true ∨ v ∈ allocsOf (flushSeg rs)) ∧
    (∀ v, Event.use v ∈ flushSeg rs → live.contains v = true ∨ v ∈ allocsOf (flushSeg rs))
  | [], live, r, s₁, h => by
    simp only [flushS, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => Or.inl h, fun _ h => by simp [flushSeg] at h⟩
  | e :: es, live, r, s₁, h => by
    cases e with
    | alloc vs kind =>
      obtain ⟨r', h'⟩ : ∃ r', flushS rc es (addLive live vs) r' = .ok s₁ := by
        simp only [flushS] at h
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      obtain ⟨h1, h2, h3⟩ := flushS_seg rc es _ r' s₁ h'
      simp only [flushSeg, allocsOf_alloc, List.cons_append, List.mem_cons, List.mem_append]
      have hl : ∀ v, (addLive live vs).contains v = true ∨ v ∈ allocsOf (flushSeg es) →
          live.contains v = true ∨ v ∈ vs ∨ v ∈ allocsOf (flushSeg es) := fun v h =>
        h.elim (fun h => (addLive_contains vs live v h).elim Or.inl fun h => Or.inr (Or.inl h))
          fun h => Or.inr (Or.inr h)
      refine ⟨by rw [← h1], fun v hv => hl v (h2 v hv), fun v hv => ?_⟩
      rcases hv with hv | hv
      · cases hv
      · exact hl v (h3 v hv)
    | use w =>
      simp only [flushS] at h
      split at h
      · next hc =>
        obtain ⟨h1, h2, h3⟩ := flushS_seg rc es live r s₁ h
        simp only [flushSeg, allocsOf_other (e := Event.use w) (fun _ _ h => nomatch h),
          List.cons_append, List.mem_cons]
        refine ⟨by rw [← h1], h2, fun v hv => ?_⟩
        rcases hv with hv | hv
        · cases hv
          exact Or.inl hc
        · exact h3 v hv
      · cases h
    | shift w x =>
      simp only [flushS] at h
      split at h
      · obtain ⟨h1, h2, h3⟩ := flushS_seg rc es live r s₁ h
        simp only [flushSeg, allocsOf_other (e := Event.shift w x) (fun _ _ h => nomatch h),
          List.cons_append, List.mem_cons]
        refine ⟨by rw [← h1], h2, fun v hv => ?_⟩
        rcases hv with hv | hv
        · cases hv
        · exact h3 v hv
      · cases h
    | chain =>
      simp only [flushS] at h
      obtain ⟨h1, h2, h3⟩ := flushS_seg rc es live r s₁ h
      simp only [flushSeg, allocsOf_other (e := Event.chain) (fun _ _ h => nomatch h),
        List.cons_append, List.mem_cons]
      refine ⟨by rw [← h1], h2, fun v hv => ?_⟩
      rcases hv with hv | hv
      · cases hv
      · exact h3 v hv
    | note n =>
      simp only [flushS] at h
      obtain ⟨h1, h2, h3⟩ := flushS_seg rc es live r s₁ h
      simp only [flushSeg, allocsOf_other (e := Event.note n) (fun _ _ h => nomatch h),
        List.cons_append, List.mem_cons]
      refine ⟨by rw [← h1], h2, fun v hv => ?_⟩
      rcases hv with hv | hv
      · cases hv
      · exact h3 v hv
    | emit =>
      simp only [flushS, Except.ok.injEq] at h
      subst h
      exact ⟨by simp [flushSeg], fun _ h => Or.inl h, fun _ h => by simp [flushSeg] at h⟩
    | enter =>
      simp only [flushS, Except.ok.injEq] at h
      subst h
      exact ⟨by simp [flushSeg], fun _ h => Or.inl h, fun _ h => by simp [flushSeg] at h⟩
    | leave =>
      simp only [flushS, Except.ok.injEq] at h
      subst h
      exact ⟨by simp [flushSeg], fun _ h => Or.inl h, fun _ h => by simp [flushSeg] at h⟩

/-- **A straight-line statement of the scope walk**: its flush, its `emit`, its own values in
scope. -/
theorem scopeFlat_inv {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeFlat rc st s = .ok s') :
    ∃ s₁, flushS rc s.rest s.live s.retDone = .ok s₁ ∧ s₁.rest = .emit :: s'.rest ∧
      s'.live = s₁.live ∧ s'.retDone = s₁.retDone ∧ ∀ v ∈ ownUses st, s'.live.contains v = true := by
  unfold scopeFlat flushAt at h
  split at h
  · cases h
  next s₁ h₁ =>
  split at h
  · cases h
  next s₂ h₂ =>
  split at h
  · cases h
  next h₃ =>
  split at h
  · cases h
  cases h
  unfold expectS at h₂
  split at h₂
  · next ev es hr =>
    split at h₂
    · next he =>
      cases h₂
      cases ev <;> simp [isEmit] at he
      refine ⟨s₁, h₁, hr, rfl, rfl, ?_⟩
      unfold needScope at h₃
      split at h₃
      · next hin =>
        intro v hv
        simp only [inScope, List.all_eq_true] at hin
        exact hin v hv
      · cases h₃
    · cases h₂
  · cases h₂

theorem scopeFlat_sub {rc : ℕ} {st : Stmt} {s s' : SSt} (h : scopeFlat rc st s = .ok s') :
    (∀ v, s'.live.contains v = true → s.live.contains v = true ∨ v ∈ allocsOf s.rest) ∧
    (∀ v ∈ allocsOf s'.rest, v ∈ allocsOf s.rest) := by
  obtain ⟨s₁, h₁, hr, hl, -, -⟩ := scopeFlat_inv h
  obtain ⟨e1, e2, -⟩ := flushS_seg rc _ _ _ s₁ h₁
  have ha : allocsOf s.rest = allocsOf (flushSeg s.rest) ++ allocsOf s'.rest := by
    conv_lhs => rw [e1]
    rw [allocsOf_append, hr, allocsOf_other (e := Event.emit) (fun _ _ h => nomatch h)]
  refine ⟨fun v hv => ?_, fun v hv => by rw [ha]; exact List.mem_append_right _ hv⟩
  rw [hl] at hv
  rcases e2 v hv with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [ha]; exact List.mem_append_left _ h)

/-- **The atoms a scoped block starts with** name values in scope at its start or made by the
rest of the trace. -/
theorem scope_lead (rc : ℕ) : ∀ (rest : List Stmt) (s s'' : SSt), scopeBlock rc rest s = .ok s'' →
    ∀ (k : ℕ) (a : Atom), (∀ j < k, ∃ b, rest[j]? = some (Stmt.atom b)) →
    rest[k]? = some (Stmt.atom a) → ∀ v ∈ ownUses (.atom a),
      s.live.contains v = true ∨ v ∈ allocsOf s.rest
  | [], _, _, _, _, _, _, h => nomatch h
  | st :: rest, s, s'', h, k, a, hj, hk => by
    rw [scopeBlock] at h
    split at h
    · cases h
    next s₁ h₁ =>
    cases k with
    | zero =>
      cases hk
      simp only [scopeStmt] at h₁
      obtain ⟨-, -, -, -, -, hu⟩ := scopeFlat_inv h₁
      intro v hv
      exact (scopeFlat_sub h₁).1 v (hu v hv)
    | succ k =>
      obtain ⟨b, hb⟩ := hj 0 (Nat.succ_pos k)
      cases hb
      simp only [scopeStmt] at h₁
      intro v hv
      rcases scope_lead rc rest s₁ s'' h k a (fun j hj' => hj (j + 1) (by omega)) hk v hv
        with h' | h'
      · exact (scopeFlat_sub h₁).1 v h'
      · exact Or.inr ((scopeFlat_sub h₁).2 v h')

/-! ## Combinators -/

section Comb

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

theorem expect_fat {e : Event → Bool} {what : String} {ev : Event} {es : List Event}
    (hr : st.rest = ev :: es) (he : e ev = true) :
    FAt ctx I C st (expect e what) (fun _ C' st' => C' = C ∧ st' = { st with rest := es }) := by
  unfold expect
  refine FAt.peek_bind ?_
  rw [hr]
  simp only [List.head?_cons, he, ↓reduceIte]
  refine FAt.mono advance_fat fun _ C' st' _ _ _ ⟨h1, h2⟩ => ⟨h1, ?_⟩
  rw [h2, hr]
  rfl

/-- An action's spec on the path with a fact of all its successes. -/
theorem FBAt.and_wp {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    {Q : α → St → Prop} (h : FBAt ctx I C st m R) (hq : wpP m ctx st Q) :
    FBAt ctx I C st m fun a C' st' => R a C' st' ∧ Q a st' :=
  fun hc a st' he =>
    let ⟨C', h1, h2, h3, h4, h5, h6⟩ := h hc a st' he
    ⟨C', h1, h2, h3, h4, h5, h6, hq a st' he⟩

end Comb

/-! ## Owed by the primitives' agent -/

/-- **`flush_lock` on the flushed events** (R1, R2 of the primitives' agent): the uses asked of
the flushed events only, and the places the flush adds are the values it makes. -/
def FlushSegStmt : Prop :=
  ∀ (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (up : List Stmt) (live : VMap Unit)
    (r : Bool) (s₁ : SSt) (ok : V → Prop), I.Ok →
    flushS ctx.retCells st.rest live r = .ok s₁ → st.rest.length ≤ ctx.fuel →
    (∀ (k : ℕ) (d s : V), (∀ j < k, ∃ a, up[j]? = some (Stmt.atom a)) →
      up[k]? = some (Stmt.atom (.copy d s)) → ok s ∧ I.σ d = I.σ s) →
    (∀ v n e, Event.use v ∈ flushSeg st.rest → st.locs[v]? = some (.shifted n e) → ok v) →
    2 + ctx.argCells + ctx.retCells ≤ st.next → 2 ≤ st.next → VW I C st ok →
    (r = false → RetBlind ctx C) →
    FAt ctx I C st (flush up) (fun _ C' st' => st'.rest = s₁.rest ∧
      FlushR I C' st st' ok ∧ (s₁.retDone = false → RetBlind ctx C') ∧
      ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest))

/-- **A statement leaves no `match` chaining out** if none did before it (P2 of the primitives'
agent, for statements other than a `match`). -/
def ChainKeep (ctx : Ctx) (s : Stmt) (rest : List Stmt) : Prop :=
  ∀ st : St, wpP (placeStmt s rest >>= fun _ => endStmt) ctx st fun _ st' =>
    st'.chainIn = st.chainIn

/-! ## Straight-line statements: the flush before, the invariant after -/

section Flat

variable {ctx : Ctx} {I : Inst}

/-- **A statement begins** (`beginStmt`) in lockstep with the scope walk's `scopeFlat`: the
values in scope after it are known, the return cells stay free until the path's return area, and
the flush places no value but those it makes. -/
theorem begin_fat (hflush : FlushSegStmt) (hI : I.Ok) {s : Stmt} {rest : List Stmt}
    {C : (ℕ → E) → Prop} {st : St} {sc sc' : SSt}
    (hsc : scopeFlat ctx.retCells s sc = .ok sc') (hinv : WInv ctx I C st sc)
    (hcp : ∀ (k : ℕ) (d x : V), (∀ j < k, ∃ b, (s :: rest)[j]? = some (Stmt.atom b)) →
      (s :: rest)[k]? = some (Stmt.atom (.copy d x)) →
      (sc.live.contains x = true ∨ st.locs[x]? = none) ∧ I.σ d = I.σ x) :
    FAt ctx I C st (beginStmt (s :: rest)) fun _ C₂ st₂ =>
      st₂.rest = sc'.rest ∧ VW I C₂ st₂ (fun v => sc'.live.contains v = true) ∧
      (sc'.retDone = false → RetBlind ctx C₂) ∧
      (∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest)) := by
  obtain ⟨s₁, hfl, hr₁, hl₁, hd₁, -⟩ := scopeFlat_inv hsc
  rw [hinv.rest] at hfl
  obtain ⟨hseg, hlive, huseS⟩ := flushS_seg _ _ _ _ _ hfl
  have hsegA : ∀ v ∈ allocsOf (flushSeg st.rest), st.locs[v]? = none := fun v hv =>
    (hinv.fresh v (by rw [hseg, allocsOf_append]; exact List.mem_append_left _ hv)).1
  have hokOf : ∀ v, sc'.live.contains v = true →
      sc.live.contains v = true ∨ st.locs[v]? = none := fun v hv => by
    rw [hl₁] at hv
    exact (hlive v hv).elim Or.inl fun h => Or.inr (hsegA v h)
  have huse : ∀ v n e, Event.use v ∈ flushSeg st.rest → st.locs[v]? = some (.shifted n e) →
      sc.live.contains v = true ∨ st.locs[v]? = none := fun v n e hv hl =>
    (huseS v hv).elim Or.inl fun h => absurd hl (by rw [hsegA v h]; simp)
  have hvw : VW I C st fun v => sc.live.contains v = true ∨ st.locs[v]? = none :=
    fun v l hv hl => hv.elim (fun h => hinv.vw v l h hl) fun h => by rw [h] at hl; cases hl
  unfold beginStmt
  refine FAt.bind (hflush ctx I C st _ sc.live sc.retDone s₁ _ hI hfl hinv.fuel hcp huse
    hinv.abi hinv.two hvw fun hr k hk Ψ w hC => hinv.ret hr Ψ k w hk hC)
    fun _ st₁ C₁ _ _ _ ⟨h1, h2, h3, h4⟩ => ?_
  refine FAt.mono (expect_fat (ev := .emit) (es := sc'.rest) (by rw [h1, hr₁]) rfl)
    fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
  subst hC hst
  exact ⟨rfl, (h2.right rfl rfl).2.anti fun v hv => Or.inl (hokOf v hv),
    by rw [hd₁]; exact h3, h4⟩

/-- **The invariant after a straight-line statement** that falls through: the constraint kept,
the trace and the values in scope the scope walk's, the values the rest of the trace makes not
placed by it. -/
theorem winv_flat {s : Stmt} {C C' : (ℕ → E) → Prop} {st st' : St} {sc sc' : SSt}
    (hsc : scopeFlat ctx.retCells s sc = .ok sc') (hinv : WInv ctx I C st sc)
    (hcok : COk I C' st'.next st'.scope st'.locs) (hn : st.next ≤ st'.next)
    (hr : st'.rest = sc'.rest) (hvw : VW I C' st' fun v => sc'.live.contains v = true)
    (hret : sc'.retDone = false → RetBlind ctx C')
    (hloc : ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨
      v ∈ allocsOf (flushSeg st.rest) ∨ sc'.live.contains v = true)
    (hch : st'.chainIn = none) : WInv ctx I C' st' sc' := by
  obtain ⟨s₁, hfl, hr₁, hl₁, -, -⟩ := scopeFlat_inv hsc
  rw [hinv.rest] at hfl
  obtain ⟨hseg, hlive, -⟩ := flushS_seg _ _ _ _ _ hfl
  have hall : allocsOf st.rest = allocsOf (flushSeg st.rest) ++ allocsOf sc'.rest := by
    conv_lhs => rw [hseg]
    rw [allocsOf_append, hr₁, allocsOf_other (e := Event.emit) (fun _ _ h => nomatch h)]
  have hnd : (allocsOf (flushSeg st.rest) ++ allocsOf sc'.rest).Nodup := hall ▸ hinv.nodup
  have hlen : sc'.rest.length ≤ st.rest.length := by
    have h' := congrArg List.length hseg
    rw [List.length_append, hr₁, List.length_cons] at h'
    omega
  have hfr : ∀ v ∈ allocsOf st'.rest, st'.locs[v]? = none ∧ sc'.live.contains v = false := by
    intro v hv
    rw [hr] at hv
    obtain ⟨hst, hlv⟩ := hinv.fresh v (by rw [hall]; exact List.mem_append_right _ hv)
    have hns : v ∉ allocsOf (flushSeg st.rest) := fun h => List.disjoint_of_nodup_append hnd h hv
    have hlv' : sc'.live.contains v = false := by
      cases hx : sc'.live.contains v with
      | false => rfl
      | true =>
        rw [hl₁] at hx
        exact ((hlive v hx).elim (fun h => by rw [hlv] at h; cases h) hns).elim
    refine ⟨?_, hlv'⟩
    cases hx : st'.locs[v]? with
    | none => rfl
    | some x =>
      rcases hloc v (by rw [hx]; simp) with h | h | h
      · exact absurd hst h
      · exact absurd h hns
      · rw [hlv'] at h
        cases h
  exact ⟨hcok, hr.symm, hvw, le_trans hinv.two hn, le_trans hinv.abi hn,
    by rw [hr]; exact le_trans hlen hinv.fuel, fun hr' Ψ k w hk hC => hret hr' k hk Ψ w hC,
    by rw [hr]; exact hnd.of_append_right, hfr, hch⟩

end Flat

/-! ## The atom -/

section Atom

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst}

/-- **An atom on the path**: its flush, its `emit`, the atom (`AtomFAt`), its end; its words are
straight-line instructions (`FAt.toBlk`). The atom is no frame address, and a store's value is
placed in no shifted pointer. -/
theorem stmtW_atom (hflush : FlushSegStmt) (hok : OpOK Γ I Ag cl) (hI : I.Ok)
    (hmain : ctx.isMain = true → I.fp = 0)
    (hRd : ∀ rd, I.Rd rd → ∀ e ∈ I.es, evNT rd I.σ e)
    {a : Atom} (hat : AtomFAt a) {rest tl : List Stmt} (hck : ChainKeep ctx (.atom a) rest)
    (hu : ∀ v ∈ Memory.atomUses a, v ∉ I.tmps) (ht : ∀ t ∈ Memory.atomTmps a, t ∈ I.tmps)
    (hnm : ∀ v ∈ Memory.atomUses a, v ∈ I.named)
    (hfa : ∀ p run, a ≠ .frameAddr p run)
    (hld : ∀ d p off, a = .load d p off → ∀ n e, I.locs[d]? ≠ some (.shifted n e)) :
    StmtW Γ Ag cl ctx I (.atom a) rest tl := by
  intro C st sc sc' i₀ o hsc ⟨sc'', hrest⟩ hw _ hes _ hup hinv
  simp only [walk1] at hw
  subst hw
  simp only [scopeStmt] at hsc
  obtain ⟨s₁, hfl, hr₁, -, -, hown⟩ := scopeFlat_inv hsc
  rw [hinv.rest] at hfl
  obtain ⟨hseg, -, -⟩ := flushS_seg _ _ _ _ _ hfl
  have hall : allocsOf st.rest = allocsOf (flushSeg st.rest) ++ allocsOf sc'.rest := by
    conv_lhs => rw [hseg]
    rw [allocsOf_append, hr₁, allocsOf_other (e := Event.emit) (fun _ _ h => nomatch h)]
  have hcopy : ∀ d s, Memory.Ev.atom (.copy d s) ∈ I.es → I.σ d = I.σ s := fun d s he => by
    obtain ⟨rd, hrd⟩ := hI.rd
    have := hRd rd hrd _ he
    simpa [evNT, holdsNT, Atom.Holds] using this
  have hok' : ∀ v, sc.live.contains v = true ∨ v ∈ allocsOf sc.rest →
      sc.live.contains v = true ∨ st.locs[v]? = none :=
    fun v h => h.elim Or.inl fun h => Or.inr (hinv.fresh v (by rwa [← hinv.rest])).1
  have hcp : ∀ (k : ℕ) (d s : V), (∀ j < k, ∃ b, (Stmt.atom a :: rest)[j]? = some (Stmt.atom b)) →
      (Stmt.atom a :: rest)[k]? = some (Stmt.atom (.copy d s)) →
      (sc.live.contains s = true ∨ st.locs[s]? = none) ∧ I.σ d = I.σ s := by
    intro k d s hj hk
    cases k with
    | zero =>
      cases hk
      exact ⟨hok' s ((scopeFlat_sub hsc).1 s (hown s (by simp [ownUses, atomUses]))),
        hcopy d s (hes _ (by simp [outEs]))⟩
    | succ k =>
      refine ⟨?_, hcopy d s (hup _ rfl k _ (fun j hj' => hj (j + 1) (by omega)) hk)⟩
      rcases scope_lead _ rest sc' sc'' hrest k _ (fun j hj' => hj (j + 1) (by omega)) hk s
        (by simp [ownUses, atomUses]) with h | h
      · exact hok' s ((scopeFlat_sub hsc).1 s h)
      · exact Or.inr (hinv.fresh s (by rw [hall]; exact List.mem_append_right _ h)).1
  have hA : FAt ctx I C st (beginStmt (.atom a :: rest) >>= fun _ => placeAtom a)
      fun _ C₃ st₃ => st₃.rest = sc'.rest ∧
        (Fits I st₃ → VW I C₃ st₃ fun v => sc'.live.contains v = true) ∧
        (sc'.retDone = false → RetBlind ctx C₃) ∧
        (∀ v, st₃.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest) ∨
          sc'.live.contains v = true) := by
    refine FAt.bind (begin_fat hflush hI hsc hinv hcp) fun _ st₂ C₂ _ hn₂ _ ⟨h1, h2, h3, h4⟩ => ?_
    refine FAt.mono (hat ctx I C₂ st₂ (fun v => sc'.live.contains v = true) hI hmain
      (hes _ (by simp [outEs]))
      (fun rd hrd => hRd rd hrd (Memory.Ev.atom a) (hes _ (by simp [outEs])))
      hu ht hnm (fun _ p run h => absurd h (hfa p run))
      (fun hF d p off hd n e hl => hld d p off hd n e (hF.2 _ _ hl))
      (le_trans hinv.two hn₂) h2 (fun v hv => Or.inl (hown v hv)))
      fun _ C₃ st₃ _ _ _ ⟨g1, g2, g3, g4⟩ => ⟨g2.trans h1,
        fun hF => (g1 hF).anti fun v hv => Or.inl hv,
        fun hr k hk => g4 (2 + ctx.argCells + k)
          (by have := hinv.abi; simp only [Cell] at *; omega) (h3 hr k hk),
        fun v hv => (g3 v hv).elim (fun h => (h4 v h).elim Or.inl fun h => Or.inr (Or.inl h))
          fun h => Or.inr (Or.inr (hown v h))⟩
  have hF : FAt ctx I C st ((beginStmt (.atom a :: rest) >>= fun _ => placeAtom a) >>=
      fun _ => endStmt) fun _ C₃ st₃ => st₃.rest = sc'.rest ∧
        (Fits I st₃ → VW I C₃ st₃ fun v => sc'.live.contains v = true) ∧
        (sc'.retDone = false → RetBlind ctx C₃) ∧
        (∀ v, st₃.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest) ∨
          sc'.live.contains v = true) :=
    FAt.bind hA fun _ st₃ C₃ _ _ _ hr => by
      unfold endStmt
      exact FAt.quiet rfl rfl rfl rfl hr
  rw [placeStmt]
  refine FBAt.mono (FBAt.and_wp (FAt.toBlk (main := ctx.isMain) (ss := [.atom a])
    (tl := rest ++ tl) (es := [.atom a]) (i₀ := i₀) hok rfl rfl hF) (hck st)) ?_
  rintro _ C' st' _ hn _ ⟨⟨hcok, ⟨h1, h2, h3, h4⟩, blk, hblk, hbw⟩, hch⟩
  have hch' : st'.chainIn = none := by rw [hch]; exact hinv.chain
  exact ⟨fun _ _ hF' => winv_flat hsc hinv hcok hn h1 (h2 hF') h3 h4 hch', hch',
    fun hF' => ⟨blk, hblk, hbw hF'⟩⟩

end Atom

/-! ## Control statements: a straight-line prefix, then the statement -/

section Ctl

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

/-- An on-path action, then a control placement from the state it reached, its emitted
instructions known. -/
theorem FBAt.fat_bind {α β : Type} {m : P α} {f : α → P β}
    {R₁ : α → ((ℕ → E) → Prop) → St → Prop} {R₂ : β → ((ℕ → E) → Prop) → St → Prop}
    (hm : FAt ctx I C st m R₁)
    (hf : ∀ a st₁ C₁, Stronger C₁ C → st.next ≤ st₁.next → LocsLe st.locs st₁.locs →
      COk I C₁ st₁.next st₁.scope st₁.locs → EmitsW I C₁ st st₁ → R₁ a C₁ st₁ →
      FBAt ctx I C₁ st₁ (f a) R₂) :
    FBAt ctx I C st (m >>= f) R₂ := by
  intro hc
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨C₁, hc₁, hs₁, hn₁, hl₁, hE₁, hr₁⟩ := hm hc a st₁ he
  obtain ⟨C₂, h0, hb, hs₂, hn₂, hl₂, hr₂⟩ := hf a st₁ C₁ hs₁ hn₁ hl₁ hc₁ hE₁ hr₁ hc₁ b st₂ he'
  exact ⟨C₂, h0, hb, hs₁.trans hs₂, le_trans hn₁ hn₂, hl₁.trans hl₂, hr₂⟩

/-- Emitted instructions from the start, one more action on. -/
theorem EmitsW.step {st₁ st₂ : St} {C₁ C₂ : (ℕ → E) → Prop} (h₁ : EmitsW I C₁ st st₁)
    (h₂ : EmitsW I C₂ st₁ st₂) (hs : Stronger C₂ C₁) (hn : st₁.next ≤ st₂.next)
    (hl : LocsLe st₁.locs st₂.locs) : EmitsW I C₂ st st₂ :=
  (h₁.mono hs).trans h₂ hn hl

theorem takeHints_fat :
    FAt ctx I C st takeHints (fun _ C' st' => C' = C ∧ st' = { st with pending := #[] }) :=
  fun hc => by
    unfold takeHints
    exact wp_modifyGet.mpr ⟨C, hc, Stronger.refl C, le_rfl, LocsLe.refl _,
      ⟨[], by simp, fun _ _ _ h => nomatch h⟩, rfl, rfl⟩

theorem cellAt_keep (v : V) : wpP (cellAt v) ctx st fun _ st' => st' = st := by
  unfold cellAt
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · exact wp_pure.mpr rfl
  · exact wp_failP

theorem mapM_cellAt_keep : ∀ (l : List V) (st : St),
    wpP (l.mapM cellAt) ctx st fun _ st' => st' = st
  | [], st => by
    rw [List.mapM_nil]
    exact wp_pure.mpr rfl
  | v :: l, st => by
    rw [List.mapM_cons]
    refine wp_bind.mpr (wp_mono (cellAt_keep v) fun _ st₁ h => ?_)
    subst h
    exact wp_bind.mpr (wp_mono (mapM_cellAt_keep l st₁) fun _ st₂ h => by
      subst h
      exact wp_pure.mpr rfl)

/-- A control statement pushed, then the statement's end. -/
theorem push_end {X : PStmt} {R : PUnit → ((ℕ → E) → Prop) → St → Prop}
    (h : ∀ st' : St, st'.out.toList = st.out.toList ++ [X] → st'.next = st.next →
      st'.locs = st.locs → R ⟨⟩ C st') :
    FBAt ctx I C st (push X >>= fun _ => endStmt) R := fun hc => by
  unfold push endStmt
  exact wp_bind.mpr (wp_modify.mpr (wp_modify.mpr ⟨C, hc.sat, hc.blind, Stronger.refl C, le_rfl,
    LocsLe.refl _, h _ (by simp) rfl rfl⟩))

theorem not_tc_of (hI : I.Ok) {o : LOp} (ho : o ∈ I.ops) {c : ℕ} (hc : c ∈ opCells o)
    (hnd : ∀ p, o ≠ .deref p 0 c .cell) : ¬ I.tc c := fun ht =>
  let ⟨p, hp, _⟩ := hI.tops c ht o ho hc
  hnd p hp

theorem fwd_patch {Ψ : ℕ → E} {σ' : Val} {kh : ℕ → E × E} {n : ℕ} (h2 : 2 ≤ n) (ht : ¬ I.tc n) :
    fwd I.hdr ⟨patchT I Ψ σ', kh⟩ n = Ψ n := by
  simp [fwd, patchT, show n ≠ 0 by omega, show n ≠ 1 by omega, ht]

end Ctl

section Ret

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst}

/-- The words of straight-line instructions the constraint gives, then one control statement. -/
theorem blkW_ops_ctl (hok : OpOK Γ I Ag cl) {C : (ℕ → E) → Prop} {ops : List PStmt}
    {X : PStmt} {main : Bool} {ss tl : List Stmt} {es : List Ev} {vs : List V} {i₀ : ℕ}
    (hc : calls es = [])
    (hW : (∀ h o, PStmt.op h o ∈ ops → o ∈ I.ops) →
      ∀ s ∈ ops, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C Ψ → OpW I Ψ o)
    (hX : ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ (kh : ℕ → E × E) (cs : List Stmt) (pos : ℕ)
      (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
      (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
      (∀ o' ∈ stmtOps X pos, o' ∈ I.ops) → (if main then khalt else kret) →
      wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl [X] cs pos ks next kj kret khalt) :
    BlkW Γ I main Ag cl C (ops ++ [X]) ss tl (.ret es vs) i₀ := by
  refine ⟨fun _ => [], fun _ => by simp [outEs, hc],
    fun Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hbo _ _ hk => ?_⟩
  rw [wLc_append _ _ _ _ _ _ _ ops [X] (List.cons_ne_nil _ _)]
  have hbo₁ : ∀ o' ∈ blockOps ops pos, o' ∈ I.ops := fun o' ho =>
    hbo o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  refine wLc_ops hok hΨ hσ kh ops (hW fun _ o hm => hbo₁ o (op_mem_blockOps ops pos hm)) pos hbo₁
    cs ks _ _ kret khalt (hX Ψ hΨ σ' hσ kh cs _ ks next kj kret khalt (fun o' ho => hbo o' (by
      rw [bops_append]
      exact List.mem_append_right _ (by simpa [blockOps] using ho))) hk)

/-- **A return on the path**: the statement's flush and `emit`, the return cells checked, the
pooled `1`; a function's frame return `JUMP one 0 1` (header words in `K`), `main`'s closing
`SET dest endSentinel; JUMP one dest one` (frame `0`). -/
theorem stmtW_ret (hflush : FlushSegStmt) (hok : OpOK Γ I Ag cl) (hI : I.Ok)
    (hmain : ctx.isMain = true → I.fp = 0) {vs : List V} {rest tl : List Stmt}
    (hck : ChainKeep ctx (.ret vs) rest)
    (hAg : ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L → ∀ n < I.size,
      L.read (addressOfIndex (I.fp + n)) = some (fwd I.hdr ⟨patchT I Ψ σ', kh⟩ n))
    (hhdr : ctx.isMain = false → IsInK I.hdr.1 ∧ IsInK I.hdr.2)
    (hkend : IsInK (I.kw .endSentinel)) :
    StmtW Γ Ag cl ctx I (.ret vs) rest tl := by
  intro C st sc sc' i₀ o hsc _ hw _ _ _ _ hinv
  simp only [walk1] at hw
  subst hw
  simp only [scopeStmt] at hsc
  have hcp : ∀ (k : ℕ) (d x : V), (∀ j < k, ∃ b, (Stmt.ret vs :: rest)[j]? = some (Stmt.atom b)) →
      (Stmt.ret vs :: rest)[k]? = some (Stmt.atom (.copy d x)) →
      (sc.live.contains x = true ∨ st.locs[x]? = none) ∧ I.σ d = I.σ x := by
    intro k d x hj hk
    cases k with
    | zero => simp at hk
    | succ k =>
      obtain ⟨b, hb⟩ := hj 0 (Nat.succ_pos _)
      simp at hb
  have h1K : IsInK (1 : E) := (isInK_iff 1).mpr ⟨1, ofK_one.symm⟩
  refine FBAt.mono (FBAt.and_wp (R := fun _ C' st' => Fits I st' → ∃ blk,
    st'.out.toList = st.out.toList ++ blk ∧
      BlkW Γ I ctx.isMain Ag cl C' blk [.ret vs] (rest ++ tl) (.ret [] vs) i₀) ?_ (hck st)) ?_
  rotate_left
  · exact fun _ C' st' _ _ _ h =>
      ⟨fun _ h' => (nomatch h'), by rw [h.2]; exact hinv.chain, h.1⟩
  · rw [placeStmt]
    simp only [bind_assoc]
    refine FBAt.fat_bind (begin_fat hflush hI hsc hinv hcp)
      fun _ st₁ C₁ hs₁ hn₁ hl₁ _ hE₁ _ => ?_
    refine FBAt.read_bind ?_
    refine FBAt.fat_bind (FAt.ofSame (R := fun _ _ st' => st' = st₁)
      (wp_mono (mapM_cellAt_keep vs st₁) fun _ st' h => by
        subst h
        exact ⟨rfl, rfl, rfl, LocsLe.refl _, rfl⟩))
      fun _ st₂ C₂ hs₂ hn₂ hl₂ _ hE₂ hst₂ => ?_
    subst hst₂
    have hE₂' := hE₁.step hE₂ hs₂ hn₂ hl₂
    split
    · simp only [bind_assoc]
      exact fun _ => wp_bind.mpr wp_failP
    · simp only [bind_assoc]
      unfold oneCell
      refine FBAt.fat_bind (constCell_fat (1, 0) (hI.kconst 1 0)
        (le_trans hinv.two (le_trans hn₁ hn₂)))
        fun one st₃ C₃ hs₃ hn₃ hl₃ _ hE₃ ⟨ho2, hon, _, _, hoΨ⟩ => ?_
      have hE₃' := hE₂'.step hE₃ hs₃ hn₃ hl₃
      refine FBAt.read_bind ?_
      split
      · next hm =>
        simp only [bind_assoc]
        refine FBAt.fat_bind (fresh_fat (fun _ => I.kw .endSentinel) (wblind_const _ _))
          fun dest st₄ C₄ hs₄ hn₄ hl₄ _ hE₄ ⟨hd, hst₄, hC₄⟩ => ?_
        have hE₄' := hE₃'.step hE₄ hs₄ hn₄ hl₄
        refine FBAt.fat_bind takeHints_fat fun hints st₅ C₅ hs₅ hn₅ hl₅ _ hE₅ ⟨hC₅, hst₅⟩ => ?_
        have hE₅' := hE₄'.step hE₅ hs₅ hn₅ hl₅
        subst hC₅ hst₅ hC₄ hst₄ hd
        refine push_end fun st' ho hn hl hF => ?_
        obtain ⟨ops, hops, hopsW⟩ := hE₅'
        have hF₅ : Fits I { st₃ with next := st₃.next + 1, pending := #[] } :=
          ⟨by rw [← hn]; exact hF.1, by rw [← hl]; exact hF.2⟩
        refine ⟨ops ++ [.halt hints one st₃.next], by rw [ho, hops, List.append_assoc], ?_⟩
        refine blkW_ops_ctl hok rfl (hopsW hF₅) fun Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt
          hX hk => ?_
        have hset : LOp.set st₃.next .endSentinel ∈ I.ops := hX _ (by simp [stmtOps])
        have hjmp : LOp.jump one st₃.next one ∈ I.ops := hX _ (by simp [stmtOps])
        have hdtc : ¬ I.tc st₃.next := not_tc_of hI hset (by simp [opCells])
          fun _ h => nomatch h
        have hotc : ¬ I.tc one := not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h
        have hd2 : 2 ≤ st₃.next := le_trans ho2 (le_of_lt hon)
        have hsz : st₃.next + 1 ≤ I.size := hF₅.1
        have hΨo : Ψ one = 1 := (hoΨ Ψ hΨ.1).trans word_one
        have hkh : khalt := by simpa [hm] using hk
        have honsz : one < I.size := by have := hon; simp only [Cell] at *; omega
        have hfo : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ one = 1 := (fwd_patch ho2 hotc).trans hΨo
        have hfd : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ st₃.next = I.kw .endSentinel :=
          (fwd_patch hd2 hdtc).trans hΨ.2
        have hHW := And.left (hok Ψ σ' hσ kh [] (.set st₃.next .endSentinel) pos cs ks
          (fun _ _ => True) kj kret khalt hset (by
            show fw I Ψ st₃.next = I.kw .endSentinel
            rw [fw_of_two hd2]
            exact hΨ.2) trivial)
        dsimp only [wLc, wS, JW]
        refine ⟨hHW, fun κ L hL n hn => ?_, by rw [hfo]; exact h1K, by rw [hfd]; exact hkend,
          by rw [hfo]; exact h1K, fun h0 => by rw [hfo] at h0; exact one_ne_zero h0,
          fun _ => ⟨by rw [hfo, hmain hm, ofK_gpow_zero], hkh⟩⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;> exact hAg σ' Ψ kh κ L hL _ (by simp only [Cell] at *; omega)
      · next hm =>
        simp only [bind_assoc]
        refine FBAt.fat_bind takeHints_fat fun hints st₅ C₅ hs₅ hn₅ hl₅ _ hE₅ ⟨hC₅, hst₅⟩ => ?_
        have hE₅' := hE₃'.step hE₅ hs₅ hn₅ hl₅
        subst hC₅ hst₅
        refine push_end fun st' ho hn hl hF => ?_
        obtain ⟨ops, hops, hopsW⟩ := hE₅'
        have hF₅ : Fits I { st₃ with pending := #[] } :=
          ⟨by rw [← hn]; exact hF.1, by rw [← hl]; exact hF.2⟩
        refine ⟨ops ++ [.ret hints one], by rw [ho, hops, List.append_assoc], ?_⟩
        refine blkW_ops_ctl hok rfl (hopsW hF₅) fun Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt
          hX hk => ?_
        have hjmp : LOp.jump one 0 1 ∈ I.ops := hX _ (by simp [stmtOps])
        have hotc : ¬ I.tc one := not_tc_of hI hjmp (by simp [opCells]) fun _ h => nomatch h
        have hm' : ctx.isMain = false := by simpa using hm
        have hkr : kret := by simpa [hm'] using hk
        have hfo : fwd I.hdr ⟨patchT I Ψ σ', kh⟩ one = 1 :=
          (fwd_patch ho2 hotc).trans ((hoΨ Ψ hΨ).trans word_one)
        have hsz : st₃.next ≤ I.size := hF₅.1
        dsimp only [wLc, wS, JW]
        refine ⟨fun κ L hL n hn => ?_, by rw [hfo]; exact h1K, by simpa [fwd] using (hhdr hm').1,
          by simpa [fwd] using (hhdr hm').2, fun h0 => by rw [hfo] at h0; exact one_ne_zero h0,
          fun _ => hkr⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        have honsz : one < I.size := by have := hon; simp only [Cell] at *; omega
        rcases hn with rfl | rfl | rfl <;> exact hAg σ' Ψ kh κ L hL _ (by simp only [Cell] at *; omega)

end Ret


end
end LeanVM.Guest.Backend.Complete
