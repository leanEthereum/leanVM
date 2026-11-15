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
    (hfa : ∀ p run, a ≠ .frameAddr p run)
    (hld : ∀ d p off, a = .load d p off → ∀ n e, I.locs[d]? ≠ some (.shifted n e)) :
    StmtW Γ Ag cl ctx I (.atom a) rest tl := by
  intro C st sc sc' i₀ o hsc ⟨sc'', hrest⟩ hw _ hes _ hup hinv
  simp only [walk1] at hw
  subst hw
  simp only [scopeStmt] at hsc
  obtain ⟨s₁, hfl, hr₁, hl₁, hd₁, hown⟩ := scopeFlat_inv hsc
  rw [hinv.rest] at hfl
  obtain ⟨hseg, hlive, huseS⟩ := flushS_seg _ _ _ _ _ hfl
  have hall : allocsOf st.rest = allocsOf (flushSeg st.rest) ++ allocsOf sc'.rest := by
    conv_lhs => rw [hseg]
    rw [allocsOf_append, hr₁, allocsOf_other (e := Event.emit) (fun _ _ h => nomatch h)]
  have hnd : (allocsOf (flushSeg st.rest) ++ allocsOf sc'.rest).Nodup := hall ▸ hinv.nodup
  have hsegA : ∀ v ∈ allocsOf (flushSeg st.rest), st.locs[v]? = none ∧
      sc.live.contains v = false :=
    fun v hv => hinv.fresh v (by rw [hall]; exact List.mem_append_left _ hv)
  have hsc'live : ∀ v, sc'.live.contains v = true →
      sc.live.contains v = true ∨ v ∈ allocsOf (flushSeg st.rest) := by
    intro v hv
    rw [hl₁] at hv
    exact hlive v hv
  let ok : V → Prop := fun v => sc.live.contains v = true ∨ st.locs[v]? = none
  have hokOf : ∀ v, sc'.live.contains v = true → ok v := fun v hv =>
    (hsc'live v hv).elim Or.inl fun h => Or.inr (hsegA v h).1
  have hcopy : ∀ d s, Memory.Ev.atom (.copy d s) ∈ I.es → I.σ d = I.σ s := fun d s he => by
    obtain ⟨rd, hrd⟩ := hI.rd
    have := hRd rd hrd _ he
    simpa [evNT, holdsNT, Atom.Holds] using this
  have hcp : ∀ (k : ℕ) (d s : V), (∀ j < k, ∃ b, (Stmt.atom a :: rest)[j]? = some (Stmt.atom b)) →
      (Stmt.atom a :: rest)[k]? = some (Stmt.atom (.copy d s)) → ok s ∧ I.σ d = I.σ s := by
    intro k d s hj hk
    cases k with
    | zero =>
      cases hk
      exact ⟨hokOf s (hown s (by simp [ownUses, atomUses])),
        hcopy d s (hes _ (by simp [outEs]))⟩
    | succ k =>
      refine ⟨?_, hcopy d s (hup _ rfl k _ (fun j hj' => hj (j + 1) (by omega)) hk)⟩
      rcases scope_lead _ rest sc' sc'' hrest k _ (fun j hj' => hj (j + 1) (by omega)) hk s
        (by simp [ownUses, atomUses]) with h | h
      · exact hokOf s h
      · exact Or.inr (hinv.fresh s (by rw [hall]; exact List.mem_append_right _ h)).1
  have huse : ∀ v n e, Event.use v ∈ flushSeg st.rest → st.locs[v]? = some (.shifted n e) →
      ok v := fun v n e hv hl =>
    (huseS v hv).elim Or.inl fun h => absurd hl (by rw [(hsegA v h).1]; simp)
  have hvw : VW I C st ok := fun v l hv hl =>
    hv.elim (fun h => hinv.vw v l h hl) fun h => by rw [h] at hl; cases hl
  -- the flush and the `emit`
  have hB : FAt ctx I C st (beginStmt (.atom a :: rest)) fun _ C₂ st₂ =>
      st₂.rest = sc'.rest ∧ FlushR I C₂ st st₂ ok ∧ (s₁.retDone = false → RetBlind ctx C₂) ∧
      (∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest)) := by
    unfold beginStmt
    refine FAt.bind (hflush ctx I C st _ sc.live sc.retDone s₁ ok hI hfl hinv.fuel hcp huse
      hinv.abi hinv.two hvw fun hr k hk Ψ w hC => hinv.ret hr Ψ k w hk hC)
      fun _ st₁ C₁ _ _ _ ⟨h1, h2, h3, h4⟩ => ?_
    refine FAt.mono (expect_fat (ev := .emit) (es := sc'.rest) (by rw [h1, hr₁]) rfl)
      fun _ C' st' _ _ _ ⟨hC, hst⟩ => ?_
    subst hC hst
    exact ⟨rfl, h2.right rfl rfl, h3, h4⟩
  -- the atom
  have hA : FAt ctx I C st (beginStmt (.atom a :: rest) >>= fun _ => placeAtom a)
      fun _ C₃ st₃ => st₃.rest = sc'.rest ∧
        (Fits I st₃ → VW I C₃ st₃ fun v => sc'.live.contains v = true) ∧
        (sc'.retDone = false → RetBlind ctx C₃) ∧
        (∀ v, st₃.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest) ∨
          sc'.live.contains v = true) := by
    refine FAt.bind hB fun _ st₂ C₂ _ hn₂ _ ⟨h1, h2, h3, h4⟩ => ?_
    refine FAt.mono (hat ctx I C₂ st₂ (fun v => ok v ∨ st.locs[v]? = none) hI hmain
      (hes _ (by simp [outEs]))
      (fun rd hrd => hRd rd hrd (Memory.Ev.atom a) (hes _ (by simp [outEs])))
      hu ht (fun _ p run h => absurd h (hfa p run))
      (fun hF d p off hd n e hl => hld d p off hd n e (hF.2 _ _ hl))
      (le_trans hinv.two hn₂) h2.2 (fun v hv => Or.inl (Or.inl (hokOf v (hown v hv)))))
      fun _ C₃ st₃ _ _ _ ⟨g1, g2, g3, g4⟩ => ⟨g2.trans h1,
        fun hF => (g1 hF).anti fun v hv => Or.inl (Or.inl (hokOf v hv)),
        fun hr k hk => g4 (2 + ctx.argCells + k)
          (by have := hinv.abi; simp only [Cell] at *; omega)
          (h3 (by rw [← hd₁]; exact hr) k hk),
        fun v hv => (g3 v hv).elim (fun h => (h4 v h).elim Or.inl fun h => Or.inr (Or.inl h))
          fun h => Or.inr (Or.inr (hown v h))⟩
  -- its end
  have hF : FAt ctx I C st ((beginStmt (.atom a :: rest) >>= fun _ => placeAtom a) >>=
      fun _ => endStmt) fun _ C₃ st₃ => st₃.rest = sc'.rest ∧
        (Fits I st₃ → VW I C₃ st₃ fun v => sc'.live.contains v = true) ∧
        (sc'.retDone = false → RetBlind ctx C₃) ∧
        (∀ v, st₃.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest) ∨
          sc'.live.contains v = true) :=
    FAt.bind hA fun _ st₃ C₃ _ _ _ hr => by
      unfold endStmt
      exact FAt.quiet rfl rfl rfl rfl hr
  have hlen : sc'.rest.length ≤ st.rest.length := by
    have h' := congrArg List.length hseg
    rw [List.length_append, hr₁, List.length_cons] at h'
    omega
  rw [placeStmt]
  refine FBAt.mono (FBAt.and_wp (FAt.toBlk (main := ctx.isMain) (ss := [.atom a])
    (tl := rest ++ tl) (es := [.atom a]) (i₀ := i₀) hok rfl rfl hF) (hck st)) ?_
  rintro _ C' st' _ hn _ ⟨⟨hcok, ⟨h1, h2, h3, h4⟩, blk, hblk, hbw⟩, hch⟩
  refine ⟨fun _ _ hF' => ?_, by rw [hch]; exact hinv.chain, fun hF' => ⟨blk, hblk, hbw hF'⟩⟩
  have hfr : ∀ v ∈ allocsOf st'.rest, st'.locs[v]? = none ∧ sc'.live.contains v = false := by
    intro v hv
    rw [h1] at hv
    obtain ⟨hst, hlv⟩ := hinv.fresh v (by rw [hall]; exact List.mem_append_right _ hv)
    have hns : v ∉ allocsOf (flushSeg st.rest) := fun h => List.disjoint_of_nodup_append hnd h hv
    have hlv' : sc'.live.contains v = false := by
      cases hx : sc'.live.contains v with
      | false => rfl
      | true => exact ((hsc'live v hx).elim (fun h => by rw [hlv] at h; cases h) hns).elim
    refine ⟨?_, hlv'⟩
    cases hx : st'.locs[v]? with
    | none => rfl
    | some x =>
      rcases h4 v (by rw [hx]; simp) with h | h | h
      · exact absurd hst h
      · exact absurd h hns
      · rw [hlv'] at h
        cases h
  exact ⟨hcok, h1.symm, h2 hF', le_trans hinv.two hn, le_trans hinv.abi hn,
    by rw [h1]; exact le_trans hlen hinv.fuel, fun hr Ψ k w hk hC => h3 hr k hk Ψ w hC,
    by rw [h1]; exact hnd.of_append_right, hfr, by rw [hch]; exact hinv.chain⟩

end Atom

end
end LeanVM.Guest.Backend.Complete
