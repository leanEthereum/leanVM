/-
  LeanVM.Compiler.Complete.FrameAddr

  A frame address statement on the path.
-/

module

public import LeanVM.Compiler.Complete.FrameStmts

/-!
# A frame address on the path

`stmtW_frameAddr`: the frame address atom's `StmtW`, its pointer's word the address of its run's
first cell in the frame (`addrs` of the path). The run's first value placed in a cell gives
`AtomFAt`'s frame address premise (`frameAddr_fatA`); placed otherwise, the placement fails
(`frameAddr_nocell`). The scope walk rejects a run of no cells (`badAddr`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The scope walk takes a frame address of a run of cells only. -/
theorem scopeFlat_run {rc : ℕ} {p : V} {run : List V} {s s' : SSt}
    (h : scopeFlat rc (.atom (.frameAddr p run)) s = .ok s') : run ≠ [] := by
  unfold scopeFlat at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · next hb =>
    intro h0
    subst h0
    simp [badAddr] at hb

section Prims

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

/-- **A frame address whose run's first value has no cell** fails to place. -/
theorem frameAddr_nocell {p r0 : V} {rs : List V} {R : PUnit → ((ℕ → E) → Prop) → St → Prop}
    (hmain : ctx.isMain = true → I.fp = 0) (h : ∀ b, st.locs[r0]? ≠ some (.cell b)) :
    FAt ctx I C st (placeAtom (.frameAddr p (r0 :: rs))) R := by
  unfold placeAtom
  dsimp only
  refine FAt.bind (isLazy_fat p .addr) fun z st₀ C₀ _ _ _ ⟨hC₀, hst₀⟩ => ?_
  subst C₀ st₀
  split
  · split
    · next r0' hr0 =>
      simp only [List.head?_cons, Option.some.injEq] at hr0
      subst hr0
      exact FAt.bind (cellAt_fat r0) fun base _ _ _ _ _ ⟨_, _, hb⟩ => absurd hb (h base)
    · exact FAt.fail
  · refine FAt.get_bind ?_
    split
    · refine FAt.get_bind ?_
      split
      · refine FAt.bind (isSelfFp_fat _ hmain) fun b st₁ C₁ _ _ _ ⟨hC₁, hst₁, _⟩ => ?_
        subst C₁ st₁
        refine FAt.guard fun _ => ?_
        refine FAt.bind (mapM_cellAt_fat (r0 :: rs))
          fun cs st₁ C₁ _ _ _ ⟨_, _, hlen, hcs⟩ => ?_
        exfalso
        cases cs with
        | nil => cases hlen
        | cons c0 _ => exact h c0 (hcs c0 r0 rfl rfl)
      · exact FAt.fail
    · exact FAt.fail

/-- **A frame address atom's placement** (`AtomFAt` of it), its pointer's word the address of its
run's first cell in the final placement (`addrs` of the path). -/
theorem frameAddr_fatA {p : V} {run : List V} (hne : run ≠ []) (ok : V → Prop) (hok : I.Ok)
    (hmain : ctx.isMain = true → I.fp = 0) (hes : Memory.Ev.atom (.frameAddr p run) ∈ I.es)
    (hrd : ∀ rd, I.Rd rd → holdsNT rd I.σ (.frameAddr p run))
    (hu : ∀ v ∈ Memory.atomUses (.frameAddr p run), v ∉ I.tmps)
    (ht : ∀ t ∈ Memory.atomTmps (.frameAddr p run), t ∈ I.tmps)
    (hnm : ∀ v ∈ Memory.atomUses (.frameAddr p run), v ∈ I.named)
    (haddr : ∀ q ∈ addrs I.es, I.σ q.1 = ofK (addressOfIndex (I.fp + (cellP I.locs q.2).getD 0)))
    (hld : Fits I st → ∀ d p' off, Atom.frameAddr p run = .load d p' off →
      ∀ n, st.locs[d]? ≠ some (.shifted n 0))
    (h2 : 2 ≤ st.next) (hv : VW I C st ok) (hpn : OutOps I st → PoolNT I st.scope)
    (hops : ∀ v ∈ Memory.atomUses (.frameAddr p run) ++ Memory.atomTmps (.frameAddr p run),
      ok v ∨ ∃ s, s ≠ v ∧ Atom.frameAddr p run = .copy v s ∧
        st.aliasRun.any (·.contains v) = true) :
    FAt ctx I C st (placeAtom (.frameAddr p run)) fun _ C' st' =>
      (Fits I st' → VW I C' st' (fun v => ok v ∨
        v ∈ Memory.atomUses (.frameAddr p run) ++ Memory.atomTmps (.frameAddr p run))) ∧
        st'.rest = st.rest ∧
        (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨
          v ∈ Memory.atomUses (.frameAddr p run) ++ Memory.atomTmps (.frameAddr p run)) ∧
        ∀ c, c < st.next → (∀ Ψ w, C Ψ → C (Function.update Ψ c w)) →
          ∀ Ψ w, C' Ψ → C' (Function.update Ψ c w) := by
  obtain ⟨r0, rs, rfl⟩ : ∃ r0 rs, run = r0 :: rs := by
    cases run with
    | nil => exact absurd rfl hne
    | cons r0 rs => exact ⟨r0, rs, rfl⟩
  by_cases hb : ∃ base, st.locs[r0]? = some (.cell base)
  · obtain ⟨base, hb⟩ := hb
    refine place_frameAddr_fat p (r0 :: rs) ctx I C st ok hok hmain hes hrd hu ht hnm
      (fun hF p' run' heq => ?_) hld h2 hv hpn hops
    cases heq
    have hI' : I.locs[r0]? = some (.cell base) := hF.2 r0 _ hb
    have hc : cellP I.locs r0 = some base := by simp [cellP, hI']
    have hm : (p, r0) ∈ addrs I.es := List.mem_filterMap.mpr ⟨_, hes, rfl⟩
    have := haddr _ hm
    rw [hc] at this
    exact ⟨r0, base, rfl, hb, this⟩
  · exact frameAddr_nocell hmain fun b h => hb ⟨b, h⟩

end Prims

section Stmt

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst}

/-- **A frame address on the path**: its flush, its `emit`, the atom (`frameAddr_fatA`), its end;
its words are straight-line instructions (`FAt.toBlk`). -/
theorem stmtW_frameAddr (hpk : PoolKeepStmt) (hok : OpOK Γ I Ag cl)
    (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0)
    (hRd : ∀ rd, I.Rd rd → ∀ e ∈ I.es, evNT rd I.σ e) {p : V} {run : List V}
    {rest tl : List Stmt}
    (hu : ∀ v ∈ Memory.atomUses (.frameAddr p run), v ∉ I.tmps)
    (ht : ∀ t ∈ Memory.atomTmps (.frameAddr p run), t ∈ I.tmps)
    (hnm : ∀ v ∈ Memory.atomUses (.frameAddr p run), v ∈ I.named)
    (haddr : ∀ q ∈ addrs I.es, I.σ q.1 = ofK (addressOfIndex (I.fp + (cellP I.locs q.2).getD 0))) :
    StmtW Γ Ag cl ctx I (.atom (.frameAddr p run)) rest tl := by
  intro C st sc sc' i₀ p₀ o hsc ⟨sc'', hrest⟩ hw _ hes _ hup hinv
  simp only [walk1] at hw
  subst hw
  simp only [scopeStmt] at hsc
  have hne : run ≠ [] := scopeFlat_run hsc
  have hck : ChainKeep ctx (.atom (.frameAddr p run)) rest := chainKeep_atom'
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
  have hcp : ∀ (k : ℕ) (d s : V),
      (∀ j < k, ∃ b, (Stmt.atom (.frameAddr p run) :: rest)[j]? = some (Stmt.atom b)) →
      (Stmt.atom (.frameAddr p run) :: rest)[k]? = some (Stmt.atom (.copy d s)) →
      (sc.live.contains s = true ∨ st.locs[s]? = none) ∧ I.σ d = I.σ s := by
    intro k d s hj hk
    cases k with
    | zero => cases hk
    | succ k =>
      refine ⟨?_, hcopy d s (hup _ rfl k _ (fun j hj' => hj (j + 1) (by omega)) hk)⟩
      rcases scope_lead _ rest sc' sc'' hrest k _ (fun j hj' => hj (j + 1) (by omega)) hk s
        (by simp [ownUses, atomUses]) with h | h
      · exact hok' s ((scopeFlat_sub hsc).1 s h)
      · exact Or.inr (hinv.fresh s (by rw [hall]; exact List.mem_append_right _ h)).1
  have hA : FAt ctx I C st (beginStmt (.atom (.frameAddr p run) :: rest) >>= fun _ =>
      placeAtom (.frameAddr p run))
      fun _ C₃ st₃ => st₃.rest = sc'.rest ∧
        (Fits I st₃ → VW I C₃ st₃ fun v => sc'.live.contains v = true) ∧
        (sc'.retDone = false → RetBlind ctx C₃) ∧
        (∀ v, st₃.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest) ∨
          sc'.live.contains v = true) := by
    refine FAt.bind (FAt.and_wp (begin_fat flushSeg_lock hI hsc hinv hcp)
      ((hpk ctx I st (.atom (.frameAddr p run) :: rest) (.atom (.frameAddr p run)) rest).1 hI
        hinv.pnt))
      fun _ st₂ C₂ _ hn₂ _ ⟨⟨h1, h2, h3, h4⟩, hp₂⟩ => ?_
    refine FAt.mono (frameAddr_fatA (ctx := ctx) (C := C₂) (st := st₂) hne
      (fun v => sc'.live.contains v = true) hI hmain
      (hes _ (by simp [outEs]))
      (fun rd hrd => hRd rd hrd (Memory.Ev.atom (.frameAddr p run)) (hes _ (by simp [outEs])))
      hu ht hnm haddr (fun _ _ _ _ h => nomatch h)
      (le_trans hinv.two hn₂) h2 hp₂ (fun v hv => Or.inl (hown v hv)))
      fun _ C₃ st₃ _ _ _ ⟨g1, g2, g3, g4⟩ => ⟨g2.trans h1,
        fun hF => (g1 hF).anti fun v hv => Or.inl hv,
        fun hr k hk => g4 (2 + ctx.argCells + k)
          (by have := hinv.abi; simp only [Cell] at *; omega) (h3 hr k hk),
        fun v hv => (g3 v hv).elim (fun h => (h4 v h).elim Or.inl fun h => Or.inr (Or.inl h))
          fun h => Or.inr (Or.inr (hown v h))⟩
  have hF : FAt ctx I C st ((beginStmt (.atom (.frameAddr p run) :: rest) >>= fun _ =>
      placeAtom (.frameAddr p run)) >>= fun _ => endStmt) fun _ C₃ st₃ => (st₃.rest = sc'.rest ∧
        (Fits I st₃ → VW I C₃ st₃ fun v => sc'.live.contains v = true) ∧
        (sc'.retDone = false → RetBlind ctx C₃) ∧
        (∀ v, st₃.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest) ∨
          sc'.live.contains v = true)) ∧
        st₃.lazy = none :=
    FAt.bind hA fun _ st₃ C₃ _ _ _ hr => by
      unfold endStmt
      exact FAt.quiet rfl rfl rfl rfl ⟨hr, rfl⟩
  rw [placeStmt]
  refine FBAt.mono (FBAt.and_wp (FBAt.and_wp (FAt.toBlk (bx := ctx)
    (ss := [.atom (.frameAddr p run)]) (tl := rest ++ tl) (es := [.atom (.frameAddr p run)])
    (i₀ := i₀) hok rfl rfl hF) (hck st))
    ((hpk ctx I st (.atom (.frameAddr p run) :: rest) (.atom (.frameAddr p run)) rest).2 hI
      hinv.pnt)) ?_
  rintro _ C' st' _ hn _ ⟨⟨⟨hcok, ⟨⟨h1, h2, h3, h4⟩, hlz⟩, blk, hblk, hbw⟩, hch⟩, hpn⟩
  have hch' : st'.chainIn = none := by rw [hch]; exact hinv.chain
  refine ⟨fun _ _ ⟨hF', hO', _⟩ => winv_flat hsc hinv hcok hn h1 (h2 hF') h3 h4 hch'
    (hpn hO'.outOps) hlz, hch', fun ⟨hF', hO', _⟩ => ⟨blk, hblk, hbw hF' hO'.outOps _,
    fun v hv => ?_⟩⟩
  have hvu : v ∈ Memory.atomUses (.frameAddr p run) := by
    simpa [pathVals, outEs, retVals, pathSels, sels1, walk1, Memory.Ev.uses] using hv
  have hlive : sc'.live.contains v = true := hown v (by simp [ownUses, hvu])
  exact ⟨by rw [h1]; exact scopeFlat_fresh hsc hinv v hlive,
    fun _ l hl => h2 hF' v l hlive hl⟩

end Stmt

end

end LeanVM.Compiler.Complete
