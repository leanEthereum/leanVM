/-
  LeanVM.Compiler.Complete.FrameEdge

  The invariant at a block's edge flush and past an event that makes no value.
-/

module

public import LeanVM.Compiler.Complete.FrameInner

/-!
# The invariant at a block's edges

`winv_edge`: the walk's invariant after the flush before a branch or a `match` (`flushEdge`) and
the cells taken after it. `WInv.past`: past an event that makes no value (a branch's `emit`).
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The scope walk of a branch -/

theorem scopeIte_inv {rc : ℕ} {c : V} {z nz : List Stmt} {s s' : SSt}
    (h : scopeStmt rc (.ite c z nz) s = .ok s') : ∃ s₀ s₁, flushEdge rc s = .ok s₀ ∧
      s₀.live.contains c = true ∧ scopeInner rc (fun s' => scopeBlock rc z s') s₀ = .ok s₁ ∧
      scopeIteTail nz.isEmpty (scopeInner rc (fun s' => scopeBlock rc nz s')) s₀.retDone s₁ =
        .ok s' := by
  simp only [scopeStmt] at h
  split at h
  · cases h
  next s₀ h₀ =>
  split at h
  · cases h
  next hn =>
  split at h
  · cases h
  next s₁ h₁ =>
  refine ⟨s₀, s₁, h₀, ?_, h₁, h⟩
  unfold needScope at hn
  split at hn
  · next hc => simpa [inScope] using hc
  · cases hn

theorem scopeIteTail_inv {e : Bool} {nz : SSt → Except String SSt} {b : Bool} {s₁ s' : SSt}
    (h : scopeIteTail e nz b s₁ = .ok s') :
    (∃ r s₂, s₁.rest = .enter :: r ∧ nz { s₁ with retDone := b } = .ok s₂ ∧
      expectS isEmit "a branch" { s₂ with retDone := s₁.retDone || s₂.retDone } = .ok s') ∨
    ((∀ r, s₁.rest ≠ .enter :: r) ∧ e = true ∧ expectS isEmit "a branch" s₁ = .ok s') := by
  unfold scopeIteTail at h
  split at h
  · next r hr =>
    split at h
    · cases h
    · next s₂ h₂ => exact Or.inl ⟨r, s₂, hr, h₂, h⟩
  · next hne =>
    split at h
    · cases h
    · next he => exact Or.inr ⟨fun r hr => hne r hr, by simpa using he, h⟩

/-! ## The invariant at a branch's edges -/

section Inv

variable {ctx : Compiler.Ctx} {I : Inst}

/-- **The invariant after a block's edge flush** (`flushEdge`), once the cells after it are
taken: the constraint's properties, the trace and the values in scope the scope walk's, the flush
placing only values it makes. -/
theorem winv_edge {C C' : (ℕ → E) → Prop} {st st' : St} {sc s₀ : SSt}
    (hinv : WInv ctx I C st sc) (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hcok : COk I C' st'.next st'.scope st'.locs) (hn : st.next ≤ st'.next)
    (hr : st'.rest = s₀.rest) (hvw : VW I C' st' fun v => s₀.live.contains v = true)
    (hret : s₀.retDone = false → RetBlind ctx C')
    (hloc : ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest))
    (hch : st'.chainIn = none) (hpnt : PoolNT I st'.scope) (hlz : st'.lazy = none) :
    WInv ctx I C' st' s₀ := by
  have hfl : flushS ctx.retCells st.rest sc.live sc.retDone = .ok s₀ := by
    rw [← hinv.rest]
    exact (flushEdge_ok h₀).2
  obtain ⟨hseg, hlive, -⟩ := flushS_seg _ _ _ _ _ hfl
  have hall : allocsOf st.rest = allocsOf (flushSeg st.rest) ++ allocsOf s₀.rest := by
    conv_lhs => rw [hseg]
    rw [allocsOf_append]
  have hnd : (allocsOf (flushSeg st.rest) ++ allocsOf s₀.rest).Nodup := hall ▸ hinv.nodup
  have hlen : s₀.rest.length ≤ st.rest.length := by
    have h' := congrArg List.length hseg
    rw [List.length_append] at h'
    omega
  have hfr : ∀ v ∈ allocsOf st'.rest, st'.locs[v]? = none ∧ s₀.live.contains v = false := by
    intro v hv
    rw [hr] at hv
    obtain ⟨hst, hlv⟩ := hinv.fresh v (by rw [hall]; exact List.mem_append_right _ hv)
    have hns : v ∉ allocsOf (flushSeg st.rest) := fun h => List.disjoint_of_nodup_append hnd h hv
    have hlv' : s₀.live.contains v = false := by
      cases hx : s₀.live.contains v with
      | false => rfl
      | true => exact ((hlive v hx).elim (fun h => by rw [hlv] at h; cases h) hns).elim
    refine ⟨?_, hlv'⟩
    cases hx : st'.locs[v]? with
    | none => rfl
    | some x =>
      rcases hloc v (by rw [hx]; simp) with h | h
      · exact absurd hst h
      · exact absurd h hns
  exact ⟨hcok, hr.symm, hvw, le_trans hinv.two hn, le_trans hinv.abi hn,
    by rw [hr]; exact le_trans hlen hinv.fuel, fun hr' Ψ k w hk hC => hret hr' k hk Ψ w hC,
    by rw [hr]; exact hnd.of_append_right, hfr, hch, hpnt, hlz⟩

/-- **The invariant past an event that makes no value** (a branch's `emit`), the state's cells,
places, pools and chaining kept and no value waiting, the return area made later or no
earlier. -/
theorem WInv.past {C : (ℕ → E) → Prop} {st st' : St} {s s' : SSt} (hinv : WInv ctx I C st s)
    (hev : ∃ ev, s.rest = ev :: s'.rest ∧ ∀ vs k, ev ≠ .alloc vs k)
    (hlv : s'.live = s.live) (hrd : s'.retDone = false → s.retDone = false)
    (hn : st'.next = st.next) (hl : st'.locs = st.locs) (hs : st'.scope = st.scope)
    (hr : st'.rest = s'.rest) (hch : st'.chainIn = st.chainIn) (hz : st'.lazy = none) :
    WInv ctx I C st' s' := by
  obtain ⟨ev, hev, hna⟩ := hev
  have hst : st.rest = ev :: st'.rest := by rw [← hinv.rest, hev, hr]
  have hall : allocsOf st.rest = allocsOf st'.rest := by rw [hst, allocsOf_other hna]
  refine ⟨by rw [hn, hs, hl]; exact hinv.cok, hr.symm, fun v l hv hvl => ?_,
    by rw [hn]; exact hinv.two, by rw [hn]; exact hinv.abi, ?_, fun h => hinv.ret (hrd h),
    by rw [← hall]; exact hinv.nodup, fun v hv => ?_, by rw [hch]; exact hinv.chain,
    by rw [hs]; exact hinv.pnt, hz⟩
  · rw [hl] at hvl
    rw [hn]
    exact hinv.vw v l (by rw [← hlv]; exact hv) hvl
  · have := hinv.fuel
    rw [hst, List.length_cons] at this
    omega
  · obtain ⟨h1, h2⟩ := hinv.fresh v (by rw [hall]; exact hv)
    exact ⟨by rw [hl]; exact h1, by rw [hlv]; exact h2⟩

/-- A branch's `emit`, past the scope walk's. -/
theorem emit_past {s s' : SSt} (h : expectS isEmit "a branch" s = .ok s') :
    ∃ ev, s.rest = ev :: s'.rest ∧ ∀ vs k, ev ≠ .alloc vs k := by
  obtain ⟨ev, hr, he, -, -⟩ := expectS_ok h
  exact ⟨ev, hr, fun vs k h' => by subst h'; simp [isEmit] at he⟩

end Inv


/-! ## Placement on and off the path -/

section FB

variable {ctx : Compiler.Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

/-- An action that gives the scope back keeps the constraint's properties in its result. -/
theorem FBAt.cok {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : FBAt ctx I C st m R) (hsc : ∀ a C' st', R a C' st' → st'.scope = st.scope) :
    FBAt ctx I C st m fun a C' st' => R a C' st' ∧ COk I C' st'.next st'.scope st'.locs :=
  fun hc => wp_mono (h hc) fun a st' ⟨C', h0, hb, hs, hn, hl, hr⟩ =>
    ⟨C', h0, hb, hs, hn, hl, hr, ⟨h0, hb, fun Ψ hΨ => by
      rw [hsc a C' st' hr]; exact (hc.pools Ψ (hs Ψ hΨ)).grow hl,
      by rw [hsc a C' st' hr]; exact hc.cells.mono hn⟩⟩

theorem FBAt.peek_bind {β : Type} {f : Option Event → P β}
    {R : β → ((ℕ → E) → Prop) → St → Prop} (h : FBAt ctx I C st (f st.rest.head?) R) :
    FBAt ctx I C st (peek >>= f) R :=
  fun hc => wp_bind.mpr (wp_peek.mpr (h hc))

theorem FBAt.fail_bind {α β : Type} {msg : String} {f : α → P β}
    {R : β → ((ℕ → E) → Prop) → St → Prop} : FBAt ctx I C st ((failP msg : P α) >>= f) R :=
  fun _ => wp_bind.mpr wp_failP

end FB

/-! ## An inner block on or off the path -/

section Inner

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Compiler.Ctx} {I : Inst}

/-- What an inner block's placement gives whatever the path (`InBlockOff`). -/
def OffR (b : List Stmt) (st st' : St) (sc' : SSt) : Prop :=
  st'.rest = sc'.rest ∧ st'.scope = st.scope ∧ st'.out = st.out ∧
    (st.chainIn = none → st'.chainIn = none) ∧ st.next ≤ st'.next ∧ LocsLe st.locs st'.locs ∧
    (st.lazy = none → st'.lazy = none ∧
      (∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨
        ∃ run, Atom.frameAddr v run ∈ atomsIn b) ∧
      ((allocsOf st.rest).Nodup →
        ∀ v ∈ allocsOf st'.rest, st.locs[v]? = none → st'.locs[v]? = none)) ∧ (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧
    ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared

/-- What an inner block's placement gives on the path (`InBlockW`). -/
def InR (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop)
    (cl : List Call) (ctx : Compiler.Ctx) (I : Inst) (b : List Stmt) (sc' : SSt) (o : Out)
    (i₀ p₁ : ℕ) (st : St) (blk : List PStmt) (C' : (ℕ → E) → Prop) (st' : St) : Prop :=
  st'.out = st.out ∧ st'.scope = st.scope ∧ st'.chainIn = none ∧
    (∀ es, o = .fall es → Fits I st' → OpsIn I p₁ (blockOps blk p₁) → TabsW Γ Ag st' →
      FillsIn Γ Ag p₁ blk → WInv ctx I C' st' sc') ∧
    (Fits I st' → OpsIn I p₁ (blockOps blk p₁) → TabsW Γ Ag st' → FillsIn Γ Ag p₁ blk →
      BlkW Γ I ctx Ag cl C' blk b [] o i₀ p₁ ∧ RW I C' st' (pathVals I.σ b o))

/-- **An inner block that may be on the path**: on it (its statements so far final, so the
invariant at its start) as `InBlockW` has it, off it with the constraint kept; whatever the path,
as `InBlockOff` has it. -/
theorem inBlock_fb {b : List Stmt} (hb : InBlockW Γ Ag cl ctx I b) {C : (ℕ → E) → Prop}
    {st : St} {sc sc' : SSt} {i₀ p₁ : ℕ} {o : Out}
    (hsc : scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells b s') sc = .ok sc')
    (hw : walk I.σ b = o) (hns : o ≠ .stuck) (hes : ∀ e ∈ outEs o, e ∈ I.es)
    (hcl : ∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?)
    (hr : st.rest = sc.rest) (hf : st.rest.length ≤ ctx.fuel)
    (hinv : OutOps I st → WInv ctx I C st sc) :
    FBAt ctx I C st (inBlock (placeBlock b)) fun blk C' st' =>
      COk I C' st'.next st'.scope st'.locs ∧ OffR b st st' sc' ∧
      (OutOps I st → InR Γ Ag cl ctx I b sc' o i₀ p₁ st blk C' st') ∧ (¬ OutOps I st → C' = C) := by
  have hoff : wpP (inBlock (placeBlock b)) ctx st fun _ st' => OffR b st st' sc' :=
    inBlockOff_ok b st sc sc' hsc hr hf
  by_cases hO : OutOps I st
  · refine FBAt.mono (FBAt.cok (FBAt.and_wp (hb C st sc sc' i₀ p₁ o hsc hw hns hes hcl (hinv hO))
      hoff) fun _ _ _ h => h.1.2.1) fun _ _ _ _ _ _ ⟨⟨hW, ho⟩, hc⟩ =>
      ⟨hc, ho, fun _ => hW, fun h => absurd hO h⟩
  · refine FBAt.mono (FBAt.offPath (wp_mono hoff fun _ st' h => ⟨h.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h⟩)) fun _ C' _ _ _ _ ⟨hC, hc, h⟩ => ⟨hC ▸ hc, h, fun h' => absurd h' hO,
      fun _ => hC⟩

end Inner

/-! ## A statement's words after the block's instructions -/

section Words

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Compiler.Ctx} {I : Inst}

theorem FillsIn.drop {p₀ : ℕ} {a b : List PStmt} (h : FillsIn Γ Ag p₀ (a ++ b)) :
    FillsIn Γ Ag (p₀ + blockSize a) b :=
  fun f k i hm => h f k i (by rw [blockFills_append]; exact List.mem_append_right _ hm)

theorem OpsAt.last {p₀ : ℕ} {st st' : St} {X : PStmt} (h : OpsAt I p₀ st')
    (ho : st'.out.toList = st.out.toList ++ [X]) :
    OpsIn I (p₀ + blockSize st.out.toList) (stmtOps X (p₀ + blockSize st.out.toList)) := by
  unfold OpsAt at h
  rw [ho, bops_append] at h
  have := h.right
  rw [blockOps_length] at this
  simpa [blockOps] using this

/-- Straight-line instructions with their words, then a statement with its own. -/
theorem blkW_ops_X (hok : OpOK Γ I Ag cl) {C : (ℕ → E) → Prop} {ops : List PStmt} {X : PStmt}
    {bx : Compiler.Ctx} {ss tl : List Stmt} {o : Out} {i₀ pos : ℕ}
    (hW : ∀ s ∈ ops, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C Ψ → OpW I Ψ o)
    (hX : BlkW Γ I bx Ag cl C [X] ss tl o i₀ (pos + blockSize ops)) :
    BlkW Γ I bx Ag cl C (ops ++ [X]) ss tl o i₀ pos := by
  obtain ⟨hs, hl, hh, h⟩ := hX
  refine ⟨hs, hl, hh, fun hp hK Ψ hΨ σ' hσ kh cs ks next kj kret khalt hbo hcs hks hk => ?_⟩
  rw [wLc_append _ _ _ _ _ _ _ ops [X] (List.cons_ne_nil _ _)]
  refine wLc_ops hok hΨ hσ kh ops hW pos
    (fun o' ho => hbo o' (by rw [bops_append]; exact List.mem_append_left _ ho)) cs ks _ _ kret
    khalt (h hp hK Ψ hΨ σ' hσ kh cs ks next kj kret khalt
      (fun o' ho => hbo o' (by rw [bops_append]; exact List.mem_append_right _ ho)) hcs hks hk)

/-- A state the final placement extends, past a branch whose statement ends its output: the
states before it, the branch's instructions and slots. -/
theorem fin_ite {p₀ : ℕ} {st₆ st' stb : St} {X : PStmt} (hF : FinAt Γ I Ag p₀ st')
    (ho : st'.out.toList = st₆.out.toList ++ [X]) (hn : stb.next ≤ st'.next)
    (hl : LocsLe stb.locs st'.locs) (ht : ∀ x ∈ stb.tables.shared, x ∈ st'.tables.shared) :
    Fits I stb ∧ TabsW Γ Ag stb ∧
      OpsIn I (p₀ + blockSize st₆.out.toList) (stmtOps X (p₀ + blockSize st₆.out.toList)) ∧
      FillsIn Γ Ag (p₀ + blockSize st₆.out.toList) [X] :=
  ⟨hF.1.back hn hl, fun fs first hm => hF.2.2.1 fs first (ht _ hm), OpsAt.last hF.2.1 ho,
    FillsIn.drop (by rw [← ho]; exact hF.2.2.2)⟩

end Words

end

end LeanVM.Compiler.Complete
