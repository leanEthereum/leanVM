/-
  LeanVM.Guest.Backend.Sound.Stmts

  Placement of the statements that end or leave a frame is sound: return, call, a loop helper's
  closing call, fused dispatch.
-/

module

public import LeanVM.Guest.Backend.Sound.Calls

/-!
# Returns and calls

One lemma a statement of the core IR that is no branch: every success of its placement lays
placed statements that mean it (`LaysAt`), its obligations `Obl` and its relation `Stmt.Holds`.

The relation is `StmtS`: `Stmt.Holds` given that, when the rest of the block is a bare return,
the frame having returned gives `next`. That is what a loop helper's closing call to itself
needs: the callee returns for this frame, so what follows the call is never run, and placement
has checked that it is `return` alone in a function that returns no cells.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : VMap Loc} {ctx : Ctx} {C : CallRel}
  {U : String → List E → Prop} {slots : Array KVal} {B : ℕ}

/-- A statement's relation, the frame's return standing for a rest that is a bare return. -/
def StmtS (C : CallRel) (rd : Reader) (σ : Val) (s : Stmt) (rest : List Stmt) :
    Prop → (List E → Prop) → Prop :=
  fun next kret => (rest = [Stmt.ret []] → kret [] → next) → Stmt.Holds C rd σ s next kret

theorem map_valP_cells {L : MemoryImage κ} {vs : List V} {cells : List Cell}
    (h : List.Forall₂ (fun v n => F[v]? = some (.cell n)) vs cells) :
    vs.map (valP L fp F) = cells.map (wd L fp) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [valP_of_cell h, ih]

theorem retWords_eq {cells : List Cell}
    (h : cells = (List.range ctx.retCells).map (2 + ctx.argCells + ·)) :
    cells.map (wd Γ.L fp) = retWords Γ fp ctx := by
  rw [h, retWords, frameWords, List.map_map]
  rfl

section

variable (env : PlaceEnv Γ fp ctx C U slots B)

include env in
/-- An atom. -/
theorem atom_lays (a : Atom) (rest : List Stmt) (st : St) :
    LaysAt Γ fp F ctx slots B True st (placeStmt (.atom a) rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) (.atom a))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.atom a) rest) := by
  rw [placeStmt]
  exact LaysAt.callT (beginStmt_spec _) fun _ _ =>
    LaysAt.ofSpec (placeAtom_spec env.main a _) fun _ _ ha g next kret hG hn _ => ⟨ha, hn (hG ha)⟩

/-- `return`: the frame's return cells are the returned values, and the frame returns (or, in
`main`, halts). -/
theorem ret_lays (vs : List V) (rest : List Stmt) (st : St) :
    LaysAt Γ fp F ctx slots B True st (placeStmt (.ret vs) rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) (.ret vs))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.ret vs) rest) := by
  rw [placeStmt]
  refine LaysAt.callT (beginStmt_spec _) fun _ _ => ?_
  refine LaysAt.read_bind ?_
  refine LaysAt.call (mapM_spec cellAt_spec vs) fun cells _ => ?_
  refine LaysAt.guard fun hc => ?_
  have hcells : cells = (List.range ctx.retCells).map (2 + ctx.argCells + ·) := by simpa using hc
  refine LaysAt.call oneCell_spec fun one _ => ?_
  refine LaysAt.read_bind ?_
  split
  · next hm =>
    refine LaysAt.callT fresh_spec fun dest _ => ?_
    refine LaysAt.callT takeHints_spec fun hints _ => ?_
    refine LaysAt.push fun pos N kj kretP khalt g next kret hH _ _ _ _ _ _ _ _ hret _ => ?_
    show kret (vs.map (valP Γ.L fp F))
    rw [map_valP_cells hH.1.2, retWords_eq hcells]
    exact hret (Or.inl hm)
  · refine LaysAt.callT takeHints_spec fun hints _ => ?_
    refine LaysAt.push fun pos N kj kretP khalt g next kret hH _ _ _ _ _ hsem _ _ hret _ => ?_
    obtain ⟨c, hc', hk⟩ := hsem
    have hne : c ≠ 0 := by
      rw [← wd_of_read hc', hH.2]
      exact one_ne_zero
    show kret (vs.map (valP Γ.L fp F))
    rw [map_valP_cells hH.1.2, retWords_eq hcells]
    exact hret (Or.inr (hk hne))

theorem loopCount_spec (f : String) (args : List V) (cells : List Cell) :
    Spec Γ fp F ctx (loopCount f args cells)
      (fun r => (ctx.loops[f]?).any (·.registered) = true → r.isSome = true) := by
  intro st
  unfold loopCount
  refine SpecAt.read_bind ?_
  split
  · split
    · exact SpecAt.pure fun _ _ _ h => by simp_all
    · refine SpecAt.get_bind ?_
      extract_lets lo
      split
      · exact SpecAt.pure fun _ _ _ _ => rfl
      · exact SpecAt.pure fun _ _ _ _ => rfl
      · exact SpecAt.fail
  · exact SpecAt.pure fun _ _ _ h => by simp_all

include env in
/-- **The call node** `placeCall` pushes means whatever follows from `call_node`. -/
theorem placeCall_lays {H : Prop} {st : St} {f : String} {argVs : List V} {args rets : List Cell}
    {cond : Option Cell} {tail : Bool} {G : Prop → Prop} {S : Prop → (List E → Prop) → Prop}
    (hcal : H → isCallee ctx.sigs args.length rets.length f = true)
    (htail : tail = true → rets = [])
    (hfin : ∀ (oc : Cell) (N kretP g next : Prop) (kret : List E → Prop), H →
      (cond = none → wd Γ.L fp oc = 1) → (∀ c, cond = some c → oc = c) →
      (IsInK (wd Γ.L fp oc) ∧ (wd Γ.L fp oc = 0 → N) ∧
        (wd Γ.L fp oc ≠ 0 → U f (args.map (wd Γ.L fp)) →
          C f (args.map (wd Γ.L fp)) (rets.map (wd Γ.L fp)) ∧ (if tail then kretP else N))) →
      G g → (N → g → next) → (ctx.isMain = true ∨ kretP → kret (retWords Γ fp ctx)) →
      S next kret) :
    LaysAt Γ fp F ctx slots B H st (placeCall f argVs args rets cond tail) G S := by
  have hk : ∀ (nfp entry oc : Cell) (st' : St), LaysAt Γ fp F ctx slots B
      (H ∧ ((cond = none → wd Γ.L fp oc = 1) ∧ ∀ c, cond = some c → oc = c)) st'
      (do
        let hints ← takeHints
        let loop ← loopCount f argVs args
        push (.call hints { callee := f, nfp, entry, oc, args, rets, loop, tail })) G S := by
    intro nfp entry oc st'
    refine LaysAt.callT takeHints_spec fun hints _ => ?_
    refine LaysAt.call (loopCount_spec f argVs args) fun loop _ => ?_
    refine LaysAt.push fun pos N kj kretP khalt g next kret hH _ hp _ _ _ hsem hG hnext hret => ?_
    have hnode := call_node env (c := ⟨f, nfp, entry, oc, args, rets, loop, tail⟩)
      (hcal hH.1.1) hH.2 htail hsem
    exact hfin oc N kretP g next kret hH.1.1 hH.1.2.1 hH.1.2.2 hnode hG
      (fun hN hg => hnext hp hN hg) hret
  unfold placeCall
  refine LaysAt.callT fresh_spec fun nfp _ => ?_
  refine LaysAt.callT fresh_spec fun entry st₁ => ?_
  cases cond with
  | none =>
      exact LaysAt.call oneCell_spec fun oc st' =>
        (hk nfp entry oc st').weaken fun h => ⟨h.1, fun _ => h.2, fun _ h' => nomatch h'⟩
  | some c =>
      refine LaysAt.bind (Q₁ := fun oc => oc = c) (SpecAt.pure fun _ _ _ => rfl) fun oc st' => ?_
      exact (hk nfp entry oc st').weaken fun h =>
        ⟨h.1, (fun h' => nomatch h'), fun c' h' => h.2.trans (Option.some.inj h')⟩

theorem forall₂_len {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : l₁.length = l₂.length := (forall₂_getElem h).1

include env in
/-- A call. -/
theorem call_lays (f : String) (args rets : List V) (rest : List Stmt) (st : St) :
    LaysAt Γ fp F ctx slots B True st (placeStmt (.call f args rets) rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) (.call f args rets))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.call f args rets) rest) := by
  rw [placeStmt]
  refine LaysAt.callT (beginStmt_spec _) fun _ _ => ?_
  refine LaysAt.read_bind ?_
  refine LaysAt.guard fun hcal => ?_
  have hcal' : isCallee ctx.sigs args.length rets.length f = true := by simpa using hcal
  refine LaysAt.call (mapM_spec cellOf_spec args) fun las _ => ?_
  refine LaysAt.call (mapM_spec cellAt_spec rets) fun lrs st₁ => ?_
  refine placeCall_lays env (fun h => by
      rw [← forall₂_len h.1.2, ← forall₂_len h.2]
      exact hcal') (fun h => nomatch h)
    fun oc N kretP g next kret hH hone _ hnode hG hnext _ _ => ?_
  have ha := forall₂_cells hH.1.2
  have hr := map_valP_cells (L := Γ.L) (fp := fp) hH.2
  obtain ⟨hU, hg⟩ : U f (args.map (valP Γ.L fp F)) ∧
    (C f (args.map (valP Γ.L fp F)) (rets.map (valP Γ.L fp F)) → g) := hG
  obtain ⟨hC, hN⟩ := hnode.2.2 (by rw [hone rfl]; exact one_ne_zero) (ha ▸ hU)
  rw [ha, ← hr] at hC
  exact ⟨hC, hnext hN (hg hC)⟩

/-- The conditional call ending a loop helper, from what its node gives. -/
theorem callIf_finish {c : V} {f : String} {args : List V} {lc : Cell} {las : List Cell}
    {N kretP g next : Prop} {kret : List E → Prop} {tail : Bool}
    (hlc : wd Γ.L fp lc = valP Γ.L fp F c)
    (hlas : las.map (wd Γ.L fp) = args.map (valP Γ.L fp F))
    (hnode : IsInK (wd Γ.L fp lc) ∧ (wd Γ.L fp lc = 0 → N) ∧
      (wd Γ.L fp lc ≠ 0 → U f (las.map (wd Γ.L fp)) →
        C f (las.map (wd Γ.L fp)) [] ∧ (if tail then kretP else N)))
    (hG : Obl C U Γ.L.read (valP Γ.L fp F) (.callIf c f args) g) (hnext : N → g → next)
    (hesc : tail = true → kretP → next) :
    Stmt.Holds C Γ.L.read (valP Γ.L fp F) (.callIf c f args) next kret := by
  rw [hlc, hlas] at hnode
  obtain ⟨hK, hfall, htaken⟩ := hnode
  obtain ⟨hU, hg⟩ : (valP Γ.L fp F c ≠ 0 → U f (args.map (valP Γ.L fp F))) ∧
    ((valP Γ.L fp F c ≠ 0 → C f (args.map (valP Γ.L fp F)) []) → g) := hG hK
  by_cases h0 : valP Γ.L fp F c = 0
  · exact ⟨hK, fun hne => absurd h0 hne, hnext (hfall h0) (hg fun hne => absurd h0 hne)⟩
  · obtain ⟨hC, hk⟩ := htaken h0 (hU h0)
    refine ⟨hK, fun _ => hC, ?_⟩
    cases tail with
    | true => exact hesc rfl hk
    | false => exact hnext hk (hg fun _ => hC)

include env in
/-- The conditional call ending a loop helper. -/
theorem callIf_lays (c : V) (f : String) (args : List V) (rest : List Stmt) (st : St) :
    LaysAt Γ fp F ctx slots B True st (placeStmt (.callIf c f args) rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) (.callIf c f args))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.callIf c f args) rest) := by
  rw [placeStmt]
  refine LaysAt.callT (beginStmt_spec _) fun _ _ => ?_
  refine LaysAt.read_bind ?_
  refine LaysAt.guard fun hcal => ?_
  have hcal' : isCallee ctx.sigs args.length 0 f = true := by simpa using hcal
  refine LaysAt.call (cellOf_spec c) fun lc _ => ?_
  refine LaysAt.call (mapM_spec cellOf_spec args) fun las st₁ => ?_
  refine LaysAt.read_bind ?_
  have hplace : ∀ (tail : Bool) (st' : St),
      (tail = true → rest = [Stmt.ret []] ∧ ctx.retCells = 0) →
      LaysAt Γ fp F ctx slots B ((True ∧ wd Γ.L fp lc = valP Γ.L fp F c) ∧
        List.Forall₂ (fun b n => wd Γ.L fp n = valP Γ.L fp F b) args las) st'
        (placeCall f args las [] (some lc) tail)
        (Obl C U Γ.L.read (valP Γ.L fp F) (.callIf c f args))
        (StmtS C Γ.L.read (valP Γ.L fp F) (.callIf c f args) rest) := by
    intro tail st' htl
    refine placeCall_lays env (fun h => by rw [← forall₂_len h.2]; exact hcal') (fun _ => rfl)
      fun oc N kretP g next kret hH _ hoc hnode hG hnext hret hesc => ?_
    obtain rfl := hoc lc rfl
    refine callIf_finish hH.1.2 (forall₂_cells hH.2) (by simpa using hnode) hG hnext
      fun ht hk => ?_
    obtain ⟨hr, h0⟩ := htl ht
    have := hret (Or.inr hk)
    rw [retWords, h0] at this
    exact hesc hr this
  by_cases hself : (f == ctx.name) = true
  · simp only [hself, ↓reduceIte, Bool.true_and]
    split
    · refine LaysAt.guard fun hrc => ?_
      have hrc' : ctx.retCells = 0 := by simpa using hrc
      split
      · next hreg =>
        refine LaysAt.call (selfFp_spec env.main) fun ownFp _ => ?_
        refine LaysAt.callT fresh_spec fun scale _ => ?_
        refine LaysAt.call (emitOp_spec rfl) fun _ _ => ?_
        refine LaysAt.callT (pushHint_spec _) fun _ _ => ?_
        refine LaysAt.call (mulCell_spec ownFp scale) fun nfp _ => ?_
        refine LaysAt.callT fresh_spec fun entry _ => ?_
        refine LaysAt.call oneCell_spec fun one _ => ?_
        refine LaysAt.callT takeHints_spec fun hints _ => ?_
        refine LaysAt.push fun pos N kj kretP khalt g next kret hH _ hp _ _ _ hsem hG hnext hret
          hesc => ?_
        obtain ⟨⟨⟨⟨⟨⟨-, hlc⟩, hlas⟩, hown⟩, hset⟩, hnfp⟩, hone⟩ := hH
        have hnfp' : wd Γ.L fp nfp = ofK (fp * addressOfIndex Γ.frame) := by
          rw [hnfp, hown, holds_set_frame env.pow env.frameLt hset.choose_spec, ofK_mul]
        have hnode := loopNext_node env (by rw [← forall₂_len hlas]; exact hcal') hone hnfp' hsem
        refine callIf_finish (tail := true) hlc (forall₂_cells hlas) hnode hG
          (fun hN hg => hnext hp hN hg) fun _ hk => ?_
        have := hret (Or.inr hk)
        rw [retWords, hrc'] at this
        exact hesc rfl this
      · exact hplace true _ fun _ => ⟨rfl, hrc'⟩
    · exact LaysAt.fail_bind
  · simp only [hself, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    exact hplace false _ fun h => nomatch h

/-- The shared table of a dispatch is among the shared tables. -/
theorem sharedTable_wp (fs : List String) (st : St) :
    wpP (sharedTable fs) ctx st (fun first st₁ => Quiet st st₁ ∧
      (fs, first) ∈ st₁.tables.shared) := by
  unfold sharedTable
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · next cs first hfind =>
    refine wp_pure.mpr ⟨⟨rfl, Sub.refl _, rfl, TablesLe.refl _, rfl⟩, ?_⟩
    have hmem := List.mem_of_find?_eq_some hfind
    have hcs : cs = fs := by simpa using List.find?_some hfind
    exact hcs ▸ hmem
  · extract_lets first
    exact wp_bind.mpr (wp_set.mpr (wp_pure.mpr ⟨⟨rfl, Sub.refl _, rfl,
      ⟨List.suffix_cons _ _⟩, rfl⟩, List.mem_cons_self⟩))

include env in
/-- A fused `match` of calls. -/
theorem dispatch_lays (x : V) (fs : List String) (args rets : List V) (rest : List Stmt)
    (st : St) :
    LaysAt Γ fp F ctx slots B True st (placeStmt (.dispatch x fs args rets) rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) (.dispatch x fs args rets))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.dispatch x fs args rets) rest) := by
  rw [placeStmt]
  refine LaysAt.callT (beginStmt_spec _) fun _ _ => ?_
  refine LaysAt.read_bind ?_
  refine LaysAt.guard fun hreg => ?_
  refine LaysAt.guard fun hcal => ?_
  refine LaysAt.call (mapM_spec cellOf_spec args) fun las _ => ?_
  refine LaysAt.call (mapM_spec cellAt_spec rets) fun lrs _ => ?_
  refine LaysAt.call (cellOf_spec x) fun lx _ => ?_
  refine LaysAt.call oneCell_spec fun one _ => ?_
  refine LaysAt.callT fresh_spec fun nfp _ => ?_
  refine LaysAt.callT takeHints_spec fun hints _ => ?_
  refine LaysAt.callT fresh_spec fun joinCell st₁ => ?_
  refine LaysAt.step (R := fun first => ∀ j (h : j < fs.length),
    slots[first + j]? = some (.entry fs[j])) ?_ fun first _ => ?_
  · exact wp_mono (sharedTable_wp fs st₁) fun first st₂ ⟨hq, hin⟩ =>
      ⟨hq, fun hent _ _ j hj => hent _ hin j hj⟩
  refine LaysAt.callT fresh_spec fun entry _ => ?_
  refine LaysAt.push fun pos N kj kretP khalt g next kret hH _ hp hB _ _ hsem hG hnext _ _ => ?_
  obtain ⟨⟨⟨⟨⟨-, hlas⟩, hlrs⟩, hlx⟩, hone⟩, hslots⟩ := hH
  have ha := forall₂_cells hlas
  have hr := map_valP_cells (L := Γ.L) (fp := fp) hlrs
  obtain ⟨⟨j, hj, hxj⟩, hU, hg⟩ := hG
  have hcal' : ∀ f ∈ fs, isCallee ctx.sigs las.length lrs.length f = true := by
    intro f hf
    rw [← forall₂_len hlas, ← forall₂_len hlrs]
    have := hcal
    simp only [Bool.not_eq_true, Bool.not_eq_false', List.all_eq_true] at this
    exact this f hf
  have hnreg : ∀ f ∈ fs, (ctx.loops[f]?).any (·.registered) = false := by
    intro f hf
    have := hreg
    simp only [Bool.not_eq_true, List.any_eq_false] at this
    simpa using this f hf
  have hB' : pos + (las.length + 5 + lrs.length) ≤ B := by
    simpa [blockSize, stmtSize] using hB
  obtain ⟨hC, hN⟩ := dispatch_node env hB' hcal' hnreg hone hj (hlx.trans hxj) (hslots j hj)
    (ha ▸ hU j hj hxj) hsem
  rw [ha, ← hr] at hC
  exact ⟨⟨j, hj, hxj, hC⟩, hnext hp hN (hg ⟨j, hj, hxj, hC⟩)⟩

end

end
end LeanVM.Guest.Backend
