/-
  LeanVM.Guest.Backend.Sound.Blocks

  Placement of branches is sound: a block of its own, `if`, `match`, and with them every
  statement and every block.
-/

module

public import LeanVM.Guest.Backend.Sound.Stmts

/-!
# Blocks and branches
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : Std.HashMap V Loc} {ctx : Ctx} {C : CallRel}
  {U : String → List E → Prop} {slots : Array KVal} {B : ℕ}

/-- Two states that agree on everything a proof reads. -/
structure Eqv (st st' : St) : Prop where
  out : st'.out = st.out
  locs : st'.locs = st.locs
  scope : st'.scope = st.scope
  tables : st'.tables = st.tables
  chainIn : st'.chainIn = st.chainIn
  chain : st'.chain = st.chain

theorem Eqv.emits {st st' : St} (h : Eqv st st') : Emits Γ fp F True st st' True :=
  Emits.frame h.out h.locs ⟨h.tables, h.chainIn, h.chain⟩ fun _ _ hp => h.scope ▸ hp

theorem Eqv.same {st st' : St} (h : Eqv st st') : Same st st' :=
  ⟨h.tables, h.chainIn, h.chain⟩

/-- Passing an event moves the trace position only. -/
theorem wp_expect {st : St} {e : Event → Bool} {what : String} {Q : Unit → St → Prop}
    (h : ∀ st', Eqv st st' → Q () st') : wpP (expect e what) ctx st Q := by
  unfold expect
  refine wp_bind.mpr (wp_peek.mpr ?_)
  split
  · split
    · exact wp_modify.mpr (h _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    · exact wp_failP
  · exact wp_failP

/-- The end of a block of its own: the statements and pools of the state before it are put
back, and what was laid inside is returned. -/
theorem inBlock_finish {st st1 s5 : St} {Gb : Prop → Prop} {Sb : Prop → (List E → Prop) → Prop}
    (hpl : Plain st) (hpl5 : Plain s5) (h1 : Eqv st st1)
    (L : Lays Γ fp F ctx slots B True { st1 with out := #[] } s5 Gb Sb) :
    Plain { s5 with out := st1.out, scope := st1.scope } ∧
      Quiet st { s5 with out := st1.out, scope := st1.scope } ∧
      (TablesOK st.tables → Means Γ fp F ctx slots B True s5.locs st.scope st.scope s5.tables
        s5.out.toList Gb Sb) := by
  obtain ⟨ps, ho, hl, ht, hmn⟩ := L
  have hps : s5.out.toList = ps := by simpa using ho
  refine ⟨⟨hpl5.chainIn, hpl5.chain⟩, ⟨h1.out, h1.locs ▸ hl, h1.scope, h1.tables ▸ ht,
    hpl5.chainIn.trans hpl.chainIn.symm, hpl5.chain.trans hpl.chain.symm⟩, fun hok => ?_⟩
  · rw [hps]
    intro pos N kj kretP khalt g next kret hH hF hp hB hfill hent hsem hG hnext hret
    exact hmn (h1.tables ▸ hok) pos N kj kretP khalt g next kret hH hF (h1.scope ▸ hp) hB hfill hent
      hsem hG (fun _ hN hg => hnext hp hN hg) hret

section

variable (hnc : ∀ e ∈ ctx.trace.toList, e.isChain = false)

include hnc in
/-- **A block of its own**: the statements and the pools of the state are as before, and the
statements returned mean what the block's walk lays. -/
theorem inBlock_spec {m : P Unit} {Gb : Prop → Prop} {Sb : Prop → (List E → Prop) → Prop}
    (hm : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ m Gb Sb) (st : St) (hpl : Plain st) :
    wpP (inBlock m) ctx st (fun blk st₁ => Plain st₁ ∧ Quiet st st₁ ∧
      (TablesOK st.tables →
        Means Γ fp F ctx slots B True st₁.locs st.scope st.scope st₁.tables blk Gb Sb)) := by
  unfold inBlock
  refine wp_bind.mpr (wp_expect fun st1 h1 => ?_)
  refine wp_bind.mpr (wp_get.mpr ?_)
  dsimp only
  refine wp_bind.mpr (wp_set.mpr ?_)
  refine wp_bind.mpr fun _ st2 he2 => ?_
  obtain ⟨hp2, l2⟩ := hm { st1 with out := #[] }
    ⟨h1.chainIn.trans hpl.chainIn, h1.chain.trans hpl.chain⟩ _ st2 he2
  refine wp_bind.mpr fun _ st3 he3 => ?_
  have e3 := flush_spec (Γ := Γ) (fp := fp) (F := F) hnc [] st2 _ st3 he3
  refine wp_bind.mpr (wp_expect fun st4 h4 => ?_)
  have l4 := (l2.suffix e3).suffix h4.emits
  have hp4 : Plain st4 := (hp2.of_same e3.same).of_same h4.same
  refine wp_bind.mpr (wp_get.mpr ?_)
  split
  · refine wp_bind.mpr fun o s5a hea => wp_bind.mpr fun _ s5 heb => ?_
    have ea := fresh_spec (Γ := Γ) (fp := fp) (F := F) st4 o s5a hea
    have eb := (emitOp_spec (Γ := Γ) (fp := fp) (F := F) (ctx := ctx)
      (o := .set o (.const 0 0)) rfl s5a _ s5 heb).imp fun _ _ _ _ => trivial
    refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr ?_))))
    exact inBlock_finish hpl ((hp4.of_same ea.same).of_same eb.same) h1 ((l4.suffix ea).suffix eb)
  · refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr (wp_pure.mpr ?_))))
    exact inBlock_finish hpl hp4 h1 l4

include hnc in
/-- A block of its own, then the rest knowing what the block means. -/
theorem LaysAt.block {H : Prop} {st : St} {β : Type} {m : P Unit} {f : List PStmt → P β}
    {Gb G : Prop → Prop} {Sb S : Prop → (List E → Prop) → Prop}
    (hm : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ m Gb Sb)
    (hf : ∀ blk st₁, LaysAt Γ fp F ctx slots B (H ∧ BlockSem Γ fp ctx slots B blk Gb Sb) st₁
      (f blk) G S) :
    LaysAt Γ fp F ctx slots B H st (inBlock m >>= f) G S :=
  LaysAt.plain fun hpl => LaysAt.step
    (wp_mono (inBlock_spec hnc hm st hpl) fun _ _ ⟨_, hq, hmn⟩ =>
      ⟨hq, fun hok hent hF hp => (hmn hok).blockSem hF hp hent⟩) hf

end

/-! ## `if` -/

section

variable (env : PlaceEnv Γ fp ctx C U slots B)

include env in
/-- A branch with an `else` block: the block the condition selects runs, then the code after. -/
theorem ite_means_else {H : Prop} {locs : Std.HashMap V Loc} {sc : Scope} {t : Tables} {c : V}
    {z nz rest : List Stmt} {hints : List LHint} {lc bdest sfp edest one : Cell}
    {zeroBlk nonzero : List PStmt}
    (hH : H → wd Γ.L fp lc = valP Γ.L fp F c ∧ wd Γ.L fp sfp = ofK fp ∧ wd Γ.L fp one = 1 ∧
      BlockSem Γ fp ctx slots B zeroBlk (OblList C U Γ.L.read (valP Γ.L fp F) z)
        (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) z next kret) ∧
      BlockSem Γ fp ctx slots B nonzero (OblList C U Γ.L.read (valP Γ.L fp F) nz)
        (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) nz next kret)) :
    Means Γ fp F ctx slots B H locs sc sc t
      [.ite hints lc bdest sfp zeroBlk true edest one nonzero]
      (Obl C U Γ.L.read (valP Γ.L fp F) (.ite c z nz))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.ite c z nz) rest) := by
  intro pos N kj kretP khalt g next kret hH' _ hp hB hfill _ hsem hG hnext hret _
  obtain ⟨hlc, hsfp, hone, hbz, hbnz⟩ := hH hH'
  simp only [PStmt.SemList, PStmt.Sem, ↓reduceIte] at hsem
  obtain ⟨hset, hj⟩ := hsem
  obtain ⟨hK, -, hfall, htaken⟩ := jumpAt_wd hj
  have hBs : pos + (2 + blockSize zeroBlk + (2 + blockSize nonzero)) ≤ B := by
    simpa [blockSize, stmtSize] using hB
  have hpc := env.pcLt
  simp only [blockFills, stmtFills, List.append_nil, ↓reduceIte] at hfill
  have hbd := holds_set_local env.pow (by simp only [elseAt, ↓reduceIte]; omega) hset
  rw [hlc] at hK hfall htaken
  obtain ⟨hGz, hGnz⟩ := hG hK
  refine ⟨hK, fun h0 => ?_, fun hne => ?_⟩
  · refine hbz (pos + 2) _ kj kretP khalt g next kret (by omega) hfill.left (hfall h0) (hGz h0)
      (fun hN' hg => ?_) hret
    obtain ⟨hset', hj'⟩ := hN'
    obtain ⟨-, -, -, htk⟩ := jumpAt_wd hj'
    exact hnext hp (htk (by rw [hone]; exact one_ne_zero)
      (holds_set_local env.pow (by simp only [elseAt, ↓reduceIte]; omega) hset') hsfp) hg
  · exact hbnz _ N kj kretP khalt g next kret (by simp only [elseAt, ↓reduceIte]; omega)
      hfill.right (htaken hne hbd hsfp) (hGnz hne) (fun hN hg => hnext hp hN hg) hret

include env in
/-- A branch with no `else` block. -/
theorem ite_means_noelse {H : Prop} {locs : Std.HashMap V Loc} {sc : Scope} {t : Tables} {c : V}
    {z rest : List Stmt} {hints : List LHint} {lc bdest sfp : Cell} {zeroBlk : List PStmt}
    (hH : H → wd Γ.L fp lc = valP Γ.L fp F c ∧ wd Γ.L fp sfp = ofK fp ∧
      BlockSem Γ fp ctx slots B zeroBlk (OblList C U Γ.L.read (valP Γ.L fp F) z)
        (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) z next kret)) :
    Means Γ fp F ctx slots B H locs sc sc t [.ite hints lc bdest sfp zeroBlk false 0 0 []]
      (Obl C U Γ.L.read (valP Γ.L fp F) (.ite c z []))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.ite c z []) rest) := by
  intro pos N kj kretP khalt g next kret hH' _ hp hB hfill _ hsem hG hnext hret _
  obtain ⟨hlc, hsfp, hbz⟩ := hH hH'
  simp only [PStmt.SemList, PStmt.Sem, Bool.false_eq_true, ↓reduceIte] at hsem
  obtain ⟨hset, hj⟩ := hsem
  obtain ⟨hK, -, hfall, htaken⟩ := jumpAt_wd hj
  have hBs : pos + (2 + blockSize zeroBlk) ≤ B := by simpa [blockSize, stmtSize] using hB
  have hpc := env.pcLt
  simp only [blockFills, stmtFills, List.append_nil, Bool.false_eq_true, ↓reduceIte] at hfill
  have hbd := holds_set_local env.pow
    (by simp only [elseAt, Bool.false_eq_true, ↓reduceIte]; omega) hset
  rw [hlc] at hK hfall htaken
  obtain ⟨hGz, hGnz⟩ := hG hK
  refine ⟨hK, fun h0 => ?_, fun hne => ?_⟩
  · exact hbz (pos + 2) _ kj kretP khalt g next kret (by omega) hfill (hfall h0) (hGz h0)
      (fun hN hg => hnext hp hN hg) hret
  · exact hnext hp (htaken hne hbd hsfp) (hGnz hne)

variable (hnc : ∀ e ∈ ctx.trace.toList, e.isChain = false)

include env hnc in
/-- `if`, its blocks' placement sound. -/
theorem ite_lays (c : V) (z nz rest : List Stmt) (st : St)
    (ihz : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock z)
      (OblList C U Γ.L.read (valP Γ.L fp F) z)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) z next kret))
    (ihnz : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock nz)
      (OblList C U Γ.L.read (valP Γ.L fp F) nz)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) nz next kret)) :
    LaysAt Γ fp F ctx slots B True st (placeStmt (.ite c z nz) rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) (.ite c z nz))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.ite c z nz) rest) := by
  rw [placeStmt]
  refine LaysAt.callT (flush_spec hnc []) fun _ _ => ?_
  refine LaysAt.call (cellOf_spec c) fun lc _ => ?_
  refine LaysAt.call (selfFp_spec env.main) fun sfp _ => ?_
  refine LaysAt.call oneCell_spec fun one _ => ?_
  refine LaysAt.callT fresh_spec fun bdest _ => ?_
  refine LaysAt.callT takeHints_spec fun hints _ => ?_
  refine LaysAt.block hnc ihz fun zeroBlk _ => ?_
  refine LaysAt.peek_bind ?_
  split
  · refine LaysAt.callT fresh_spec fun edest _ => ?_
    refine LaysAt.block hnc ihnz fun nonzero _ => ?_
    refine LaysAt.callT (expect_spec _ _) fun _ _ => ?_
    exact LaysAt.push fun _ => ite_means_else env fun h =>
      ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · refine LaysAt.guard fun hnz => ?_
    have hnz' : nz = [] := by simpa using hnz
    subst hnz'
    refine LaysAt.callT (expect_spec _ _) fun _ _ => ?_
    exact LaysAt.push fun _ => ite_means_noelse env fun h => ⟨h.1.1.1.2, h.1.1.2, h.2⟩

end

end
end LeanVM.Guest.Backend
