/-
  LeanVM.Guest.Backend.Sound.Chain

  What a chain of `match`es means: one placed statement of several stages, an arm of each stage
  leaving through the next stage's jump table.
-/

module

public import LeanVM.Guest.Backend.Sound.Blocks

/-!
# Chains of `match`es

A `match` whose arms dispatch into the next `match` is placed with it in one statement
(`PStmt.chain`): its stages are the `match`es, and an arm of a stage ends by reading the next
stage's table at the next selector and jumping there. `TailOK` says what the stages from one
`match` on, and the statements placed after the chain, mean: a jump into them whose target is
the arm the selector names satisfies the core block from that `match` on.

* `tail_closed`: the last stage, whose arms jump to the join;
* `tail_open`: a stage whose arms dispatch into the stages after it;
* `head_means`: the chain statement, from its stages' `TailOK`.

**The walk.** In the core IR a chain is the bare sequence of its `match`es, so the walk places
it across several statements of one block: the first `match` pushes the chain statement and
leaves the chain open (`St.chainIn`), and each later `match` adds a stage to the statement last
placed, nothing being placed between them (`back_chain`). `OpenOK` is what the rest of the block
lays from a state with the chain open: the chain's later stages, then the statements after it,
with their `TailOK`. It is proved by recursion on the block (`open_step`, `entered_wp`) beside
`placeBlock_lays` (`Body.lean`), which takes it at a chain's first `match` (`chain_head_lays`,
`chain_finish`, `match_block_lays`).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : Std.HashMap V Loc} {ctx : Ctx} {C : CallRel}
  {U : String → List E → Prop} {slots : Array KVal} {B : ℕ}

/-- **A table read at a selector in range**: the cell holds the pc of the arm the slot names. -/
theorem slot_entry (env : PlaceEnv Γ fp ctx C U slots B) {pc lx first e : ℕ} {x : V} {j i : ℕ}
    (hslot : Holds Γ.L pc fp (Γ.R (.slot lx first e)))
    (hlx : wd Γ.L fp lx = valP Γ.L fp F x) (hxj : valP Γ.L fp F x = ofK (addressOfIndex j))
    (hfill : slots[first + j]? = some (.at ctx.name i)) (hi : Γ.pc0 + i < 2 ^ 128) :
    wd Γ.L fp e = Γ.tgt i := by
  have hread := (holds_slot hslot).2
  rw [hlx, hxj] at hread
  have e' : (ofK (addressOfIndex j)).limb 0 * addressOfIndex (Γ.l.tablesBase + first) =
      addressOfIndex (Γ.l.tablesBase + (first + j)) := by
    simp only [limb_ofK, Fin.val_zero, ↓reduceIte, addressOfIndex, ← pow_add]
    congr 1
    omega
  rw [e', env.jt _ _ _ hfill rfl, env.self] at hread
  exact (Option.some.inj hread).symm.trans (Γ.l.immediateWord_pow env.pow hi)

section

variable (Γ fp F ctx C U slots B)

/-- The placed arms of a `match` whose arms dispatch into the next: each the arm's block, which
means the arm, then the read of the next table at the next selector and the jump. -/
def ArmsSemN (lx' : Cell) (nf : ℕ) (one sfp : Cell) : List (List Stmt) → List (List PStmt) → Prop
  | [], [] => True
  | arm :: more, b :: blocks =>
      (∃ blk e, b = blk ++ [PStmt.op [] (.slot lx' nf e), PStmt.op [] (.jump one e sfp)] ∧
        BlockSem Γ fp ctx slots B blk (OblList C U Γ.L.read (valP Γ.L fp F) arm)
          (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) ∧
        ArmsSemN lx' nf one sfp more blocks
  | _, _ => False

/-- **What the stages of a chain from one `match` on mean**, with the statements `ps` placed
after the chain: a jump into them at the arm the selector of `match x arms` names satisfies the
core block `match x arms :: rest'`. `sc'` is the scope after `ps`. -/
def TailOK (join : Cell) (nf : ℕ) (x : V) (arms : List (List Stmt)) (rest' : List Stmt)
    (sc' : Scope) (F' : List ℕ) (blocks : List (List PStmt)) (Sg : List (List (List PStmt)))
    (ps : List PStmt) : Prop :=
  arms.length = blocks.length ∧ ∀ (pos : ℕ) (N : Prop) (kj : E → E → Prop) (kretP : Prop)
    (khalt : E → E → Prop) (g next : Prop) (kret : List E → Prop) (d f : E),
    pos + stagesSize (blocks :: Sg) + blockSize ps ≤ B →
    FillsIn slots (stagesFills ctx.name (nf :: F') (blocks :: Sg) pos) →
    FillsIn slots (blockFills ctx.name ps (pos + stagesSize (blocks :: Sg))) →
    wd Γ.L fp join = Γ.tgt (pos + stagesSize (blocks :: Sg)) →
    PStmt.StagesJump Γ fp (blocks :: Sg) pos
      (PStmt.SemList Γ fp ps (pos + stagesSize (blocks :: Sg)) N kj kretP khalt) kretP khalt d f →
    f = ofK fp →
    (∀ j, j < arms.length → valP Γ.L fp F x = ofK (addressOfIndex j) →
      d = Γ.tgt (pos + armsSize (blocks.take j))) →
    OblList C U Γ.L.read (valP Γ.L fp F) (.match_ x arms :: rest') g →
    (PoolOK Γ.L fp sc' → N → g → next) →
    (ctx.isMain = true ∨ kretP → kret (retWords Γ fp ctx)) →
    Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) (.match_ x arms :: rest') next kret

end

theorem armsSemN_get {lx' : Cell} {nf : ℕ} {one sfp : Cell} : ∀ (arms : List (List Stmt))
    (blocks : List (List PStmt)), ArmsSemN Γ fp F ctx C U slots B lx' nf one sfp arms blocks →
    arms.length = blocks.length ∧ ∀ j (h1 : j < arms.length) (h2 : j < blocks.length),
      ∃ blk e, blocks[j] = blk ++ [PStmt.op [] (.slot lx' nf e), PStmt.op [] (.jump one e sfp)] ∧
        BlockSem Γ fp ctx slots B blk (OblList C U Γ.L.read (valP Γ.L fp F) arms[j])
          (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arms[j] next kret)
  | [], [], _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | arm :: more, b :: blocks, h => by
      obtain ⟨hhead, htail⟩ := h
      obtain ⟨hlen, hget⟩ := armsSemN_get more blocks htail
      refine ⟨by simp [hlen], fun j h1 h2 => ?_⟩
      cases j with
      | zero => simpa using hhead
      | succ j =>
          simpa using hget j (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

/-- **The last stage of a chain**: its arms jump to the join, where the statements after the
chain run. -/
theorem tail_closed {join one sfp : Cell} {nf : ℕ} {x : V} {arms : List (List Stmt)}
    {rest' : List Stmt} {sc' : Scope} {blocks : List (List PStmt)} {ps : List PStmt}
    (hone : wd Γ.L fp one = 1) (hsfp : wd Γ.L fp sfp = ofK fp)
    (harms : ArmsSem Γ fp F ctx C U slots B join one sfp arms.length arms blocks 0)
    (hps : ∀ (pos : ℕ) (N : Prop) (kj : E → E → Prop) (kretP : Prop) (khalt : E → E → Prop)
      (g next : Prop) (kret : List E → Prop), pos + blockSize ps ≤ B →
      FillsIn slots (blockFills ctx.name ps pos) → PStmt.SemList Γ fp ps pos N kj kretP khalt →
      OblList C U Γ.L.read (valP Γ.L fp F) rest' g → (PoolOK Γ.L fp sc' → N → g → next) →
      (ctx.isMain = true ∨ kretP → kret (retWords Γ fp ctx)) →
      Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) rest' next kret) :
    TailOK Γ fp F ctx C U slots B join nf x arms rest' sc' [] blocks [] ps := by
  refine ⟨(armsSem_get arms blocks 0 harms).1, ?_⟩
  intro pos N kj kretP khalt g next kret d f hB hfill hfps hjoin hgo hf hd hG hnext hret
  simp only [stagesSize, Nat.add_zero] at hB hfps hjoin hgo
  simp only [PStmt.StagesJump] at hgo
  obtain ⟨⟨j, hjlt, hxj⟩, hGarms⟩ := hG
  obtain ⟨hlen, hget⟩ := armsSem_get arms blocks 0 harms
  have hjb : j < blocks.length := hlen ▸ hjlt
  obtain ⟨blk, hblk, hbs⟩ := hget j hjlt hjb
  have hsucc := armsSize_take_succ blocks j hjb
  have hle' := armsSize_take_le blocks (j + 1)
  have hfill' : FillsIn slots (armsFills ctx.name nf blocks 0 pos) := by
    simpa [stagesFills] using hfill
  obtain ⟨-, hbf⟩ := armsFills_mem ctx.name nf blocks 0 pos j hjb
  have hsemj := armsJump_get blocks pos j hjb hgo.1 (hd j hjlt hxj) hf
  have hsizej : blockSize blocks[j] = blockSize blk +
      blockSize (if 0 + j + 1 != arms.length then [PStmt.op [] (.jump one join sfp)] else []) := by
    rw [hblk, blockSize_append]
  have hbfj : FillsIn slots (blockFills ctx.name blk (pos + armsSize (blocks.take j))) := by
    intro y hy
    refine hfill' y (hbf y ?_)
    rw [hblk, blockFills_append]
    exact List.mem_append_left _ hy
  rw [hblk, semList_append] at hsemj
  refine (holds_match_iff x arms _ kret).mpr ⟨j, hjlt, hxj, ?_⟩
  refine hbs _ _ _ kretP khalt _ _ kret (by omega) hbfj hsemj
    (oblArms_get arms 0 hGarms j hjlt (by simpa using hxj)) (fun hN' hg => ?_) hret
  have hNps : PStmt.SemList Γ fp ps (pos + armsSize blocks) N kj kretP khalt := by
    by_cases hlast : 0 + j + 1 = arms.length
    · have hall : armsSize (blocks.take (j + 1)) = armsSize blocks := by
        rw [show j + 1 = blocks.length by omega, List.take_length]
      simp only [hlast, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, PStmt.SemList,
        List.append_nil, blockSize, Nat.add_zero] at hN' hsizej
      refine hN' ?_ trivial
      show Γ.tgt _ = Γ.tgt _
      congr 1
      omega
    · have hne : (0 + j + 1 != arms.length) = true := by simpa using hlast
      simp only [hne, ↓reduceIte, PStmt.SemList, PStmt.Sem, OpSem] at hN'
      obtain ⟨-, -, -, htk⟩ := jumpAt_wd hN'
      exact htk (by rw [hone]; exact one_ne_zero) hjoin hsfp
  exact hps _ N kj kretP khalt g next kret (by omega) hfps hNps hg hnext hret

section

variable (env : PlaceEnv Γ fp ctx C U slots B)

include env in
/-- **A stage whose arms dispatch into the next**: the arm the selector names runs, reads the
next stage's table at the next selector and jumps into the stages after it. -/
theorem tail_open {join one sfp lx'' : Cell} {nf nf'' : ℕ} {x x'' : V}
    {arms arms'' : List (List Stmt)} {rest'' : List Stmt} {sc' : Scope} {F'' : List ℕ}
    {blocks blocks'' : List (List PStmt)} {Sg'' : List (List (List PStmt))} {ps : List PStmt}
    (hone : wd Γ.L fp one = 1) (hsfp : wd Γ.L fp sfp = ofK fp)
    (hlx : wd Γ.L fp lx'' = valP Γ.L fp F x'')
    (harms : ArmsSemN Γ fp F ctx C U slots B lx'' nf'' one sfp arms blocks)
    (htail : TailOK Γ fp F ctx C U slots B join nf'' x'' arms'' rest'' sc' F'' blocks'' Sg'' ps) :
    TailOK Γ fp F ctx C U slots B join nf x arms (.match_ x'' arms'' :: rest'') sc' (nf'' :: F'')
      blocks (blocks'' :: Sg'') ps := by
  obtain ⟨hlen, hget⟩ := armsSemN_get arms blocks harms
  refine ⟨hlen, ?_⟩
  intro pos N kj kretP khalt g next kret d f hB hfill hfps hjoin hgo hf hd hG hnext hret
  have e : pos + stagesSize (blocks :: blocks'' :: Sg'') =
      pos + armsSize blocks + stagesSize (blocks'' :: Sg'') := by
    simp only [stagesSize]
    omega
  rw [e] at hB hfps hjoin hgo
  obtain ⟨hga, -⟩ : PStmt.ArmsJump Γ fp blocks pos
      (PStmt.StagesJump Γ fp (blocks'' :: Sg'') (pos + armsSize blocks)
        (PStmt.SemList Γ fp ps (pos + armsSize blocks + stagesSize (blocks'' :: Sg'')) N kj kretP
          khalt) kretP khalt) kretP khalt d f ∧ _ := hgo
  obtain ⟨⟨j, hjlt, hxj⟩, hGarms⟩ := hG
  have hjb : j < blocks.length := hlen ▸ hjlt
  obtain ⟨blk, e₁, hblk, hbs⟩ := hget j hjlt hjb
  have hsucc := armsSize_take_succ blocks j hjb
  have hle' := armsSize_take_le blocks (j + 1)
  have hpc := env.pcLt
  simp only [stagesFills, List.headD_cons, List.tail_cons] at hfill
  have hfillA := hfill.left
  have hfillT : FillsIn slots (stagesFills ctx.name (nf'' :: F'') (blocks'' :: Sg'')
      (pos + armsSize blocks)) := by
    simpa [stagesFills] using hfill.right
  obtain ⟨-, hbf⟩ := armsFills_mem ctx.name nf blocks 0 pos j hjb
  have hsemj := armsJump_get blocks pos j hjb hga (hd j hjlt hxj) hf
  have hsizej : blockSize blocks[j] = blockSize blk + 2 := by
    rw [hblk, blockSize_append]
    rfl
  have hbfj : FillsIn slots (blockFills ctx.name blk (pos + armsSize (blocks.take j))) := by
    intro y hy
    refine hfillA y (hbf y ?_)
    rw [hblk, blockFills_append]
    exact List.mem_append_left _ hy
  rw [hblk, semList_append] at hsemj
  refine (holds_match_iff x arms _ kret).mpr ⟨j, hjlt, hxj, ?_⟩
  refine hbs _ _ _ kretP khalt _ _ kret (by omega) hbfj hsemj
    (oblArms_get arms 0 hGarms j hjlt (by simpa using hxj)) (fun hN' hg => ?_) hret
  simp only [PStmt.SemList, PStmt.Sem, OpSem] at hN'
  obtain ⟨hsl, hjmp⟩ := hN'
  obtain ⟨-, -, -, htk⟩ := jumpAt_wd hjmp
  have hgo' := htk (by rw [hone]; exact one_ne_zero)
  have hss : stagesSize (blocks'' :: Sg'') = armsSize blocks'' + stagesSize Sg'' := rfl
  refine htail.2 (pos + armsSize blocks) N kj kretP khalt g next kret _ _ (by omega) hfillT hfps
    hjoin hgo' hsfp (fun j'' hj'' hx'' => ?_) hg hnext hret
  have hjb'' : j'' < blocks''.length := htail.1 ▸ hj''
  have hle'' := armsSize_take_le blocks'' j''
  obtain ⟨hmem, -⟩ := armsFills_mem ctx.name nf'' blocks'' 0 (pos + armsSize blocks) j'' hjb''
  have hfill'' : FillsIn slots (armsFills ctx.name nf'' blocks'' 0 (pos + armsSize blocks)) := by
    intro y hy
    refine hfillT y ?_
    simp only [stagesFills, List.headD_cons, List.mem_append]
    exact Or.inl hy
  refine slot_entry env hsl hlx hx'' (by simpa using hfill'' _ hmem) (by omega)

include env in
/-- **A chain of `match`es**: the table jump at the first selector enters the stages, and the
statements placed after the chain follow it. -/
theorem head_means {H : Prop} {locs : Std.HashMap V Loc} {sc sc' : Scope} {t : Tables} {x : V}
    {arms : List (List Stmt)} {rest' : List Stmt} {hints : List LHint}
    {join lx entry one sfp : Cell} {first : ℕ} {F' : List ℕ} {blocks : List (List PStmt)}
    {Sg : List (List (List PStmt))} {ps : List PStmt}
    (hH : H → Sub locs F → PoolOK Γ.L fp sc → SharedIn slots t →
      wd Γ.L fp lx = valP Γ.L fp F x ∧ wd Γ.L fp sfp = ofK fp ∧ wd Γ.L fp one = 1 ∧
      TailOK Γ fp F ctx C U slots B join first x arms rest' sc' F' blocks Sg ps) :
    Means Γ fp F ctx slots B H locs sc sc' t
      ([.chain hints join lx entry one sfp (first :: F') (blocks :: Sg)] ++ ps)
      (OblList C U Γ.L.read (valP Γ.L fp F) (.match_ x arms :: rest'))
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) (.match_ x arms :: rest') next
        kret) := by
  intro pos N kj kretP khalt g next kret hH' hF hp hB hfill hent hsem hG hnext hret
  obtain ⟨hlx, hsfp, hone, htail⟩ := hH hH' hF hp hent
  simp only [List.singleton_append, PStmt.SemList, PStmt.Sem, List.headD_cons] at hsem
  obtain ⟨hsetj, hslot, hj⟩ := hsem
  obtain ⟨-, -, -, htaken⟩ := jumpAt_wd hj
  have hgo := htaken (by rw [hone]; exact one_ne_zero)
  have hpc := env.pcLt
  have hBs : pos + (3 + stagesSize (blocks :: Sg) + blockSize ps) ≤ B := by
    simpa [blockSize, stmtSize] using hB
  simp only [List.singleton_append, blockFills, stmtFills, stmtSize] at hfill
  have e : pos + (3 + stagesSize (blocks :: Sg)) = pos + 3 + stagesSize (blocks :: Sg) := by omega
  simp only [stmtSize] at hgo
  rw [e] at hgo hfill
  have hjoin := holds_set_local env.pow (by omega) hsetj
  have hss : stagesSize (blocks :: Sg) = armsSize blocks + stagesSize Sg := rfl
  refine htail.2 (pos + 3) N kj kretP khalt g next kret _ _ (by omega) hfill.left hfill.right
    hjoin hgo hsfp (fun j hj hxj => ?_) hG hnext hret
  have hjb : j < blocks.length := htail.1 ▸ hj
  have hle := armsSize_take_le blocks j
  obtain ⟨hmem, -⟩ := armsFills_mem ctx.name first blocks 0 (pos + 3) j hjb
  have hfillA : FillsIn slots (armsFills ctx.name first blocks 0 (pos + 3)) := by
    intro y hy
    refine hfill.left y ?_
    simp only [stagesFills, List.headD_cons, List.mem_append]
    exact Or.inl hy
  exact slot_entry env hslot hlx hxj (by simpa using hfillA _ hmem) (by omega)

end

/-! ## The walk of a chain -/

/-- **The arms of a `match` whose arms dispatch into the next**, each a block of its own. -/
theorem placeArms_next_wp (lx' : Cell) (nf : ℕ) (one sfp : Cell) (n base : ℕ) :
    ∀ (arms : List (List Stmt)) (j : ℕ) (st : St),
    (∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) → Plain st →
    wpP (placeArms arms j n base (.next lx' nf one sfp)) ctx st (fun blocks st₁ => Plain st₁ ∧
      Quiet st st₁ ∧ (SharedIn slots st₁.tables → Sub st₁.locs F →
        PoolOK Γ.L fp st.scope → ArmsSemN Γ fp F ctx C U slots B lx' nf one sfp arms blocks))
  | [], j, st, _, hpl => by
      rw [placeArms]
      exact wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ⟨⟨hpl.chainIn⟩,
        Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ _ _ => trivial⟩))
  | arm :: more, j, st, ih, hpl => by
      rw [placeArms]
      refine wp_bind.mpr (wp_modify.mpr ?_)
      refine wp_bind.mpr fun blk st1 he1 => ?_
      obtain ⟨hp1, hq1, hm1⟩ := inBlock_spec (ih arm List.mem_cons_self)
        { st with next := base } ⟨hpl.chainIn⟩ blk st1 he1
      refine wp_bind.mpr (wp_modifyGet.mpr (wp_bind.mpr (wp_pure.mpr ?_)))
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr fun blocks st2 he2 => ?_
      obtain ⟨hp2, hq2, ha2⟩ := placeArms_next_wp lx' nf one sfp n base more (j + 1)
        { st1 with next := st1.next + 1 } (fun a ha => ih a (List.mem_cons_of_mem _ ha))
        ⟨hp1.chainIn⟩ blocks st2 he2
      refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
      have hq0 : Quiet st { st with next := base } := Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hq1' : Quiet st1 { st1 with next := st1.next + 1 } :=
        Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨⟨hp2.chainIn⟩, (((hq0.trans hq1).trans hq1').trans hq2).trans
        (Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, rfl⟩), fun hent hF hp => ?_⟩
      exact ⟨⟨blk, st1.next, rfl, hm1.blockSem (hq2.locs.trans hF) hp (hent.of_le hq2.tables)⟩,
        ha2 hent hF (hq1.scope ▸ hp)⟩

/-- The last placed statement is the chain, when nothing but single instructions was placed after
it and the last is a chain: nothing was placed after it. -/
theorem back_chain {out : Array PStmt} {pre ops : List PStmt} {Cn : PStmt}
    (ho : out.toList = pre ++ [Cn] ++ ops) (hops : OpsOnly ops) {h : List LHint}
    {j x e o s : Cell} {f : List ℕ} {sg : List (List (List PStmt))}
    (hb : out.back? = some (.chain h j x e o s f sg)) :
    ops = [] ∧ Cn = .chain h j x e o s f sg ∧
      ∀ node, (out.pop.push node).toList = pre ++ [node] := by
  have hlast : out.toList.getLast? = some (.chain h j x e o s f sg) := by
    rw [← hb]
    simp [Array.back?, List.getLast?_eq_getElem?]
  rcases List.eq_nil_or_concat ops with rfl | ⟨ops', o', rfl⟩
  · rw [ho] at hlast
    simp only [List.append_nil, List.getLast?_append, List.getLast?_singleton] at hlast
    refine ⟨rfl, Option.some.inj hlast, fun node => ?_⟩
    rw [Array.toList_push, Array.toList_pop, ho]
    simp
  · exfalso
    rw [ho] at hlast
    obtain ⟨hh, oo, rfl⟩ := hops o' (by simp)
    rw [List.concat_eq_append, ← List.append_assoc, List.getLast?_append] at hlast
    simp at hlast

/-- A stage was added to the chain the walk has open. -/
structure StageOut (st st' : St) (pre : List PStmt) (h : List LHint) (j₀ x₀ e₀ o₀ s₀ : Cell)
    (firsts : List ℕ) (stages : List (List (List PStmt))) (nf : ℕ) (blocks : List (List PStmt)) :
    Prop where
  out : st'.out.toList = pre ++ [.chain h j₀ x₀ e₀ o₀ s₀ (firsts ++ [nf]) (stages ++ [blocks])]
  locs : Sub st.locs st'.locs
  tables : TablesLe st.tables st'.tables

theorem opsOnly_append {a b : List PStmt} (ha : OpsOnly a) (hb : OpsOnly b) : OpsOnly (a ++ b) :=
  fun s hs => (List.mem_append.mp hs).elim (ha s) (hb s)

section

variable (env : PlaceEnv Γ fp ctx C U slots B) {pre : List PStmt} {h : List LHint}
  {j₀ x₀ e₀ o₀ s₀ : Cell} {firsts : List ℕ} {stages : List (List (List PStmt))}
  {ops₀ : List PStmt}

include env in
/-- **The last `match` of a chain**: placed as one more stage of the chain before it, its arms
jumping to the join. Nothing is placed between the chain and it. -/
theorem entered_closed_wp (x : V) (arms : List (List Stmt)) (rest : List Stmt) (nf : ℕ)
    (join : Cell) (st : St) (hpl : Plain st)
    (hout : st.out.toList = pre ++ [.chain h j₀ x₀ e₀ o₀ s₀ firsts stages] ++ ops₀)
    (hops₀ : OpsOnly ops₀)
    (ih : ∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) :
    wpP (placeMatch x arms.length rest (some (nf, join)) false fun base exit =>
        placeArms arms 0 arms.length base exit) ctx st (fun _ st' => ops₀ = [] ∧ ∃ blocks,
      StageOut st st' pre h j₀ x₀ e₀ o₀ s₀ firsts stages nf blocks ∧ Plain st' ∧
      (Sub st'.locs F → SharedIn slots st'.tables → PoolOK Γ.L fp st.scope →
        PoolOK Γ.L fp st'.scope ∧ ∃ one sfp, wd Γ.L fp one = 1 ∧ wd Γ.L fp sfp = ofK fp ∧
          ArmsSem Γ fp F ctx C U slots B join one sfp arms.length arms blocks 0)) := by
  unfold placeMatch
  rw [matchCells_false]
  simp only [bind_assoc, pure_bind]
  refine wp_bind.mpr fun lx s1 h1 => wp_bind.mpr fun sfp s2 h2 => wp_bind.mpr fun one s3 h3 => ?_
  have e1 := cellOf_spec (Γ := Γ) (fp := fp) (F := F) x st lx s1 h1
  have e2 := selfFp_spec (Γ := Γ) (F := F) env.main s1 sfp s2 h2
  have e3 := oneCell_spec (Γ := Γ) (fp := fp) (F := F) (ctx := ctx) s2 one s3 h3
  have e := (e1.trans (e2.weaken fun _ => trivial)).trans (e3.weaken fun _ => trivial)
  show wpP _ ctx s3 _
  obtain ⟨ops, ho, hops, hl, hs, hf⟩ := e
  refine wp_bind.mpr (wp_get.mpr ?_)
  refine wp_bind.mpr fun blocks s4 h4 => ?_
  obtain ⟨hp4, hq4, ha4⟩ := placeArms_wp join one sfp arms.length s3.next arms 0 s3 ih
    (hpl.of_same hs) blocks s4 h4
  refine wp_bind.mpr (wp_expect fun s5 h5 => ?_)
  refine wp_bind.mpr (wp_get.mpr ?_)
  have ho5 : s5.out.toList = pre ++ [.chain h j₀ x₀ e₀ o₀ s₀ firsts stages] ++ (ops₀ ++ ops) := by
    rw [h5.out, hq4.out, ho, hout]
    simp only [List.append_assoc]
  split
  · next hh jj xx ee oo ss ff sg hb =>
    obtain ⟨hnil, hC, hpush⟩ := back_chain ho5 (opsOnly_append hops₀ hops) hb
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil
    cases hC
    refine wp_bind.mpr (wp_set.mpr (wp_pure.mpr ⟨rfl, blocks, ⟨hpush _, ?_, ?_⟩, ⟨?_⟩,
      fun hF hent hp => ?_⟩))
    · show Sub st.locs s5.locs
      rw [h5.locs]
      exact hl.trans hq4.locs
    · show TablesLe st.tables s5.tables
      rw [h5.tables]
      exact (TablesLe.of_eq hs.tables).trans hq4.tables
    · show s5.chainIn = none
      rw [h5.chainIn]
      exact hp4.chainIn
    · have hF4 : Sub s4.locs F := h5.locs ▸ hF
      obtain ⟨hp3, ⟨⟨-, h2q⟩, h3q⟩, -⟩ := hf 0 True (fun _ _ => True) True (fun _ _ => True)
        trivial (hq4.locs.trans hF4) hp (by simp [PStmt.SemList])
      refine ⟨?_, one, sfp, h3q, h2q, ha4 (h5.tables ▸ hent) hF4 hp3⟩
      show PoolOK Γ.L fp s5.scope
      rw [h5.scope, hq4.scope]
      exact hp3
  · exact wp_bind.mpr wp_failP

include env in
/-- **A `match` of a chain that is neither its first nor its last**: one more stage, its arms
dispatching into the `match` after it. -/
theorem entered_open_wp (x x'' : V) (arms arms'' : List (List Stmt)) (rest'' : List Stmt)
    (nf : ℕ) (join : Cell) (st : St) (hpl : Plain st)
    (hout : st.out.toList = pre ++ [.chain h j₀ x₀ e₀ o₀ s₀ firsts stages] ++ ops₀)
    (hops₀ : OpsOnly ops₀)
    (ih : ∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) :
    wpP (placeMatch x arms.length (.match_ x'' arms'' :: rest'') (some (nf, join)) true
        fun base exit => placeArms arms 0 arms.length base exit) ctx st (fun _ st' =>
      ops₀ = [] ∧ ∃ blocks nf'' lx'',
        StageOut st st' pre h j₀ x₀ e₀ o₀ s₀ firsts stages nf blocks ∧
      st'.chainIn = some (nf'', join) ∧
      (Sub st'.locs F → SharedIn slots st'.tables → PoolOK Γ.L fp st.scope →
        PoolOK Γ.L fp st'.scope ∧ ∃ one sfp, wd Γ.L fp one = 1 ∧ wd Γ.L fp sfp = ofK fp ∧
          wd Γ.L fp lx'' = valP Γ.L fp F x'' ∧
          ArmsSemN Γ fp F ctx C U slots B lx'' nf'' one sfp arms blocks)) := by
  unfold placeMatch
  rw [matchCells_true]
  simp only [bind_assoc, pure_bind]
  refine wp_bind.mpr fun lx s1 h1 => wp_bind.mpr fun lx'' s2 h2 => wp_bind.mpr fun sfp s3 h3 =>
    wp_bind.mpr fun one s4 h4 => ?_
  have e1 := cellOf_spec (Γ := Γ) (fp := fp) (F := F) x st lx s1 h1
  have e2 := cellOf_spec (Γ := Γ) (fp := fp) (F := F) x'' s1 lx'' s2 h2
  have e3 := selfFp_spec (Γ := Γ) (F := F) env.main s2 sfp s3 h3
  have e4 := oneCell_spec (Γ := Γ) (fp := fp) (F := F) (ctx := ctx) s3 one s4 h4
  have e := ((e1.trans (e2.weaken fun _ => trivial)).trans (e3.weaken fun _ => trivial)).trans
    (e4.weaken fun _ => trivial)
  show wpP _ ctx s4 _
  obtain ⟨ops, ho, hops, hl, hs, hf⟩ := e
  refine wp_bind.mpr (wp_modifyGet.mpr ?_)
  refine wp_bind.mpr (wp_get.mpr ?_)
  refine wp_bind.mpr (wp_mono (placeArms_next_wp lx'' _ one sfp arms.length _ arms 0 _ ih
    ⟨(hpl.of_same hs).chainIn⟩) fun blocks s5 ⟨_, hq5, ha5⟩ => ?_)
  refine wp_bind.mpr (wp_expect fun s6 h6 => ?_)
  refine wp_bind.mpr (wp_get.mpr ?_)
  have ho6 : s6.out.toList = pre ++ [.chain h j₀ x₀ e₀ o₀ s₀ firsts stages] ++ (ops₀ ++ ops) := by
    rw [h6.out, hq5.out, ho, hout]
    simp only [List.append_assoc]
  split
  · next hh jj xx ee oo ss ff sg hb =>
    obtain ⟨hnil, hC, hpush⟩ := back_chain ho6 (opsOnly_append hops₀ hops) hb
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil
    cases hC
    refine wp_bind.mpr (wp_set.mpr (wp_modify.mpr ⟨rfl, blocks, s4.tables.len, lx'',
      ⟨hpush _, ?_, ?_⟩, rfl, fun hF hent hp => ?_⟩))
    · show Sub st.locs s6.locs
      rw [h6.locs]
      exact hl.trans hq5.locs
    · show TablesLe st.tables s6.tables
      rw [h6.tables]
      exact (TablesLe.of_eq hs.tables).trans ⟨fun p hp => hq5.tables.shared p hp⟩
    · have hF5 : Sub s5.locs F := h6.locs ▸ hF
      obtain ⟨hp4, ⟨⟨⟨-, h2q⟩, h3q⟩, h4q⟩, -⟩ := hf 0 True (fun _ _ => True) True
        (fun _ _ => True) trivial (hq5.locs.trans hF5) hp (by simp [PStmt.SemList])
      refine ⟨?_, one, sfp, h4q, h3q, h2q, ha5 (h6.tables ▸ hent) hF5 hp4⟩
      show PoolOK Γ.L fp s6.scope
      rw [h6.scope, hq5.scope]
      exact hp4
  · exact wp_bind.mpr wp_failP

include env in
/-- **A `match` the open chain enters**: one more stage of the chain, its last if the trace marks
no `chain` before it, else one whose arms dispatch into the `match` after it. -/
theorem entered_wp (x : V) (arms : List (List Stmt)) (rest : List Stmt) (nf : ℕ) (join : Cell)
    (st : St) (hci : st.chainIn = some (nf, join))
    (hout : st.out.toList = pre ++ [.chain h join x₀ e₀ o₀ s₀ firsts stages])
    (ih : ∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) :
    wpP (placeStmt (.match_ x arms) rest) ctx st (fun _ st' => ∃ blocks,
      StageOut st st' pre h join x₀ e₀ o₀ s₀ firsts stages nf blocks ∧
      (Sub st'.locs F → SharedIn slots st'.tables → PoolOK Γ.L fp st.scope →
        PoolOK Γ.L fp st'.scope) ∧
      ((st'.chainIn = none ∧ (Sub st'.locs F → SharedIn slots st'.tables →
          PoolOK Γ.L fp st.scope → ∃ one sfp, wd Γ.L fp one = 1 ∧ wd Γ.L fp sfp = ofK fp ∧
            ArmsSem Γ fp F ctx C U slots B join one sfp arms.length arms blocks 0)) ∨
        ∃ x'' arms'' rest'' nf'' lx'', rest = .match_ x'' arms'' :: rest'' ∧
          st'.chainIn = some (nf'', join) ∧
          (Sub st'.locs F → SharedIn slots st'.tables → PoolOK Γ.L fp st.scope →
            ∃ one sfp, wd Γ.L fp one = 1 ∧ wd Γ.L fp sfp = ofK fp ∧
              wd Γ.L fp lx'' = valP Γ.L fp F x'' ∧
              ArmsSemN Γ fp F ctx C U slots B lx'' nf'' one sfp arms blocks))) := by
  rw [placeStmt]
  refine wp_bind.mpr fun _ st1 he1 => ?_
  obtain ⟨ops1, ho1, hops1, hl1, hs1, hf1⟩ :=
    flush_spec (Γ := Γ) (fp := fp) (F := F) [] st _ st1 he1
  refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr ?_)))
  have hci1 : st1.chainIn = some (nf, join) := hs1.chainIn.trans hci
  have hout1 : ({ st1 with chainIn := none, chain := false } : St).out.toList =
      pre ++ [.chain h join x₀ e₀ o₀ s₀ firsts stages] ++ ops1 := by
    show st1.out.toList = _
    rw [ho1, hout]
  have hp1 : ops1 = [] → Sub st1.locs F → PoolOK Γ.L fp st.scope → PoolOK Γ.L fp st1.scope :=
    fun hnil hF hp => (hf1 0 True (fun _ _ => True) True (fun _ _ => True) trivial hF hp
      (by subst hnil; simp [PStmt.SemList])).1
  rw [hci1]
  cases hc : st1.chain
  · refine wp_mono (entered_closed_wp env x arms rest nf join _ ⟨rfl⟩ hout1 hops1 ih) ?_
    rintro _ st' ⟨hnil, blocks, hso, hpl', hfin⟩
    refine ⟨blocks, ⟨hso.out, hl1.trans hso.locs, (TablesLe.of_eq hs1.tables).trans hso.tables⟩,
      fun hF hent hp => (hfin hF hent (hp1 hnil (hso.locs.trans hF) hp)).1,
      Or.inl ⟨hpl'.chainIn, fun hF hent hp => (hfin hF hent (hp1 hnil (hso.locs.trans hF) hp)).2⟩⟩
  · by_cases hr : ∃ x'' arms'' rest'', rest = .match_ x'' arms'' :: rest''
    · obtain ⟨x'', arms'', rest'', rfl⟩ := hr
      refine wp_mono
        (entered_open_wp env x x'' arms arms'' rest'' nf join _ ⟨rfl⟩ hout1 hops1 ih) ?_
      rintro _ st' ⟨hnil, blocks, nf'', lx'', hso, hci', hfin⟩
      refine ⟨blocks, ⟨hso.out, hl1.trans hso.locs, (TablesLe.of_eq hs1.tables).trans hso.tables⟩,
        fun hF hent hp => (hfin hF hent (hp1 hnil (hso.locs.trans hF) hp)).1,
        Or.inr ⟨x'', arms'', rest'', nf'', lx'', rfl, hci', fun hF hent hp =>
          (hfin hF hent (hp1 hnil (hso.locs.trans hF) hp)).2⟩⟩
    · unfold placeMatch
      exact wp_bind.mpr (matchCells_true_fail x rest (fun a b c e => hr ⟨a, b, c, e⟩) _)

end

section

variable (Γ fp F ctx C U slots B)

/-- **What a block entered by an open chain lays**: from a state whose last placed statement is
the chain and whose open chain is `(nf, join)`, the block, a `match` first, adds its stages to the
chain and places the statements after them, and `TailOK` says what the stages from that `match`
on and those statements mean. -/
def OpenOK : List Stmt → Prop
  | .match_ x arms :: rest => ∀ (st : St) (nf : ℕ) (join : Cell) (pre : List PStmt)
      (h : List LHint) (x₀ e₀ o₀ s₀ : Cell) (firsts : List ℕ) (stages : List (List (List PStmt))),
      st.chainIn = some (nf, join) →
      st.out.toList = pre ++ [.chain h join x₀ e₀ o₀ s₀ firsts stages] →
      wpP (placeBlock (.match_ x arms :: rest)) ctx st (fun _ st' => Plain st' ∧
        ∃ F' blocks Sg ps, st'.out.toList =
            pre ++ [.chain h join x₀ e₀ o₀ s₀ (firsts ++ nf :: F') (stages ++ blocks :: Sg)] ++ ps ∧
          Sub st.locs st'.locs ∧ TablesLe st.tables st'.tables ∧
          (Sub st'.locs F → SharedIn slots st'.tables → PoolOK Γ.L fp st.scope →
            TailOK Γ fp F ctx C U slots B join nf x arms rest st'.scope F' blocks Sg ps))
  | _ => True

end

/-- A statement, then the rest of its block. -/
theorem LaysAt.seq {H : Prop} {st : St} {s : Stmt} {rest : List Stmt} {m : P Unit}
    (h1 : LaysAt Γ fp F ctx slots B H st m (Obl C U Γ.L.read (valP Γ.L fp F) s)
      (StmtS C Γ.L.read (valP Γ.L fp F) s rest))
    (h2 : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock rest)
      (OblList C U Γ.L.read (valP Γ.L fp F) rest)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) rest next kret)) :
    LaysAt Γ fp F ctx slots B H st (m >>= fun _ => endStmt >>= fun _ => placeBlock rest)
      (OblList C U Γ.L.read (valP Γ.L fp F) (s :: rest))
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) (s :: rest) next kret) := by
  intro hpl
  refine wp_bind.mpr fun _ st1 he1 => wp_bind.mpr fun _ st2 he2 _ st3 he3 => ?_
  obtain ⟨hp1, l1⟩ := h1 hpl _ st1 he1
  have e2 := endStmt_spec (Γ := Γ) (fp := fp) (F := F) st1 _ st2 he2
  obtain ⟨hp3, l3⟩ := h2 st2 (hp1.of_same e2.same) _ st3 he3
  refine ⟨hp3, ((l1.suffix e2).cons (l3.weaken fun _ => trivial)).imp (fun g h => h)
    fun next kret h => ?_⟩
  exact h fun hr hk => by
    subst hr
    exact hk

section

variable (env : PlaceEnv Γ fp ctx C U slots B)

include env in
/-- **A block that an open chain enters**, its `match`'s arms, the rest of the block and the
chain's later stages sound. -/
theorem open_step (x : V) (arms : List (List Stmt)) (rest : List Stmt)
    (iha : ∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret))
    (ihr : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock rest)
      (OblList C U Γ.L.read (valP Γ.L fp F) rest)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) rest next kret))
    (iho : OpenOK Γ fp F ctx C U slots B rest) :
    OpenOK Γ fp F ctx C U slots B (.match_ x arms :: rest) := by
  intro st nf join pre h x₀ e₀ o₀ s₀ firsts stages hci hout
  rw [placeBlock]
  refine wp_bind.mpr fun _ st1 he1 => ?_
  obtain ⟨blocks, hso, hpool, hcase⟩ := entered_wp env x arms rest nf join st hci hout iha _ st1 he1
  refine wp_bind.mpr (wp_modify.mpr ?_)
  rcases hcase with ⟨hci1, harms⟩ | ⟨x'', arms'', rest'', nf'', lx'', rfl, hci1, harms⟩
  · intro _ st' he3
    obtain ⟨hpl', ps, ho, hl, ht, hm⟩ := ihr _ (by exact ⟨hci1⟩) _ st' he3
    refine ⟨hpl', [], blocks, [], ps, ?_, hso.locs.trans hl, hso.tables.trans ht,
      fun hF hent hp => ?_⟩
    · rw [ho]
      show st1.out.toList ++ ps = _
      rw [hso.out]
    · have hF1 : Sub st1.locs F := hl.trans hF
      have hent1 : SharedIn slots st1.tables := hent.of_le ht
      have hp1 := hpool hF1 hent1 hp
      obtain ⟨one, sfp, hone, hsfp, harms'⟩ := harms hF1 hent1 hp
      exact tail_closed hone hsfp harms'
        fun pos N kj kretP khalt g next kret hB hfill hsem hG hnext hret =>
          hm pos N kj kretP khalt g next kret trivial hF hp1 hB hfill hent hsem hG hnext hret
  · intro _ st' he3
    obtain ⟨hpl', F'', blocks'', Sg'', ps, ho, hl, ht, htail⟩ :=
      iho _ nf'' join pre h x₀ e₀ o₀ s₀ (firsts ++ [nf]) (stages ++ [blocks]) (by exact hci1)
        (by exact hso.out) _ st' he3
    refine ⟨hpl', nf'' :: F'', blocks, blocks'' :: Sg'', ps, by rw [ho]; simp,
      hso.locs.trans hl, hso.tables.trans ht, fun hF hent hp => ?_⟩
    have hF1 : Sub st1.locs F := hl.trans hF
    have hent1 : SharedIn slots st1.tables := hent.of_le ht
    obtain ⟨one, sfp, hone, hsfp, hlx, harms'⟩ := harms hF1 hent1 hp
    exact tail_open env hone hsfp hlx harms' (htail hF hent (hpool hF1 hent1 hp))

include env in
/-- **The chain statement is placed**: the chain is open in the walk, the block's later
`match`es add their stages to it, and the statement with what follows it means the block. -/
theorem chain_finish {H : Prop} {st : St} {x x' : V} {arms arms' : List (List Stmt)}
    {rest' : List Stmt} {hints : List LHint} {join lx entry one sfp lx' : Cell} {first nf : ℕ}
    {blocks : List (List PStmt)}
    (hH : H → wd Γ.L fp lx = valP Γ.L fp F x ∧ wd Γ.L fp sfp = ofK fp ∧ wd Γ.L fp one = 1 ∧
      wd Γ.L fp lx' = valP Γ.L fp F x' ∧
      ArmsSemN Γ fp F ctx C U slots B lx' nf one sfp arms blocks)
    (iho : OpenOK Γ fp F ctx C U slots B (.match_ x' arms' :: rest')) :
    LaysAt Γ fp F ctx slots B H st
      (push (.chain hints join lx entry one sfp [first] [blocks]) >>= fun _ =>
        modify (fun s : St => { s with chainIn := some (nf, join) }) >>= fun _ =>
          endStmt >>= fun _ => placeBlock (.match_ x' arms' :: rest'))
      (OblList C U Γ.L.read (valP Γ.L fp F) (.match_ x arms :: .match_ x' arms' :: rest'))
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F)
        (.match_ x arms :: .match_ x' arms' :: rest') next kret) := by
  intro _
  refine wp_bind.mpr (wp_modify.mpr (wp_bind.mpr (wp_modify.mpr (wp_bind.mpr
    (wp_modify.mpr ?_)))))
  refine wp_mono (iho _ nf join st.out.toList hints lx entry one sfp [first] [blocks] rfl
    (by simp)) ?_
  rintro _ st' ⟨hpl', F', blocks', Sg, ps, ho, hl, ht, htail⟩
  refine ⟨hpl', [.chain hints join lx entry one sfp (first :: nf :: F') (blocks :: blocks' :: Sg)]
    ++ ps, by rw [ho]; simp, hl, ht, head_means env fun hH' hF hp hent => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH hH'
  exact ⟨h1, h2, h3, tail_open env h3 h2 h4 h5 (htail hF hent hp)⟩

include env in
/-- **The first `match` of a chain**: its arms dispatch into the next `match`'s table. -/
theorem chain_head_lays {H : Prop} (x x' : V) (arms arms' : List (List Stmt)) (rest' : List Stmt)
    (st : St)
    (iha : ∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret))
    (iho : OpenOK Γ fp F ctx C U slots B (.match_ x' arms' :: rest')) :
    LaysAt Γ fp F ctx slots B H st
      (placeMatch x arms.length (.match_ x' arms' :: rest') none true
          (fun base exit => placeArms arms 0 arms.length base exit) >>= fun _ =>
        endStmt >>= fun _ => placeBlock (.match_ x' arms' :: rest'))
      (OblList C U Γ.L.read (valP Γ.L fp F) (.match_ x arms :: .match_ x' arms' :: rest'))
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F)
        (.match_ x arms :: .match_ x' arms' :: rest') next kret) := by
  unfold placeMatch
  rw [matchCells_true]
  simp only [bind_assoc, pure_bind]
  refine LaysAt.call (cellOf_spec x) fun lx _ => ?_
  refine LaysAt.call (cellOf_spec x') fun lx' _ => ?_
  refine LaysAt.call (selfFp_spec env.main) fun sfp _ => ?_
  refine LaysAt.call oneCell_spec fun one _ => ?_
  refine LaysAt.callT fresh_spec fun join _ => ?_
  refine LaysAt.callT takeHints_spec fun hints _ => ?_
  refine LaysAt.step (R := fun _ => True) (wp_modifyGet.mpr
    ⟨⟨rfl, Sub.refl _, rfl, ⟨fun _ h => h⟩, rfl⟩, fun _ _ _ => trivial⟩) fun first _ => ?_
  refine LaysAt.callT fresh_spec fun entry _ => ?_
  refine LaysAt.step (R := fun _ => True) (wp_modifyGet.mpr
    ⟨⟨rfl, Sub.refl _, rfl, ⟨fun _ h => h⟩, rfl⟩, fun _ _ _ => trivial⟩) fun nf _ => ?_
  refine LaysAt.get_bind ?_
  refine LaysAt.plain fun hpl => ?_
  refine LaysAt.step (R := fun blocks => ArmsSemN Γ fp F ctx C U slots B lx' nf one sfp arms blocks)
    (wp_mono (placeArms_next_wp lx' nf one sfp arms.length _ arms 0 _ iha hpl)
      fun _ _ ⟨_, hq, ha⟩ => ⟨hq, ha⟩) fun blocks _ => ?_
  refine LaysAt.callT (expect_spec _ _) fun _ _ => ?_
  exact chain_finish env (fun ⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, h4⟩, _⟩, _⟩, h5⟩ => ⟨h1, h3, h4, h2, h5⟩)
    iho

include env in
/-- **A block that begins with a `match`**: a `match` of its own, or the first of a chain. -/
theorem match_block_lays (x : V) (arms : List (List Stmt)) (rest : List Stmt) (st : St)
    (iha : ∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret))
    (ihr : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock rest)
      (OblList C U Γ.L.read (valP Γ.L fp F) rest)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) rest next kret))
    (iho : OpenOK Γ fp F ctx C U slots B rest) :
    LaysAt Γ fp F ctx slots B True st (placeBlock (.match_ x arms :: rest))
      (OblList C U Γ.L.read (valP Γ.L fp F) (.match_ x arms :: rest))
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) (.match_ x arms :: rest) next
        kret) := by
  rw [placeBlock, placeStmt]
  simp only [bind_assoc]
  refine LaysAt.callT (flush_spec []) fun _ st₁ => ?_
  refine LaysAt.plain fun hpl => ?_
  refine LaysAt.get_bind ?_
  refine LaysAt.step (R := fun _ => True) (wp_set.mpr
    ⟨Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, hpl.chainIn.symm⟩, fun _ _ _ => trivial⟩) fun _ _ => ?_
  rw [hpl.chainIn]
  cases st₁.chain
  · exact LaysAt.seq ((placeMatch_plain_lays env x arms rest _ iha).weaken fun _ => trivial) ihr
  · by_cases hr : ∃ x' arms' rest', rest = .match_ x' arms' :: rest'
    · obtain ⟨x', arms', rest', rfl⟩ := hr
      exact chain_head_lays env x x' arms arms' rest' _ iha iho
    · refine fun _ => wp_bind.mpr ?_
      unfold placeMatch
      exact wp_bind.mpr (matchCells_true_fail x rest (fun a b c e => hr ⟨a, b, c, e⟩) _)

end

end
end LeanVM.Guest.Backend
