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
      Means Γ fp F ctx slots B True s5.locs st.scope st.scope s5.tables s5.out.toList Gb Sb := by
  obtain ⟨ps, ho, hl, ht, hmn⟩ := L
  have hps : s5.out.toList = ps := by simpa using ho
  refine ⟨⟨hpl5.chainIn, hpl5.chain⟩, ⟨h1.out, h1.locs ▸ hl, h1.scope, h1.tables ▸ ht,
    hpl5.chainIn.trans hpl.chainIn.symm, hpl5.chain.trans hpl.chain.symm⟩, ?_⟩
  · rw [hps]
    intro pos N kj kretP khalt g next kret hH hF hp hB hfill hent hsem hG hnext hret
    exact hmn pos N kj kretP khalt g next kret hH hF (h1.scope ▸ hp) hB hfill hent
      hsem hG (fun _ hN hg => hnext hp hN hg) hret

section

variable (hnc : ∀ e ∈ ctx.trace.toList, e.isChain = false)

include hnc in
/-- **A block of its own**: the statements and the pools of the state are as before, and the
statements returned mean what the block's walk lays. -/
theorem inBlock_spec {m : P Unit} {Gb : Prop → Prop} {Sb : Prop → (List E → Prop) → Prop}
    (hm : ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ m Gb Sb) (st : St) (hpl : Plain st) :
    wpP (inBlock m) ctx st (fun blk st₁ => Plain st₁ ∧ Quiet st st₁ ∧
      Means Γ fp F ctx slots B True st₁.locs st.scope st.scope st₁.tables blk Gb Sb) := by
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
      ⟨hq, fun hent hF hp => hmn.blockSem hF hp hent⟩) hf

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
    exact LaysAt.push (ite_means_else env fun h =>
      ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩)
  · refine LaysAt.guard fun hnz => ?_
    have hnz' : nz = [] := by simpa using hnz
    subst hnz'
    refine LaysAt.callT (expect_spec _ _) fun _ _ => ?_
    exact LaysAt.push (ite_means_noelse env fun h => ⟨h.1.1.1.2, h.1.1.2, h.2⟩)

end

/-! ## `match` -/

theorem armsSize_take_succ : ∀ (as : List (List PStmt)) (j : ℕ) (hj : j < as.length),
    armsSize (as.take (j + 1)) = armsSize (as.take j) + blockSize as[j]
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | a :: as, 0, _ => by simp [armsSize]
  | a :: as, j + 1, hj => by
      have := armsSize_take_succ as j (Nat.lt_of_succ_lt_succ hj)
      simp only [List.take_succ_cons, armsSize, List.getElem_cons_succ, this]
      omega

theorem armsSize_take_le : ∀ (as : List (List PStmt)) (j : ℕ),
    armsSize (as.take j) ≤ armsSize as
  | [], _ => by simp [armsSize]
  | a :: as, 0 => by simp [armsSize]
  | a :: as, j + 1 => by
      have := armsSize_take_le as j
      simp only [List.take_succ_cons, armsSize]
      omega

theorem armsSize_take_length (as : List (List PStmt)) : armsSize (as.take as.length) = armsSize as := by
  rw [List.take_length]

/-- Arm `j`'s slot and the slots its block fills are among the stage's. -/
theorem armsFills_mem (f : String) (first : ℕ) : ∀ (as : List (List PStmt)) (j₀ pos j : ℕ)
    (hj : j < as.length),
    (first + (j₀ + j), KVal.at f (pos + armsSize (as.take j))) ∈ armsFills f first as j₀ pos ∧
      ∀ x ∈ blockFills f as[j] (pos + armsSize (as.take j)), x ∈ armsFills f first as j₀ pos
  | [], _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | a :: as, j₀, pos, 0, _ => by
      simp only [armsFills, List.take_zero, armsSize, Nat.add_zero, List.getElem_cons_zero,
        List.mem_cons, List.mem_append]
      exact ⟨Or.inl trivial, fun x hx => Or.inr (Or.inl hx)⟩
  | a :: as, j₀, pos, j + 1, hj => by
      obtain ⟨h1, h2⟩ := armsFills_mem f first as (j₀ + 1) (pos + blockSize a) j
        (Nat.lt_of_succ_lt_succ hj)
      have e : pos + blockSize a + armsSize (as.take j) =
          pos + armsSize ((a :: as).take (j + 1)) := by
        simp only [List.take_succ_cons, armsSize]
        omega
      have e' : j₀ + 1 + j = j₀ + (j + 1) := by omega
      rw [e, e'] at h1
      rw [e] at h2
      simp only [armsFills, List.mem_cons, List.mem_append, List.getElem_cons_succ]
      exact ⟨Or.inr (Or.inr h1), fun x hx => Or.inr (Or.inr (h2 x hx))⟩

section

variable {kj : E → E → Prop} {kretP : Prop} {khalt : E → E → Prop}

/-- A jump to arm `j`'s first instruction runs arm `j`. -/
theorem armsJump_get : ∀ (as : List (List PStmt)) (pos j : ℕ) (hj : j < as.length) {d f : E},
    PStmt.ArmsJump Γ fp as pos kj kretP khalt d f → d = Γ.tgt (pos + armsSize (as.take j)) →
    f = ofK fp →
    PStmt.SemList Γ fp as[j] (pos + armsSize (as.take j))
      (kj (Γ.tgt (pos + armsSize (as.take j) + blockSize as[j])) (ofK fp)) kj kretP khalt
  | [], _, _, hj, _, _, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | a :: as, pos, 0, _, d, f, h, hd, hf => by
      simp only [PStmt.ArmsJump] at h
      simpa [armsSize] using h.1 (by simpa [armsSize] using hd) hf
  | a :: as, pos, j + 1, hj, d, f, h, hd, hf => by
      simp only [PStmt.ArmsJump] at h
      have e : pos + blockSize a + armsSize (as.take j) =
          pos + armsSize ((a :: as).take (j + 1)) := by
        simp only [List.take_succ_cons, armsSize]
        omega
      have := armsJump_get as (pos + blockSize a) j (Nat.lt_of_succ_lt_succ hj) h.2
        (by rw [e]; exact hd) hf
      rw [e] at this
      exact this

end

section

variable (Γ fp F ctx slots B C U)

/-- What the placed arms of a `match` are: each the arm's block, which means the arm, then its
jump to the join, the last falling into it. -/
def ArmsSem (join one sfp : Cell) (n : ℕ) : List (List Stmt) → List (List PStmt) → ℕ → Prop
  | [], [], _ => True
  | arm :: more, b :: blocks, j =>
      (∃ blk, b = blk ++ (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else []) ∧
        BlockSem Γ fp ctx slots B blk (OblList C U Γ.L.read (valP Γ.L fp F) arm)
          (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) ∧
        ArmsSem join one sfp n more blocks (j + 1)
  | _, _, _ => False

end

theorem armsSem_get {join one sfp : Cell} {n : ℕ} : ∀ (arms : List (List Stmt))
    (blocks : List (List PStmt)) (j₀ : ℕ), ArmsSem Γ fp F ctx C U slots B join one sfp n arms blocks j₀ →
    arms.length = blocks.length ∧ ∀ j (h1 : j < arms.length) (h2 : j < blocks.length),
      ∃ blk, blocks[j] = blk ++ (if j₀ + j + 1 != n then [PStmt.op [] (.jump one join sfp)]
        else []) ∧
        BlockSem Γ fp ctx slots B blk (OblList C U Γ.L.read (valP Γ.L fp F) arms[j])
          (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arms[j] next kret)
  | [], [], _, _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | arm :: more, b :: blocks, j₀, h => by
      obtain ⟨hhead, htail⟩ := h
      obtain ⟨hlen, hget⟩ := armsSem_get more blocks (j₀ + 1) htail
      refine ⟨by simp [hlen], fun j h1 h2 => ?_⟩
      cases j with
      | zero => simpa using hhead
      | succ j =>
          have := hget j (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)
          have e : j₀ + 1 + j + 1 = j₀ + (j + 1) + 1 := by omega
          rw [e] at this
          simpa using this

theorem oblArms_get {rd : Reader} {σ : Val} {x : V} {g : Prop} : ∀ (arms : List (List Stmt))
    (j₀ : ℕ), OblArms C U rd σ x j₀ arms g → ∀ j (h : j < arms.length),
      σ x = ofK (addressOfIndex (j₀ + j)) → OblList C U rd σ arms[j] g
  | [], _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | a :: as, j₀, hobl, 0, _, hx => hobl.1 (by simpa using hx)
  | a :: as, j₀, hobl, j + 1, h, hx => by
      have := oblArms_get as (j₀ + 1) hobl.2 j (Nat.lt_of_succ_lt_succ h)
        (by rw [hx]; congr 2; omega)
      simpa using this

section

variable (env : PlaceEnv Γ fp ctx C U slots B)

include env in
/-- **A `match`**: at a selector in range the table jump enters the arm the selector names, the
arm runs, and its jump, or for the last arm its end, is the join. -/
theorem chain_means {H : Prop} {locs : Std.HashMap V Loc} {sc : Scope} {t : Tables} {x : V}
    {arms : List (List Stmt)} {rest : List Stmt} {hints : List LHint}
    {join lx entry one sfp : Cell} {first : ℕ} {blocks : List (List PStmt)}
    (hH : H → wd Γ.L fp lx = valP Γ.L fp F x ∧ wd Γ.L fp sfp = ofK fp ∧ wd Γ.L fp one = 1 ∧
      ArmsSem Γ fp F ctx C U slots B join one sfp arms.length arms blocks 0) :
    Means Γ fp F ctx slots B H locs sc sc t
      [.chain hints join lx entry one sfp [first] [blocks]]
      (Obl C U Γ.L.read (valP Γ.L fp F) (.match_ x arms))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.match_ x arms) rest) := by
  intro pos N kj kretP khalt g next kret hH' _ hp hB hfill _ hsem hG hnext hret _
  obtain ⟨hlx, hsfp, hone, harms⟩ := hH hH'
  simp only [PStmt.SemList, PStmt.Sem, List.headD_cons] at hsem
  obtain ⟨hsetj, hslot, hj⟩ := hsem
  obtain ⟨-, -, -, htaken⟩ := jumpAt_wd hj
  have hgo := htaken (by rw [hone]; exact one_ne_zero)
  simp only [PStmt.StagesJump] at hgo
  obtain ⟨⟨j, hjlt, hxj⟩, hGarms⟩ := hG
  obtain ⟨hlen, hget⟩ := armsSem_get arms blocks 0 harms
  have hjb : j < blocks.length := hlen ▸ hjlt
  obtain ⟨blk, hblk, hbs⟩ := hget j hjlt hjb
  have hB' : pos + (3 + armsSize blocks) ≤ B := by
    simpa [blockSize, stmtSize, stagesSize] using hB
  have hpc := env.pcLt
  have hle := armsSize_take_le blocks j
  have hsucc := armsSize_take_succ blocks j hjb
  have hle' := armsSize_take_le blocks (j + 1)
  have hfill' : FillsIn slots (armsFills ctx.name first blocks 0 (pos + 3)) := by
    simpa [blockFills, stmtFills, stagesFills] using hfill
  obtain ⟨hslotj, hbf⟩ := armsFills_mem ctx.name first blocks 0 (pos + 3) j hjb
  have hjoin : wd Γ.L fp join = Γ.tgt (pos + 3 + armsSize blocks) := by
    have := holds_set_local env.pow (by simp only [stagesSize]; omega) hsetj
    simpa [stagesSize] using this
  have hent : wd Γ.L fp entry = Γ.tgt (pos + 3 + armsSize (blocks.take j)) := by
    have hread := (holds_slot hslot).2
    rw [hlx, hxj] at hread
    have e : (ofK (addressOfIndex j)).limb 0 * addressOfIndex (Γ.l.tablesBase + first) =
        addressOfIndex (Γ.l.tablesBase + (first + (0 + j))) := by
      simp only [limb_ofK, Fin.val_zero, ↓reduceIte, addressOfIndex, ← pow_add]
      congr 1
      omega
    rw [e, env.jt _ _ _ (hfill' _ hslotj) rfl, env.self] at hread
    exact (Option.some.inj hread).symm.trans (Γ.l.immediateWord_pow env.pow (by
      show _ < 2 ^ 128
      omega))
  have hsemj := armsJump_get blocks (pos + 3) j hjb hgo.1 hent hsfp
  have hsizej : blockSize blocks[j] = blockSize blk +
      blockSize (if 0 + j + 1 != arms.length then [PStmt.op [] (.jump one join sfp)] else []) := by
    rw [hblk, blockSize_append]
  have hbfj : FillsIn slots (blockFills ctx.name blk (pos + 3 + armsSize (blocks.take j))) := by
    intro y hy
    refine hfill' y (hbf y ?_)
    rw [hblk, blockFills_append]
    exact List.mem_append_left _ hy
  rw [hblk, semList_append] at hsemj
  refine (holds_match_iff x arms next kret).mpr ⟨j, hjlt, hxj, ?_⟩
  refine hbs _ _ _ kretP khalt g next kret (by omega) hbfj hsemj
    (oblArms_get arms 0 hGarms j hjlt (by simpa using hxj)) (fun hN' hg => ?_) hret
  by_cases hlast : 0 + j + 1 = arms.length
  · have hall : armsSize (blocks.take (j + 1)) = armsSize blocks := by
      rw [show j + 1 = blocks.length by omega, List.take_length]
    simp only [hlast, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, PStmt.SemList,
      List.append_nil, blockSize, Nat.add_zero] at hN' hsizej
    refine hnext hp (hN' ?_ trivial) hg
    show Γ.tgt _ = Γ.tgt _
    congr 1
    omega
  · have hne : (0 + j + 1 != arms.length) = true := by simpa using hlast
    simp only [hne, ↓reduceIte, PStmt.SemList, PStmt.Sem, OpSem] at hN'
    obtain ⟨-, -, -, htk⟩ := jumpAt_wd hN'
    exact hnext hp (htk (by rw [hone]; exact one_ne_zero) hjoin hsfp) hg

end

theorem Quiet.of_eqv {st st' : St} (h : Eqv st st') : Quiet st st' :=
  ⟨h.out, h.locs ▸ Sub.refl _, h.scope, TablesLe.of_eq h.tables, h.chainIn, h.chain⟩

theorem Quiet.trans {st st' st'' : St} (h₁ : Quiet st st') (h₂ : Quiet st' st'') : Quiet st st'' :=
  ⟨h₂.out.trans h₁.out, h₁.locs.trans h₂.locs, h₂.scope.trans h₁.scope, h₁.tables.trans h₂.tables,
    h₂.chainIn.trans h₁.chainIn, h₂.chain.trans h₁.chain⟩

section

variable (hnc : ∀ e ∈ ctx.trace.toList, e.isChain = false)

include hnc in
/-- **The arms of a `match`**, each a block of its own from one cell on. -/
theorem placeArms_wp (join one sfp : Cell) (n base : ℕ) : ∀ (arms : List (List Stmt)) (j : ℕ)
    (st : St), (∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) → Plain st →
    wpP (placeArms arms j n base (.join join one sfp)) ctx st (fun blocks st₁ => Plain st₁ ∧
      Quiet st st₁ ∧ (SharedIn slots st₁.tables → Sub st₁.locs F →
        PoolOK Γ.L fp st.scope → ArmsSem Γ fp F ctx C U slots B join one sfp n arms blocks j))
  | [], j, st, _, hpl => by
      rw [placeArms]
      exact wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ⟨⟨hpl.chainIn, hpl.chain⟩,
        Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ _ => trivial⟩))
  | arm :: more, j, st, ih, hpl => by
      rw [placeArms]
      refine wp_bind.mpr (wp_modify.mpr ?_)
      refine wp_bind.mpr fun blk st1 he1 => ?_
      obtain ⟨hp1, hq1, hm1⟩ := inBlock_spec hnc (ih arm List.mem_cons_self)
        { st with next := base } ⟨hpl.chainIn, hpl.chain⟩ blk st1 he1
      refine wp_bind.mpr (wp_pure.mpr ?_)
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr fun blocks st2 he2 => ?_
      obtain ⟨hp2, hq2, ha2⟩ := placeArms_wp join one sfp n base more (j + 1) st1
        (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hp1 blocks st2 he2
      refine wp_bind.mpr (wp_modify.mpr (wp_pure.mpr ?_))
      have hq0 : Quiet st { st with next := base } := Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨⟨hp2.chainIn, hp2.chain⟩, ((hq0.trans hq1).trans hq2).trans
        (Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩), fun hent hF hp => ?_⟩
      exact ⟨⟨blk, rfl, hm1.blockSem (hq2.locs.trans hF) hp (hent.of_le hq2.tables)⟩,
        ha2 hent hF (hq1.scope ▸ hp)⟩

variable (env : PlaceEnv Γ fp ctx C U slots B)

include env hnc in
/-- `match`, not chained, its arms' placement sound. -/
theorem match_lays (x : V) (arms : List (List Stmt)) (rest : List Stmt) (st : St)
    (ih : ∀ arm ∈ arms, ∀ st₀, LaysAt Γ fp F ctx slots B True st₀ (placeBlock arm)
      (OblList C U Γ.L.read (valP Γ.L fp F) arm)
      (fun next kret => Stmt.HoldsList C Γ.L.read (valP Γ.L fp F) arm next kret)) :
    LaysAt Γ fp F ctx slots B True st (placeStmt (.match_ x arms) rest)
      (Obl C U Γ.L.read (valP Γ.L fp F) (.match_ x arms))
      (StmtS C Γ.L.read (valP Γ.L fp F) (.match_ x arms) rest) := by
  rw [placeStmt]
  refine LaysAt.callT (flush_spec hnc []) fun _ st₁ => ?_
  refine LaysAt.plain fun hpl => ?_
  refine LaysAt.get_bind ?_
  simp only [hpl.chainIn, hpl.chain, Bool.false_eq_true, ↓reduceIte, pure_bind]
  refine LaysAt.step (R := fun _ => True) (wp_set.mpr
    ⟨Quiet.of_eqv ⟨rfl, rfl, rfl, rfl, hpl.chainIn.symm, hpl.chain.symm⟩,
      fun _ _ _ => trivial⟩) fun _ _ => ?_
  refine LaysAt.call (cellOf_spec x) fun lx _ => ?_
  refine LaysAt.call (selfFp_spec env.main) fun sfp _ => ?_
  refine LaysAt.call oneCell_spec fun one _ => ?_
  refine LaysAt.callT fresh_spec fun join _ => ?_
  refine LaysAt.callT takeHints_spec fun hints st₂ => ?_
  refine LaysAt.step (R := fun _ => True) (wp_modifyGet.mpr
    ⟨⟨rfl, Sub.refl _, rfl, ⟨fun _ h => h⟩, rfl, rfl⟩, fun _ _ _ => trivial⟩)
    fun first _ => ?_
  refine LaysAt.callT fresh_spec fun entry st₃ => ?_
  refine LaysAt.get_bind ?_
  refine LaysAt.plain fun hpl' => ?_
  refine LaysAt.step (R := fun blocks => ArmsSem Γ fp F ctx C U slots B join one sfp arms.length
      arms blocks 0)
    (wp_mono (placeArms_wp hnc join one sfp arms.length st₃.next arms 0 st₃ ih hpl')
      fun _ _ ⟨_, hq, ha⟩ => ⟨hq, ha⟩) fun blocks _ => ?_
  refine LaysAt.callT (expect_spec _ _) fun _ _ => ?_
  refine fun hpl'' => wp_bind.mpr (wp_mono (LaysAt.push (chain_means env fun h =>
    ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.2⟩) hpl'') fun _ _ hq => wp_pure.mpr hq)

end

end
end LeanVM.Guest.Backend
