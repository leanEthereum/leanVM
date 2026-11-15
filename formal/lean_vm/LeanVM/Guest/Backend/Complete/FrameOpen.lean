/-
  LeanVM.Guest.Backend.Complete.FrameOpen

  A block entered by an open chain: its leading `match`es extend the chain node.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameStage
public import LeanVM.Guest.Backend.Complete.FrameOpOut

/-!
# Blocks entered by an open chain

`openOff`: placing a block entered by an open chain (its first statement a `match` the `match`
before it dispatches into) only extends the chain node at the end of the output by the stages
its leading `match`es make, then appends the rest's output; no `match` chains out after it. A
stage's flush and cells push straight-line instructions only, so the chain node is the last of
the output when the stage extends it only if they pushed nothing (`last_chain`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

section Off

variable {ctx : Backend.Ctx}

/-- The last of an output ending in straight-line instructions is a chain node only if there are
none, and it is the node before them. -/
theorem last_chain {O ops : List PStmt} {a b : PStmt}
    (hops : ∀ s ∈ ops, ∃ h o, s = PStmt.op h o)
    (hb : (O ++ [a] ++ ops).getLast? = some b) (hc : ∀ h o, b ≠ .op h o) : ops = [] ∧ b = a := by
  rcases List.eq_nil_or_concat ops with rfl | ⟨L, c, rfl⟩
  · simp at hb
    exact ⟨rfl, hb.symm⟩
  · rw [List.concat_eq_append] at hb hops ⊢
    rw [← List.append_assoc, List.getLast?_concat, Option.some.injEq] at hb
    subst hb
    obtain ⟨h, o, e⟩ := hops c (by simp)
    exact absurd e (hc h o)

/-- **The output of a block entered by an open chain**: the chain node extended by the stages of
its leading `match`es (the first in the table `first`), then the rest's output; no `match`
chaining out. -/
theorem openOff_out (hmono : PlaceMono ctx) : ∀ (ss : List Stmt) (st : St) (O : List PStmt)
    (h : List LHint) (join lx entry one sfp first : ℕ) (firsts : List ℕ)
    (stages : List (List (List PStmt))) (join' : ℕ),
    (∃ x arms rest, ss = .match_ x arms :: rest) → st.chainIn = some (first, join') →
    st.out.toList = O ++ [.chain h join lx entry one sfp firsts stages] →
    wpP (placeBlock ss) ctx st fun _ st' => st'.chainIn = none ∧
      ∃ (firstsN : List ℕ) (stagesN : List (List (List PStmt))) (blk : List PStmt),
        st'.out.toList = O ++ [.chain h join lx entry one sfp (firsts ++ firstsN)
          (stages ++ stagesN)] ++ blk ∧ firstsN.head? = some first
  | [], _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, hs⟩, _, _ => nomatch hs
  | s :: rest, st, O, h, join, lx, entry, one, sfp, first, firsts, stages, join',
      ⟨x, arms, tl, hs⟩, hc, ho => by
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    rw [placeBlock, placeStmt]
    simp only [bind_assoc]
    refine wp_bind.mpr (wp_mono (wp_and (flush_op (st := st) (up := []))
      (flush_keep (st := st) (up := []))) fun _ st₁ ⟨ho₁, hk₁⟩ => ?_)
    have hc₁ : st₁.chainIn = some (first, join') :=
      (show st₁.chainIn = st.chainIn from hk₁).trans hc
    refine wp_bind.mpr (wp_get.mpr (wp_bind.mpr (wp_set.mpr ?_)))
    rw [hc₁]
    unfold placeMatch
    simp only [bind_assoc]
    refine wp_bind.mpr (wp_mono (wp_and (wp_and (matchCells_op (x := x) (rest := rest))
      (matchCells_keep (x := x) (rest := rest))) (matchCells_next _))
      fun r st₃ ⟨⟨ho₃, hk₃⟩, hnx⟩ => ?_)
    have hc₃ : st₃.chainIn = none := hk₃
    obtain ⟨ops₁, hops₁, hop₁⟩ := ho₁.trans ho₃
    obtain ⟨lx₀, nextSel, sfp₀, one₀⟩ := r
    dsimp only at hnx ⊢
    simp only [pure_bind]
    cases nextSel with
    | none =>
      dsimp only
      simp only [bind_assoc]
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr (wp_mono (wp_and (placeArms_mono arms 0 arms.length _ _ _)
        (placeArms_chain arms 0 arms.length _ _ _ hc₃)) fun blocks st₅ ⟨⟨_, _, ho₅⟩, hc₅⟩ => ?_)
      refine wp_bind.mpr (wp_mono (wp_and (expect_op (st := st₅)) (expect_keep (st := st₅)))
        fun _ st₆ ⟨ho₆, hk₆⟩ => ?_)
      have hc₆ : st₆.chainIn = none := (show st₆.chainIn = st₅.chainIn from hk₆).trans hc₅
      obtain ⟨ops₂, hops₂, hop₂⟩ := ho₆
      have hout₆ : st₆.out.toList =
          O ++ [.chain h join lx entry one sfp firsts stages] ++ (ops₁ ++ ops₂) := by
        rw [hops₂, ho₅, hops₁, ho, List.append_assoc]
      have hop : ∀ s ∈ ops₁ ++ ops₂, ∃ h o, s = PStmt.op h o := fun s hs =>
        (List.mem_append.mp hs).elim (hop₁ s) (hop₂ s)
      refine wp_bind.mpr (wp_get.mpr ?_)
      split
      rotate_left
      · exact wp_bind.mpr wp_failP
      next h' j' x' e' o' s' firsts' stages' hb =>
      rw [Rev.back?_eq, hout₆] at hb
      obtain ⟨hn, hnode⟩ := last_chain hop hb (fun _ _ h => nomatch h)
      cases hnode
      have ho₇ : (st₆.out.pop.push (PStmt.chain h join lx entry one sfp (firsts ++ [first])
          (stages ++ [blocks]))).toList = O ++ [.chain h join lx entry one sfp (firsts ++ [first])
          (stages ++ [blocks])] := by
        rw [Rev.toList_push, Rev.toList_pop, hout₆, hn]
        simp
      refine wp_bind.mpr (wp_set.mpr ?_)
      refine wp_bind.mpr (wp_mono (wp_and (endStmt_op (st := _)) (endStmt_keep (st := _)))
        fun _ st₈ ⟨⟨ops, hops, _⟩, hk₈⟩ => ?_)
      have hc₈ : st₈.chainIn = none := (show st₈.chainIn = _ from hk₈).trans hc₆
      refine wp_mono (hmono rest st₈) fun _ st₉ ⟨_, _, hch⟩ => ?_
      obtain ⟨hc₉, blk, hblk⟩ := hch hc₈
      refine ⟨hc₉, [first], [blocks], ops ++ blk, ?_, rfl⟩
      rw [hblk, hops]
      erw [ho₇]
      simp
    | some q =>
      obtain ⟨x', n'⟩ := q
      obtain ⟨x'', arms'', tl', htl⟩ := hnx (by simp)
      dsimp only
      simp only [bind_assoc]
      unfold allocTable
      refine wp_bind.mpr (wp_modifyGet.mpr ?_)
      refine wp_bind.mpr (wp_get.mpr ?_)
      refine wp_bind.mpr (wp_mono (wp_and (placeArms_mono arms 0 arms.length _ _ _)
        (placeArms_chain arms 0 arms.length _ _ _ hc₃)) fun blocks st₅ ⟨⟨_, _, ho₅⟩, hc₅⟩ => ?_)
      refine wp_bind.mpr (wp_mono (wp_and (expect_op (st := st₅)) (expect_keep (st := st₅)))
        fun _ st₆ ⟨ho₆, hk₆⟩ => ?_)
      have hc₆ : st₆.chainIn = none := (show st₆.chainIn = st₅.chainIn from hk₆).trans hc₅
      obtain ⟨ops₂, hops₂, hop₂⟩ := ho₆
      have hout₆ : st₆.out.toList =
          O ++ [.chain h join lx entry one sfp firsts stages] ++ (ops₁ ++ ops₂) := by
        rw [hops₂, ho₅, hops₁, ho, List.append_assoc]
      have hop : ∀ s ∈ ops₁ ++ ops₂, ∃ h o, s = PStmt.op h o := fun s hs =>
        (List.mem_append.mp hs).elim (hop₁ s) (hop₂ s)
      refine wp_bind.mpr (wp_get.mpr ?_)
      split
      rotate_left
      · exact wp_bind.mpr wp_failP
      next h' j' x' e' o' s' firsts' stages' hb =>
      rw [Rev.back?_eq, hout₆] at hb
      obtain ⟨hn, hnode⟩ := last_chain hop hb (fun _ _ h => nomatch h)
      cases hnode
      have ho₇ : (st₆.out.pop.push (PStmt.chain h join lx entry one sfp (firsts ++ [first])
          (stages ++ [blocks]))).toList = O ++ [.chain h join lx entry one sfp (firsts ++ [first])
          (stages ++ [blocks])] := by
        rw [Rev.toList_push, Rev.toList_pop, hout₆, hn]
        simp
      refine wp_bind.mpr (wp_set.mpr ?_)
      unfold endStmt
      refine wp_bind.mpr (wp_modify.mpr ?_)
      refine wp_mono (openOff_out hmono rest _ O h join lx entry one sfp st₃.tables.len
        (firsts ++ [first]) (stages ++ [blocks]) join' ⟨x'', arms'', tl', htl⟩ rfl ho₇)
        fun _ st₉ ⟨hc₉, firstsN, stagesN, blk, hout, _⟩ => ?_
      refine ⟨hc₉, first :: firstsN, blocks :: stagesN, blk, ?_, rfl⟩
      rw [hout]
      simp

/-- **A block entered by an open chain, off the path** (`openOff`): the chain node at the end of
the output extended by the stages of its leading `match`es, the first in the table `first`, the
rest's output after it; no `match` chaining out, the next free cell up, the places and the shared
tables kept. -/
theorem openOff (hmono : PlaceMono ctx) : ∀ (x : V) (arms : List (List Stmt)) (rest : List Stmt)
    (st : St) (O : List PStmt) (h : List LHint) (join lx entry one sfp first : ℕ)
    (firsts : List ℕ) (stages : List (List (List PStmt))) (join' : ℕ),
    st.chainIn = some (first, join') →
    st.out.toList = O ++ [.chain h join lx entry one sfp firsts stages] →
    wpP (placeBlock (.match_ x arms :: rest)) ctx st fun _ st' => st'.chainIn = none ∧
      st.next ≤ st'.next ∧ LocsLe st.locs st'.locs ∧
      (∀ y ∈ st.tables.shared, y ∈ st'.tables.shared) ∧
      ∃ (firstsN : List ℕ) (stagesN : List (List (List PStmt))) (blk : List PStmt),
        st'.out.toList = O ++ [.chain h join lx entry one sfp (firsts ++ firstsN)
          (stages ++ stagesN)] ++ blk ∧ firstsN.head? = some first := by
  intro x arms rest st O h join lx entry one sfp first firsts stages join' hc ho
  exact wp_mono (wp_and (placeBlock_mono _ st) (wp_and (placeBlock_r _ st)
    (openOff_out hmono _ st O h join lx entry one sfp first firsts stages join'
      ⟨x, arms, rest, rfl⟩ hc ho)))
    fun _ _ ⟨⟨hn, hl⟩, ⟨_, _, _, _, ht⟩, hc', hout⟩ => ⟨hc', hn, hl, ht, hout⟩

/-- **`OpenOffW`.** -/
theorem openOffW (hmono : PlaceMono ctx) : OpenOffW (ctx := ctx) := openOff hmono

end Off

/-- info: 'LeanVM.Guest.Backend.Complete.openOffW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms openOffW

/-! ## The words of an open chain's stages -/

section SWords

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

theorem ksAt_left {kf : List ℕ} {kh : ℕ → E × E} {i₀ : ℕ} {bc₁ bc₂ : List Call}
    {hs₁ hs₂ : List (E × E)} {ks : List (ℕ × ℕ)} (hl₁ : hs₁.length = bc₁.length)
    (h : KsAt cl kf kh i₀ (bc₁ ++ bc₂) (hs₁ ++ hs₂) ks) : KsAt cl kf kh i₀ bc₁ hs₁ ks := by
  obtain ⟨-, hks⟩ := h
  refine ⟨hl₁, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hks j (by rw [List.length_append]; omega)
  refine ⟨h1, by rw [h2, List.getElem?_append_left hj], ?_⟩
  rw [h3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [hl₁]; exact hj)]

theorem ksAt_right {kf : List ℕ} {kh : ℕ → E × E} {i₀ : ℕ} {bc₁ bc₂ : List Call}
    {hs₁ hs₂ : List (E × E)} {ks : List (ℕ × ℕ)} (hl₁ : hs₁.length = bc₁.length)
    (hl₂ : hs₂.length = bc₂.length)
    (h : KsAt cl kf kh i₀ (bc₁ ++ bc₂) (hs₁ ++ hs₂) ks) :
    KsAt cl kf kh (i₀ + bc₁.length) bc₂ hs₂ (ks.drop bc₁.length) := by
  obtain ⟨-, hks⟩ := h
  refine ⟨hl₂, fun j hj => ?_⟩
  obtain ⟨⟨kfp, h1, h1'⟩, h2, h3⟩ := hks (bc₁.length + j) (by rw [List.length_append]; omega)
  refine ⟨⟨kfp, by rw [List.getElem?_drop, h1, Nat.add_assoc], by rw [Nat.add_assoc]; exact h1'⟩,
    ?_, ?_⟩
  · rw [Nat.add_assoc, h2, List.getElem?_append_right (by omega)]
    simp
  · rw [Nat.add_assoc, h3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hl₁]
    simp

theorem outK_pre {es₁ : List Ev} {o₂ : Out} {tl : List Stmt}
    {next : List Stmt → List (ℕ × ℕ) → Prop} {K : Prop} {ks : List (ℕ × ℕ)}
    (h : OutK (o₂.pre es₁) tl next K ks) : OutK o₂ tl next K (ks.drop (calls es₁).length) := by
  cases o₂ with
  | stuck => exact h.elim
  | ret es₂ vs => exact h
  | fall es₂ =>
    intro cs' hcs'
    have := h cs' hcs'
    rwa [calls_append', List.length_append, ← List.drop_drop] at this

theorem kLast_pre {es₁ : List Ev} {o₂ : Out} {i₀ : ℕ} (h : KLast I (o₂.pre es₁) i₀) :
    KLast I o₂ (i₀ + (calls es₁).length) := by
  intro es vs he
  subst he
  have := h (es₁ ++ es) vs rfl
  rw [calls_append', List.length_append] at this
  omega

theorem calls_pre {es₁ : List Ev} {o₂ : Out} (h : o₂ ≠ .stuck) :
    calls (outEs (o₂.pre es₁)) = calls es₁ ++ calls (outEs o₂) := by
  cases o₂ with
  | stuck => exact absurd rfl h
  | fall es₂ => simp [outEs, Out.pre, calls_append']
  | ret es₂ vs => simp [outEs, Out.pre, calls_append']

theorem stagesSize_append : ∀ (a b : List (List (List PStmt))),
    stagesSize (a ++ b) = stagesSize a + stagesSize b
  | [], b => by simp [stagesSize]
  | s :: ss, b => by
    rw [List.cons_append, stagesSize, stagesSize, stagesSize_append ss b, Nat.add_assoc]

/-- **The words of a last stage** (its arms jumping to the join): the picked arm's block, then the
jump to the join (or the fall into it), then the block after the chain. -/
theorem stagesW_join {C : (ℕ → E) → Prop} {blocks : List (List PStmt)} {x : V}
    {arms : List (List Stmt)} {rest tl : List Stmt} {o o₁ o₂ : Out} {i₀ q j : ℕ}
    {blk blkj : List PStmt} {join one sfp : ℕ} (hj : j < blocks.length) (ha : j < arms.length)
    (hbj : blocks[j] = blkj ++
      (if j + 1 != blocks.length then [PStmt.op [] (.jump one join sfp)] else []))
    (hx : I.σ x = ofK (addressOfIndex j)) (hne : ∀ i < j, I.σ x ≠ ofK (addressOfIndex i))
    (hxS : ∀ σ', I.Same σ' → σ' x = I.σ x) (ho : o = o₁.seq o₂)
    (hB₁ : BlkW Γ I ctx Ag cl C blkj arms[j] [] o₁ i₀ (q + armsSize (blocks.take j)))
    (hB₂ : ∀ es₁, o₁ = .fall es₁ →
      BlkW Γ I ctx Ag cl C blk rest tl o₂ (i₀ + (calls es₁).length) (q + armsSize blocks))
    (hjn : PremW I ctx → ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ kh : ℕ → E × E,
      j + 1 ≠ blocks.length → JumpTo Γ I.fp I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) one join sfp
        (q + armsSize blocks)) :
    StagesW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) C [blocks] blk
      (.match_ x arms :: rest) tl o i₀ q (q + armsSize (blocks.take j)) := by
  have hops_arm : ∀ (hs : List PStmt), (∀ o' ∈ stagesOps [blocks] q ++ blockOps hs (q + stagesSize [blocks]),
      o' ∈ I.ops) → ∀ o' ∈ blockOps blkj (q + armsSize (blocks.take j)), o' ∈ I.ops :=
    fun _ hops o' ho' => hops o' (by
      have h1 : o' ∈ blockOps blocks[j] (q + armsSize (blocks.take j)) := by
        rw [hbj, bops_append]; exact List.mem_append_left _ ho'
      have h2 := armsOps_mem blocks q j hj o' h1
      simp only [stagesOps, List.append_nil, List.mem_append]
      exact Or.inl h2)
  have hfin : j + 1 = blocks.length →
      q + armsSize (blocks.take j) + blockSize blkj = q + armsSize blocks := fun hlast => by
    have hb0 : blocks[j] = blkj := by rw [hbj]; simp [hlast]
    have := armsSize_take_succ blocks j hj
    rw [hlast, List.take_length, hb0] at this
    omega
  have hpos : q + stagesSize [blocks] = q + armsSize blocks := by simp [stagesSize]
  -- the words, given the arm's continuation
  have hwords : ∀ (hs₁ : List (E × E)) (Ψ : ℕ → E) (σ' : Val) (kh : ℕ → E × E)
      (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
      (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop) (N : List (ℕ × ℕ) → Prop),
      PremW I ctx → C Ψ → I.Same σ' →
      (∀ nx kx, OutK o₁ [] nx (if ctx.isMain then khalt else kret) ks →
        wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blkj arms[j]
          (q + armsSize (blocks.take j)) ks nx kx kret khalt) →
      OutK o₁ [] (fun _ ks' => N ks') (if ctx.isMain then khalt else kret) ks →
      N = (fun ks' => wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk
        (rest ++ tl) (q + stagesSize [blocks]) ks' next kj kret khalt) →
      wStages Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl [blocks]
        ((Stmt.match_ x arms :: rest).take [blocks].length) q
        (fun ks' => wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk
          ((Stmt.match_ x arms :: rest).drop [blocks].length ++ tl) (q + stagesSize [blocks]) ks'
          next kj kret khalt)
        kret khalt ks (Γ.tgt (q + armsSize (blocks.take j))) (ofK (addressOfIndex I.fp)) := by
    intro _ Ψ σ' kh ks next kj kret khalt N hP hΨ hσ hblk hout hN
    subst hN
    simp only [List.length_singleton, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
      List.drop_zero, wStages]
    refine wArms_pick blocks arms 0 q j hj ha (by rw [hxS σ' hσ]; simpa using hx)
      (fun i hi => by rw [hxS σ' hσ]; simpa using hne i hi) (by simp) rfl ?_
    simp only [true_and]
    rw [hbj]
    rw [hpos] at hout
    exact wL_arm_join hblk hout hfin (hjn hP Ψ hΨ σ' hσ kh)
  obtain ⟨hs₁, hl₁, hh₁, hW₁⟩ := hB₁
  cases o₁ with
  | stuck =>
    subst ho
    exact ⟨[], by simp [outEs, Out.seq, calls], HsOk.nil _ _ _,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk => by simp [Out.seq, OutK] at hk⟩
  | ret es vs =>
    subst ho
    refine ⟨hs₁, by simpa [Out.seq] using hl₁, by simpa [Out.seq] using hh₁, ?_⟩
    intro hP hK Ψ hΨ σ' hσ kh ks next kj kret khalt hops hks hk
    exact hwords hs₁ Ψ σ' kh ks next kj kret khalt _ hP hΨ hσ
      (fun nx kx hk' => hW₁ hP hK Ψ hΨ σ' hσ kh arms[j] ks nx kx kret khalt (hops_arm blk hops)
        (by simp) hks hk') hk rfl
  | fall es₁ =>
    obtain ⟨hs₂, hl₂, hh₂, hW₂⟩ := hB₂ es₁ rfl
    simp only [Out.seq] at ho
    subst ho
    by_cases hst : o₂ = .stuck
    · subst hst
      exact ⟨[], by simp [outEs, Out.pre, calls], HsOk.nil _ _ _,
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk => by simp [Out.pre, OutK] at hk⟩
    have hc := calls_pre (es₁ := es₁) hst
    simp only [outEs] at hl₁ hh₁
    refine ⟨hs₁ ++ hs₂, by rw [List.length_append, hl₁, hl₂, hc, List.length_append],
      by rw [hc]; exact hh₁.append hh₂ hl₁, ?_⟩
    intro hP hK Ψ hΨ σ' hσ kh ks next kj kret khalt hops hks hk
    rw [hc] at hks
    refine hwords hs₁ Ψ σ' kh ks next kj kret khalt _ hP hΨ hσ
      (fun nx kx hk' => hW₁ hP (fun _ _ h => by cases h) Ψ hΨ σ' hσ kh arms[j] ks nx kx kret khalt
        (hops_arm blk hops) (by simp) (ksAt_left hl₁ hks) hk') ?_ rfl
    intro cs' _
    have hops₂ : ∀ o' ∈ blockOps blk (q + armsSize blocks), o' ∈ I.ops := fun o' ho' =>
      hops o' (List.mem_append_right _ (by rw [hpos]; exact ho'))
    rw [hpos]
    exact hW₂ hP (kLast_pre hK) Ψ hΨ σ' hσ kh (rest ++ tl) _ next kj kret khalt hops₂ rfl
      (ksAt_right hl₁ hl₂ hks) (outK_pre hk)

/-- **The words of a stage dispatching into the next**: the picked arm's block, then the read of
the next stage's table and the jump to its picked arm `T'`, where the next stages' words hold. -/
theorem stagesW_next {C : (ℕ → E) → Prop} {blocks : List (List PStmt)}
    {stagesN : List (List (List PStmt))} {x : V} {arms : List (List Stmt)} {rest tl : List Stmt}
    {o o₁ o₂ : Out} {i₀ q j T' : ℕ} {blk blkj : List PStmt} {lx' nf e one sfp : ℕ}
    (hj : j < blocks.length) (ha : j < arms.length)
    (hbj : blocks[j] = blkj ++ [PStmt.op [] (.slot lx' nf e), .op [] (.jump one e sfp)])
    (hx : I.σ x = ofK (addressOfIndex j)) (hne : ∀ i < j, I.σ x ≠ ofK (addressOfIndex i))
    (hxS : ∀ σ', I.Same σ' → σ' x = I.σ x) (ho : o = o₁.seq o₂)
    (hB₁ : BlkW Γ I ctx Ag cl C blkj arms[j] [] o₁ i₀ (q + armsSize (blocks.take j)))
    (hS₂ : ∀ es₁, o₁ = .fall es₁ →
      StagesW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) C stagesN blk rest tl o₂
        (i₀ + (calls es₁).length) (q + armsSize blocks) T')
    (hsl : ∀ es₁, o₁ = .fall es₁ → PremW I ctx → ∀ Ψ, C Ψ → ∀ σ', I.Same σ' →
      ∀ kh : ℕ → E × E,
      HW Γ I.fp (Ag σ' Ψ kh) (Γ.pc0 + (q + armsSize (blocks.take j) + blockSize blkj))
        (.slot lx' nf e) ∧
      JumpTo Γ I.fp I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) one e sfp T') :
    StagesW (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) C (blocks :: stagesN) blk
      (.match_ x arms :: rest) tl o i₀ q (q + armsSize (blocks.take j)) := by
  have hpos : q + stagesSize (blocks :: stagesN) = q + armsSize blocks + stagesSize stagesN := by
    simp [stagesSize, Nat.add_assoc]
  have hops_arm : ∀ (hs : List PStmt), (∀ o' ∈ stagesOps (blocks :: stagesN) q ++
      blockOps hs (q + stagesSize (blocks :: stagesN)), o' ∈ I.ops) →
      ∀ o' ∈ blockOps blocks[j] (q + armsSize (blocks.take j)), o' ∈ I.ops :=
    fun _ hops o' ho' => hops o' (by
      have h2 := armsOps_mem blocks q j hj o' ho'
      simp only [stagesOps, List.mem_append]
      exact Or.inl (Or.inl h2))
  have hops_rest : ∀ (hs : List PStmt), (∀ o' ∈ stagesOps (blocks :: stagesN) q ++
      blockOps hs (q + stagesSize (blocks :: stagesN)), o' ∈ I.ops) →
      ∀ o' ∈ stagesOps stagesN (q + armsSize blocks) ++
        blockOps hs (q + armsSize blocks + stagesSize stagesN), o' ∈ I.ops :=
    fun _ hops o' ho' => hops o' (by
      rw [hpos]
      simp only [stagesOps, List.mem_append] at ho' ⊢
      tauto)
  have hblkj : ∀ (hs : List PStmt), (∀ o' ∈ stagesOps (blocks :: stagesN) q ++
      blockOps hs (q + stagesSize (blocks :: stagesN)), o' ∈ I.ops) →
      ∀ o' ∈ blockOps blkj (q + armsSize (blocks.take j)), o' ∈ I.ops :=
    fun hs hops o' ho' => hops_arm hs hops o' (by rw [hbj, bops_append]; exact List.mem_append_left _ ho')
  have hpick : ∀ (Ψ : ℕ → E) (σ' : Val) (kh : ℕ → E × E) (ks : List (ℕ × ℕ))
      (N : List (ℕ × ℕ) → Prop) (kret khalt : Prop), I.Same σ' →
      wL Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blocks[j] arms[j]
        (q + armsSize (blocks.take j)) ks
        (fun ks' => wStages Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl stagesN
          (rest.take stagesN.length) (q + armsSize blocks) N kret khalt ks'
          (Γ.tgt (q + armsSize (blocks.take j) + blockSize blocks[j])) (ofK (addressOfIndex I.fp)))
        (wStages Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl stagesN
          (rest.take stagesN.length) (q + armsSize blocks) N kret khalt) kret khalt →
      wStages Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl (blocks :: stagesN)
        ((Stmt.match_ x arms :: rest).take (blocks :: stagesN).length) q N kret khalt ks
        (Γ.tgt (q + armsSize (blocks.take j))) (ofK (addressOfIndex I.fp)) := by
    intro Ψ σ' kh ks N kret khalt hσ hw
    simp only [List.length_cons, List.take_succ_cons, wStages]
    exact wArms_pick blocks arms 0 q j hj ha (by rw [hxS σ' hσ]; simpa using hx)
      (fun i hi => by rw [hxS σ' hσ]; simpa using hne i hi) (by simp) rfl hw
  obtain ⟨hs₁, hl₁, hh₁, hW₁⟩ := hB₁
  cases o₁ with
  | stuck =>
    subst ho
    exact ⟨[], by simp [outEs, Out.seq, calls], HsOk.nil _ _ _,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk => by simp [Out.seq, OutK] at hk⟩
  | ret es vs =>
    subst ho
    refine ⟨hs₁, by simpa [Out.seq] using hl₁, by simpa [Out.seq] using hh₁, ?_⟩
    intro hP hK Ψ hΨ σ' hσ kh ks next kj kret khalt hops hks hk
    refine hpick Ψ σ' kh ks _ kret khalt hσ ?_
    rw [hbj, wL_eq_wLc, wLc_append Γ _ σ' _ _ _ cl _ _ (List.cons_ne_nil _ _)]
    exact hW₁ hP hK Ψ hΨ σ' hσ kh arms[j] ks _ _ kret khalt (hblkj blk hops) (by simp) hks hk
  | fall es₁ =>
    obtain ⟨hs₂, hl₂, hh₂, hW₂⟩ := hS₂ es₁ rfl
    simp only [Out.seq] at ho
    subst ho
    by_cases hst : o₂ = .stuck
    · subst hst
      exact ⟨[], by simp [outEs, Out.pre, calls], HsOk.nil _ _ _,
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk => by simp [Out.pre, OutK] at hk⟩
    have hc := calls_pre (es₁ := es₁) hst
    simp only [outEs] at hl₁ hh₁
    refine ⟨hs₁ ++ hs₂, by rw [List.length_append, hl₁, hl₂, hc, List.length_append],
      by rw [hc]; exact hh₁.append hh₂ hl₁, ?_⟩
    intro hP hK Ψ hΨ σ' hσ kh ks next kj kret khalt hops hks hk
    rw [hc] at hks
    obtain ⟨hsl₁, hjp⟩ := hsl es₁ rfl hP Ψ hΨ σ' hσ kh
    refine hpick Ψ σ' kh ks _ kret khalt hσ ?_
    rw [hbj]
    refine wL_arm_next (fun nx kx hk' => hW₁ hP (fun _ _ h => by cases h) Ψ hΨ σ' hσ kh arms[j] ks
      nx kx kret khalt (hblkj blk hops) (by simp) (ksAt_left hl₁ hks) hk') ?_ hsl₁ hjp
    intro cs' _
    have := hW₂ hP (kLast_pre hK) Ψ hΨ σ' hσ kh _ next kj kret khalt (hops_rest blk hops)
      (ksAt_right hl₁ hl₂ hks) (outK_pre hk)
    simp only [List.length_cons, List.drop_succ_cons] at this ⊢
    rw [hpos]
    exact this

end SWords

/-! ## A stage inside the final chain node -/

section Node

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {I : Inst}

theorem stagesFills_append (f : String) : ∀ (firsts : List ℕ) (stages : List (List (List PStmt)))
    (fs : List ℕ) (ss : List (List (List PStmt))) (pos : ℕ), firsts.length = stages.length →
    stagesFills f (firsts ++ fs) (stages ++ ss) pos =
      stagesFills f firsts stages pos ++ stagesFills f fs ss (pos + stagesSize stages)
  | [], [], fs, ss, pos, _ => by simp [stagesFills, stagesSize]
  | _ :: firsts, s :: stages, fs, ss, pos, hl => by
    simp only [List.cons_append, stagesFills, List.headD_cons, List.tail_cons, stagesSize]
    rw [stagesFills_append f firsts stages fs ss _ (by simpa using hl), List.append_assoc,
      Nat.add_assoc]
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl

/-- **The final node's instructions**: its join's `SET` at its position, a stage's arms at theirs,
and the node within the final instructions. -/
theorem opsIn_node {p₀ : ℕ} {O blk : List PStmt} {h : List LHint} {join lx entry one sfp : ℕ}
    {fs : List ℕ} {stages more : List (List (List PStmt))} {blocks : List (List PStmt)}
    (hO : OpsIn I p₀ (blockOps (O ++ [.chain h join lx entry one sfp fs (stages ++ blocks :: more)] ++
      blk) p₀)) :
    I.ops[p₀ + blockSize O]? = some (.set join
        (.local (p₀ + blockSize O + 3 + stagesSize (stages ++ blocks :: more)))) ∧
      OpsIn I (p₀ + blockSize O + 3 + stagesSize stages)
        (armsOps blocks (p₀ + blockSize O + 3 + stagesSize stages)) ∧
      p₀ + blockSize O + 3 + stagesSize (stages ++ blocks :: more) ≤ I.ops.length := by
  rw [bops_append, bops_append] at hO
  have h1 := hO.left.right
  rw [blockOps_length] at h1
  simp only [blockOps, stmtOps, List.append_nil] at h1
  have hset := h1 0 (by simp)
  have hlast := h1 (2 + stagesSize (stages ++ blocks :: more))
    (by simp [stagesOps_length]; omega)
  have hS := h1.right
  simp only [List.length_cons, List.length_nil] at hS
  rw [stagesOps_append] at hS
  have hA := hS.right
  rw [stagesOps_length] at hA
  simp only [stagesOps] at hA
  refine ⟨by simpa using hset, ?_, ?_⟩
  · have := hA.left
    simpa [Nat.add_assoc] using this
  · have := (List.getElem?_eq_some_iff.mp hlast).1
    omega

/-- **The final node's slots**: a stage's table slot `first + j` holds its arm `j`'s position, and
the slots that arm fills hold theirs. -/
theorem fills_node {p₀ : ℕ} {O blk : List PStmt} {h : List LHint} {join lx entry one sfp : ℕ}
    {firsts fs : List ℕ} {first : ℕ} {stages more : List (List (List PStmt))}
    {blocks : List (List PStmt)} (hl : firsts.length = stages.length)
    (hF : FillsIn Γ Ag p₀ (O ++ [.chain h join lx entry one sfp (firsts ++ first :: fs)
      (stages ++ blocks :: more)] ++ blk)) (j : ℕ) (hj : j < blocks.length) :
    (∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
      L.read (addressOfIndex (Γ.l.tablesBase + (first + j))) =
        some (Γ.tgt (p₀ + blockSize O + 3 + stagesSize stages + armsSize (blocks.take j)))) ∧
      FillsIn Γ Ag (p₀ + blockSize O + 3 + stagesSize stages + armsSize (blocks.take j))
        blocks[j] := by
  have hmem : ∀ f y, y ∈ armsFills f first blocks 0 (p₀ + blockSize O + 3 + stagesSize stages) →
      y ∈ blockFills f (O ++ [.chain h join lx entry one sfp (firsts ++ first :: fs)
        (stages ++ blocks :: more)] ++ blk) p₀ := fun f y hy => by
    rw [blockFills_append, blockFills_append]
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    simp only [blockFills, stmtFills, List.append_nil]
    rw [stagesFills_append f firsts stages _ _ _ hl]
    refine List.mem_append_right _ ?_
    simp only [stagesFills, List.headD_cons, List.tail_cons]
    exact List.mem_append_left _ (by simpa [Nat.add_assoc] using hy)
  refine ⟨fun σ' Ψ kh κ L hA => hF "" _ _ (hmem "" _ (by
      have := armsFills_mem "" first blocks 0 (p₀ + blockSize O + 3 + stagesSize stages) j hj
      simpa using this)) σ' Ψ kh κ L hA, fun f k i hm => hF f k i (hmem f _
        (armsFills_blk f first blocks 0 _ j hj hm))⟩

end Node

/-! ## An entered stage -/

section Stage

variable {ctx : Backend.Ctx} {I : Inst}

/-- **`match_pre` for a `match` some chaining enters** (`chainIn = e`): the facts after its edge
flush and the reset of the chaining flags, from the invariant of the state with no chaining. -/
theorem match_preE (hI : I.Ok) {x : V} {arms : List (List Stmt)} {rest : List Stmt}
    {C : (ℕ → E) → Prop} {st : St} {sc s₀ : SSt} {R : Unit → ((ℕ → E) → Prop) → St → Prop}
    {g : Unit → P Unit}
    {e : Option (ℕ × Cell)} (hinv : WInv ctx I C { st with chainIn := none } sc)
    (hche : st.chainIn = e) (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hf : ∀ (b : Bool) (st₂ : St) (C₂ : (ℕ → E) → Prop), Stronger C₂ C → OpR st st₂ →
      st.next ≤ st₂.next →
      COk I C₂ st₂.next st₂.scope st₂.locs → EmitsW I C₂ st st₂ → PK st st₂ →
      st₂.rest = s₀.rest → st₂.rest.length ≤ ctx.fuel →
      VW I C₂ st₂ (fun v => s₀.live.contains v = true) →
      (s₀.retDone = false → RetBlind ctx C₂) →
      (∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest)) →
      st₂.chainIn = none → st₂.lazy = none →
      FBAt ctx I C₂ st₂ (placeMatch x arms.length rest e b
        (fun base exit => placeArms arms 0 arms.length base exit) >>= g) R) :
    FBAt ctx I C st (placeStmt (.match_ x arms) rest >>= g) R := by
  obtain ⟨hlf, hfl₀⟩ := flushEdge_ok h₀
  have hfl : flushS ctx.retCells st.rest sc.live sc.retDone = .ok s₀ := by
    rw [← hinv.rest]; exact hfl₀
  obtain ⟨hseg, hlive, huseS⟩ := flushS_seg _ _ _ _ _ hfl
  have hsegA : ∀ v ∈ allocsOf (flushSeg st.rest), st.locs[v]? = none := fun v hv =>
    (hinv.fresh v (by rw [hseg, allocsOf_append]; exact List.mem_append_left _ hv)).1
  have hvw : VW I C st fun v => sc.live.contains v = true ∨ st.locs[v]? = none :=
    fun v l hv hl => hv.elim (fun h => hinv.vw v l h hl) fun h => by rw [h] at hl; cases hl
  have hokOf : ∀ v, s₀.live.contains v = true →
      sc.live.contains v = true ∨ st.locs[v]? = none := fun v hv =>
    (hlive v hv).elim Or.inl fun h => Or.inr (hsegA v h)
  rw [placeStmt]
  simp only [bind_assoc]
  refine FBAt.fat_bind (FAt.and_wp (flushSeg_lock ctx I C st [] sc.live sc.retDone s₀
      (fun v => sc.live.contains v = true ∨ st.locs[v]? = none) hI hfl hinv.fuel
      (fun k _ _ _ hk => by simp at hk)
      (fun v _ _ hv _ => (huseS v hv).elim Or.inl fun h => Or.inr (hsegA v h))
      hinv.abi hinv.two hvw (fun hr k hk Ψ w hC => hinv.ret hr Ψ k w hk hC))
    (wp_and flush_pk (wp_and (flushLazy [] st (hinv.rest ▸ hlf)) (wp_and flush_keep flush_op))))
    fun _ st₁ C₁ hsC₁ hn₁ _ _ hE₁ ⟨⟨hr₁, hFR₁, hrb₁, hloc₁⟩, hpk₁, hz₁, hk₁, hop₁⟩ => ?_
  have hvw₁ : VW I C₁ st₁ fun v => s₀.live.contains v = true :=
    hFR₁.2.anti fun v hv => Or.inl (hokOf v hv)
  have hch₁ : st₁.chainIn = e := (show st₁.chainIn = st.chainIn from hk₁).trans hche
  have hf₁ : st₁.rest.length ≤ ctx.fuel := by
    have h1 : st.rest.length ≤ ctx.fuel := hinv.fuel
    have h2 := congrArg List.length hseg
    rw [List.length_append] at h2
    rw [hr₁]
    omega
  refine FBAt.get_bind ?_
  rw [hch₁]
  refine FBAt.fat_bind (FAt.ofSame (R := fun _ C' st' => C' = C₁ ∧
      st' = { st₁ with chainIn := none, chain := false })
    (wp_set.mpr ⟨rfl, rfl, rfl, LocsLe.refl _, rfl, rfl⟩))
    fun _ st₂ C₂ _ hn₂ hl₂ hc₂ hE₂ ⟨hC₂, hst₂⟩ => ?_
  subst hC₂ hst₂
  obtain ⟨ops, hops, hopo⟩ := hop₁
  exact hf st₁.chain _ _ hsC₁ ⟨ops, hops, hopo⟩ hn₁ hc₂ (hE₁.step hE₂ (Stronger.refl _) hn₂ hl₂)
    (hpk₁.trans (pk_same rfl rfl rfl)) hr₁ hf₁ hvw₁ hrb₁ hloc₁ rfl (by rw [hz₁]; exact hinv.lazy)

end Stage

end

end LeanVM.Guest.Backend.Complete
