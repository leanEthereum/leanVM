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
          (stages ++ stagesN)] ++ blk ∧ firstsN.head? = some first ∧
        firstsN.length = stagesN.length ∧ stagesN.length ≤ ss.length
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
      refine ⟨hc₉, [first], [blocks], ops ++ blk, ?_, rfl, rfl, by simp⟩
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
        fun _ st₉ ⟨hc₉, firstsN, stagesN, blk, hout, _, hl₁, hl₂⟩ => ?_
      refine ⟨hc₉, first :: firstsN, blocks :: stagesN, blk, ?_, rfl, by simp [hl₁], by simp; omega⟩
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
    fun _ _ ⟨⟨hn, hl⟩, ⟨_, _, _, _, ht⟩, hc', fN, sN, b, hout, hh, _, _⟩ => ⟨hc', hn, hl, ht, fN, sN, b, hout, hh⟩

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

section Last

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst}

theorem seq_es {o₁ o₂ : Out} (h : o₁.seq o₂ ≠ .stuck) : ∃ l, outEs (o₁.seq o₂) = outEs o₁ ++ l := by
  cases o₁ with
  | stuck => exact absurd rfl h
  | ret es vs => exact ⟨[], by simp [Out.seq, outEs]⟩
  | fall es =>
    have h2 : o₂ ≠ .stuck := fun h' => h (by rw [h']; rfl)
    exact ⟨outEs o₂, by simp only [Out.seq]; rw [outEs_pre h2]; rfl⟩

/-- The values the picked arm's path reads are read by the `match`'s path. -/
theorem pathVals_arm {σ : Val} {x : V} {arms : List (List Stmt)} {j : ℕ} (hj : j < arms.length)
    {o : Out} (hsel : armSels σ x 0 arms = pathSels σ arms[j]) :
    ∀ v ∈ pathVals σ arms[j] o, v ∈ pathVals σ [.match_ x arms] o := by
  intro v hv
  have hs : pathSels σ [Stmt.match_ x arms] = sels1 σ (.match_ x arms) := by
    simp only [pathSels]
    split <;> simp
  simp only [pathVals, hs, sels1, hsel] at hv ⊢
  simp only [List.mem_append, List.mem_cons] at hv ⊢
  tauto

set_option maxHeartbeats 4000000 in
/-- **The last stage of an open chain** (an entered `match` whose arms jump to the join), from the
state after its edge flush, then the rest of its block: `OpenOut`. -/
theorem stage_last (hmono : PlaceMono ctx) (hnew : PlaceNew ctx)
    (hI : I.Ok) (hmain : ctx.isMain = true → I.fp = 0) (hAg : AgOwn I Ag)
    (hkw : ∀ k, I.kw k = kwOf Γ k) (hlocB : ∀ q, q ≤ I.ops.length → kwOf Γ (.local q) = Γ.tgt q)
    {x : V} {arms : List (List Stmt)} {rest tl : List Stmt} (hu : x ∉ I.tmps)
    (hin : ∀ j (hj : j < arms.length), InBlockW Γ Ag cl ctx I arms[j])
    (hafa : ∀ j (hj : j < arms.length), ∀ v ∈ pathVals I.σ arms[j] (walk I.σ arms[j]), ∀ run,
      Atom.frameAddr v run ∉ armsAtoms (arms.drop (j + 1)))
    (hfa : FaAfter I.σ (.match_ x arms) rest) (hrw : BlockW Γ Ag cl ctx I (placeBlock rest) rest tl)
    {Q : Prop}
    {C C₂ : (ℕ → E) → Prop} {st st₂ : St} {sc s₀ s₁ sc' sc'' : SSt} {i₀ p₀ : ℕ} {o : Out}
    {O : List PStmt} {h : List LHint} {join lx entry one sfp first : ℕ} {firsts : List ℕ}
    {stages : List (List (List PStmt))}
    (hinv : WInv ctx I C { st with chainIn := none } sc)
    (hjw : 2 ≤ join ∧ join < st.next ∧ ∀ Ψ, C Ψ → Ψ join = joinW I (p₀ + blockSize O))
    (hout : st.out.toList = O ++ [.chain h join lx entry one sfp firsts stages])
    (hlen : firsts.length = stages.length)
    (h₀ : flushEdge ctx.retCells sc = .ok s₀)
    (hx : s₀.live.contains x = true) (hsa : scopeArms ctx.retCells arms s₀ s₀.retDone = .ok s₁)
    (hem : expectS isEmit "a match" s₁ = .ok sc')
    (hsc : scopeBlock ctx.retCells rest sc' = .ok sc'')
    (hw : walk I.σ (.match_ x arms :: rest) = o) (hns : o ≠ .stuck)
    (hes : ∀ e ∈ outEs o, e ∈ I.es)
    (hcl : ∀ k < (calls (outEs o)).length, cl[i₀ + k]? = (calls (outEs o))[k]?)
    (hs₂ : Stronger C₂ C) (hop₂ : OpR st st₂)
    (hn₂ : st.next ≤ st₂.next)
    (hpk₂ : PK st st₂)
    (hr₂ : st₂.rest = s₀.rest) (hf₂ : st₂.rest.length ≤ ctx.fuel)
    (hvw₂ : VW I C₂ st₂ (fun v => s₀.live.contains v = true))
    (hrb₂ : s₀.retDone = false → RetBlind ctx C₂)
    (hloc₂ : ∀ v, st₂.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf (flushSeg st.rest))
    (hch₂ : st₂.chainIn = none) (hz₂ : st₂.lazy = none) :
    FBAt ctx I C₂ st₂ (placeMatch x arms.length rest (some (first, join)) false
        (fun base exit => placeArms arms 0 arms.length base exit) >>= fun _ =>
          endStmt >>= fun _ => placeBlock rest)
      fun _ C' st' => OpenOut (Γ := Γ) (Ag := Ag) (cl := cl) (ctx := ctx) (I := I) Q O h join lx
        entry one sfp firsts stages first x sc'' (.match_ x arms :: rest) tl o i₀ p₀ C' st' := by
  rw [walk] at hw
  have hst : walk1 I.σ (.match_ x arms) ≠ .stuck := fun h' => hns (by rw [← hw, h']; rfl)
  have hns' : walkArms I.σ x 0 arms ≠ .stuck := fun h' => hst (by rw [walk1, h'])
  obtain ⟨j, hj, hxj, hne, hwj, hsel⟩ := walkArms_pick arms 0 hns'
  simp only [Nat.zero_add] at hxj hne
  have hw1 : walk1 I.σ (.match_ x arms) = walk I.σ arms[j] := by rw [walk1, hwj]
  rw [hw1] at hw hst
  obtain ⟨l₁, hl₁⟩ := seq_es (o₁ := walk I.σ arms[j]) (o₂ := walk I.σ rest) (by rw [hw]; exact hns)
  rw [hw] at hl₁
  have hes₁ : ∀ e ∈ outEs (walk I.σ arms[j]), e ∈ I.es := fun e he =>
    hes e (by rw [hl₁]; exact List.mem_append_left _ he)
  have hcl₁ : ∀ k < (calls (outEs (walk I.σ arms[j]))).length,
      cl[i₀ + k]? = (calls (outEs (walk I.σ arms[j])))[k]? := fun k hk => by
    rw [hcl k (by rw [hl₁, calls_append', List.length_append]; omega), hl₁, calls_append',
      List.getElem?_append_left hk]
  have hxS : ∀ σ', I.Same σ' → σ' x = I.σ x := fun σ' h => h x hu
  set q := p₀ + blockSize O + 3 + stagesSize stages with hq
  unfold placeMatch
  simp only [bind_assoc]
  refine FBAt.fat_bind (FAt.and_wp (matchCells_fatB hI hmain hvw₂ hx (le_trans hinv.two hn₂))
    (wp_and matchCells_pk (wp_and matchCells_lz (wp_and matchCells_keep
      (wp_and matchCells_op matchCells_placed)))))
    fun r st₃ C₃ hs₃ hn₃ hl₃ hc₃ hE₃ ⟨⟨hnone, hx2, hxlt, hxw, hf2, hflt, hfw, ho2, holt, how,
      hlo₃, hr₃, hkb₃⟩, hpk₃, hz₃, hk₃, hop₃, hpl₃⟩ => ?_
  obtain ⟨lx₀, ns, sfp₀, one₀⟩ := r
  simp only at hnone hx2 hxlt hxw hf2 hflt hfw ho2 holt how
  subst hnone
  simp only [pure_bind, bind_assoc]
  have hpkS : PK st st₃ := hpk₂.trans hpk₃
  have hinvS : OutOps I st₃ → WInv ctx I C₃ st₃ s₀ := fun hO =>
    winv_edge hinv h₀ hc₃ (le_trans hn₂ hn₃) (hr₃.trans hr₂) (hvw₂.step hs₃ hn₃ hlo₃)
      (fun hr => RetBlind.keep (hrb₂ hr) (le_trans hinv.abi hn₂) hkb₃)
      (fun v hv => hloc₂ v (by rwa [hlo₃] at hv)) ((show st₃.chainIn = st₂.chainIn from hk₃).trans hch₂)
      ⟨fun k o' hk => (hpkS.2.1 k o' hk).nt hI hinv.pnt hO,
        fun c' l hc' p hp => (hpkS.2.2 c' l hc' p hp).nt hI hinv.pnt hO⟩ (hz₃.1.trans hz₂)
  have hfS : st₃.rest.length ≤ ctx.fuel := by rw [hr₃]; exact hf₂
  refine FBAt.get_bind ?_
  refine FBAt.bind (FBAt.and_wp (arms_fb (q := q) (i₀ := i₀) (exit := .join join one₀ sfp₀) 0 hj
    (hin j hj) hsa (hr₃.trans hr₂) hfS hinvS rfl hst hes₁ hcl₁ (hafa j hj)) wp_eq)
    (fun _ _ _ h => h.1.1) ?_
  rintro bs st₈ C₈ hs₈ hn₈ hl₈ ⟨⟨hc₈, hlenb, hr₈, hsc₈, ho₈, hch₈, hoff₈, hsub₈, ht₈, hpick, -⟩, heq⟩
  obtain ⟨ev, hev, heS, -, -⟩ := expectS_ok hem
  refine FBAt.bind (FBAt.ofFAt (expect_fat (hr₈.trans hev) heS)) (fun _ _ _ h => h.1) ?_
  rintro _ st₉ C₉ - - - ⟨-, rfl, rfl⟩
  refine FBAt.get_bind ?_
  obtain ⟨ops, hops, hopo⟩ := hop₂.trans hop₃
  have hout₉ : st₈.out.toList = O ++ [.chain h join lx entry one sfp firsts stages] ++ ops := by
    rw [ho₈, hops, hout]
  have hlenb' : bs.length = arms.length := hlenb
  have hjb : j < bs.length := hlenb' ▸ hj
  split
  rotate_left
  · exact fun _ => wp_bind.mpr wp_failP
  next h' j' x' e' o' s' firsts' stages' hb =>
  have hb' : (O ++ [PStmt.chain h join lx entry one sfp firsts stages] ++ ops).getLast? =
      some (PStmt.chain h' j' x' e' o' s' firsts' stages') := by
    rw [← hout₉, ← Rev.back?_eq]; exact hb
  obtain ⟨hnil, hnode⟩ := last_chain hopo hb' (fun _ _ h => nomatch h)
  cases hnode
  subst hnil
  -- the state after the stage and the statement's end
  have hSo' : (st₈.out.pop.push (PStmt.chain h join lx entry one sfp (firsts ++ [first])
      (stages ++ [bs]))).toList = O ++ [.chain h join lx entry one sfp (firsts ++ [first])
      (stages ++ [bs])] := by
    rw [Rev.toList_push, Rev.toList_pop, hout₉]
    simp
  have hSc : st₈.chainIn = none := hch₈ ((show st₃.chainIn = st₂.chainIn from hk₃).trans hch₂)
  have hst₃o : st₃.out.toList = O ++ [.chain h join lx entry one sfp firsts stages] := by
    rw [hops, hout, List.append_nil]
  have hq₂ : p₀ + blockSize (O ++ [.chain h join lx entry one sfp (firsts ++ [first])
      (stages ++ [bs])]) = q + armsSize bs := by
    rw [bsize_append]
    simp [blockSize, stmtSize, stagesSize_append, stagesSize, hq, Nat.add_assoc]
  have hr₈' : ∀ v ∈ allocsOf sc'.rest, v ∈ allocsOf st₈.rest := fun v hv => by
    rw [hr₈, hev]
    simp only [allocsOf, List.flatMap_cons, List.mem_append]
    exact Or.inr hv
  -- what the final placement gives the stage
  have hfinal : ∀ (st' : St) (blk' : List PStmt), st₈.next ≤ st'.next → LocsLe st₈.locs st'.locs →
      (∀ y ∈ st₈.tables.shared, y ∈ st'.tables.shared) →
      st'.out.toList = O ++ [.chain h join lx entry one sfp (firsts ++ [first])
        (stages ++ [bs])] ++ blk' → FinAt Γ I Ag p₀ st' →
      OutOps I st₃ ∧ Fits I st₈ ∧ TabsW Γ Ag st₈ ∧ OpsIn I q (armsOps bs q) ∧
      (∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
        L.read (addressOfIndex (Γ.l.tablesBase + (first + j))) =
          some (Γ.tgt (q + armsSize (bs.take j)))) ∧
      FillsIn Γ Ag (q + armsSize (bs.take j)) bs[j] ∧
      I.ops[p₀ + blockSize O]? = some (.set join (.local (q + armsSize bs))) ∧
      q + armsSize bs ≤ I.ops.length := by
    intro st' blk' hn' hl' ht' ho' hF
    obtain ⟨hFt, hOp, hT, hFl⟩ := hF
    have hOp' := hOp
    unfold OpsAt at hOp'
    rw [ho'] at hOp'
    have hN := opsIn_node (more := []) (stages := stages) (blocks := bs) hOp'
    have hFl' := hFl
    rw [ho'] at hFl'
    have hFN := fills_node (fs := []) (more := []) hlen hFl' j hjb
    have hss : stagesSize (stages ++ [bs]) = stagesSize stages + armsSize bs := by
      rw [stagesSize_append]; simp [stagesSize]
    refine ⟨fun h₁ o₁ hm => ?_, hFt.back hn' hl', hT.back ht', hN.2.1, hFN.1, hFN.2, ?_, ?_⟩
    · refine (OpsAt.outOps hOp) h₁ o₁ ?_
      rw [hst₃o] at hm
      rw [ho']
      simp only [List.mem_append, List.mem_singleton] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl (Or.inl hm)
      · cases hm
    · rw [hN.1, hss, hq]
      simp only [Nat.add_assoc]
    · have := hN.2.2
      rw [hss] at this
      rw [hq]; omega
  -- the selector's words
  have hxrw : ∀ (C' : (ℕ → E) → Prop) (st' : St), Stronger C' C₃ → st₃.next ≤ st'.next →
      LocsLe st₃.locs st'.locs → (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st₃.rest) →
      OutOps I st₃ → RW I C' st' [x] := by
    intro C' st' hsC hn' hl' hsub hO v hv
    rw [List.mem_singleton] at hv
    subst hv
    obtain ⟨l₀, hl₀⟩ := Option.ne_none_iff_exists'.mp hpl₃
    refine ⟨fun h' => ?_, fun _ l hl => ?_⟩
    · have := ((hinvS hO).fresh v (hsub v h')).2
      rw [hx] at this
      cases this
    · have h3 : st₃.locs[v]? = some l₀ := by rw [hlo₃]; exact hl₀
      rw [hl' v l₀ h3] at hl
      cases hl
      obtain ⟨b1, b2, b3⟩ := hvw₂ v l₀ hx hl₀
      exact ⟨b1, lt_of_lt_of_le b2 (le_trans hn₃ hn'), fun Ψ hΨ => b3 Ψ (hs₃ Ψ (hsC Ψ hΨ))⟩
  -- the jump to the join
  have hjn_of : Fits I st₈ → OpsIn I q (armsOps bs q) →
      I.ops[p₀ + blockSize O]? = some (.set join (.local (q + armsSize bs))) →
      q + armsSize bs ≤ I.ops.length → ∀ blk : List PStmt,
      bs[j] = blk ++ (if j + 1 != bs.length then [PStmt.op [] (.jump one₀ join sfp₀)] else []) →
      ∀ C' : (ℕ → E) → Prop, Stronger C' C₃ → PremW I ctx → ∀ Ψ, C' Ψ → ∀ σ', I.Same σ' →
      ∀ kh : ℕ → E × E, j + 1 ≠ bs.length →
      JumpTo Γ I.fp I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) one₀ join sfp₀ (q + armsSize bs) := by
    intro hFt hA hset hle blk hbj C' hsC' _ Ψ hΨ σ' _ kh hjl
    have hc3 : C₃ Ψ := hsC' Ψ hΨ
    have hr : Rds (Ag σ' Ψ kh) I.fp I.size (fwd I.hdr ⟨patchT I Ψ σ', kh⟩) :=
      fun κ L hL m hm => hAg σ' Ψ kh κ L hL m hm
    have hbj' : bs[j] = blk ++ [PStmt.op [] (.jump one₀ join sfp₀)] := by
      rw [hbj]; simp [hjl]
    have hjm : LOp.jump one₀ join sfp₀ ∈ I.ops :=
      hA.mem _ (armsOps_mem bs q j hjb _ (by
        rw [hbj', bops_append]; simp [blockOps, stmtOps]))
    have hto : ¬ I.tc one₀ := not_tc_of hI hjm (by simp [opCells]) fun _ h => nomatch h
    have hts : ¬ I.tc sfp₀ := not_tc_of hI hjm (by simp [opCells]) fun _ h => nomatch h
    have htj : ¬ I.tc join :=
      not_tc_of hI (List.mem_of_getElem? hset) (by simp [opCells]) fun _ h => nomatch h
    have hsz : st₈.next ≤ I.size := hFt.1
    have hj3 : join < st₃.next := lt_of_lt_of_le hjw.2.1 (le_trans hn₂ hn₃)
    exact jumpTo_of hr (lt_of_lt_of_le holt (le_trans hn₈ hsz))
      (lt_of_lt_of_le hj3 (le_trans hn₈ hsz)) (lt_of_lt_of_le hflt (le_trans hn₈ hsz))
      ((fwd_patchT ho2 hto).trans (how Ψ hc3))
      ((fwd_patchT hjw.1 htj).trans ((hjw.2.2 Ψ (hs₂ Ψ (hs₃ Ψ hc3))).trans
        ((joinW_eq hset).trans ((hkw _).trans (hlocB _ hle)))))
      ((fwd_patchT hf2 hts).trans (hfw Ψ hc3))
  suffices H : ∀ S : St, S.next = st₈.next → S.locs = st₈.locs → S.rest = sc'.rest →
      S.chainIn = none → S.tables = st₈.tables → S.lazy = none →
      S.out.toList = O ++ [.chain h join lx entry one sfp (firsts ++ [first]) (stages ++ [bs])] →
      (∀ hO : OutOps I st₃, ∃ blk leave, bs[j]? = some (blk ++ leave) ∧
        LeaveOK (.join join one₀ sfp₀) j arms.length leave C₉ 0 st₃.next st₈.next ∧
        (∀ es, walk I.σ arms[j] = .fall es → Fits I st₈ →
          OpsIn I (q + armsSize (bs.take j)) (blockOps blk (q + armsSize (bs.take j))) →
          TabsW Γ Ag st₈ → FillsIn Γ Ag (q + armsSize (bs.take j)) blk → WInv ctx I C₉ S sc') ∧
        (Fits I st₈ →
          OpsIn I (q + armsSize (bs.take j)) (blockOps blk (q + armsSize (bs.take j))) →
          TabsW Γ Ag st₈ → FillsIn Γ Ag (q + armsSize (bs.take j)) blk →
          BlkW Γ I ctx Ag cl C₉ blk arms[j] [] (walk I.σ arms[j]) i₀ (q + armsSize (bs.take j)) ∧
            RW I C₉ st₈ (pathVals I.σ arms[j] (walk I.σ arms[j])))) →
      FBAt ctx I C₉ S (placeBlock rest) fun _ C' st' => OpenOut (Γ := Γ) (Ag := Ag) (cl := cl)
        (ctx := ctx) (I := I) Q O h join lx entry one sfp firsts stages first x sc''
        (.match_ x arms :: rest) tl o i₀ p₀ C' st' by
    intro hc
    refine wp_bind.mpr (wp_set.mpr ?_)
    unfold endStmt
    refine wp_bind.mpr (wp_modify.mpr ?_)
    exact H _ (by rfl) (by rfl) (by rfl) (by exact hSc) (by rfl) (by rfl) (by exact hSo') (fun hO =>
      let ⟨blk, leave, hbs, hlv, hW, hB⟩ := hpick hO
      ⟨blk, leave, hbs, hlv, fun es hfe a b c d =>
        winv_out (winv_emit (hW es hfe a b c d) hem (PStmt.op [] (.jump 0 0 0))).2 _, hB⟩) hc
  intro S hSn hSl hSr hSc' hSt hSz hSo hPick
  have hdead := FBAt.dead (ctx := ctx) (I := I) (C := C₉) (st := S) (m := placeBlock rest)
    (Q := fun _ st' => (S.chainIn = none → st'.chainIn = none ∧
        ∃ blk, st'.out.toList = S.out.toList ++ blk) ∧
      ((S.lazy = none → ∀ v, st'.locs[v]? ≠ none → S.locs[v]? ≠ none ∨ v ∈ allocsOf S.rest ∨
        ∃ run, Atom.frameAddr v run ∈ atomsIn rest) ∧
      (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf S.rest) ∧
      ∀ y ∈ S.tables.shared, y ∈ st'.tables.shared))
    (wp_mono (wp_and (hmono rest S) (hnew rest S)) fun _ _ ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩)
  have hfin' : ∀ (st' : St) (blk' : List PStmt), S.next ≤ st'.next → LocsLe S.locs st'.locs →
      (∀ y ∈ S.tables.shared, y ∈ st'.tables.shared) → st'.out.toList = S.out.toList ++ blk' →
      FinAt Γ I Ag p₀ st' → _ := fun st' blk' hn' hl' ht' ho' hF =>
    hfinal st' blk' (by rw [← hSn]; exact hn') (by rw [← hSl]; exact hl')
      (by rw [hSt] at ht'; exact ht') (by rw [ho', hSo]) hF
  by_cases hO : OutOps I st₃
  swap
  · refine FBAt.mono hdead ?_
    rintro _ C' st' - hn' hl' ⟨-, hcm, -, -, ht'⟩
    obtain ⟨hc', blk', hblk'⟩ := hcm hSc'
    exact ⟨hc', fun _ _ hF _ => absurd (hfin' st' blk' hn' hl' ht' hblk' hF).1 hO,
      fun hF _ => absurd (hfin' st' blk' hn' hl' ht' hblk' hF).1 hO⟩
  obtain ⟨blk, leave, hbs, hlv, hWS, hB⟩ := hPick hO
  have hbj : bs[j] = blk ++
      (if j + 1 != bs.length then [PStmt.op [] (.jump one₀ join sfp₀)] else []) := by
    have e1 : bs[j] = blk ++ leave :=
      Option.some.inj ((List.getElem?_eq_getElem hjb).symm.trans hbs)
    rw [e1, hlenb']
    simp only [LeaveOK] at hlv
    rw [hlv]
  have hfa' : ∀ v ∈ pathVals I.σ arms[j] (walk I.σ arms[j]), ∀ run,
      Atom.frameAddr v run ∉ atomsIn rest := fun v hv run =>
    hfa v (by rw [hw1]; exact pathVals_arm hj hsel v hv) run
  have hgrow : ∀ (C' : (ℕ → E) → Prop) (st' : St), Stronger C' C₉ → S.next ≤ st'.next →
      LocsLe S.locs st'.locs →
      (∀ v, st'.locs[v]? ≠ none → S.locs[v]? ≠ none ∨ v ∈ allocsOf S.rest ∨
        ∃ run, Atom.frameAddr v run ∈ atomsIn rest) →
      (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf S.rest) →
      RW I C₉ st₈ (pathVals I.σ arms[j] (walk I.σ arms[j])) →
      RW I C' st' ([x] ++ pathVals I.σ arms[j] (walk I.σ arms[j])) := by
    intro C' st' hsC hn' hl' hnw hrr hR
    have hsub : ∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st₈.rest := fun v hv =>
      hr₈' v (by rw [← hSr]; exact hrr v hv)
    refine (hxrw C' st' (fun Ψ h => hs₈ Ψ (hsC Ψ h)) (le_trans hn₈ (hSn ▸ hn'))
      (hl₈.trans (hSl ▸ hl')) (fun v hv => hsub₈ v (hsub v hv)) hO).append
      (hR.grow hsC (hSn ▸ hn') (hSl ▸ hl') (fun v hv hp => ?_) hsub)
    rcases hnw v hp with h1 | h1 | ⟨run, h1⟩
    · exact Or.inl (by rw [← hSl]; exact h1)
    · exact Or.inr (hr₈' v (by rw [← hSr]; exact h1))
    · exact absurd h1 (hfa' v hv run)
  generalize ho₁ : walk I.σ arms[j] = o₁ at hw hWS hB hgrow hst
  cases o₁ with
  | stuck => exact absurd rfl hst
  | ret es₁ vs =>
    have ho : o = .ret es₁ vs := by rw [← hw]; rfl
    have hw1' : walk1 I.σ (.match_ x arms) = .ret es₁ vs := by rw [hw1, ho₁]
    refine FBAt.mono hdead ?_
    rintro _ C' st' - hn' hl' ⟨rfl, hcm, hnw, hrr, ht'⟩
    obtain ⟨hc', blk', hblk'⟩ := hcm hSc'
    refine ⟨hc', fun es he _ _ => (by rw [ho] at he; cases he), fun hF _ => ?_⟩
    obtain ⟨-, hFt, hT, hA, hslot, hFa, hset, hle⟩ := hfin' st' blk' hn' hl' ht' hblk' hF
    have hA' := armsOps_in bs q j hjb hA
    rw [hbj, bops_append] at hA'
    have hFa' : FillsIn Γ Ag (q + armsSize (bs.take j)) blk := by
      rw [hbj] at hFa; exact hFa.left
    obtain ⟨hBw, hRw⟩ := hB hFt hA'.left hT hFa'
    refine ⟨[first], [bs], blk', j, q + armsSize (bs.take j), by rw [hblk', hSo], rfl, rfl,
      by simp, by simp, hxj, hne, rfl, hslot, ?_, ?_⟩
    · exact stagesW_join hjb hj hbj hxj hne hxS hw.symm hBw (fun _ h => by cases h)
        (hjn_of hFt hA hset hle blk hbj C' hs₈)
    · rw [ho, pathVals_ret hw1']
      exact (hgrow C' st' (Stronger.refl _) hn' hl' (hnw hSz) hrr hRw).anti fun v hv => by
        simpa using pathVals_match hj hsel v hv
  | fall es₁ =>
    have hw1' : walk1 I.σ (.match_ x arms) = .fall es₁ := by rw [hw1, ho₁]
    have ho : o = (walk I.σ rest).pre es₁ := by rw [← hw]; rfl
    have hns₂ : walk I.σ rest ≠ .stuck := fun h' => hns (by rw [ho, h']; rfl)
    have hes' : outEs o = es₁ ++ outEs (walk I.σ rest) := by rw [ho, outEs_pre hns₂]
    have hc' : calls (outEs o) = calls es₁ ++ calls (outEs (walk I.σ rest)) := by
      rw [hes', calls_append']
    by_cases hF : Fits I st₈ ∧
        OpsIn I (q + armsSize (bs.take j)) (blockOps blk (q + armsSize (bs.take j))) ∧
        TabsW Γ Ag st₈ ∧ FillsIn Γ Ag (q + armsSize (bs.take j)) blk
    swap
    · refine FBAt.mono hdead ?_
      rintro _ C' st' - hn' hl' ⟨-, hcm, -, -, ht'⟩
      obtain ⟨hc', blk', hblk'⟩ := hcm hSc'
      have hF' : FinAt Γ I Ag p₀ st' → False := fun hFin => by
        obtain ⟨-, hFt, hT, hA, -, hFa, -, -⟩ := hfin' st' blk' hn' hl' ht' hblk' hFin
        have hA' := armsOps_in bs q j hjb hA
        rw [hbj, bops_append] at hA'
        have hFa' : FillsIn Γ Ag (q + armsSize (bs.take j)) blk := by
          rw [hbj] at hFa; exact hFa.left
        exact hF ⟨hFt, hA'.left, hT, hFa'⟩
      exact ⟨hc', fun _ _ hFin _ => (hF' hFin).elim, fun hFin _ => (hF' hFin).elim⟩
    obtain ⟨hFt₈, hA₈, hT₈, hFa₈⟩ := hF
    have hwinv := hWS es₁ rfl hFt₈ hA₈ hT₈ hFa₈
    obtain ⟨hBw, hRw⟩ := hB hFt₈ hA₈ hT₈ hFa₈
    refine FBAt.mono (FBAt.and_wp (hrw C₉ S sc' sc'' (i₀ + (calls es₁).length) p₀ _ hsc rfl hns₂
      (fun e he => hes e (by rw [hes']; exact List.mem_append_right _ he))
      (fun k hk => by
        rw [Nat.add_assoc, hcl _ (by rw [hc', List.length_append]; omega), hc',
          List.getElem?_append_right (by omega)]
        simp) hwinv) (hnew rest S)) ?_
    rintro _ C' st' hsC' hn' hl' ⟨⟨hWo, hc', hBo⟩, hnw, hrr, ht'⟩
    refine ⟨hc', fun es he hFin _ => ?_, fun hFin _ => ?_⟩
    · obtain ⟨es₂, h2⟩ : ∃ es₂, walk I.σ rest = .fall es₂ := by
        cases h : walk I.σ rest with
        | fall es₂ => exact ⟨es₂, rfl⟩
        | ret es₂ vs => rw [ho, h] at he; cases he
        | stuck => exact absurd h hns₂
      exact hWo es₂ h2 hFin
    · obtain ⟨blk', hblk', hBk, hRk⟩ := hBo hFin
      obtain ⟨-, -, -, hA, hslot, -, hset, hle⟩ := hfin' st' blk' hn' hl' ht' hblk' hFin
      rw [hSo, hq₂] at hBk
      refine ⟨[first], [bs], blk', j, q + armsSize (bs.take j), by rw [hblk', hSo], rfl, rfl,
        by simp, by simp, hxj, hne, rfl, hslot, ?_, ?_⟩
      · exact stagesW_join hjb hj hbj hxj hne hxS hw.symm (hBw.mono hsC')
          (fun _ h => by cases h; exact hBk)
          (hjn_of hFt₈ hA hset hle blk hbj C' fun Ψ h => hs₈ Ψ (hsC' Ψ h))
      · rw [ho]
        refine ((hgrow C' st' hsC' hn' hl' (hnw hSz) hrr hRw).append hRk).anti fun v hv => ?_
        rcases List.mem_append.mp (pathVals_fall hw1' hns₂ v hv) with h | h
        · exact List.mem_append_left _ (by simpa using pathVals_match hj hsel v h)
        · exact List.mem_append_right _ h

end Last

end

end LeanVM.Guest.Backend.Complete
