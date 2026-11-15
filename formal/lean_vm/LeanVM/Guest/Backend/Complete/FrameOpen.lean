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

end

end LeanVM.Guest.Backend.Complete
