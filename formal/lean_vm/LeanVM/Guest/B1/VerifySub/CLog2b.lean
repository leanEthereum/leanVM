/-
  LeanVM.Guest.B1.VerifySub.CLog2b

  `verify_log2_ceil`'s path: its body walks a straight-line prefix, the minimality check's two
  branches, and two copies.
-/

module

public import LeanVM.Guest.B1.VerifySub.CLog2a

/-!
# `verify_log2_ceil`'s path

`vlBody fl` is the straight-line `vlPre fl`, the branch on `L = floor` (and inside it on `L = 0`)
and the two copies of the returned words. `vl_walk`: its walk under any valuation, the branches'
events `vlMid`; `vl_parts`: one `HeapBuf` of 35 words at `.n 3`, no frame, no call, and the loads
of the prefix and, through both branches, of the check proper.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

/-- The tail's statements before the branch. -/
def vlTailPre (fl : ℕ) : List Stmt :=
  [.atom (.hint (.log2Ceil (.heap (.n 0) 0 34) 34 fl (.n 409))),
    .atom (.const (.n 410) (word (2 ^ 33) 0 0)), .atom (.rangeCheck (.n 409) (.n 411) (.n 412) (.n 413) (.n 410)),
    .atom (.const (.n 414) (word (2 ^ 33) 0 0)), .atom (.const (.n 415) (word (2 ^ fl) 0 0)),
    .atom (.mul (.n 409) (.n 416) (.n 415)),
    .atom (.rangeCheck (.n 416) (.n 417) (.n 418) (.n 419) (.n 414)),
    .atom (.mul (.n 420) (.n 3) (.n 409)), .atom (.load (.n 421) (.n 420) 0),
    .atom (.add (.n 422) (.n 421) (.n 408)), .atom (.mul (.n 423) (.n 422) (.n 421)),
    .atom (.const (.n 424) (word 0 0 0)), .atom (.assertEq (.n 423) (.n 424)),
    .atom (.mul (.n 425) (.n 1) (.n 409)), .atom (.load (.n 426) (.n 425) 0),
    .atom (.add (.n 427) (.n 408) (.n 426)), .atom (.mul (.n 428) (.n 422) (.n 427)),
    .atom (.const (.n 429) (word 0 0 0)), .atom (.assertEq (.n 428) (.n 429)),
    .atom (.const (.n 430) (word (2 ^ fl) 0 0)), .atom (.add (.n 431) (.n 409) (.n 430))]

/-- The straight-line prefix. -/
def vlPre (fl : ℕ) : List Stmt :=
  [.atom (.hint (.alloc (.n 3) 35)), .atom (.const (.n 4) (word 0 0 0)),
    .atom (.load (.n 4) (.n 3) 0)] ++ ((List.range 34).map vlBlk).flatten ++ vlTailPre fl

/-- The copies of the returned words. -/
def vlCopies : List Stmt := [.atom (.copy (.n 449) (.n 409)), .atom (.copy (.n 450) (.n 405))]

/-- The minimality check's first statements. -/
def vlMin0 : List Stmt := [.atom (.const (.n 432) (word 1 0 0)), .atom (.add (.n 433) (.n 409) (.n 432))]

theorem vlBody_eq (fl : ℕ) :
    vlBody fl = vlPre fl ++ .ite (.n 431) [] vlMin :: (vlCopies ++ [.ret [.n 449, .n 450]]) := by
  simp [vlBody, vlPre, vlTail, vlTailPre, vlCopies]

theorem vlBlk_straight : ∀ j, (vlBlk j).all Main.Stmt.straight = true
  | 0 => rfl
  | _ + 1 => rfl

theorem vlPre_straight (fl : ℕ) : (vlPre fl).all Main.Stmt.straight = true := by
  simp only [vlPre, List.all_append, List.all_flatten, List.all_map, Bool.and_eq_true]
  refine ⟨⟨rfl, ?_⟩, rfl⟩
  simp only [List.all_eq_true, List.mem_range, Function.comp_apply]
  exact fun j _ => List.all_eq_true.mp (vlBlk_straight j)

/-- The branches' events. -/
noncomputable def vlMid (σ : Val) : List Memory.Ev :=
  .inK (.n 431) :: if σ (.n 431) = 0 then [] else vlMin0.flatMap (Main.slEvs σ) ++
    .inK (.n 433) :: if σ (.n 433) = 0 then [] else vlMinIn.flatMap (Main.slEvs σ)

/-- The path's events. -/
noncomputable def vlEvs (fl : ℕ) (σ : Val) : List Memory.Ev :=
  (vlPre fl).flatMap (Main.slEvs σ) ++ vlMid σ ++ vlCopies.flatMap (Main.slEvs σ)

theorem walk_straight_fall (σ : Val) (pre : List Stmt) (h : pre.all Main.Stmt.straight = true) :
    walk σ pre = .fall (pre.flatMap (Main.slEvs σ)) := by
  have := walk_pre_straight σ [] pre h
  simpa [walk, Out.pre] using this

/-- **`verify_log2_ceil`'s path.** -/
theorem vl_walk (fl : ℕ) (σ : Val) : walk σ (vlBody fl) = .ret (vlEvs fl σ) [.n 449, .n 450] := by
  rw [vlBody_eq, walk_pre_straight σ _ _ (vlPre_straight fl), walk,
    Main.walk_straight σ _ vlCopies rfl]
  have h0 : walk σ vlMin0 = .fall (vlMin0.flatMap (Main.slEvs σ)) := walk_straight_fall σ _ rfl
  have h1 : walk σ vlMinIn = .fall (vlMinIn.flatMap (Main.slEvs σ)) := walk_straight_fall σ _ rfl
  have hm : walk σ vlMin = (walk σ [.ite (.n 433) [] vlMinIn]).pre (vlMin0.flatMap (Main.slEvs σ)) :=
    walk_pre_straight σ _ vlMin0 rfl
  simp only [walk1, hm, walk, h1]
  by_cases a : σ (.n 431) = 0 <;> by_cases b : σ (.n 433) = 0 <;>
    simp [a, b, Out.pre, Out.seq, vlEvs, vlMid]

theorem vlBlk_parts : ∀ j, (vlBlk j).filterMap Main.Stmt.allocSz = [] ∧
    (vlBlk j).filterMap Main.Stmt.addrS = [] ∧ (vlBlk j).filterMap Main.Stmt.callS = [] ∧
    (vlBlk j).filterMap Stmt.loadS = [(.n 0, j), (.n 2, j), (.n 3, j + 1)]
  | 0 => ⟨rfl, rfl, rfl, rfl⟩
  | _ + 1 => ⟨rfl, rfl, rfl, rfl⟩

theorem vlPre_parts (fl : ℕ) : (vlPre fl).filterMap Main.Stmt.allocSz = [(.n 3, .inl 35)] ∧
    (vlPre fl).filterMap Main.Stmt.addrS = [] ∧ (vlPre fl).filterMap Main.Stmt.callS = [] ∧
    (vlPre fl).filterMap Stmt.loadS = (.n 3, 0) :: (((List.range 34).map fun j =>
      [(.n 0, j), (.n 2, j), (.n 3, j + 1)]).flatten ++ [(.n 420, 0), (.n 425, 0)]) := by
  have hb : ∀ {β : Type} (f : Stmt → Option β) (g : ℕ → List β), (∀ j, (vlBlk j).filterMap f = g j) →
      ((List.range 34).map vlBlk).flatten.filterMap f = ((List.range 34).map g).flatten := by
    intro β f g h
    rw [List.filterMap_flatten, List.map_map]
    exact congrArg List.flatten (List.map_congr_left fun j _ => h j)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [vlPre, List.filterMap_append, List.filterMap_append]
  · rw [hb _ (fun _ => []) fun j => (vlBlk_parts j).1]
    simp [vlTailPre, Main.Stmt.allocSz]
  · rw [hb _ (fun _ => []) fun j => (vlBlk_parts j).2.1]
    simp [vlTailPre, Main.Stmt.addrS]
  · rw [hb _ (fun _ => []) fun j => (vlBlk_parts j).2.2.1]
    simp [vlTailPre, Main.Stmt.callS]
  · rw [hb _ _ fun j => (vlBlk_parts j).2.2.2]
    rfl

/-- **The path's parts**: one `HeapBuf` of 35 words at `.n 3`, no frame, no call; the loads
those of the prefix, and of the check proper through both branches. -/
theorem vl_parts (fl : ℕ) (σ : Val) : allocDsts (vlEvs fl σ) = [.n 3] ∧
    allocs σ (vlEvs fl σ) = [35] ∧ addrs (vlEvs fl σ) = [] ∧ calls (vlEvs fl σ) = [] ∧
    ∀ A ∈ loadAddrs σ (vlEvs fl σ),
      (∃ q ∈ (vlPre fl).filterMap Stmt.loadS, A = (σ q.1).limb 0 * Parameters.gpow q.2) ∨
      (σ (.n 431) ≠ 0 ∧ σ (.n 433) ≠ 0 ∧
        (A = (σ (.n 436)).limb 0 * Parameters.gpow 0 ∨ A = (σ (.n 440)).limb 0 * Parameters.gpow 0)) := by
  obtain ⟨a1, a2, a3, a4⟩ := Main.straight_parts σ (vlPre fl) (vlPre_straight fl)
  obtain ⟨b1, b2, b3, b4⟩ := Main.straight_parts σ vlCopies rfl
  have l1 := loadAddrs_straight σ (vlPre fl) (vlPre_straight fl)
  obtain ⟨p1, p2, p3, -⟩ := vlPre_parts fl
  rw [p1] at a1 a2
  rw [p2] at a3
  rw [p3] at a4
  refine ⟨?_, ?_, ?_, ?_, fun A hA => ?_⟩
  · simp only [allocDsts, vlEvs, List.filterMap_append] at a1 b1 ⊢
    rw [a1, b1]
    unfold vlMid
    split_ifs <;> simp [vlMin0, vlMinIn, Main.slEvs, Ev.allocDst?, vlCopies, Main.Stmt.allocSz]
  · simp only [allocs, vlEvs, List.filterMap_append] at a2 b2 ⊢
    rw [a2, b2]
    unfold vlMid
    split_ifs <;> simp [vlMin0, vlMinIn, Main.slEvs, Ev.alloc?, vlCopies, Main.Stmt.allocSz]
  · simp only [addrs, vlEvs, List.filterMap_append] at a3 b3 ⊢
    rw [a3, b3]
    unfold vlMid
    split_ifs <;> simp [vlMin0, vlMinIn, Main.slEvs, Ev.addr?, vlCopies, Main.Stmt.addrS]
  · simp only [calls, vlEvs, List.filterMap_append] at a4 b4 ⊢
    rw [a4, b4]
    unfold vlMid
    split_ifs <;> simp [vlMin0, vlMinIn, Main.slEvs, Ev.call?, vlCopies, Main.Stmt.callS]
  · simp only [loadAddrs, vlEvs, List.filterMap_append, List.mem_append] at l1 hA
    rcases hA with (hA | hA) | hA
    · rw [l1] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      exact Or.inl ⟨q, hq, rfl⟩
    · unfold vlMid at hA
      by_cases a : σ (.n 431) = 0 <;> by_cases b : σ (.n 433) = 0 <;>
        simp [a, b, vlMin0, vlMinIn, Main.slEvs, Ev.loadAddr?] at hA
      refine Or.inr ⟨a, b, ?_⟩
      simp only [Parameters.gpow, pow_zero, mul_one]
      rcases hA with h | h
      exacts [Or.inl h.symm, Or.inr h.symm]
    · simp [vlCopies, Main.slEvs, Ev.loadAddr?] at hA

end
end LeanVM.Guest.B1.VerifySub
