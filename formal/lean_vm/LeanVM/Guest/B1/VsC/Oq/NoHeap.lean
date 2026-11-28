/-
  LeanVM.Guest.B1.VsC.Oq.NoHeap

  `opening_queries`' hints write no heap word: its witness hints write frame cells.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.Sel
public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Memory.HintsCheck
public import LeanVM.Guest.Memory.HintsIn

/-!
# No heap hint

`noHeapA a`: the atom writes no hint word to the heap (`atomHeapDest?`). `oqQueryT_noHeap`,
`oqLoop1A_noHeap`, `oqLoop0A_noHeap`: every atom of a query (its arms included) and of an iteration
is such, by the templates' structure. `heapHintAddrs_flatM`: a flat body all of whose atoms are such
writes no heap word on its path.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory

@[expose] public section

/-- An atom writing no hint word to the heap. -/
def noHeapA (a : Atom) : Bool := (atomHeapDest? a).isNone

/-- A block of explicit atoms writing no heap word. -/
macro "nh" : tactic => `(tactic| simp [Stmt.atomsAll, noHeapA, atomHeapDest?, hintDest?, destHeap?])

theorem atomsAll_flatten_map {α : Type} {p : Atom → Bool} {f : α → List Stmt} :
    ∀ {l : List α}, (∀ x ∈ l, Stmt.atomsAll p (f x) = true) → Stmt.atomsAll p (l.map f).flatten = true
  | [], _ => by rw [List.map_nil, List.flatten_nil, Stmt.atomsAll]
  | x :: l, h => by
    rw [List.map_cons, List.flatten_cons, Stmt.atomsAll_append, h x (by simp),
      atomsAll_flatten_map fun y hy => h y (by simp [hy])]
    rfl

theorem armsAtomsAll_map {α : Type} {p : Atom → Bool} {f : α → List Stmt} :
    ∀ {l : List α}, (∀ x ∈ l, Stmt.atomsAll p (f x) = true) → Stmt.armsAtomsAll p (l.map f) = true
  | [], _ => by rw [List.map_nil, Stmt.armsAtomsAll]
  | x :: l, h => by
    rw [List.map_cons, Stmt.armsAtomsAll, h x (by simp), armsAtomsAll_map fun y hy => h y (by simp [hy])]
    rfl

theorem atomsAll_app {p : Atom → Bool} {l l' : List Stmt} (h : Stmt.atomsAll p l = true)
    (h' : Stmt.atomsAll p l' = true) : Stmt.atomsAll p (l ++ l') = true := by
  rw [Stmt.atomsAll_append, h, h']; rfl

theorem atomsAll_ite {p : Atom → Bool} {c : Prop} [Decidable c] {l l' : List Stmt}
    (h : Stmt.atomsAll p l = true) (h' : Stmt.atomsAll p l' = true) :
    Stmt.atomsAll p (if c then l else l') = true := by
  split <;> assumption

/-! ## The query -/

section
variable (s : Oq)

theorem oqPrepT_noHeap (b : ℕ) : Stmt.atomsAll noHeapA (oqPrepT s b) = true := by
  unfold oqPrepT
  refine atomsAll_app (by unfold oqRowT; nh) ?_
  split
  · exact atomsAll_flatten_map fun _ _ => by unfold oqPackT; nh
  · nh

theorem oqLeafT_noHeap (b pr kL : ℕ) : Stmt.atomsAll noHeapA (oqLeafT s b pr kL) = true := by
  unfold oqLeafT
  refine atomsAll_flatten_map fun k _ => ?_
  unfold oqBlockT
  split_ifs
  · nh
  · refine atomsAll_app (atomsAll_flatten_map fun c _ => ?_) (by nh)
    unfold oqXorT
    dsimp only
    split_ifs <;> nh

theorem oqArmT_noHeap (pr kN ch i a : ℕ) : Stmt.atomsAll noHeapA (oqArmT s pr kN ch i a) = true := by
  unfold oqArmT
  refine atomsAll_app (atomsAll_flatten_map fun r _ => ?_) (by nh)
  unfold oqStepT
  nh

theorem oqWalkT_noHeap (bp cap flags : V) (pr kN ch : ℕ) :
    Stmt.atomsAll noHeapA (oqWalkT s bp cap flags pr kN ch) = true := by
  unfold oqWalkT oqPathT
  refine atomsAll_app (atomsAll_app (by nh) (atomsAll_flatten_map fun i _ => ?_)) (by unfold oqCapT; nh)
  unfold oqWinT
  simp [Stmt.atomsAll, noHeapA, atomHeapDest?, armsAtomsAll_map fun a _ => oqArmT_noHeap s pr kN ch i a]

theorem oqFoldT_noHeap (coefs x : V) (b F : ℕ) : Stmt.atomsAll noHeapA (oqFoldT s coefs x b F) = true := by
  unfold oqFoldT
  refine atomsAll_flatten_map fun j _ => ?_
  unfold oqRoundT
  dsimp only
  exact atomsAll_app (by nh) (atomsAll_flatten_map fun _ _ => by nh)

theorem nvLevelT_noHeap (w : V) : ∀ (ins : List ℕ) (k : ℕ), Stmt.atomsAll noHeapA (nvLevelT w ins k).1 = true
  | _ :: _ :: rest, k => by
    simp only [nvLevelT]; exact atomsAll_app (by nh) (nvLevelT_noHeap w rest (k + 2))
  | [_], _ => by simp only [nvLevelT]; nh
  | [], _ => by simp only [nvLevelT]; nh

theorem nvLevelsT_noHeap (ws : ℕ → ℕ) : ∀ (c i : ℕ) (ins : List ℕ) (k : ℕ),
    Stmt.atomsAll noHeapA (nvLevelsT ws c i ins k).1 = true
  | 0, _, _, _ => by simp only [nvLevelsT]; nh
  | c + 1, i, ins, k => by
    simp only [nvLevelsT]; exact atomsAll_app (nvLevelT_noHeap _ _ _) (nvLevelsT_noHeap ws c _ _ _)

theorem oqFinT_noHeap (x hs : V) (v : ℕ) : Stmt.atomsAll noHeapA (oqFinT s x hs v) = true := by
  unfold oqFinT oqWsT oqNovel nvLevel0T
  dsimp only
  refine atomsAll_app (atomsAll_app (atomsAll_app (by nh) (atomsAll_flatten_map fun _ _ => by nh))
    (atomsAll_app (atomsAll_flatten_map fun _ _ => by nh) (nvLevelsT_noHeap _ _ _ _ _))) (by nh)

theorem oqPad_noHeap (emit : Bool) (k : ℕ) :
    Stmt.atomsAll noHeapA (if emit then oqPadT k else []) = true := by
  split
  · unfold oqPadT; nh
  · nh

theorem oqFin_noHeap (x hs : V) (v : ℕ) :
    Stmt.atomsAll noHeapA (if s.final = 1 then oqFinT s x hs v else []) = true := by
  split
  · exact oqFinT_noHeap s x hs v
  · nh

/-- **A query writes no heap word.** -/
theorem oqQueryT_noHeap (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ) :
    Stmt.atomsAll noHeapA (oqQueryT s x bp cap flags coefs hs b emit pr) = true := by
  rw [QD.oqQueryT_eq]
  exact atomsAll_app (atomsAll_app (atomsAll_app (atomsAll_app (oqPrepT_noHeap s b)
    (oqPad_noHeap _ _)) (oqLeafT_noHeap s _ _ _)) (oqWalkT_noHeap s _ _ _ _ _ _))
    (atomsAll_app (oqFoldT_noHeap s _ _ _ _) (oqFin_noHeap s _ _ _))

theorem oqGuardA_noHeap (g : ℕ) : Stmt.atomsAll noHeapA (oqGuardA g) = true := by unfold oqGuardA; nh

/-- **A level-0 iteration writes no heap word.** -/
theorem oqLoop1A_noHeap : Stmt.atomsAll noHeapA (oqLoop1A s) = true := by
  unfold oqLoop1A
  dsimp only
  refine atomsAll_app (atomsAll_app (atomsAll_app (atomsAll_app (atomsAll_app (by nh)
    (oqQueryT_noHeap s _ _ _ _ _ _ _ _ _)) (by nh)) (oqQueryT_noHeap s _ _ _ _ _ _ _ _ _)) ?_)
    (oqGuardA_noHeap _)
  split <;> nh

/-- **A deeper iteration writes no heap word.** -/
theorem oqLoop0A_noHeap : Stmt.atomsAll noHeapA (oqLoop0A s) = true := by
  unfold oqLoop0A
  dsimp only
  refine atomsAll_app (atomsAll_app (atomsAll_app (by nh) (oqQueryT_noHeap s _ _ _ _ _ _ _ _ _)) ?_)
    (oqGuardA_noHeap _)
  split <;> nh

end

/-! ## Paths -/

theorem armEvs_noHeap {σ : Val} : ∀ {arm : List Stmt}, Stmt.atomsAll noHeapA arm = true →
    (armEvs arm).flatMap (Ev.hintAddrs σ) = []
  | [], _ => rfl
  | .atom a :: arm, h => by
    simp only [Stmt.atomsAll, Bool.and_eq_true] at h
    have ih := armEvs_noHeap (σ := σ) h.2
    simp only [armEvs, List.filterMap_cons, List.flatMap_cons] at ih ⊢
    rw [ih, List.append_nil]
    have hn := h.1
    cases a with
    | hint hh =>
      simp only [noHeapA, atomHeapDest?] at hn
      simp only [Ev.hintAddrs]
      split
      · rename_i hx; rw [hx] at hn; simp at hn
      · rfl
    | _ => rfl
  | .ite .. :: arm, h | .match_ .. :: arm, h => by
    simp only [Stmt.atomsAll, Bool.and_eq_true] at h
    have ih := armEvs_noHeap (σ := σ) h.2
    simpa [armEvs] using ih
  | .call .. :: arm, h | .callIf .. :: arm, h | .dispatch .. :: arm, h | .ret _ :: arm, h => by
    simp only [Stmt.atomsAll] at h
    have ih := armEvs_noHeap (σ := σ) h
    simpa [armEvs] using ih

theorem armsAtomsAll_getD {p : Atom → Bool} : ∀ {arms : List (List Stmt)} (i : ℕ),
    Stmt.armsAtomsAll p arms = true → Stmt.atomsAll p (arms.getD i []) = true
  | [], _, _ => by simp [Stmt.atomsAll]
  | a :: as, 0, h => by simp only [Stmt.armsAtomsAll, Bool.and_eq_true] at h; simpa using h.1
  | a :: as, i + 1, h => by
    simp only [Stmt.armsAtomsAll, Bool.and_eq_true] at h; simpa using armsAtomsAll_getD i h.2

/-- **A flat body whose atoms write no heap word** writes none on its path. -/
theorem heapHintAddrs_flatM (σ : Val) : ∀ pre : List Stmt, pre.all Stmt.flatM = true →
    Stmt.atomsAll noHeapA pre = true → heapHintAddrs σ (pre.flatMap (fmEvs σ)) = []
  | [], _, _ => rfl
  | st :: pre, hf, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    rw [List.flatMap_cons, heapHintAddrs, List.flatMap_append, ← heapHintAddrs, ← heapHintAddrs]
    match st, hf.1, h with
    | .atom a, _, h =>
      simp only [Stmt.atomsAll, Bool.and_eq_true] at h
      rw [heapHintAddrs_flatM σ pre hf.2 h.2, List.append_nil]
      have hn := h.1
      cases a with
      | hint hh =>
        simp only [noHeapA, atomHeapDest?] at hn
        simp only [heapHintAddrs, fmEvs, slEvs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          Ev.hintAddrs]
        split
        · rename_i hx; rw [hx] at hn; simp at hn
        · rfl
      | _ => rfl
    | .call .., _, h =>
      simp only [Stmt.atomsAll] at h
      rw [heapHintAddrs_flatM σ pre hf.2 h]; rfl
    | .callIf .., _, h =>
      simp only [Stmt.atomsAll] at h
      rw [heapHintAddrs_flatM σ pre hf.2 h]
      simp only [heapHintAddrs, fmEvs, slEvs, List.flatMap_cons, List.flatMap_nil]
      split <;> rfl
    | .match_ x arms, _, h =>
      simp only [Stmt.atomsAll, Bool.and_eq_true] at h
      rw [heapHintAddrs_flatM σ pre hf.2 h.2, List.append_nil, heapHintAddrs, fmEvs]
      exact armEvs_noHeap (armsAtomsAll_getD _ h.1)

end
end LeanVM.Guest.B1
