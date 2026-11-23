/-
  LeanVM.Guest.CoreMode.RouteWin

  A long body's passes of `CfOk` (`honB`'s, `faOkB`'s), in windows.
-/

module

public import LeanVM.Guest.CoreMode.Route
public import LeanVM.Guest.CoreMode.LoopWin

/-!
# A long body's core data checks in windows

`honB`'s passes over a body (`bodyCore`, `ptrCellB`, `retCellB`, `selGo`) are each one kernel evaluation;
for `main_loop2` each takes past the memory a module may take. Each is additive over a split of the body
(`selGo` from the top-level atoms before the split, `seenF`), so each is checked over consecutive slices:
`BWins` for the cells and the top-level statements, `SWins` for the selectors.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (stmtsOf)

@[expose] public section

/-- **A check over slices from `a`**, the last cut `e`. -/
abbrev BWins {α : Type} (F : List α → Bool) (l : List α) (e : ℕ) : ℕ → List ℕ → Prop :=
  Wins id (fun a b ↦ F (slice l a b) = true) e

theorem bwins_spec {α : Type} {F : List α → Bool} (hF : ∀ x y, F x = true → F y = true → F (x ++ y) = true)
    (h0 : F [] = true) {l : List α} {e : ℕ} :
    ∀ {a : ℕ} {cs : List ℕ}, BWins F l e a cs → a ≤ e ∧ F (slice l a e) = true :=
  wins_fold (Q := fun a _ ↦ F (slice l a e) = true) (by rw [slice_self]; exact h0) fun {a b _} hab hbe hw hq ↦ by
    simp only [id] at hab hbe hw hq
    rw [slice_split l hab hbe]; exact hF _ _ hw hq

/-- The cells' checks and the top-level statements', over statements. -/
noncomputable def cellsB (j : ℕ) (l : List Stmt) : Bool :=
  (stmtsOf l).all (fun s ↦ ptrCellB j s && retCellB j s) && l.all topOk

theorem cellsB_append {j : ℕ} (x y : List Stmt) (hx : cellsB j x = true) (hy : cellsB j y = true) :
    cellsB j (x ++ y) = true := by
  simp only [cellsB, Bool.and_eq_true, List.all_eq_true] at hx hy ⊢
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rw [stmtsOf_append] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hx.1 s hs
    · exact hy.1 s hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact hx.2 s hs
    · exact hy.2 s hs

/-! ## The selectors -/

/-- The top-level atoms of a block, the last first, before `seen`. -/
def seenF (seen : List Atom) : List Stmt → List Atom
  | [] => seen
  | .atom a :: ss => seenF (a :: seen) ss
  | _ :: ss => seenF seen ss

/-- No top-level `ret`. -/
def noRetTop : List Stmt → Bool
  | [] => true
  | .ret _ :: _ => false
  | _ :: ss => noRetTop ss

theorem seenF_append : ∀ (seen : List Atom) (x y : List Stmt), seenF seen (x ++ y) = seenF (seenF seen x) y
  | _, [], _ => rfl
  | seen, s :: x, y => by
    cases s with
    | atom a => exact seenF_append (a :: seen) x y
    | _ => exact seenF_append seen x y

theorem noRetTop_append : ∀ (x y : List Stmt), noRetTop x = true → noRetTop y = true → noRetTop (x ++ y) = true
  | [], _, _, hy => hy
  | s :: x, y, hx, hy => by
    cases s with
    | ret vs => simp [noRetTop] at hx
    | _ => simp only [noRetTop, List.cons_append] at hx ⊢; exact noRetTop_append x y hx hy

theorem selGo_append (j : ℕ) (ps : List V) (B : List Stmt) : ∀ (seen : List Atom) (x y : List Stmt), noRetTop x = true →
    selGo j ps B seen (x ++ y) = (selGo j ps B seen x && selGo j ps B (seenF seen x) y)
  | seen, [], y, _ => by simp [selGo, seenF]
  | seen, s :: x, y, h => by
    cases s with
    | atom a => simp only [List.cons_append, selGo, seenF]; exact selGo_append j ps B (a :: seen) x y h
    | ret vs => simp [noRetTop] at h
    | _ =>
      simp only [noRetTop] at h
      simp only [List.cons_append, selGo, seenF, selGo_append j ps B seen x y h, Bool.and_assoc]

/-- **The selectors' check over slices from `a`**, each with no top-level `ret`, from the top-level atoms
before it. -/
abbrev SWins (j : ℕ) (ps : List V) (l : List Stmt) (e : ℕ) : ℕ → List ℕ → Prop :=
  Wins id (fun a b ↦ (noRetTop (slice l a b) && selGo j ps l (seenF [] (l.take a)) (slice l a b)) = true) e

theorem take_slice {α : Type} (l : List α) {a b : ℕ} (hab : a ≤ b) : l.take b = l.take a ++ slice l a b := by
  unfold slice
  rw [show b = a + (b - a) by omega, List.take_add]
  simp

theorem swins_spec {j : ℕ} {ps : List V} {l : List Stmt} {e : ℕ} :
    ∀ {a : ℕ} {cs : List ℕ}, SWins j ps l e a cs →
      a ≤ e ∧ noRetTop (slice l a e) = true ∧ selGo j ps l (seenF [] (l.take a)) (slice l a e) = true := fun h ↦
  wins_fold (Q := fun a _ ↦ noRetTop (slice l a e) = true ∧ selGo j ps l (seenF [] (l.take a)) (slice l a e) = true)
    (by simp [slice_self, noRetTop, selGo]) (fun {a b _} hab hbe hw hq ↦ by
      simp only [id] at hab hbe hw hq
      rw [Bool.and_eq_true] at hw
      refine ⟨?_, ?_⟩
      · rw [slice_split l hab hbe]; exact noRetTop_append _ _ hw.1 hq.1
      · rw [slice_split l hab hbe, selGo_append j ps l _ _ _ hw.1, hw.2, ← seenF_append, ← take_slice l hab, hq.2]
        rfl) h

/-! ## The core data's checks of a long body -/

/-- The last statement is `ret []`. -/
def lastRet (l : List Stmt) : Bool :=
  match l.drop (l.length - 1) with
  | [.ret []] => true
  | _ => false

theorem lastRet_spec {l : List Stmt} (h : lastRet l = true) : l.drop (l.length - 1) = [.ret []] := by
  unfold lastRet at h
  split at h
  · assumption
  · cases h

/-- **`honB`'s passes over a long body**, from its windows: the cells and the top-level statements over the
whole body (`BWins`), the selectors over the body but its last statement (`SWins`), which is a `ret`. -/
theorem honB_long {j : ℕ} {fn : Fn} {cs ss : List ℕ} (hc : BWins (cellsB j) fn.body fn.body.length 0 cs)
    (hs : SWins j fn.params fn.body (fn.body.length - 1) 0 ss)
    (hl : lastRet fn.body = true) :
    (bodyCore fn.body || loopBC fn) = true ∧ (stmtsOf fn.body).all (ptrCellB j) = true ∧
      (stmtsOf fn.body).all (retCellB j) = true ∧ (selGo j fn.params fn.body [] fn.body || loopBC fn) = true := by
  obtain ⟨-, hcb⟩ := bwins_spec cellsB_append (by simp [cellsB, stmtsOf]) hc
  rw [slice_all] at hcb
  simp only [cellsB, Bool.and_eq_true, List.all_eq_true] at hcb
  obtain ⟨-, -, hsel⟩ := swins_spec hs
  have hb : fn.body = slice fn.body 0 (fn.body.length - 1) ++ [.ret []] := by
    rw [← lastRet_spec hl, slice, List.drop_zero, Nat.sub_zero, List.take_append_drop]
  rw [List.take_zero] at hsel
  refine ⟨?_, List.all_eq_true.mpr fun s hs ↦ (hcb.1 s hs).1, List.all_eq_true.mpr fun s hs ↦ (hcb.1 s hs).2, ?_⟩
  · simp only [bodyCore, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true]
    exact Or.inl ⟨fun s _ ↦ by cases s <;> rfl, hcb.2⟩
  · simp only [Bool.or_eq_true]
    left
    have hn := (swins_spec hs).2.1
    rw [show seenF [] [] = [] from rfl] at hsel
    have e := selGo_append j fn.params fn.body [] _ [.ret []] hn
    rw [hsel, ← hb] at e
    rw [e]
    simp [selGo, noMatch, noDsp, stmtsOf]

/-- **`faOkB` of a function with no `frameAddr`.** -/
theorem faOkB_of_noFA {j : ℕ} {Cf : CFun} (h : noFA Cf.fn.body = true) : faOkB j Cf = true := by
  simp [faOkB, faNeed, h]

end

end LeanVM.Guest.CoreMode
