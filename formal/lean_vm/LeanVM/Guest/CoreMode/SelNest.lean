/-
  LeanVM.Guest.CoreMode.SelNest

  A `match` the path reaches at the top level of a top-level `ite`'s branch (`selBr`): its selector is used by an
  atom the path walks.
-/

module

public import LeanVM.Guest.CoreMode.RouteWin
public import LeanVM.Guest.CoreMode.WalkS
public import LeanVM.Guest.Bridge.AlignRun
public import LeanVM.Guest.Bridge.JumpCellsSound

/-!
# Reached `match`es in a branch

* `zok_cases`: a cursor's statement is at the body's top level, at the top level of a top-level statement's
  sub-block, or deeper;
* `selGo_deep`, `selGo_arms`: `selGo` leaves no `match` deeper, nor in a top-level `match`'s arms;
* `sel_nested`: a `match` at the top level of a top-level `ite`'s branch, from which the path's events are its
  last ones, has its selector used by an atom the path walks: a path through the other branch would have
  walked the branch's atom that is once in the body (`selBr`'s `onceAfter`) elsewhere.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (stmtsOf stmtsSub stmtsArms subBlock blockAt Zip ZOk zUp upKeys zOk_iff evsC
  seq_eq_ret pre_eq_ret mem_stmtsOf sub_stmtsOf sub_stmtsSub sub_stmtsArms subBlock_sub walk_atomS)

public section

/-! ## Statements and walks -/

theorem stmtsOf_cases {w : Stmt} : ∀ {l : List Stmt}, w ∈ stmtsOf l → w ∈ l ∨ ∃ v ∈ l, w ∈ stmtsSub v
  | [], h => by simp [stmtsOf] at h
  | s :: l, h => by
    rw [stmtsOf, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact Or.inl List.mem_cons_self
    · exact Or.inr ⟨_, List.mem_cons_self, h⟩
    · rcases stmtsOf_cases h with h | ⟨v, hv, h⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, h⟩

theorem noRetList_append : ∀ (a b : List Stmt),
    Core.Stmt.noRetList (a ++ b) = (Core.Stmt.noRetList a && Core.Stmt.noRetList b)
  | [], b => by simp [Core.Stmt.noRetList]
  | s :: a, b => by simp only [List.cons_append, Core.Stmt.noRetList, noRetList_append a b, Bool.and_assoc]

theorem noMatch_mem {l : List Stmt} (h : noMatch l = true) {x : V} {arms : List (List Stmt)}
    (hm : Stmt.match_ x arms ∈ l) : False := by
  have := List.all_eq_true.mp h _ hm
  simp at this

theorem mem_seenF {a : Atom} : ∀ {seen : List Atom} {l : List Stmt}, a ∈ seenF seen l → a ∈ seen ∨ Stmt.atom a ∈ l
  | _, [], h => Or.inl h
  | seen, s :: l, h => by
    cases s with
    | atom b =>
      rcases mem_seenF (seen := b :: seen) (l := l) h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    | _ =>
      rcases mem_seenF (seen := seen) (l := l) h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem seq_eq_fall {o k : Out} {es : List Ev} (h : o.seq k = .fall es) :
    ∃ e1 e2, o = .fall e1 ∧ k = .fall e2 ∧ es = e1 ++ e2 := by
  cases o with
  | fall e1 =>
    cases k with
    | fall e2 =>
      simp only [Out.seq, Out.pre, Out.fall.injEq] at h
      exact ⟨e1, e2, rfl, rfl, h.symm⟩
    | ret e2 v => simp [Out.seq, Out.pre] at h
    | stuck => simp [Out.seq, Out.pre] at h
  | ret e1 v => simp [Out.seq] at h
  | stuck => simp [Out.seq] at h

theorem pre_eq_fall {o : Out} {pre es : List Ev} (h : o.pre pre = .fall es) :
    ∃ es', o = .fall es' ∧ es = pre ++ es' := by
  cases o with
  | fall e =>
    simp only [Out.pre, Out.fall.injEq] at h
    exact ⟨e, rfl, h.symm⟩
  | ret e v => simp [Out.pre] at h
  | stuck => simp [Out.pre] at h

section Walk

variable {σ : Val}

/-- A top-level atom of a block that falls through is on its path. -/
theorem walk_fall_atom {a : Atom} : ∀ {l : List Stmt} {es : List Ev}, walk σ l = .fall es →
    Stmt.atom a ∈ l → Ev.atom a ∈ es
  | [], _, _, hm => absurd hm List.not_mem_nil
  | s :: l, es, hw, hm => by
    rw [walk] at hw
    obtain ⟨e1, e2, h1, h2, rfl⟩ := seq_eq_fall hw
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [walk1, Out.fall.injEq] at h1
      subst h1
      exact List.mem_append_left _ List.mem_cons_self
    · exact List.mem_append_right _ (walk_fall_atom h2 hm)

/-- A block of top-level statements (`topOk`) with no top-level `ret` does not return. -/
theorem walk_noRetTop : ∀ (l : List Stmt), noRetTop l = true → l.all topOk = true →
    ∀ es vs, walk σ l ≠ .ret es vs
  | [], _, _, _, _, h => by simp [walk] at h
  | s :: l, hn, ht, es, vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    rw [walk] at h
    have hn' : noRetTop l = true := by
      cases s
      case ret => simp [noRetTop] at hn
      all_goals exact hn
    have hs : ∀ es vs, walk1 σ s ≠ .ret es vs := by
      have h1 := ht.1
      cases s with
      | ret _ => simp [noRetTop] at hn
      | call f a r => intro _ _ h'; simp [walk1] at h'
      | dispatch x fs args rets => intro _ _ h'; rw [walk1] at h'; exact pick_noRetP fs 0 h'
      | _ =>
        simp only [topOk, Bool.and_eq_true] at h1
        exact walk1_noRetP _ h1.1
    rcases seq_eq_ret h with ⟨e1, e2, -, h2, -⟩ | h1
    · exact walk_noRetTop l hn' ht.2 e2 vs h2
    · exact hs es vs h1

end Walk

/-! ## `selBr` and `selGo` -/

theorem onceAfter_spec {B S : List Stmt} (h : onceAfter B S = true) : ∃ b, Stmt.atom b ∈ S ∧ onceB B b = true := by
  simp only [onceAfter, List.any_eq_true] at h
  obtain ⟨s, hs, h⟩ := h
  cases s with
  | atom b => exact ⟨b, hs, h⟩
  | _ => simp at h

/-- **A branch's `match`**: its selector at its cell, used by a top-level atom before it, a top-level atom after it
once in the body. -/
theorem selBr_at {j : ℕ} {B : List Stmt} {x : V} {arms : List (List Stmt)} {S : List Stmt} :
    ∀ {seen : List Atom} {Q : List Stmt}, selBr j B seen (Q ++ .match_ x arms :: S) = true →
      cellB j x = true ∧ (∃ a ∈ seenF seen Q, x ∈ Memory.atomUses a) ∧ onceAfter B S = true
  | seen, [], h => by
    simp only [List.nil_append, selBr, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨⟨⟨⟨hc, a, ha, hu⟩, -⟩, ho⟩, -⟩ := h
    exact ⟨hc, ⟨a, ha, hu⟩, ho⟩
  | seen, s :: Q, h => by
    cases s with
    | atom b => exact selBr_at (seen := b :: seen) (Q := Q) h
    | match_ y as =>
      simp only [List.cons_append, selBr, Bool.and_eq_true] at h
      exact selBr_at (seen := seen) (Q := Q) h.2
    | ite c z n =>
      simp only [List.cons_append, selBr, Bool.and_eq_true] at h
      exact selBr_at (seen := seen) (Q := Q) h.2
    | _ => exact selBr_at (seen := seen) (Q := Q) h

/-- **No `match` below a branch's top level.** -/
theorem selBr_sub {j : ℕ} {B : List Stmt} : ∀ {seen : List Atom} {l : List Stmt}, selBr j B seen l = true →
    ∀ v ∈ l, ∀ s ∈ stmtsSub v, ∀ x arms, s ≠ .match_ x arms
  | _, [], _, v, hv, _, _, _, _, _ => absurd hv List.not_mem_nil
  | seen, u :: l, h, v, hv, s, hs, x, arms, he => by
    have hrest : ∃ seen', selBr j B seen' l = true := by
      cases u with
      | atom b => exact ⟨_, h⟩
      | match_ y as =>
        simp only [selBr, Bool.and_eq_true] at h
        exact ⟨_, h.2⟩
      | ite c z n =>
        simp only [selBr, Bool.and_eq_true] at h
        exact ⟨_, h.2⟩
      | _ => exact ⟨_, h⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · subst he
      cases v with
      | match_ y as =>
        simp only [selBr, Bool.and_eq_true] at h
        exact noMatch_mem h.1.1.2 hs
      | ite c z n =>
        simp only [selBr, Bool.and_eq_true] at h
        rw [stmtsSub, List.mem_append] at hs
        rcases hs with hs | hs
        · exact noMatch_mem h.1.1 hs
        · exact noMatch_mem h.1.2 hs
      | _ => simp [stmtsSub] at hs
    · obtain ⟨seen', h'⟩ := hrest
      exact selBr_sub h' v hv s hs x arms he

theorem selGo_cons {j : ℕ} {ps : List V} {B : List Stmt} {seen : List Atom} {u : Stmt} {ss : List Stmt}
    (h : selGo j ps B seen (u :: ss) = true) : (∃ seen', selGo j ps B seen' ss = true) ∨ noMatch (stmtsOf ss) = true := by
  cases u with
  | atom b => exact Or.inl ⟨_, h⟩
  | ret vs =>
    simp only [selGo, Bool.and_eq_true] at h
    exact Or.inr h.1
  | match_ y as =>
    simp only [selGo, Bool.and_eq_true] at h
    exact Or.inl ⟨_, h.2⟩
  | ite c z n =>
    simp only [selGo, Bool.and_eq_true] at h
    exact Or.inl ⟨_, h.2⟩
  | call f a r => exact Or.inl ⟨_, h⟩
  | callIf c f a => exact Or.inl ⟨_, h⟩
  | dispatch x fs a r =>
    simp only [selGo, Bool.and_eq_true] at h
    exact Or.inl ⟨_, h.2⟩

/-- **`selGo` before a top-level `ite` with a `match` in a branch**: no `ret` before it, its branches' `selBr`. -/
theorem selGo_split {j : ℕ} {ps : List V} {B R : List Stmt} {c : V} {z n : List Stmt}
    (hm : ∃ x arms, Stmt.match_ x arms ∈ stmtsOf z ++ stmtsOf n) :
    ∀ {seen : List Atom} {P : List Stmt}, selGo j ps B seen (P ++ .ite c z n :: R) = true →
      noRetTop P = true ∧ selBr j B (seenF seen P) z = true ∧ selBr j B (seenF seen P) n = true
  | seen, [], h => by
    simp only [List.nil_append, selGo, Bool.and_eq_true] at h
    exact ⟨rfl, h.1.1, h.1.2⟩
  | seen, s :: P, h => by
    cases s with
    | atom b => exact selGo_split hm (seen := b :: seen) (P := P) h
    | ret vs =>
      simp only [List.cons_append, selGo, Bool.and_eq_true] at h
      obtain ⟨x, arms, hx⟩ := hm
      refine (noMatch_mem h.1 (x := x) (arms := arms) ?_).elim
      rw [stmtsOf_append, stmtsOf, stmtsSub]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
    | match_ y as =>
      simp only [List.cons_append, selGo, Bool.and_eq_true] at h
      exact selGo_split hm (seen := seen) (P := P) h.2
    | ite c' z' n' =>
      simp only [List.cons_append, selGo, Bool.and_eq_true] at h
      exact selGo_split hm (seen := seen) (P := P) h.2
    | call f a r => exact selGo_split hm (seen := seen) (P := P) h
    | callIf c' f a => exact selGo_split hm (seen := seen) (P := P) h
    | dispatch x fs a r =>
      simp only [List.cons_append, selGo, Bool.and_eq_true] at h
      exact selGo_split hm (seen := seen) (P := P) h.2

/-- **No `match` two levels below the top** (`selGo`). -/
theorem selGo_deep {j : ℕ} {ps : List V} {B : List Stmt} : ∀ {seen : List Atom} {ss : List Stmt},
    selGo j ps B seen ss = true → ∀ u ∈ ss, ∀ w ∈ stmtsSub u, ∀ x arms, Stmt.match_ x arms ∈ stmtsSub w → False
  | _, [], _, u, hu, _, _, _, _, _ => absurd hu List.not_mem_nil
  | seen, v :: ss, h, u, hu, w, hw, x, arms, hs => by
    rcases List.mem_cons.mp hu with rfl | hu
    · cases u with
      | match_ y as =>
        simp only [selGo, Bool.and_eq_true] at h
        exact noMatch_mem h.1.2 (sub_stmtsArms hw hs)
      | ite c z n =>
        simp only [selGo, Bool.and_eq_true] at h
        rw [stmtsSub, List.mem_append] at hw
        rcases hw with hw | hw
        · rcases stmtsOf_cases hw with hw | ⟨v', hv', hw⟩
          · exact selBr_sub h.1.1 w hw _ hs x arms rfl
          · exact selBr_sub h.1.1 v' hv' _ (sub_stmtsSub hw hs) x arms rfl
        · rcases stmtsOf_cases hw with hw | ⟨v', hv', hw⟩
          · exact selBr_sub h.1.2 w hw _ hs x arms rfl
          · exact selBr_sub h.1.2 v' hv' _ (sub_stmtsSub hw hs) x arms rfl
      | _ => simp [stmtsSub] at hw
    · rcases selGo_cons h with ⟨seen', h'⟩ | h'
      · exact selGo_deep h' u hu w hw x arms hs
      · exact noMatch_mem h' (sub_stmtsOf (sub_stmtsOf (mem_stmtsOf hu) hw) hs)

/-- **No `match` in a top-level `match`'s arms** (`selGo`). -/
theorem selGo_arms {j : ℕ} {ps : List V} {B : List Stmt} : ∀ {seen : List Atom} {ss : List Stmt},
    selGo j ps B seen ss = true → ∀ y as, Stmt.match_ y as ∈ ss → ∀ x arms, Stmt.match_ x arms ∈ stmtsArms as → False
  | _, [], _, _, _, hu, _, _, _ => absurd hu List.not_mem_nil
  | seen, v :: ss, h, y, as, hu, x, arms, hs => by
    rcases List.mem_cons.mp hu with he | hu
    · subst he
      simp only [selGo, Bool.and_eq_true] at h
      exact noMatch_mem h.1.2 hs
    · rcases selGo_cons h with ⟨seen', h'⟩ | h'
      · exact selGo_arms h' y as hu x arms hs
      · exact noMatch_mem h' (sub_stmtsOf (mem_stmtsOf hu) hs)

/-! ## Cursors -/

theorem getD_mem_or {l : List Stmt} {t : ℕ} : l.getD t default ∈ l ∨ l.getD t default = default := by
  rcases Nat.lt_or_ge t l.length with h | h
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ h

theorem subBlock_default (c : ℕ) : subBlock (default : Stmt) c = [] := rfl

theorem blockAt_sub {body : List Stmt} : ∀ {ks : List (ℕ × ℕ)}, ks ≠ [] →
    ∀ w ∈ blockAt body ks, ∃ u ∈ body, w ∈ stmtsSub u
  | [], h, _, _ => absurd rfl h
  | (t, c) :: r, _, w, hw => by
    simp only [blockAt] at hw
    have hw' := subBlock_sub hw
    rcases getD_mem_or (l := blockAt body r) (t := t) with hv | hv
    · cases r with
      | nil => exact ⟨_, hv, hw'⟩
      | cons e r' =>
        obtain ⟨u, hu, hvu⟩ := blockAt_sub (ks := e :: r') (List.cons_ne_nil _ _) _ hv
        exact ⟨u, hu, sub_stmtsSub hvu hw'⟩
    · rw [hv, subBlock_default] at hw
      exact absurd hw List.not_mem_nil

/-- **Where a cursor's statement is**: at the body's top level, at the top level of a sub-block of a top-level
statement `u` (the body `P ++ u :: R`, the cursor's statements left those of the block then `R`), or deeper. -/
theorem zok_cases {body : List Stmt} {zs : Zip} (hz : ZOk body zs) {s : Stmt} {ss : List Stmt}
    (hc : zs.cur = s :: ss) :
    s ∈ body ∨
      (∃ t c, ∃ u ∈ body, ∃ Q, subBlock u c = Q ++ s :: ss ∧ body = body.take t ++ u :: body.drop (t + 1) ∧
        zs.pos = s :: ss ++ body.drop (t + 1)) ∨
      ∃ u ∈ body, ∃ w ∈ stmtsSub u, s ∈ stmtsSub w := by
  obtain ⟨hup, hcur⟩ := zOk_iff.mp hz
  rw [hc] at hcur
  have hs : s ∈ (blockAt body (upKeys zs.up)).drop zs.k := by rw [← hcur]; exact List.mem_cons_self
  generalize upKeys zs.up = ks at hup hcur hs
  rcases ks with _ | ⟨⟨t, c⟩, r⟩
  · exact Or.inl (List.mem_of_mem_drop hs)
  rcases r with _ | ⟨⟨t0, c0⟩, r⟩
  · right; left
    simp only [blockAt] at hcur hs
    rcases Nat.lt_or_ge t body.length with ht | ht
    · rw [List.getD_eq_getElem _ _ ht] at hcur
      refine ⟨t, c, body[t], List.getElem_mem ht, (subBlock body[t] c).take zs.k, ?_, ?_, ?_⟩
      · rw [hcur, List.take_append_drop]
      · conv_lhs => rw [← List.take_append_drop t body]
        rw [List.drop_eq_getElem_cons ht]
      · rw [Bridge.Zip.pos, hup, hc]
        simp [zUp, blockAt]
    · rw [List.getD_eq_default _ _ ht, subBlock_default] at hs
      exact absurd (List.mem_of_mem_drop hs) List.not_mem_nil
  · right; right
    have hs1 : s ∈ subBlock ((blockAt body ((t0, c0) :: r)).getD t default) c := List.mem_of_mem_drop hs
    have hs' := subBlock_sub hs1
    rcases getD_mem_or (l := blockAt body ((t0, c0) :: r)) (t := t) with hv | hv
    · obtain ⟨u, hu, hvu⟩ := blockAt_sub (List.cons_ne_nil _ _) _ hv
      exact ⟨u, hu, _, hvu, hs'⟩
    · rw [hv, subBlock_default] at hs1
      exact absurd hs1 List.not_mem_nil

/-! ## A reached `match` in a branch -/

theorem isAtom_pos {b : Atom} {l : List Stmt} (h : Stmt.atom b ∈ stmtsOf l) : 0 < (stmtsOf l).countP (isAtom b) :=
  List.countP_pos_iff.mpr ⟨_, h, by simp [isAtom]⟩

/-- An atom `selBr` saw before a branch's `match` is on the path through the branch. -/
theorem seen_on_path {σ : Val} {P Q M : List Stmt} {X Y Z : List Ev} {c0 : V} {a : Atom}
    (hP : walk σ P = .fall X) (hY : walk σ (Q ++ M) = .fall Y) (ha : a ∈ seenF (seenF [] P) Q) :
    Ev.atom a ∈ X ++ ([Ev.inK c0] ++ Y ++ Z) := by
  rw [Bridge.walk_append σ] at hY
  obtain ⟨YQ, YM, hQ, -, rfl⟩ := seq_eq_fall hY
  rcases mem_seenF ha with ha | ha
  · rcases mem_seenF ha with ha | ha
    · exact absurd ha List.not_mem_nil
    · exact List.mem_append_left _ (walk_fall_atom hP ha)
  · simp [walk_fall_atom hQ ha]

/-- **A `match` the path reaches in a branch**: at the top level of branch `c` of the top-level `ite` of
`B = P ++ ite c₀ z n :: R`, the path's events ending with the walk from the `match`, its selector is at its cell
and used by an atom of the path. -/
theorem sel_nested {σ : Val} {j : ℕ} {ps : List V} {B P R z n Q S : List Stmt} {c0 x : V}
    {arms : List (List Stmt)} {E pre es1 : List Ev} {vs : List V} {c : ℕ}
    (hsel : selGo j ps B [] B = true) (htop : B.all topOk = true) (hw : walk σ B = .ret E vs)
    (hB : B = P ++ .ite c0 z n :: R) (hbr : subBlock (.ite c0 z n) c = Q ++ .match_ x arms :: S)
    (hE : E = pre ++ es1) (hw1 : walk σ (.match_ x arms :: S ++ R) = .ret es1 vs) :
    cellB j x = true ∧ ∃ a, Ev.atom a ∈ E ∧ x ∈ Memory.atomUses a := by
  -- the branch, `z` or `n`
  have hbz : subBlock (.ite c0 z n) c = (if Nat.beq c 0 = true then z else n) := by
    cases h : Nat.beq c 0 <;> simp [subBlock, h]
  have hmB : Stmt.match_ x arms ∈ subBlock (.ite c0 z n) c := by rw [hbr]; simp
  have hm : ∃ x' arms', Stmt.match_ x' arms' ∈ stmtsOf z ++ stmtsOf n := ⟨x, arms, by
    rw [hbz] at hmB
    split at hmB
    · exact List.mem_append_left _ (mem_stmtsOf hmB)
    · exact List.mem_append_right _ (mem_stmtsOf hmB)⟩
  have hs : selGo j ps B [] (P ++ .ite c0 z n :: R) = true := by rw [← hB]; exact hsel
  obtain ⟨hnr, hz, hn⟩ := selGo_split hm hs
  have hsb : selBr j B (seenF [] P) (subBlock (.ite c0 z n) c) = true := by
    rw [hbz]; split <;> assumption
  rw [hbr] at hsb
  obtain ⟨hcell, ⟨a, ha, hu⟩, honce⟩ := selBr_at hsb
  obtain ⟨b, hbS, hb1⟩ := onceAfter_spec honce
  refine ⟨hcell, ?_⟩
  -- the walk through `P`, the `ite` and `R`
  have htB := htop
  rw [hB, List.all_append, Bool.and_eq_true, List.all_cons, Bool.and_eq_true] at htB
  obtain ⟨htP, htI, -⟩ := htB
  have hnI : Core.Stmt.noRet (.ite c0 z n) = true := by
    simp only [topOk, Bool.and_eq_true] at htI
    exact htI.1
  rw [hB, Bridge.walk_append σ] at hw
  rcases seq_eq_ret hw with ⟨X, E2, hP, hI, rfl⟩ | hP
  swap
  · exact absurd hP (walk_noRetTop P hnr htP E vs)
  rw [walk] at hI
  rcases seq_eq_ret hI with ⟨Y1, Z, hY1, hR, rfl⟩ | hI1
  swap
  · exact absurd hI1 (walk1_noRetP _ hnI E2 vs)
  rw [walk1] at hY1
  obtain ⟨Y, hY, rfl⟩ := pre_eq_fall hY1
  -- the walk from the `match`
  have hnS : Core.Stmt.noRetList (.match_ x arms :: S) = true := by
    simp only [Core.Stmt.noRet, Bool.and_eq_true] at hnI
    have h' : Core.Stmt.noRetList (subBlock (.ite c0 z n) c) = true := by
      rw [hbz]; split
      exacts [hnI.1, hnI.2]
    rw [hbr, noRetList_append, Bool.and_eq_true] at h'
    exact h'.2
  rw [Bridge.walk_append σ] at hw1
  rcases seq_eq_ret hw1 with ⟨W, Z', hW, hR', rfl⟩ | hW
  swap
  · exact absurd hW (walk_noRetP _ hnS es1 vs)
  rw [hR] at hR'
  obtain ⟨hZ, -⟩ := Out.ret.inj hR'
  rw [← hZ] at hE
  -- the path's events before the `match`'s
  have hEq : pre ++ W = X ++ ([Ev.inK c0] ++ Y) := by
    have h2 : (pre ++ W) ++ Z = (X ++ ([Ev.inK c0] ++ Y)) ++ Z := by
      simpa only [List.append_assoc] using hE.symm
    exact List.append_cancel_right h2
  -- the atom once in `B`, walked from the `match`
  have hbW : Ev.atom b ∈ W := by
    rw [walk] at hW
    obtain ⟨W0, W1, -, hS, rfl⟩ := seq_eq_fall hW
    exact List.mem_append_right _ (walk_fall_atom hS hbS)
  have hbXY : Ev.atom b ∈ X ∨ Ev.atom b ∈ Y := by
    have : Ev.atom b ∈ X ++ ([Ev.inK c0] ++ Y) := hEq ▸ List.mem_append_right _ hbW
    simpa using this
  have hcount : (stmtsOf B).countP (isAtom b) = (stmtsOf P).countP (isAtom b) +
      ((stmtsOf z).countP (isAtom b) + (stmtsOf n).countP (isAtom b)) + (stmtsOf R).countP (isAtom b) := by
    rw [hB, stmtsOf_append, List.countP_append, stmtsOf, stmtsSub, List.countP_cons, List.countP_append,
      List.countP_append]
    simp [isAtom]
    omega
  simp only [onceB, Nat.beq_eq] at hb1
  have hbBr : 0 < (stmtsOf (subBlock (.ite c0 z n) c)).countP (isAtom b) :=
    isAtom_pos (mem_stmtsOf (by rw [hbr]; simp [hbS]))
  have hbX : Ev.atom b ∈ X → 0 < (stmtsOf P).countP (isAtom b) := fun h ↦
    isAtom_pos (walk_atomS (σ := σ) P (by rw [hP]; exact h))
  -- the path takes the branch with the `match` (else `b` would be twice in `B`)
  by_cases h0 : σ c0 = 0
  · rw [ite_eq_left h0] at hY
    have hbz' : Nat.beq c 0 = true := by
      by_contra hc
      rw [hbz, ite_eq_right hc] at hbBr
      rcases hbXY with h | h
      · have := hbX h; omega
      · have := isAtom_pos (walk_atomS (σ := σ) z (by rw [hY]; exact h)); omega
    rw [hbz, ite_eq_left hbz'] at hbr
    subst hbr
    exact ⟨a, seen_on_path hP hY ha, hu⟩
  · rw [ite_eq_right h0] at hY
    have hbz' : Nat.beq c 0 = false := by
      by_contra hc
      rw [hbz, ite_eq_left (by simpa using hc)] at hbBr
      rcases hbXY with h | h
      · have := hbX h; omega
      · have := isAtom_pos (walk_atomS (σ := σ) n (by rw [hY]; exact h)); omega
    rw [hbz, ite_eq_right (by simp [hbz'])] at hbr
    subst hbr
    exact ⟨a, seen_on_path hP hY ha, hu⟩

end

end LeanVM.Guest.CoreMode
