/-
  LeanVM.Guest.Backend.Sound.Obl.Walk

  The obligations of `opening_queries`' specializations and loop helpers, whose calls of
  `walk_path` read windows the walk relations bound, from B1's facts on their templates
  (`B1.Opening.QueriesWalk`).
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.GuestU
public import LeanVM.Guest.B1.Opening.QueriesWalk

/-!
# The windowed Merkle walk

`walk_path__L{pd}_L{cd}` dispatches on the words at its argument `2`, `wins`, which the table
bounds (`Sig.mem`, if read, below `g^64`). Its callers load `wins` from a window pointer table:

* a loop helper of shape `s` (`oqLoop0T`, `oqLoop1T` at level `0`) on `[x, N, positions, qptrs,
  …]` runs the walk from `x` to `N` on `qptrs` (`XSpec.loop`, B1's `WinWalk`, `WinWalk2`, with
  `x ≠ N`): the pointers it loads name windows (`oqLoop0T_wins`, `oqLoop1T_wins1`,
  `oqLoop1T_wins2`), facts at the statements after the loads, and its tail call at `x·g` keeps
  the walk (`oqLoop0T_tail`, `oqLoop1T_tail`) and `x·g ≠ N` (its condition `x·g + N ≠ 0`);
* a specialization (`oqMainT`) on `[…, qptrs, N]` has `OqMainWins` (`XSpec.main`): an odd count's
  first query's pointer names windows (`oqMainT_wins`), and its loop call at `x = 1` gets the walk
  (`oqMainT_loop`) and `1 ≠ N` (its condition `1 + N ≠ 0`).

`loopOk`, `mainOk`: the decided checks, the body the template, the table's `ext` entries, the
analysis with those facts and the loop call as an `ext` site; `loop_obl`, `main_obl`: `OblFn` from
them.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Windows -/

/-- A path window of a walk of shape `(pd + cd, cd)` is at most `6` bits wide. -/
theorem qwWin_path {pd cd i : ℕ} (hi : i < (pd + 5) / 6) :
    i < qwN (pd + cd) cd ∧ (qwWin (pd + cd) cd i).2 ≤ 6 := by
  have e : pd + cd - cd = pd := by omega
  simp only [qwN, qwNp, qwWin, e]
  refine ⟨by omega, ?_⟩
  split_ifs <;> dsimp only <;> omega

/-- **A path window, if read, is below `g^64`.** -/
theorem winsAt_mem {rd : Reader} {pd cd : ℕ} {w : E} (h : WinsAt rd (pd + cd) cd w) {i : ℕ}
    (hi : i < (pd + 5) / 6) : MemB rd w i 64 := by
  intro v hv
  obtain ⟨h1, h2⟩ := qwWin_path (cd := cd) hi
  obtain ⟨e, he, rfl⟩ := h i h1 v hv
  exact ⟨e, lt_of_lt_of_le he (le_trans (Nat.pow_le_pow_right (by norm_num) h2) (by norm_num)), rfl⟩

/-- The facts that the path windows at `w`, if read, are below `g^64`, at statement `i`. -/
def winFacts (s : Oq) (i w : ℕ) : List (ℕ × Hyp) :=
  (List.range (oqNpw s)).map fun c => (i, .mem (.n w) c 64)

theorem mem_winFacts {s : Oq} {i w : ℕ} {p : ℕ × Hyp} (h : p ∈ winFacts s i w) :
    ∃ c < (s.pd + 5) / 6, p = (i, .mem (.n w) c 64) := by
  simp only [winFacts, List.mem_map, List.mem_range] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, rfl⟩

/-- A walk's shape from a template's. -/
def wOf (s : Oq) (odd : ℕ) : WalkSpec := ⟨s.pd + s.cd, s.cd, odd, s.base⟩

theorem oqQueryT_length_walk' (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool)
    (pr : ℕ) (walk : String) : (oqQueryT s x bp cap flags coefs hs b emit pr walk).length =
      (oqQueryT s x bp cap flags coefs hs b emit pr "").length := by
  simp [oqQueryT]

theorem oqLoop0A_length' (s : Oq) (walk : String) :
    (oqLoop0A s walk).length = (oqLoop0A s "").length := by
  simp only [oqLoop0A, List.length_append, oqQueryT_length_walk']

theorem oqLoop1A_length' (s : Oq) (odd : ℕ) (walk : String) :
    (oqLoop1A s odd walk).length = (oqLoop1A s odd "").length := by
  simp only [oqLoop1A, List.length_append, oqQueryT_length_walk']

theorem oqMainA_length' (s : Oq) (odd : ℕ) (walk : String) :
    (oqMainA s odd walk).length = (oqMainA s odd "").length := by
  unfold oqMainA
  split <;> simp only [List.length_append, oqQueryT_length_walk']

/-! ## The loop helpers -/

/-- A loop helper's facts: the window pointers it loads, at the statement after each load. -/
def loopFacts (s : Oq) : List (ℕ × Hyp) :=
  if s.base = 1 then
    winFacts s 6 15 ++
      winFacts s ((oqQueryT s (.n 14) (.n 15) (.n 4) (.n 5) (.n 6) (.n 7) 16 true 0 "").length + 8)
        (oqE1 s + 1)
  else winFacts s 4 13

/-- A loop helper's tail call: its `ext` site. -/
def loopSite (s : Oq) (odd : ℕ) : ℕ :=
  if s.base = 1 then (oqLoop1A s odd "").length else (oqLoop0A s "").length

/-- A loop helper's body. -/
def loopT (s : Oq) (odd : ℕ) (name : String) : List Stmt :=
  if s.base = 1 then oqLoop1T s odd (oqWalkOf s) name else oqLoop0T s (oqWalkOf s) name

/-- **A loop helper's decided check**: function `j` is named `name`, has ten parameters, its body
is the template, its table entry the walk, and the analysis accepts it with its facts and its
tail call as a site. -/
def loopOkF (g : Fn) (name : String) (sh : OqShape) (odd : ℕ) : Bool :=
  decide (g.name = name) && decide (g.params = (List.range 10).map V.n) &&
    decide (xSpecOf name = some (.loop (wOf sh.oq odd))) && (guestTab.sig name).ext &&
    stmtsEqb g.body (loopT sh.oq odd name) &&
    chkFnX guestTab (loopFacts sh.oq) [loopSite sh.oq odd] g

/-- `loopOkF` of function `j`. -/
noncomputable def loopOk (j : ℕ) (name : String) (sh : OqShape) (odd : ℕ) : Bool :=
  loopOkF (coreProgram.getD j default) name sh odd

theorem guard_ne {C : CallRel} {rd : Reader} {σ : Val} {A : List Stmt} {g : ℕ}
    (hb : BlockOkC C rd σ A) (hsub : ∀ a, Stmt.atom a ∈ oqGuardA g → Stmt.atom a ∈ A)
    (hc : σ (.n (g + 2)) ≠ 0) : σ (.n (g + 4)) ≠ σ (.n 1) := by
  have c0 := hb.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.const (.n g) (word 2 0)) ∈ _)
  have c1 := hb.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.mul (.n (g + 1)) (.n 0) (.n g)) ∈ _)
  have c2 := hb.atom
    (hsub _ (by simp [oqGuardA]) : Stmt.atom (.add (.n (g + 2)) (.n (g + 1)) (.n 1)) ∈ _)
  have c3 := hb.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.const (.n (g + 3)) (word 2 0)) ∈ _)
  have c4 := hb.atom
    (hsub _ (by simp [oqGuardA]) : Stmt.atom (.mul (.n (g + 4)) (.n 0) (.n (g + 3))) ∈ _)
  simp only [Atom.Holds] at c0 c1 c2 c3 c4
  intro he
  apply hc
  rw [c2, c1, c0, ← c3, ← c4, he, e_add_self]

theorem loop_tail_args {σ : Val} (g : ℕ) :
    ((V.n (g + 4) :: (List.range' 1 9).map V.n).map σ).getD 3 0 = σ (.n 3) ∧
    ((V.n (g + 4) :: (List.range' 1 9).map V.n).map σ).getD 0 0 = σ (.n (g + 4)) ∧
    ((V.n (g + 4) :: (List.range' 1 9).map V.n).map σ).getD 1 0 = σ (.n 1) := by
  simp [List.range'_succ]

theorem oqNextT_eq (g : ℕ) (name : String) : oqNextT g name =
    [.callIf (.n (g + 2)) name (V.n (g + 4) :: (List.range' 1 9).map V.n), .ret []] := by
  simp [oqNextT, List.range'_succ]

/-- **A loop helper's obligations**, from its decided check. -/
theorem loop_obl {j : ℕ} {name : String} {sh : OqShape} {odd : ℕ}
    (hok : loopOk j name sh odd = true) : OblFn (coreProgram.getD j default) := by
  simp only [loopOk, loopOkF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hn, hp⟩, hx⟩, he⟩, hb⟩, hc⟩ := hok
  have hb := stmtsEqb_sound hb
  set s := sh.oq
  have own : ∀ {rd : Reader} {σ : Val}, guestU rd (coreProgram.getD j default).name
      ((coreProgram.getD j default).params.map σ) →
      LoopWalk rd (wOf s odd) (σ (.n 3)) (σ (.n 0)) (σ (.n 1)) ∧ σ (.n 0) ≠ σ (.n 1) := by
    intro rd σ h
    have := own_spec h (by rw [hn]; exact he) (by rw [hn]; exact hx)
    rw [hp] at this
    simpa only [XSpec.Holds, getD_range_map (by norm_num : 3 < 10),
      getD_range_map (by norm_num : 0 < 10), getD_range_map (by norm_num : 1 < 10)] using this
  apply oblFn_of_chkX hc
  · intro κ L _ _ C σ _ hpre p hp hl
    obtain ⟨hw, hne⟩ := own hpre
    rw [hb] at hl
    unfold loopFacts at hp
    unfold loopT at hl
    unfold LoopWalk wOf at hw
    by_cases hbase : s.base = 1
    · simp only [hbase, ↓reduceIte] at hp hl hw
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨c, hc, rfl⟩ := mem_winFacts hp
        exact winsAt_mem (oqLoop1T_wins1 le_rfl hl hw hne) hc
      · obtain ⟨c, hc, rfl⟩ := mem_winFacts hp
        rw [← oqQueryT_length_walk' (walk := oqWalkOf s)] at hl
        exact winsAt_mem (oqLoop1T_wins2 le_rfl hl hw hne) hc
    · simp only [hbase, ↓reduceIte] at hp hl hw
      obtain ⟨c, hc, rfl⟩ := mem_winFacts hp
      exact winsAt_mem (oqLoop0T_wins le_rfl hl hw hne) hc
  · intro κ L _ _ C σ _ hpre i hi st ss hd hl
    simp only [List.mem_singleton] at hi
    subst hi
    obtain ⟨hw, hne⟩ := own hpre
    rw [hb] at hd hl
    unfold loopSite loopT at hd hl
    unfold LoopWalk wOf at hw
    by_cases hbase : s.base = 1
    · simp only [hbase, ↓reduceIte] at hd hl hw
      rw [oqLoop1T, ← oqLoop1A_length' s odd (oqWalkOf s), List.drop_left, oqNextT_eq] at hd
      obtain ⟨rfl, -⟩ := List.cons.inj hd
      intro hc0 _ sp hsp
      rw [hx] at hsp
      obtain rfl := (Option.some.inj hsp).symm
      simp only [XSpec.Holds, LoopWalk, wOf, hbase, ↓reduceIte]
      rw [← oqLoop1A_length' s odd (oqWalkOf s)] at hl
      obtain ⟨e3, e0, e1⟩ := loop_tail_args (σ := σ) (oqG1 s)
      rw [e3, e0, e1]
      have hbk : BlockOkC C L.read σ (oqLoop1A s odd (oqWalkOf s)) :=
        blockOkC_of_take (List.prefix_append _ _) (oqLoop1A_flatC s odd _) le_rfl hl
      exact ⟨oqLoop1T_tail le_rfl hl hw hne,
        guard_ne hbk (fun a h => by unfold oqLoop1A; exact List.mem_append_right _ h) hc0⟩
    · simp only [hbase, ↓reduceIte] at hd hl hw
      rw [oqLoop0T, ← oqLoop0A_length' s (oqWalkOf s), List.drop_left, oqNextT_eq] at hd
      obtain ⟨rfl, -⟩ := List.cons.inj hd
      intro hc0 _ sp hsp
      rw [hx] at hsp
      obtain rfl := (Option.some.inj hsp).symm
      simp only [XSpec.Holds, LoopWalk, wOf, hbase, ↓reduceIte]
      rw [← oqLoop0A_length' s (oqWalkOf s)] at hl
      obtain ⟨e3, e0, e1⟩ := loop_tail_args (σ := σ) (oqG0 s)
      rw [e3, e0, e1]
      have hbk : BlockOkC C L.read σ (oqLoop0A s (oqWalkOf s)) :=
        blockOkC_of_take (List.prefix_append _ _) (oqLoop0A_flatC s _) le_rfl hl
      exact ⟨oqLoop0T_tail le_rfl hl hw hne,
        guard_ne hbk (fun a h => by unfold oqLoop0A; exact List.mem_append_right _ h) hc0⟩

/-! ## The specializations -/

/-- A specialization's facts: an odd count's first query's window pointer, after its load. -/
def mainFacts (s : Oq) (odd : ℕ) : List (ℕ × Hyp) := if odd = 1 then winFacts s 5 12 else []

/-- **A specialization's decided check**: function `j` is named `name`, has eight parameters, its
body is the template calling the loop helper `loop`, its and its loop's table entries the walk,
and the analysis accepts it with its facts and its loop call as a site. -/
def mainOkF (g : Fn) (name : String) (sh : OqShape) (loop : String) : Bool :=
  decide (g.name = name) && decide (g.params = (List.range 8).map V.n) &&
    decide (xSpecOf name = some (.main (wOf sh.oq sh.odd))) && (guestTab.sig name).ext &&
    decide (xSpecOf loop = some (.loop (wOf sh.oq sh.odd))) &&
    stmtsEqb g.body (oqMainT sh.oq sh.odd (oqWalkOf sh.oq) loop) &&
    chkFnX guestTab (mainFacts sh.oq sh.odd) [(oqMainA sh.oq sh.odd "").length] g

/-- `mainOkF` of function `j`. -/
noncomputable def mainOk (j : ℕ) (name : String) (sh : OqShape) (loop : String) : Bool :=
  mainOkF (coreProgram.getD j default) name sh loop

theorem main_call_args {σ : Val} (k : ℕ) :
    (([V.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2] : List V).map σ).getD 3 0 =
      σ (.n 6) ∧
    (([V.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2] : List V).map σ).getD 0 0 =
      σ (.n (k + 2)) ∧
    (([V.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2] : List V).map σ).getD 1 0 =
      σ (.n 7) := by
  simp

/-- **A specialization's obligations**, from its decided check. -/
theorem main_obl {j : ℕ} {name : String} {sh : OqShape} {loop : String}
    (hok : mainOk j name sh loop = true) : OblFn (coreProgram.getD j default) := by
  simp only [mainOk, mainOkF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hn, hp⟩, hx⟩, he⟩, hxl⟩, hb⟩, hc⟩ := hok
  have hb := stmtsEqb_sound hb
  set s := sh.oq
  set odd := sh.odd
  have own : ∀ {rd : Reader} {σ : Val}, guestU rd (coreProgram.getD j default).name
      ((coreProgram.getD j default).params.map σ) →
      OqMainWins rd (s.pd + s.cd) s.cd odd s.base (σ (.n 6)) (σ (.n 7)) := by
    intro rd σ h
    have := own_spec h (by rw [hn]; exact he) (by rw [hn]; exact hx)
    rw [hp] at this
    simpa only [XSpec.Holds, wOf, getD_range_map (by norm_num : 6 < 8),
      getD_range_map (by norm_num : 7 < 8)] using this
  apply oblFn_of_chkX hc
  · intro κ L _ _ C σ _ hpre p hp hl
    rw [hb] at hl
    unfold mainFacts at hp
    by_cases ho : odd = 1
    · simp only [ho, ↓reduceIte] at hp
      obtain ⟨c, hc, rfl⟩ := mem_winFacts hp
      exact winsAt_mem (oqMainT_wins le_rfl ho hl (own hpre)) hc
    · simp only [ho, ↓reduceIte] at hp
      exact absurd hp List.not_mem_nil
  · intro κ L _ _ C σ _ hpre i hi st ss hd hl
    simp only [List.mem_singleton] at hi
    subst hi
    rw [hb] at hd hl
    rw [oqMainT, ← oqMainA_length' s odd (oqWalkOf s), List.append_assoc, List.drop_left] at hd
    obtain ⟨rfl, -⟩ := List.cons.inj hd
    intro hc0 _ sp hsp
    rw [hxl] at hsp
    obtain rfl := (Option.some.inj hsp).symm
    rw [← oqMainA_length' s odd (oqWalkOf s)] at hl
    obtain ⟨e3, e0, e1⟩ := main_call_args (σ := σ) (oqMK s odd)
    simp only [XSpec.Holds, LoopWalk, wOf]
    rw [e3, e0, e1]
    refine ⟨oqMainT_loop le_rfl hl (own hpre), ?_⟩
    have hbk := blockOkC_of_take ((List.prefix_append _ _).trans (List.prefix_append _ _))
      (oqMainA_flatC s odd _) le_rfl hl
    have k0 := hbk.atom (by simp [oqMainA] : Stmt.atom (.const (.n (oqMK s odd)) (word 1 0)) ∈ _)
    have k1 := hbk.atom
      (by simp [oqMainA] : Stmt.atom (.add (.n (oqMK s odd + 1)) (.n (oqMK s odd)) (.n 7)) ∈ _)
    have k2 := hbk.atom (by simp [oqMainA] : Stmt.atom (.const (.n (oqMK s odd + 2)) (word 1 0)) ∈ _)
    simp only [Atom.Holds] at k0 k1 k2
    intro he
    apply hc0
    rw [k1, k0, ← k2, he, e_add_self]

end
end LeanVM.Guest.Backend.Obl
