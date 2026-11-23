/-
  LeanVM.Guest.B1.Opening.QueriesWalk

  The walk obligations of `opening_queries`: every window a query dispatches on is a small power
  of `g`, from the window pointers' runs, carried along the loop (the definitions in `WalkDefs`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.B1.Opening.WalkDefs

/-!
# The windows a walk dispatches on (`opening_queries`, `walk_path` inline)

A query of `opening_queries` dispatches `match(log(w))` on each path window `w = wins[g^i]`,
`wins` the window pointer loaded from `query_win_ptrs` at the iteration's index
(`query_win_ptrs[xi]` deeper, `(query_win_ptrs·odd_g·xi²)[g^0]`, `[g^1]` at level 0, the odd
first query's `query_win_ptrs[g^0]` under the branch on `odd_g`). A window's bound comes from
`decode_query_windows`' range checks, in another function, through the pointer table: the
checker of the certificates takes it as an obligation on the specialization's and the loop's
arguments, carried by the loop (the definitions in `WalkDefs`).

* `WinsAt rd d cd w`: each of the `qwN d cd` windows at `w`, if read, is `g^e`, `e` below the
  window's `2^width` (`qwWin`), what `decode_query_windows` writes; `winsP_of_winsAt`: its path
  windows are `WinsP rd (d - cd) w`, what a query reads.
* `WinWalk`, `WinWalk2`, `OqMainWins`: `level_queries`' obligation (`lqTag`), from `QueryWinsOk`
  (`oqMainWins_of_queryWinsOk`); `winWalkP_of_mainWins`, `oqStartP_of_mainWins`: the
  specialization's (`oqTag`).
* `WinWalkP rd pd t x N` (deeper) / `WinWalk2P rd pd t x N` (level 0): the pointers of every
  iteration still to run name path windows: at `x·g^c` for each `c` with `x·g^c' ≠ N`, `c' ≤ c`
  (the loop runs `x, x·g, …` until `N`); `winWalkP_succ`, `winWalk2P_succ`: the tail call's
  argument `x·g` keeps them when `x ≠ N`; `winsP_of_walkP`, `winsP_of_walk2P`: the iteration at
  `x ≠ N` reads such pointers.
* The bodies: `oqLoop0T_wins`, `oqLoop1T_wins1`, `oqLoop1T_wins2` (the queries' window pointers,
  over any prefix of the body holding their loads), `oqLoop0T_tail`, `oqLoop1T_tail` (the tail
  call's argument, over the statements before the call), `oqMainT_loop1` (a level-0
  specialization's loop call's window pointers, over the start).

The walk is unbounded in `c`: a bound `c < B` on its own does not survive the tail call
(`x·g` needs `c + 1 < B`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## Windows -/

/-- The window pointers point to positions' windows: every pointer `qptrs[k]`, `k < Q`, names a
frame run holding the `qwN depth cd` windows `g^(qwVal …)` of a position below `2^depth` (the
windows part of `QueryPosOk`). -/
def QueryWinsOk (rd : Reader) (qptrs : E) (Q depth cd : ℕ) : Prop :=
  ∀ k < Q, ∀ bp, LoadHolds rd qptrs k bp →
    ∃ q < 2 ^ depth, FrameRun rd bp (qwN depth cd) fun i ↦ gen ^ qwVal depth cd q i

/-- **The windows of a position** (a run `decode_query_windows` writes) are such windows. -/
theorem winsAt_of_run {d cd q : ℕ} {w : E}
    (h : FrameRun rd w (qwN d cd) fun i ↦ gen ^ qwVal d cd q i) : WinsAt rd d cd w := by
  intro i hi v hv
  refine ⟨qwVal d cd q i, Nat.mod_lt _ (by positivity), ?_⟩
  exact (h.2 i hi v hv.2).trans (gen_pow_eq_ofK _)

/-- The windows at `t[k]`, `k < Q`, from `QueryWinsOk`. -/
theorem winsAt_of_queryWinsOk {t : E} {Q d cd : ℕ} (h : QueryWinsOk rd t Q d cd) {k : ℕ} (hk : k < Q)
    {w : E} (hw : LoadHolds rd t k w) : WinsAt rd d cd w := by
  obtain ⟨q, -, hq⟩ := h k hk w hw
  exact winsAt_of_run hq

/-! ## The walk -/

private theorem mul_pow_succ (x : E) (c : ℕ) : x * gen ^ (c + 1) = x * gen * gen ^ c := by
  rw [pow_succ', mul_assoc]

private theorem pow_succ_shift {x N : E} (hne : x ≠ N) {c : ℕ}
    (h : ∀ c' ≤ c, x * gen * gen ^ c' ≠ N) : ∀ c' ≤ c + 1, x * gen ^ c' ≠ N := by
  intro c' hc'
  rcases c' with _ | c'
  · rwa [pow_zero, mul_one]
  · rw [mul_pow_succ]
    exact h c' (by omega)

/-- The steps before `N = g^n` from `1`: fewer than `n`. -/
private theorem lt_of_ne_pow {n c : ℕ} (h : ∀ c' ≤ c, 1 * gen ^ c' ≠ gen ^ n) : c < n := by
  by_contra hc
  exact h n (by omega) (one_mul _)

/-- **The walk from `1` to `g^n`** (deeper) from the window pointers `t[k]`, `k < n`. -/
theorem winWalk_of_queryWinsOk {t : E} {n d cd : ℕ} (h : QueryWinsOk rd t n d cd) :
    WinWalk rd d cd t 1 (gen ^ n) := by
  intro c hc w hw
  rw [one_mul, loadHolds_mul_gen_pow, Nat.add_zero] at hw
  exact winsAt_of_queryWinsOk h (lt_of_ne_pow hc) hw

/-- **The walk from `1` to `g^n`** (level 0) from the window pointers `t[k]`, `k < odd + 2n`. -/
theorem winWalk2_of_queryWinsOk {t : E} {n d cd odd : ℕ} (h : QueryWinsOk rd t (odd + 2 * n) d cd) :
    WinWalk2 rd d cd odd t 1 (gen ^ n) := by
  intro c hc o ho1 ho2 w hw
  rw [one_mul, mul_assoc, ← pow_add, loadHolds_mul_gen_pow] at hw
  have := lt_of_ne_pow hc
  exact winsAt_of_queryWinsOk h (by omega) hw

/-- **`opening_queries`' obligation from `QueryWinsOk`** at `n_iters_g = g^n`. -/
theorem oqMainWins_of_queryWinsOk {t : E} {n d cd odd base : ℕ} (hodd : odd = 1 → base = 1)
    (h : QueryWinsOk rd t (oqCount odd base n) d cd) : OqMainWins rd d cd odd base t (gen ^ n) := by
  refine ⟨fun ho w hw ↦ ?_, ?_⟩
  · have hb := hodd ho
    simp only [oqCount, hb, ↓reduceIte] at h
    exact winsAt_of_queryWinsOk h (by omega) hw
  · unfold oqCount at h
    split
    · next hb => simp only [hb, ↓reduceIte] at h; exact winWalk2_of_queryWinsOk h
    · next hb => simp only [hb, ↓reduceIte] at h; exact winWalk_of_queryWinsOk h

/-! ## The path windows (`opening_queries`) -/

/-- **The path windows of a position's windows.** -/
theorem winsP_of_winsAt {d cd : ℕ} {w : E} (h : WinsAt rd d cd w) : WinsP rd (d - cd) w := by
  intro i hi v hv
  have hn : qwNp d cd = pwN (d - cd) := rfl
  have hi' : i < qwN d cd := by unfold qwN; omega
  obtain ⟨e, he, rfl⟩ := h i hi' v hv
  refine ⟨e, ?_, rfl⟩
  have hw : (qwWin d cd i).2 = pwW (d - cd) i := by
    unfold qwWin pwW
    rw [hn, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i = pwN (d - cd) by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ i = pwN (d - cd) + 1 by omega))]
    split <;> rfl
  rwa [← hw]

/-- **The tail call keeps the walk** (deeper): `x ≠ N` steps it to `x·g`. -/
theorem winWalkP_succ {pd : ℕ} {t x N : E} (h : WinWalkP rd pd t x N) (hne : x ≠ N) :
    WinWalkP rd pd t (x * gen) N := by
  intro c hc w hw
  refine h (c + 1) (pow_succ_shift hne hc) w ?_
  rw [mul_pow_succ]
  exact hw

/-- **The tail call keeps the walk** (level 0). -/
theorem winWalk2P_succ {pd : ℕ} {t x N : E} (h : WinWalk2P rd pd t x N) (hne : x ≠ N) :
    WinWalk2P rd pd t (x * gen) N := by
  intro c hc o ho w hw
  refine h (c + 1) (pow_succ_shift hne hc) o ho w ?_
  rw [mul_pow_succ]
  exact hw

private theorem ne_zero_steps {x N : E} (hne : x ≠ N) : ∀ c' ≤ 0, x * gen ^ c' ≠ N := by
  intro c' hc'
  obtain rfl : c' = 0 := by omega
  rwa [pow_zero, mul_one]

/-- **The iteration at `x ≠ N` reads path windows** (deeper): its pointer `t[x]`. -/
theorem winsP_of_walkP {pd : ℕ} {t x N : E} (h : WinWalkP rd pd t x N) (hne : x ≠ N) {w : E}
    (hw : LoadHolds rd (t * x) 0 w) : WinsP rd pd w :=
  h 0 (ne_zero_steps hne) w (by rwa [pow_zero, mul_one])

/-- **The iteration at `x ≠ N` reads path windows** (level 0): its pointers `(t·x²)[g^o]`. -/
theorem winsP_of_walk2P {pd : ℕ} {t x N : E} (h : WinWalk2P rd pd t x N) (hne : x ≠ N)
    {o : ℕ} (ho : o ≤ 1) {w : E} (hw : LoadHolds rd (t * x * x) o w) : WinsP rd pd w :=
  h 0 (ne_zero_steps hne) o ho w (by rwa [pow_zero, mul_one])

/-- **A deeper specialization's walk** from `level_queries`' obligation. -/
theorem winWalkP_of_mainWins {d cd : ℕ} {t N : E} (h : OqMainWins rd d cd 0 0 t N) :
    WinWalkP rd (d - cd) t 1 N := by
  have h2 := h.2
  simp only [show ¬ (0 : ℕ) = 1 from by decide, ↓reduceIte] at h2
  intro c hc w hw
  exact winsP_of_winsAt (h2 c hc w hw)

/-- **A level-0 specialization's obligation** for `odd` from `level_queries`' obligation for the
same `odd`, at `N = g^n` with a query (`odd = 1` or `0 < n`). -/
theorem oqStartP_of_mainWins {d cd odd n : ℕ} {t u : E} (h : OqMainWins rd d cd odd 1 t (gen ^ n))
    (hq : odd = 1 ∨ 0 < n) (hn : n < 2 ^ 64 - 1) (ho : odd < 2) :
    OqStartP rd (d - cd) odd t (gen ^ n) u := by
  have h2 := h.2
  simp only [↓reduceIte] at h2
  refine ⟨fun w hw ↦ ?_, fun hu c hc o ho1 w hw ↦ ?_⟩
  · by_cases h1 : odd = 1
    · exact winsP_of_winsAt (h.1 h1 w hw)
    · obtain rfl : odd = 0 := by omega
      have hn0 : 0 < n := by omega
      refine winsP_of_winsAt (h2 0 (fun c' hc' he ↦ ?_) 0 le_rfl (by omega) w (by simpa using hw))
      obtain rfl : c' = 0 := by omega
      rw [pow_zero, mul_one, ← pow_zero gen] at he
      have := gen_pow_inj (by norm_num) hn he
      omega
  · subst hu
    refine winsP_of_winsAt (h2 c hc (odd + o) (by omega) (by omega) w ?_)
    rw [← loadHolds_mul_gen_pow]
    rwa [show t * gen ^ odd * (1 * gen ^ c) * (1 * gen ^ c) =
      t * (1 * gen ^ c) * (1 * gen ^ c) * gen ^ odd by ring] at hw

/-! ## Prefixes of a body -/

/-- The flat statements (calls among them) before a cut hold, over any prefix of the body reaching
past them. -/
theorem blockOkC_of_take {C : CallRel} {σ : Val} {body pre : List Stmt} (hb : pre <+: body)
    (hf : FlatC pre) {n : ℕ} (hn : pre.length ≤ n) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (body.take n) next kret) : BlockOkC C rd σ pre := by
  obtain ⟨rest, rfl⟩ := hb
  rw [List.take_append, List.take_of_length_le hn, holdsList_append, holdsList_flatC hf] at h
  exact h.1

/-- The flat statements before a cut hold, over any prefix of the body reaching past them. -/
theorem blockOk_of_take {C : CallRel} {σ : Val} {body pre : List Stmt} (hb : pre <+: body)
    (hf : Flat pre) {n : ℕ} (hn : pre.length ≤ n) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (body.take n) next kret) : BlockOk rd σ pre := by
  obtain ⟨rest, rfl⟩ := hb
  rw [List.take_append, List.take_of_length_le hn, holdsList_append, holdsList_flat hf] at h
  exact h.1

/-! ## The loop bodies -/

section Bodies

variable {C : CallRel} {σ : Val} {next : Prop} {kret : List E → Prop}

/-- **A deeper iteration's window pointer** (cell `13`, `qptrs[x]`) names path windows, over any
prefix of the body holding its load (`n ≥ 4`). -/
theorem oqLoop0T_wins {s : Oq} {name : String} {n : ℕ} (hn : 4 ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop0T s name).take n) next kret)
    (hw : WinWalkP rd s.pd (σ (.n oqQp)) (σ (.n oqX)) (σ (.n oqN))) (hne : σ (.n oqX) ≠ σ (.n oqN)) :
    WinsP rd s.pd (σ (.n 13)) := by
  have hb := blockOk_of_take (pre := [.atom (.mul (.n 10) (.n oqPos) (.n oqX)), .atom (.load (.n 11) (.n 10) 0),
      .atom (.mul (.n 12) (.n oqQp) (.n oqX)), .atom (.load (.n 13) (.n 12) 0)])
    (by simp [oqLoop0T, oqLoop0A]) (flat_of_atoms (allAtoms_of_forall (by simp))) (by simpa using hn) h
  have p12 := hb.atom (by simp : Stmt.atom (.mul (.n 12) (.n oqQp) (.n oqX)) ∈ _)
  have p13 := hb.atom (by simp : Stmt.atom (.load (.n 13) (.n 12) 0) ∈ _)
  simp only [Atom.Holds] at p12 p13
  rw [p12] at p13
  exact winsP_of_walkP hw hne p13

/-- The statements of a level-0 iteration up to its second query's window pointer. -/
def oqLoop1Pre (s : Oq) : List Stmt :=
  [.atom (.mul (.n 10) (.n oqX) (.n oqX)), .atom (.mul (.n 11) (.n oqPos) (.n 10)),
    .atom (.mul (.n 12) (.n oqQp) (.n 10)), .atom (.load (.n 13) (.n 11) 0),
    .atom (.load (.n 14) (.n 12) 0)] ++
    (oqQueryT s (.n 13) (.n 14) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 15 true 0 ++
    [.atom (.load (.n (oqE1 s)) (.n 11) 1), .atom (.load (.n (oqE1 s + 1)) (.n 12) 1)])

theorem oqLoop1T_prefix (s : Oq) (name : String) : oqLoop1Pre s <+: oqLoop1T s name := by
  unfold oqLoop1Pre oqLoop1T oqLoop1A
  dsimp only
  simp only [List.append_assoc, List.prefix_append_right_inj]
  exact List.prefix_append _ _

theorem oqLoop1Pre_flatC (s : Oq) : FlatC (oqLoop1Pre s) :=
  flatC_append (flatC_atoms (allAtoms_of_forall (by simp)))
    (flatC_append (oqQueryT_flatC _ _ _ _ _ _ _ _ _ _) (flatC_atoms (allAtoms_of_forall (by simp))))

theorem oqLoop1Pre_length (s : Oq) :
    (oqLoop1Pre s).length =
      (oqQueryT s (.n 13) (.n 14) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 15 true 0).length + 7 := by
  simp only [oqLoop1Pre, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **A level-0 iteration's first window pointer** (cell `14`, `(qptrs·x²)[g^0]`) names path
windows, over any prefix of the body holding its load (`n ≥ 5`). -/
theorem oqLoop1T_wins1 {s : Oq} {name : String} {n : ℕ} (hn : 5 ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop1T s name).take n) next kret)
    (hw : WinWalk2P rd s.pd (σ (.n oqQp)) (σ (.n oqX)) (σ (.n oqN))) (hne : σ (.n oqX) ≠ σ (.n oqN)) :
    WinsP rd s.pd (σ (.n 14)) := by
  have hb := blockOk_of_take (pre := [.atom (.mul (.n 10) (.n oqX) (.n oqX)),
      .atom (.mul (.n 11) (.n oqPos) (.n 10)), .atom (.mul (.n 12) (.n oqQp) (.n 10)),
      .atom (.load (.n 13) (.n 11) 0), .atom (.load (.n 14) (.n 12) 0)])
    ((List.prefix_append _ _).trans (oqLoop1T_prefix s name))
    (flat_of_atoms (allAtoms_of_forall (by simp))) (by simpa using hn) h
  have p10 := hb.atom (by simp : Stmt.atom (.mul (.n 10) (.n oqX) (.n oqX)) ∈ _)
  have p12 := hb.atom (by simp : Stmt.atom (.mul (.n 12) (.n oqQp) (.n 10)) ∈ _)
  have p14 := hb.atom (by simp : Stmt.atom (.load (.n 14) (.n 12) 0) ∈ _)
  simp only [Atom.Holds] at p10 p12 p14
  rw [p12, p10, ← mul_assoc] at p14
  exact winsP_of_walk2P hw hne (by omega) p14

/-- **A level-0 iteration's second window pointer** (cell `oqE1 + 1`, `(qptrs·x²)[g^1]`) names
path windows, over any prefix of the body holding its load. -/
theorem oqLoop1T_wins2 {s : Oq} {name : String} {n : ℕ}
    (hn : (oqQueryT s (.n 13) (.n 14) (.n oqCap) (.n oqFlags) (.n oqCoefs) (.n oqHs) 15 true 0).length + 7 ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop1T s name).take n) next kret)
    (hw : WinWalk2P rd s.pd (σ (.n oqQp)) (σ (.n oqX)) (σ (.n oqN))) (hne : σ (.n oqX) ≠ σ (.n oqN)) :
    WinsP rd s.pd (σ (.n (oqE1 s + 1))) := by
  have hb := blockOkC_of_take (oqLoop1T_prefix s name) (oqLoop1Pre_flatC s)
    (by rw [oqLoop1Pre_length]; exact hn) h
  have p10 := hb.atom (by simp [oqLoop1Pre] : Stmt.atom (.mul (.n 10) (.n oqX) (.n oqX)) ∈ _)
  have p12 := hb.atom (by simp [oqLoop1Pre] : Stmt.atom (.mul (.n 12) (.n oqQp) (.n 10)) ∈ _)
  have pe := hb.atom (by simp [oqLoop1Pre] : Stmt.atom (.load (.n (oqE1 s + 1)) (.n 12) 1) ∈ _)
  simp only [Atom.Holds] at p10 p12 pe
  rw [p12, p10, ← mul_assoc] at pe
  exact winsP_of_walk2P hw hne le_rfl pe

/-- The guard's next counter `x·g` (cell `g + 4`), from the guard's atoms. -/
theorem oqGuard_next {A : List Stmt} {g : ℕ} (hb : BlockOkC C rd σ A)
    (hsub : ∀ a, Stmt.atom a ∈ oqGuardA g → Stmt.atom a ∈ A) : σ (.n (g + 4)) = σ (.n oqX) * gen := by
  have c3 := hb.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.const (.n (g + 3)) (word 2 0)) ∈ _)
  have c4 := hb.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.mul (.n (g + 4)) (.n oqX) (.n (g + 3))) ∈ _)
  simp only [Atom.Holds] at c3 c4
  rw [c4, c3, word_gen]

/-- **A deeper iteration's tail call** passes `x·g` (cell `oqG0 + 4`): the walk goes on. -/
theorem oqLoop0T_tail {s : Oq} {name : String} {n : ℕ} (hn : (oqLoop0A s).length ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop0T s name).take n) next kret)
    (hw : WinWalkP rd s.pd (σ (.n oqQp)) (σ (.n oqX)) (σ (.n oqN))) (hne : σ (.n oqX) ≠ σ (.n oqN)) :
    WinWalkP rd s.pd (σ (.n oqQp)) (σ (.n (oqG0 s + 4))) (σ (.n oqN)) := by
  have hb := blockOkC_of_take (List.prefix_append _ _) (oqLoop0A_flatC s) hn h
  rw [oqGuard_next hb (fun a h ↦ by unfold oqLoop0A; exact List.mem_append_right _ h)]
  exact winWalkP_succ hw hne

/-- **A level-0 iteration's tail call** passes `x·g` (cell `oqG1 + 4`): the walk goes on. -/
theorem oqLoop1T_tail {s : Oq} {name : String} {n : ℕ} (hn : (oqLoop1A s).length ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop1T s name).take n) next kret)
    (hw : WinWalk2P rd s.pd (σ (.n oqQp)) (σ (.n oqX)) (σ (.n oqN))) (hne : σ (.n oqX) ≠ σ (.n oqN)) :
    WinWalk2P rd s.pd (σ (.n oqQp)) (σ (.n (oqG1 s + 4))) (σ (.n oqN)) := by
  have hb := blockOkC_of_take (List.prefix_append _ _) (oqLoop1A_flatC s) hn h
  rw [oqGuard_next hb (fun a h ↦ by unfold oqLoop1A; exact List.mem_append_right _ h)]
  exact winWalk2P_succ hw hne

/-- The function's start holds, over any prefix of its body past it. -/
theorem oqMainT_start {s : Oq} {loop : String} {n : ℕ} (hn : (oqMainA s).length ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqMainT s loop).take n) next kret) : OqStartOk C rd σ s := by
  unfold oqMainT at h
  dsimp only at h
  rw [List.append_assoc, List.take_append, List.take_of_length_le hn, holdsList_append,
    holdsList_oqMainA] at h
  exact h.1

/-- **A level-0 specialization's loop call** passes the window
pointers past the odd query `qptrs·odd_g` (cell `oqMK - 1`): the walk from `1` of `OqStartP` for
the `odd` that `odd_g` is (`x = 1` is the call's constant). -/
theorem oqMainT_loop1 {s : Oq} {loop : String} {n : ℕ} (hb : s.base = 1) (hn : (oqMainA s).length ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqMainT s loop).take n) next kret) {odd : ℕ}
    (hu : σ (.n oqMOdd) = gen ^ odd)
    (hw : OqStartP rd s.pd odd (σ (.n oqMQp)) (σ (.n oqMN)) (σ (.n oqMOdd))) :
    WinWalk2P rd s.pd (σ (.n (oqMK s - 1))) 1 (σ (.n oqMN)) := by
  rw [(oqStart1_facts hb (oqMainT_start hn h)).2.2.1]
  exact hw.2 hu

end Bodies

end
end LeanVM.Guest.B1
