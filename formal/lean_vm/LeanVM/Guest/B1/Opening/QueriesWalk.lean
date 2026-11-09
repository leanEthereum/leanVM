/-
  LeanVM.Guest.B1.Opening.QueriesWalk

  The walk obligations of `opening_queries`: every window a query dispatches on is a small power
  of `g`, from the window pointers' runs, carried along the loop (the definitions in `WalkDefs`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesMain
public import LeanVM.Guest.B1.Opening.WalkDefs

/-!
# The windows a walk dispatches on (lean_ethereum.py:1308-1343, 1393-1415 at 40f877dc)

`walk_path__L{pd}_L{cd}` (a function) dispatches `match(log(w))` on each path window
`w = wins[g^i]`; `opening_queries` calls it on the window pointer `wins` loaded from
`query_win_ptrs` at the iteration's index (`query_win_ptrs[xi]` deeper, `(query_win_ptrs·xi²)[g^odd]`,
`[g^(odd+1)]` at level 0). A window's bound comes from `decode_query_windows`' range checks, in
another function, through the pointer table: the checker of the certificates takes it as an
obligation on the loop's arguments, carried by the loop, and hands `WinsAt` of the loaded pointer to
each call of `walk_path` (whose precondition it is: `winsTag`).

* `WinsAt rd d cd w`: each of the `qwN d cd` windows at `w`, if read, is `g^e`, `e` below the
  window's `2^width` (`qwWin`).
* `WinWalk rd d cd t x N` (deeper) / `WinWalk2 rd d cd odd t x N` (level 0): the pointers of every
  iteration still to run name such windows: at `x·g^c` for each `c` with `x·g^c' ≠ N`, `c' ≤ c`
  (the loop runs `x, x·g, …` until `N`).
* `winWalk_succ`, `winWalk2_succ`: the tail call's argument `x·g` keeps them when `x ≠ N`.
* `winsAt_of_walk`, `winsAt_of_walk2`: the iteration at `x ≠ N` reads such pointers.
* `oqMainWins_of_queryWinsOk`: `QueryWinsOk` (what `decode_query_windows` gives, the soundness
  precondition) at `n_iters_g = g^n` gives them at the loop's first `x = 1`, and the windows of an
  odd count's first query.
* The bodies: `oqLoop0T_wins`, `oqLoop1T_wins1`, `oqLoop1T_wins2` (the queries' window pointers,
  over any prefix of the body holding their loads: what the cut before each `walk_path` call hands
  on), `oqLoop0T_tail`, `oqLoop1T_tail` (the tail
  call's argument, over the statements before the call), `oqMainT_wins`, `oqMainT_loop` (the function's
  odd query and loop call); `winsAt_known`: a window read is `g^e` (a `MemKnown` triple).

The walk is unbounded in `c`: a bound `c < B` on its own does not survive the tail call
(`x·g` needs `c + 1 < B`); `winWalk_iff_bounded` is the bounded form when `x` reaches `N` within
`B` steps (a run-time test).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## Windows -/

/-- **A window read** is `g^e`, `e` below its bound: the `MemKnown` triple `(w, i, 2^width)`. -/
theorem winsAt_known {d cd : ℕ} {w : E} (h : WinsAt rd d cd w) {i : ℕ} (hi : i < qwN d cd) {v : E}
    (hv : LoadHolds rd w i v) :
    ∃ e < 2 ^ (qwWin d cd i).2, LoadHolds rd w i (ofK (addressOfIndex e)) := by
  obtain ⟨e, he, rfl⟩ := h i hi v hv
  exact ⟨e, he, hv⟩

/-- A path window's bound is its levels' count. -/
theorem winsAt_path {s : Oq} {w : E} (h : WinsAt rd (s.pd + s.cd) s.cd w) {i : ℕ} (hi : i < oqNpw s)
    {v : E} (hv : LoadHolds rd w i v) : ∃ e < 2 ^ oqWw s i, v = ofK (addressOfIndex e) := by
  have := h i (by rw [qwN_eq]; omega) v hv
  rwa [qwWin_path hi] at this

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

/-- **The tail call keeps the walk** (deeper): `x ≠ N` steps it to `x·g`. -/
theorem winWalk_succ {d cd : ℕ} {t x N : E} (h : WinWalk rd d cd t x N) (hne : x ≠ N) :
    WinWalk rd d cd t (x * gen) N := by
  intro c hc w hw
  refine h (c + 1) (pow_succ_shift hne hc) w ?_
  rw [mul_pow_succ]
  exact hw

/-- **The tail call keeps the walk** (level 0). -/
theorem winWalk2_succ {d cd odd : ℕ} {t x N : E} (h : WinWalk2 rd d cd odd t x N) (hne : x ≠ N) :
    WinWalk2 rd d cd odd t (x * gen) N := by
  intro c hc o ho1 ho2 w hw
  refine h (c + 1) (pow_succ_shift hne hc) o ho1 ho2 w ?_
  rw [mul_pow_succ]
  exact hw

/-- **The iteration at `x ≠ N` reads windows** (deeper): its pointer `t[x]`. -/
theorem winsAt_of_walk {d cd : ℕ} {t x N : E} (h : WinWalk rd d cd t x N) (hne : x ≠ N) {w : E}
    (hw : LoadHolds rd (t * x) 0 w) : WinsAt rd d cd w :=
  h 0 (fun c' hc' ↦ by obtain rfl : c' = 0 := by omega
                       rwa [pow_zero, mul_one]) w (by rwa [pow_zero, mul_one])

/-- **The iteration at `x ≠ N` reads windows** (level 0): its pointers `(t·x²)[g^o]`. -/
theorem winsAt_of_walk2 {d cd odd : ℕ} {t x N : E} (h : WinWalk2 rd d cd odd t x N) (hne : x ≠ N)
    {o : ℕ} (ho1 : odd ≤ o) (ho2 : o ≤ odd + 1) {w : E} (hw : LoadHolds rd (t * x * x) o w) :
    WinsAt rd d cd w :=
  h 0 (fun c' hc' ↦ by obtain rfl : c' = 0 := by omega
                       rwa [pow_zero, mul_one]) o ho1 ho2 w (by rwa [pow_zero, mul_one])

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

/-- **The bounded walk**: when `x` reaches `N` within `B` steps, the walk is its first `B` steps. -/
theorem winWalk_iff_bounded {d cd B : ℕ} {t x N : E} (hB : ∃ c < B, x * gen ^ c = N) :
    WinWalk rd d cd t x N ↔ ∀ c < B, (∀ c' ≤ c, x * gen ^ c' ≠ N) →
      ∀ w, LoadHolds rd (t * (x * gen ^ c)) 0 w → WinsAt rd d cd w := by
  obtain ⟨c0, hc0, he⟩ := hB
  refine ⟨fun h c _ ↦ h c, fun h c hc ↦ h c ?_ hc⟩
  by_contra hcb
  exact hc c0 (by omega) he

/-- **The bounded walk** (level 0). -/
theorem winWalk2_iff_bounded {d cd odd B : ℕ} {t x N : E} (hB : ∃ c < B, x * gen ^ c = N) :
    WinWalk2 rd d cd odd t x N ↔ ∀ c < B, (∀ c' ≤ c, x * gen ^ c' ≠ N) → ∀ o, odd ≤ o →
      o ≤ odd + 1 → ∀ w, LoadHolds rd (t * (x * gen ^ c) * (x * gen ^ c)) o w → WinsAt rd d cd w := by
  obtain ⟨c0, hc0, he⟩ := hB
  refine ⟨fun h c _ ↦ h c, fun h c hc ↦ h c ?_ hc⟩
  by_contra hcb
  exact hc c0 (by omega) he

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

/-- **A deeper iteration's window pointer** (cell `9`, `query_win_ptrs[xi]`) names windows, over
any prefix of the body holding its load (`n ≥ 2`). -/
theorem oqLoop0T_wins {s : Oq} {walk name : String} {n : ℕ} (hn : 2 ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop0T s walk name).take n) next kret)
    (hw : WinWalk rd (s.pd + s.cd) s.cd (σ (.n 2)) (σ (.n 0)) (σ (.n 1)))
    (hne : σ (.n 0) ≠ σ (.n 1)) : WinsAt rd (s.pd + s.cd) s.cd (σ (.n 9)) := by
  have hb := blockOk_of_take (pre := [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.load (.n 9) (.n 8) 0)])
    (by simp [oqLoop0T, oqLoop0A]) (flat_of_atoms (allAtoms_of_forall (by simp))) (by simpa using hn) h
  have p8 := hb.atom (by simp : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hb.atom (by simp : Stmt.atom (.load (.n 9) (.n 8) 0) ∈ _)
  simp only [Atom.Holds] at p8 p9
  rw [p8] at p9
  exact winsAt_of_walk hw hne p9

/-- The statements of a level-0 iteration up to its second query's window pointer. -/
def oqLoop1Pre (s : Oq) (odd : ℕ) (walk : String) : List Stmt :=
  [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.mul (.n 9) (.n 8) (.n 0)),
    .atom (.load (.n 10) (.n 9) odd)] ++ oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0 walk ++
    [.atom (.load (.n (oqE1 s)) (.n 9) (odd + 1))]

theorem oqLoop1T_prefix (s : Oq) (odd : ℕ) (walk name : String) :
    oqLoop1Pre s odd walk <+: oqLoop1T s odd walk name :=
  (List.prefix_append _ _).trans ((List.prefix_append _ _).trans (List.prefix_append _ _))

theorem oqLoop1Pre_flatC (s : Oq) (odd : ℕ) (walk : String) : FlatC (oqLoop1Pre s odd walk) :=
  flatC_append (flatC_append (flatC_atoms (allAtoms_of_forall (by simp)))
    (oqQueryT_flatC _ _ _ _ _ _ _ _ _)) (flatC_atoms (allAtoms_of_forall (by simp)))

theorem oqLoop1Pre_length (s : Oq) (odd : ℕ) (walk : String) :
    (oqLoop1Pre s odd walk).length =
      (oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0 walk).length + 4 := by
  simp only [oqLoop1Pre, List.length_append, List.length_cons, List.length_nil]
  omega

/-- **A level-0 iteration's first window pointer** (cell `10`, `(query_win_ptrs·xi²)[g^odd]`)
names windows, over any prefix of the body holding its load (`n ≥ 3`). -/
theorem oqLoop1T_wins1 {s : Oq} {odd : ℕ} {walk name : String} {n : ℕ} (hn : 3 ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop1T s odd walk name).take n) next kret)
    (hw : WinWalk2 rd (s.pd + s.cd) s.cd odd (σ (.n 2)) (σ (.n 0)) (σ (.n 1)))
    (hne : σ (.n 0) ≠ σ (.n 1)) : WinsAt rd (s.pd + s.cd) s.cd (σ (.n 10)) := by
  have hb := blockOk_of_take (pre := [.atom (.mul (.n 8) (.n 2) (.n 0)),
      .atom (.mul (.n 9) (.n 8) (.n 0)), .atom (.load (.n 10) (.n 9) odd)])
    ((List.prefix_append _ _).trans (((List.prefix_append _ _).trans (List.prefix_append _ _)).trans
      (oqLoop1T_prefix s odd walk name)))
    (flat_of_atoms (allAtoms_of_forall (by simp))) (by simpa using hn) h
  have p8 := hb.atom (by simp : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hb.atom (by simp : Stmt.atom (.mul (.n 9) (.n 8) (.n 0)) ∈ _)
  have p10 := hb.atom (by simp : Stmt.atom (.load (.n 10) (.n 9) odd) ∈ _)
  simp only [Atom.Holds] at p8 p9 p10
  rw [p9, p8] at p10
  exact winsAt_of_walk2 hw hne le_rfl (by omega) p10

/-- **A level-0 iteration's second window pointer** (cell `oqE1`, `(query_win_ptrs·xi²)[g^(odd+1)]`)
names windows, over any prefix of the body holding its load. -/
theorem oqLoop1T_wins2 {s : Oq} {odd : ℕ} {walk name : String} {n : ℕ}
    (hn : (oqQueryT s (.n 10) (.n 3) (.n 4) (.n 5) 11 true 0 walk).length + 4 ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop1T s odd walk name).take n) next kret)
    (hw : WinWalk2 rd (s.pd + s.cd) s.cd odd (σ (.n 2)) (σ (.n 0)) (σ (.n 1)))
    (hne : σ (.n 0) ≠ σ (.n 1)) : WinsAt rd (s.pd + s.cd) s.cd (σ (.n (oqE1 s))) := by
  have hb := blockOkC_of_take (oqLoop1T_prefix s odd walk name) (oqLoop1Pre_flatC s odd walk)
    (by rw [oqLoop1Pre_length]; exact hn) h
  have p8 := hb.atom (by simp [oqLoop1Pre] : Stmt.atom (.mul (.n 8) (.n 2) (.n 0)) ∈ _)
  have p9 := hb.atom (by simp [oqLoop1Pre] : Stmt.atom (.mul (.n 9) (.n 8) (.n 0)) ∈ _)
  have pe := hb.atom (by simp [oqLoop1Pre] : Stmt.atom (.load (.n (oqE1 s)) (.n 9) (odd + 1)) ∈ _)
  simp only [Atom.Holds] at p8 p9 pe
  rw [p9, p8] at pe
  exact winsAt_of_walk2 hw hne (by omega) le_rfl pe

/-- **A deeper iteration's tail call** passes `x·g` (cell `oqC0 + 9`): the walk goes on. -/
theorem oqLoop0T_tail {s : Oq} {walk name : String} {n : ℕ} (hn : (oqLoop0A s walk).length ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop0T s walk name).take n) next kret)
    (hw : WinWalk rd (s.pd + s.cd) s.cd (σ (.n 2)) (σ (.n 0)) (σ (.n 1)))
    (hne : σ (.n 0) ≠ σ (.n 1)) :
    WinWalk rd (s.pd + s.cd) s.cd (σ (.n 2)) (σ (.n (oqC0 s + 9))) (σ (.n 1)) := by
  have hb := blockOkC_of_take (List.prefix_append _ _) (oqLoop0A_flatC s walk) hn h
  have c8 := hb.atom (by simp [oqLoop0A] : Stmt.atom (.const (.n (oqC0 s + 8)) (word 2 0 0)) ∈ _)
  have c9 := hb.atom (by simp [oqLoop0A] : Stmt.atom (.mul (.n (oqC0 s + 9)) (.n 0) (.n (oqC0 s + 8))) ∈ _)
  simp only [Atom.Holds] at c8 c9
  rw [c9, c8, word_gen]
  exact winWalk_succ hw hne

/-- **A level-0 iteration's tail call** passes `x·g` (cell `oqC1 + 11`): the walk goes on. -/
theorem oqLoop1T_tail {s : Oq} {odd : ℕ} {walk name : String} {n : ℕ}
    (hn : (oqLoop1A s odd walk).length ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqLoop1T s odd walk name).take n) next kret)
    (hw : WinWalk2 rd (s.pd + s.cd) s.cd odd (σ (.n 2)) (σ (.n 0)) (σ (.n 1)))
    (hne : σ (.n 0) ≠ σ (.n 1)) :
    WinWalk2 rd (s.pd + s.cd) s.cd odd (σ (.n 2)) (σ (.n (oqC1 s + 11))) (σ (.n 1)) := by
  have hb := blockOkC_of_take (List.prefix_append _ _) (oqLoop1A_flatC s odd walk) hn h
  have c10 := hb.atom (by simp [oqLoop1A] : Stmt.atom (.const (.n (oqC1 s + 10)) (word 2 0 0)) ∈ _)
  have c11 := hb.atom (by simp [oqLoop1A] :
    Stmt.atom (.mul (.n (oqC1 s + 11)) (.n 0) (.n (oqC1 s + 10))) ∈ _)
  simp only [Atom.Holds] at c10 c11
  rw [c11, c10, word_gen]
  exact winWalk2_succ hw hne

/-- **An odd count's first query's window pointer** (cell `12`, `query_win_ptrs[1]`) names
windows, over any prefix of the function's body holding its load (`n ≥ 6`). -/
theorem oqMainT_wins {s : Oq} {walk loop : String} {n : ℕ} (hn : 6 ≤ n) {odd base : ℕ} (ho : odd = 1)
    (h : Stmt.HoldsList C rd σ ((oqMainT s odd walk loop).take n) next kret)
    (hw : OqMainWins rd (s.pd + s.cd) s.cd odd base (σ (.n 4)) (σ (.n 6))) :
    WinsAt rd (s.pd + s.cd) s.cd (σ (.n 12)) := by
  subst ho
  have hb := blockOk_of_take (pre := [.atom (.const (.n 7) (word 1 0 0)),
      .atom (.mul (.n 7) (.n 8) (.n 2)), .atom (.const (.n 9) (word 2 0 0)),
      .atom (.mul (.n 10) (.n 6) (.n 9)), .atom (.hint (.allocDyn (.n 11) (.n 10))),
      .atom (.load (.n 12) (.n 4) 0)]) (by simp [oqMainT, oqMainA])
    (flat_of_atoms (allAtoms_of_forall (by simp))) (by simpa using hn) h
  have p12 := hb.atom (by simp : Stmt.atom (.load (.n 12) (.n 4) 0) ∈ _)
  exact hw.1 rfl _ p12

/-- **The function's loop call** passes `x = 1` (cell `oqMK + 2`): the walk from `1`, over the
atoms before the call. -/
theorem oqMainT_loop {s : Oq} {odd base : ℕ} {walk loop : String} {n : ℕ}
    (hn : (oqMainA s odd walk).length ≤ n)
    (h : Stmt.HoldsList C rd σ ((oqMainT s odd walk loop).take n) next kret)
    (hw : OqMainWins rd (s.pd + s.cd) s.cd odd base (σ (.n 4)) (σ (.n 6))) :
    (if base = 1 then WinWalk2 rd (s.pd + s.cd) s.cd odd (σ (.n 4)) (σ (.n (oqMK s odd + 2))) (σ (.n 6))
      else WinWalk rd (s.pd + s.cd) s.cd (σ (.n 4)) (σ (.n (oqMK s odd + 2))) (σ (.n 6))) := by
  have hb := blockOkC_of_take (List.prefix_append _ _) (oqMainA_flatC s odd walk) hn h
  have k2 := hb.atom (by simp [oqMainA] : Stmt.atom (.const (.n (oqMK s odd + 2)) (word 1 0 0)) ∈ _)
  simp only [Atom.Holds] at k2
  rw [k2, word_one]
  exact hw.2

end Bodies

end
end LeanVM.Guest.B1
