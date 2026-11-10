/-
  LeanVM.Guest.B1.Whir.CHon

  An accepting run's levels as an indexed list: each level's start and data, the step to the next.
-/

module

public import LeanVM.Guest.B1.Whir.CInvNZ

/-!
# The run's levels, indexed

`LvAt`: a level of the honest run, its Spec level, the Spec's state, the carried capacity and the
roots at its start, the words and phases from it on, its data (`LvD`). `lvsAt`: the levels of a
`LvsRunD`, in order; `lvsAt_run`: their count, levels, start, each non-final level's step to the
next (`LvAt.NextStep`) and the final one's end (`LvAt.FinStep`); `lvsAt_nz`: each level's
combiners at its positions (`LvsNZ`, indexed).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A level of the honest run.** -/
structure LvAt where
  level : Whir.Level
  s : WhirState
  cap : List E
  R : List (Digest × ℕ × ℕ)
  xs : List E
  os : List (List Opening)
  d : LvD

instance : Inhabited LvAt := ⟨⟨⟨0, 0, 0⟩, ⟨0, [], []⟩, [], [], [], [], .fin [] ⟨[], 0, [], []⟩⟩⟩

namespace LvAt

variable (L : LvAt) (logN : ℕ)

/-- The level's round words. -/
def rw : List E := match L.d with
  | .next rw _ => rw
  | .fin rw _ => rw

/-- The Spec's state after the level's folds. -/
abbrev s1 : WhirState := rsSt L.level L.s L.cap L.rw

/-- The sponge after the level's folds. -/
abbrev F : Fs := rsF L.level L.cap L.rw

/-- The level's fold rounds. -/
abbrev rounds : List FoldRound := rsRounds L.level L.s L.cap L.rw

/-- The message log after the level's folds. -/
abbrev mu : ℕ := logN - L.s1.gammas.length

/-- The level's code's depth. -/
abbrev dp : ℕ := L.mu logN + L.level.logInvRate

/-- The level's positions. -/
def qs : List ℕ := match L.d with
  | .next _ W => W.qs L.F (L.mu logN) (L.dp logN) L.level.queries
  | .fin _ W => W.qs L.F (L.dp logN) L.level.queries

end LvAt

/-- **The levels of a run, in order.** -/
def lvsAt (logN : ℕ) : ℕ → List Whir.Level → WhirState → List E → List (Digest × ℕ × ℕ) → List E →
    List (List Opening) → List LvD → List LvAt
  | _, [level], s, cap, R, xs, os, [LvD.fin rw W] => [⟨level, s, cap, R, xs, os, .fin rw W⟩]
  | index, level :: next :: rest, s, cap, R, xs, os, LvD.next rw W :: ds =>
    ⟨level, s, cap, R, xs, os, .next rw W⟩ ::
      lvsAt logN (index + 1) (next :: rest)
        (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
        (capOf ((W.F3 (rsF level cap rw) (logN - (rsSt level s cap rw).gammas.length)
          (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries).nonceState W.n2))
        (W.roots (logN - (rsSt level s cap rw).gammas.length) next R)
        (xs.drop (rw.length + W.words.length)) os.tail ds
  | _, _, _, _, _, _, _, _ => []

/-- **A non-final level's step**: its reads and checks, and the next level's start. -/
def LvAt.NextStep (logN index : ℕ) (L L' : LvAt) : Prop :=
  ∃ (rw : List E) (W : NextW), L.d = .next rw W ∧ rw.length = 7 * L.level.fold ∧
    RoundsOk L.level.fold L.cap rw ∧ L.xs = rw ++ W.words ++ L'.xs ∧ L.os = W.phase :: L'.os ∧
    NextOk logN index L.level (rsSt L.level L.s L.cap rw) (rsF L.level L.cap rw) L.R W ∧
    L'.s = W.glued logN index L.level (rsSt L.level L.s L.cap rw) (rsF L.level L.cap rw)
      (rsRounds L.level L.s L.cap rw) ∧
    L'.cap = capOf ((W.F3 (rsF L.level L.cap rw) (logN - (rsSt L.level L.s L.cap rw).gammas.length)
      (logN - (rsSt L.level L.s L.cap rw).gammas.length + L.level.logInvRate)
      L.level.queries).nonceState W.n2) ∧
    L'.R = W.roots (logN - (rsSt L.level L.s L.cap rw).gammas.length) L'.level L.R

/-- **The final level's end.** -/
def LvAt.FinStep (logN lane index : ℕ) (L : LvAt) (w : WhirEnd) : Prop :=
  ∃ (rw : List E) (W : FinW), L.d = .fin rw W ∧ rw.length = 7 * L.level.fold ∧
    RoundsOk L.level.fold L.cap rw ∧ L.xs = rw ++ W.words ∧ L.os = [W.phase] ∧
    FinOk logN index L.level (rsSt L.level L.s L.cap rw) (rsRounds L.level L.s L.cap rw)
      (rsF L.level L.cap rw) L.R W ∧
    w = W.wend logN lane L.level (rsSt L.level L.s L.cap rw) (rsF L.level L.cap rw)

/-- What `lvsAt_run` gives. -/
structure LvsAtRun (logN lane index : ℕ) (levels : List Whir.Level) (s : WhirState) (cap : List E)
    (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
    (L : List LvAt) : Prop where
  len : L.length = levels.length
  level : ∀ i < L.length, levels[i]? = some (L.getD i default).level
  start : 0 < L.length → (L.getD 0 default).s = s ∧ (L.getD 0 default).cap = cap ∧
    (L.getD 0 default).R = R ∧ (L.getD 0 default).xs = xs ∧ (L.getD 0 default).os = os
  next : ∀ i, i + 1 < L.length → LvAt.NextStep logN (index + i) (L.getD i default) (L.getD (i + 1) default)
  fin : 0 < L.length → LvAt.FinStep logN lane (index + (L.length - 1)) (L.getD (L.length - 1) default) w

theorem drop_words {rw ws xs' : List E} : (rw ++ ws ++ xs').drop (rw.length + ws.length) = xs' :=
  List.drop_left' (by simp)

/-- **The levels of a run, indexed.** -/
theorem lvsAt_run (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap : List E)
      (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
      (ds : List LvD), LvsRunD logN lane index levels s cap R xs os w ds →
      LvsAtRun logN lane index levels s cap R xs os w (lvsAt logN index levels s cap R xs os ds)
  | [level], index, s, cap, R, xs, os, w, [LvD.fin rw W], hD => by
    obtain ⟨hrl, hrok, hxs, hos, hfin, hw⟩ := hD
    refine ⟨rfl, fun i h ↦ ?_, fun _ ↦ ⟨rfl, rfl, rfl, rfl, rfl⟩, fun i h ↦ absurd h (by simp [lvsAt]),
      fun _ ↦ ⟨rw, W, rfl, hrl, hrok, hxs, hos, by simpa [lvsAt] using hfin, hw⟩⟩
    obtain rfl : i = 0 := by simp [lvsAt] at h; omega
    rfl
  | level :: next :: rest, index, s, cap, R, xs, os, w, LvD.next rw W :: ds, hD => by
    obtain ⟨xs', os', hrl, hrok, hxs, hos, hnext, hD'⟩ := hD
    have hxs' : xs.drop (rw.length + W.words.length) = xs' := by rw [hxs]; exact drop_words
    have hos' : os.tail = os' := by rw [hos]; rfl
    have ih := lvsAt_run logN lane (next :: rest) (index + 1) _ _ _ xs' os' w ds hD'
    rw [← hxs', ← hos'] at ih
    set L' := lvsAt logN (index + 1) (next :: rest)
      (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
      (capOf ((W.F3 (rsF level cap rw) (logN - (rsSt level s cap rw).gammas.length)
        (logN - (rsSt level s cap rw).gammas.length + level.logInvRate) level.queries).nonceState W.n2))
      (W.roots (logN - (rsSt level s cap rw).gammas.length) next R)
      (xs.drop (rw.length + W.words.length)) os.tail ds with hL'
    have e : lvsAt logN index (level :: next :: rest) s cap R xs os (LvD.next rw W :: ds) =
        ⟨level, s, cap, R, xs, os, .next rw W⟩ :: L' := rfl
    rw [e]
    have hl0 : 0 < L'.length := by rw [ih.len]; simp
    obtain ⟨s0, c0, r0, x0, o0⟩ := ih.start hl0
    refine ⟨by simp [ih.len], fun i h ↦ ?_, fun _ ↦ ⟨rfl, rfl, rfl, rfl, rfl⟩, fun i h ↦ ?_, fun _ ↦ ?_⟩
    · rcases i with _ | i
      · rfl
      · simp only [List.getD_cons_succ, List.getElem?_cons_succ]
        exact ih.level i (by simp at h; omega)
    · rcases i with _ | i
      · simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ]
        have hl := ih.level 0 hl0
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
        refine ⟨rw, W, rfl, hrl, hrok, ?_, ?_, hnext, s0, c0, ?_⟩
        · rw [x0, hxs', hxs]
        · rw [o0, hos', hos]
        · rw [r0, ← hl]
      · simp only [List.getD_cons_succ]
        have := ih.next i (by simp at h; omega)
        rwa [show index + 1 + i = index + (i + 1) by omega] at this
    · have := ih.fin hl0
      obtain ⟨n, hn⟩ : ∃ n, L'.length = n + 1 := ⟨L'.length - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel] at this
      simp only [List.length_cons, hn, Nat.add_sub_cancel, List.getD_cons_succ]
      rwa [show index + 1 + n = index + (n + 1) by omega] at this
  | [], _, _, _, _, _, _, _, _, hD => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, [], hD => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.next _ _ :: _, hD => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.fin _ _ :: _ :: _, hD => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, [], hD => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, LvD.fin _ _ :: _, hD => by simp [LvsRunD] at hD

/-- **Each level's combiners at its positions**, indexed. -/
theorem lvsAt_nz (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap : List E)
      (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
      (ds : List LvD), LvsRunD logN lane index levels s cap R xs os w ds → LvsNZ logN index levels s cap ds →
      ∀ i < (lvsAt logN index levels s cap R xs os ds).length,
        Limits.CombinersNZ (((lvsAt logN index levels s cap R xs os ds).getD i default).qs logN)
          ((lvsAt logN index levels s cap R xs os ds).getD i default).rounds
  | [level], index, s, cap, R, xs, os, w, [LvD.fin rw W], _, hN, i, h => by
    obtain rfl : i = 0 := by simp [lvsAt] at h; omega
    exact hN
  | level :: next :: rest, index, s, cap, R, xs, os, w, LvD.next rw W :: ds, hD, hN, i, h => by
    obtain ⟨xs', os', hrl, hrok, hxs, hos, hnext, hD'⟩ := hD
    have hxs' : xs.drop (rw.length + W.words.length) = xs' := by rw [hxs]; exact drop_words
    have hos' : os.tail = os' := by rw [hos]; rfl
    rcases i with _ | i
    · exact hN.1
    · have ih := lvsAt_nz logN lane (next :: rest) (index + 1) _ _ _ xs' os' w ds hD' hN.2 i
      simp only [lvsAt, List.length_cons, List.getD_cons_succ] at h ⊢
      rw [hxs', hos'] at h ⊢
      exact ih (by omega)
  | [], _, _, _, _, _, _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, [], hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.next _ _ :: _, hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.fin _ _ :: _ :: _, hD, _, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, [], hD, _, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, LvD.fin _ _ :: _, hD, _, _, _ => by simp [LvsRunD] at hD

end
end LeanVM.Guest.B1.Whir
