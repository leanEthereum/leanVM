/-
  LeanVM.Guest.B1.Whir.CInvOpen

  An accepting run of the stacked opening, level by level: what the completeness direction of
  `open_stacked` takes from `NoZeroChallenge`.
-/

module

public import LeanVM.Guest.B1.Whir.CInvLast
public import LeanVM.Guest.B1.Whir.Level
public import LeanVM.Guest.B1.Whir.CompleteIface
public import LeanVM.Guest.B1.Whir.CInvLadder
public import LeanVM.Protocol.EndToEnd.Sound.Moves

/-!
# The stacked opening, backwards

`LvsRun logN lane index levels s cap R xs os w`: the levels `levels` from the Spec's state `s`, the
carried capacity `cap` (nothing waiting) and the roots `R`, read the words `xs` and the phases `os`
and return `w`: each level's fold rounds read `6·fold` words, every round passing (`RoundsOk`);
a non-final level then reads a `NextW` with `NextOk`, and the next level runs from its glued state,
sponge and roots; the final one reads a `FinW` with `FinOk` and returns its `wend`.

`whirLevelsOpen_inv`: an accepting run of `whirLevelsOpen` refusing zero challenges is a `LvsRun`.
`whirOpen_inv`: `NoZeroChallenge`'s run is one, at the candidate's ladder; `whirOpen_end`: the
accepting run of `whirOpen` returns the same `WhirEnd`; `whirOpen_honest`: both, at every
candidate (`ladderOk_of`, Whir/CInvLadder).

`NextW.osRec`: a non-final level's record (S1a-3's `OsRec`, Whir/Level); `NextW.glued_glued`: the
level glues `recGlued` of it.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none)
open LeanVM.Protocol.EndToEnd.Sound (oodVarsPos ladder_oodVarsPos)

@[expose] public section

/-- A level's static facts the run needs: a positive rate within the windows' width, some queries. -/
def LvOk (logN : ℕ) (level : Whir.Level) : Prop :=
  1 ≤ level.logInvRate ∧ logN + level.logInvRate ≤ 128 ∧ 0 < level.queries

theorem LvOk.hP {logN g : ℕ} {level : Whir.Level} (h : LvOk logN level) :
    1 ≤ 128 / (logN - g + level.logInvRate) := by
  obtain ⟨h1, h2, -⟩ := h
  exact Nat.div_pos (by omega) (by omega)

/-- The Spec's state after a level's folds. -/
abbrev rsSt (level : Whir.Level) (s : WhirState) (cap rw : List E) : WhirState :=
  (roundsSpec level.fold s cap rw).1

/-- The level's fold rounds. -/
abbrev rsRounds (level : Whir.Level) (s : WhirState) (cap rw : List E) : List FoldRound :=
  (roundsSpec level.fold s cap rw).2

/-- The sponge after a level's folds. -/
abbrev rsF (level : Whir.Level) (cap rw : List E) : Fs := ⟨roundsCap level.fold cap rw, []⟩

/-- **The levels, read.** -/
def LvsRun (logN lane : ℕ) : ℕ → List Whir.Level → WhirState → List E → List (Digest × ℕ × ℕ) →
    List E → List (List Opening) → WhirEnd → Prop
  | _, [], _, _, _, _, _, _ => False
  | index, [level], s, cap, R, xs, os, w =>
    ∃ (rw : List E) (W : FinW), rw.length = 5 * level.fold ∧ RoundsOk level.fold cap rw ∧
      xs = rw ++ W.words ∧ os = [W.phase] ∧
      FinOk logN index level (rsSt level s cap rw) (rsRounds level s cap rw) (rsF level cap rw) R W ∧
      w = W.wend logN lane level (rsSt level s cap rw) (rsF level cap rw)
  | index, level :: next :: rest, s, cap, R, xs, os, w =>
    ∃ (rw : List E) (W : NextW) (xs' : List E) (os' : List (List Opening)),
      rw.length = 5 * level.fold ∧ RoundsOk level.fold cap rw ∧
      xs = rw ++ W.words ++ xs' ∧ os = W.phase :: os' ∧
      NextOk logN index level (rsSt level s cap rw) (rsF level cap rw) R W ∧
      LvsRun logN lane (index + 1) (next :: rest)
        (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
        (W.F3 (rsF level cap rw) (logN - (rsSt level s cap rw).alphas.length)
          (logN - (rsSt level s cap rw).alphas.length + level.logInvRate) level.queries).squeeze.2.cap
        (W.roots (logN - (rsSt level s cap rw).alphas.length) next R) xs' os' w

theorem carries_capOf (S : KeccakState) : ∃ sp, (⟨capOf S, []⟩ : Fs).Carries sp :=
  ⟨⟨S, [], none⟩, rfl, rfl, rfl⟩

theorem glued_alphas (s : WhirState) (lam : E) (mu : ℕ) (p : List E) (v : E) (qs : List ℕ) (ws : List E)
    (b : E) : (glueLevel s lam mu p v qs ws b).alphas = s.alphas := rfl

/-- **The levels, backwards.** -/
theorem whirLevelsOpen_inv (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap xs : List E)
      (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (w : WhirEnd) (R' : List (Digest × ℕ × ℕ))
      (F' : Fs), (∃ sp, (⟨cap, []⟩ : Fs).Carries sp) → R.length = index + 1 →
      (∀ l ∈ levels, LvOk logN l) → oodVarsPos (logN - s.alphas.length) levels = true →
      runTz (whirLevelsOpen logN lane index levels s) ⟨⟨cap, []⟩, none, xs, os, R⟩ =
        some (w, ⟨F', none, [], [], R'⟩) →
      LvsRun logN lane index levels s cap R xs os w
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [whirLevelsOpen, runTz] at h
  | [level], index, s, cap, xs, os, R, w, R', F', hc, hRl, hok, _, h => by
    rw [whirLevelsOpen_last] at h
    obtain ⟨p, st1, h1, h2⟩ := runTz_bind_some h
    obtain ⟨rw, xs1, hrl, hxs, hrok, ea, est⟩ := foldRounds_inv level.fold hc h1
    subst ea est
    have hl := hok level (by simp)
    obtain ⟨W, xs', orest, hxs1, hos, hfin, ea, est⟩ := levelLast_inv
      (by obtain ⟨sp, hsp⟩ := runTz_carries h1 (by obtain ⟨sp, h⟩ := hc; exact ⟨sp, h⟩)
          exact ⟨sp, tcar_none.mp hsp⟩) hl.hP hl.2.2 h2
    simp only [TSt.mk.injEq] at est
    obtain ⟨-, -, rfl, rfl, -⟩ := est
    exact ⟨rw, W, hrl, hrok, by rw [hxs, hxs1, List.append_nil], hos, hfin, ea⟩
  | level :: next :: rest, index, s, cap, xs, os, R, w, R', F', hc, hRl, hok, hv, h => by
    rw [whirLevelsOpen_next] at h
    obtain ⟨p, st1, h1, h2⟩ := runTz_bind_some h
    obtain ⟨rw, xs1, hrl, hxs, hrok, ea, est⟩ := foldRounds_inv level.fold hc h1
    subst ea est
    have hl := hok level (by simp)
    simp only [oodVarsPos, Bool.and_eq_true, decide_eq_true_eq] at hv
    have hal := roundsSpec_alphas_length level.fold s cap rw
    obtain ⟨s2, st2, h3, h4⟩ := runTz_bind_some h2
    obtain ⟨W, xs', orest, hxs1, hos, hnext, ea, est⟩ := levelNext_inv
      (by obtain ⟨sp, hsp⟩ := runTz_carries h1 (by obtain ⟨sp, h⟩ := hc; exact ⟨sp, h⟩)
          exact ⟨sp, tcar_none.mp hsp⟩) (by omega) (by rw [hal]; omega) hl.hP hl.2.2 h3
    subst ea est
    have ih := whirLevelsOpen_inv logN lane (next :: rest) (index + 1) _ _ xs' orest _ w R' F'
      (carries_capOf _) (by simp [NextW.roots, hRl]) (fun l hl' ↦ hok l (by simp_all))
      (by rw [NextW.glued, glued_alphas, hal, show logN - (s.alphas.length + level.fold) =
        logN - s.alphas.length - level.fold by omega]; exact hv.2) h4
    exact ⟨rw, W, xs', orest, hrl, hrok, by rw [hxs, hxs1, List.append_assoc], hos, hnext, ih⟩

/-- `liftOption`, backwards. -/
theorem runTz_liftOption {α β : Type} {o : Option α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runTz ((liftOption o).bind f) st = some r) :
    ∃ a, o = some a ∧ runTz (f a) st = some r := by
  cases o with
  | none =>
    change runTz VerifierProgram.fail st = some r at h
    simp [runTz] at h
  | some a => exact ⟨a, rfl, h⟩

/-- The candidate's levels' static facts. -/
def LadderOk (μ r : ℕ) : Prop := ∀ cfg, Whir.ladder μ r = some cfg → ∀ l ∈ cfg, LvOk μ l

/-- **Every candidate's levels' static facts.** -/
theorem ladderOk_of {μ r : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    LadderOk μ r := by
  intro cfg hcfg l hl
  have h := ladderRunOk_at h1 h2 h3 h4
  unfold ladderRunOk at h
  rw [hcfg] at h
  have h' := List.all_eq_true.mp h l hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

/-- **`NoZeroChallenge`'s run, level by level.** -/
theorem whirOpen_inv {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E}
    {os : List (List Opening)} {root : Digest} {w : WhirEnd} {s' : Fs}
    {roots' : List (Digest × ℕ × ℕ)} (hlad : LadderOk μ r)
    (h : RunsWith (whirOpen μ r target).refusingZeroChallenge ⟨capOf S, []⟩ xs os
      [(root, stackShape μ r)] w s' roots') :
    ∃ cfg, Whir.ladder μ r = some cfg ∧
      LvsRun μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ (capOf S)
        [(root, stackShape μ r)] xs os w := by
  have e := runT_of_runsWith h (carries_capOf S) [] []
  rw [← runTz_rz] at e
  simp only [List.append_nil] at e
  unfold whirOpen at e
  obtain ⟨cfg, hcfg, e⟩ := runTz_liftOption e
  exact ⟨cfg, hcfg, whirLevelsOpen_inv μ _ cfg 0 _ _ xs os _ w roots' s' (carries_capOf S) rfl
    (hlad cfg hcfg) (by simpa using ladder_oodVarsPos hcfg) e⟩

/-- **The accepting run returns `NoZeroChallenge`'s `WhirEnd`.** -/
theorem whirOpen_end {μ r : ℕ} {target : E} {S : KeccakState} {xs : List E}
    {os : List (List Opening)} {root : Digest} {w w' : WhirEnd} {s' s'' : Fs}
    {roots' roots'' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : RunsWith (whirOpen μ r target).refusingZeroChallenge ⟨capOf S, []⟩ xs os
      [(root, stackShape μ r)] w' s'' roots'') : w = w' := by
  have e1 := runT_of_runsWith hrun (carries_capOf S) [] []
  have e2 := runT_of_runsWith hnz (carries_capOf S) [] []
  rw [← runTz_rz] at e2
  have e3 := runTz_runT _ _ _ e2
  rw [e1] at e3
  simp only [Option.some.injEq, Prod.mk.injEq] at e3
  exact e3.1

/-- **An accepting run with no zero challenge, level by level**, at every candidate. -/
theorem whirOpen_honest {μ r : ℕ} (h1 : 22 ≤ μ) (h2 : μ ≤ 28) (h3 : 1 ≤ r) (h4 : r ≤ 4)
    {target : E} {S : KeccakState} {xs : List E} {os : List (List Opening)} {root : Digest}
    {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : NoZeroChallenge μ r target S xs os root) :
    ∃ cfg, Whir.ladder μ r = some cfg ∧
      LvsRun μ ((cfg.head?.map (·.fold)).getD 0) 0 cfg ⟨target, [], []⟩ (capOf S)
        [(root, stackShape μ r)] xs os w := by
  obtain ⟨w', s'', roots'', h⟩ := hnz
  rw [whirOpen_end hrun h]
  exact whirOpen_inv (ladderOk_of h1 h2 h3 h4) h

/-! ## S1a-3's records -/

/-- **A non-final level's record** (`OsRec`): `λ`, the folds before its claims, its message log,
its out-of-domain point, its positions, its high part. -/
def NextW.osRec (W : NextW) (logN : ℕ) (level : Whir.Level) (s : WhirState) (F : Fs) : OsRec :=
  let mu := logN - s.alphas.length
  let d := mu + level.logInvRate
  ⟨W.lam F mu d level.queries, s.alphas.length, mu, W.ood F mu, W.qs F mu d level.queries, W.high⟩

/-- **A non-final level glues its record's claims.** -/
theorem NextW.glued_glued (W : NextW) (logN index : ℕ) (level : Whir.Level) (s : WhirState) (F : Fs)
    (rounds : List FoldRound) :
    (W.glued logN index level s F rounds).glued = s.glued ++ recGlued (W.osRec logN level s F) ∧
      (W.glued logN index level s F rounds).alphas = s.alphas := by
  simp only [NextW.glued, glueLevel]
  exact ⟨rfl, trivial⟩

end
end LeanVM.Guest.B1.Whir
