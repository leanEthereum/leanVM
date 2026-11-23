module

public import NativeRustcVm.Whir.Model
public import NativeRustcVm.Whir.Fold
public import NativeRustcVmArm.Layout.Ladder.Table
public import NativeVm.Math.Whir.Roots

/-!
# `whir_levels`' model, level by level

The ladder of the window (`ladderW`): level `k` folds `foldAt k`, so before level `k` the state
holds `alphasAt k` `α`s and `2 k` glued claims, and at most `6` levels. A run's results:
`foldRounds` adds its `n` `α`s and keeps the glued claims and the roots (`foldRounds_facts`),
`nextLevelM` keeps the `α`s, glues two claims and reads one root (`nextLevelM_facts`). `whirLevels`
from level `k` after its fold rounds (`run_none`, `run_final`, `run_next`).
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeVm.Model LeanVM.Parameters NativeRustcVm.Whir NativeVm.Math
open NativeRustcVmArm.Layout.Ladder

@[expose] public section

/-- The `α`s before level `k` of a ladder: `6` for level `0`, `4` for each later one. -/
def alphasAt (k : Nat) : Nat := if k = 0 then 0 else 4 * k + 2

/-- A result of a step satisfies `P`. -/
def Yields {α : Type} (P : α → Prop) (m : VM α) : Prop :=
  ∀ s y s', m.run s = some (y, s') → P y

end

public section

theorem alphasAt_succ (k : Nat) : alphasAt k + foldAt k = alphasAt (k + 1) := by
  unfold alphasAt foldAt; split_ifs <;> omega

theorem Yields.bind {α β : Type} {P : β → Prop} {m : VM α} {f : α → VM β}
    (hf : ∀ a, Yields P (f a)) : Yields P (m >>= f) := by
  intro s y s' h
  simp only [StateT.run_bind, Option.bind_eq_bind] at h
  cases hr : m.run s with
  | none => rw [hr] at h; cases h
  | some p => rw [hr, Option.bind_some] at h; exact hf p.1 _ _ _ h

theorem Yields.pure {α : Type} {P : α → Prop} {a : α} (h : P a) : Yields P (pure a : VM α) := by
  intro s y s' hr
  cases hr
  exact h

/-! ## The ladder -/

theorem ladderW_getElem {μ r i : Nat} (h : i < (ladderW μ r).length) :
    (ladderW μ r)[i] = ⟨foldAt i, r + 3 * i, qAt μ r i⟩ := by
  simp [ladderW]

theorem drop_cons {α : Type} {l : List α} {k : Nat} (h : k < l.length) :
    l.drop k = l[k] :: l.drop (k + 1) :=
  List.drop_eq_getElem_cons h

/-- The variables left at the final level `nOf μ - 1`, after its fold rounds: at most `5`. -/
theorem mu_final {μ : Nat} (h16 : 16 ≤ μ) (h : μ ≤ 30) : μ - alphasAt (nOf μ) ≤ 5 := by
  have h3 := (nOf_le μ).1
  unfold alphasAt
  simp only [show ¬nOf μ = 0 by omega, ↓reduceIte]
  unfold nOf
  split_ifs <;> omega

/-! ## Fold rounds -/

theorem foldRound_facts {w w' : WhirStateW} {r : FoldRoundW} {s s' : TState}
    (h : (foldRound w).run s = some ((w', r), s')) :
    w'.alphas.size = w.alphas.size + 1 ∧ w'.glued = w.glued := by
  rw [foldRound_run] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := h
  cases h
  simp [foldW]

theorem foldlM_facts : ∀ (l : List Nat) (acc : WhirStateW × Array FoldRoundW) (s : TState)
    (res : WhirStateW × Array FoldRoundW) (s' : TState),
    (l.foldlM (fun (acc : WhirStateW × Array FoldRoundW) _ ↦ do
      let (s, round) ← foldRound acc.1
      pure (s, acc.2.push round)) acc).run s = some (res, s') →
    res.1.alphas.size = acc.1.alphas.size + l.length ∧ res.1.glued = acc.1.glued
  | [], acc, s, res, s', h => by
    simp only [List.foldlM_nil] at h
    cases h
    simp
  | x :: l, acc, s, res, s', h => by
    simp only [List.foldlM_cons, StateT.run_bind, Option.bind_eq_bind] at h
    cases hr : (foldRound acc.1).run s with
    | none =>
      simp only [hr, Option.bind_none] at h
      cases h
    | some p =>
      obtain ⟨⟨w1, r1⟩, s1⟩ := p
      simp only [hr, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := foldRound_facts hr
      obtain ⟨h3, h4⟩ := foldlM_facts l (w1, acc.2.push r1) s1 res s' h
      simp only at h3 h4
      simp only [List.length_cons]
      exact ⟨by omega, h4.trans h2⟩

/-- **The fold rounds**: `n` more `α`s, the glued claims and the roots kept. -/
theorem foldRounds_facts {n : Nat} {w w' : WhirStateW} {rs : Array FoldRoundW} {s s' : TState}
    (h : (foldRounds n w).run s = some ((w', rs), s')) :
    w'.alphas.size = w.alphas.size + n ∧ w'.glued = w.glued ∧ s'.roots = s.roots := by
  have hr := (NativeVm.Math.Whir.foldRounds_roots n w).keeps s _ s' h
  unfold foldRounds at h
  have := foldlM_facts _ _ _ _ _ h
  simp only [List.length_range] at this
  exact ⟨this.1, this.2, hr⟩

/-! ## The next level -/

theorem nextLevelM_roots (index : Nat) (level next : Whir.Level) (mu : Nat) (w : WhirStateW)
    (rounds : Array FoldRoundW) : GrowsRoots 1 (nextLevelM index level next mu w rounds) := by
  unfold nextLevelM
  dsimp only [levelShape]
  refine (GrowsRoots.bind (b := 0) (readCommitment_roots _ _) fun _ ↦ KeepsRoots.grows ?_).mono
    (by omega)
  exact (KeepsRoots.readScalars _).bind fun _ ↦ (KeepsRoots.grind _).bind fun _ ↦
    (KeepsRoots.sampleChallenges _).bind fun _ ↦ KeepsRoots.readScalar.bind fun _ ↦
    (KeepsRoots.grind _).bind fun _ ↦ (NativeVm.Math.Whir.sampleQueries_keepsRoots _ _).bind fun _ ↦
    KeepsRoots.sampleChallenge.bind fun _ ↦ (NativeVm.Math.Whir.queryOpenings_keeps _ _).bind fun _ ↦
    KeepsRoots.pure _

theorem nextLevelM_yields (index : Nat) (level next : Whir.Level) (mu : Nat) (w : WhirStateW)
    (rounds : Array FoldRoundW) :
    Yields (fun w' : WhirStateW ↦ w'.alphas = w.alphas ∧ w'.glued.size = w.glued.size + 2)
      (nextLevelM index level next mu w rounds) := by
  unfold nextLevelM
  dsimp only [levelShape]
  exact Yields.bind fun _ ↦ Yields.bind fun _ ↦ Yields.bind fun _ ↦ Yields.bind fun _ ↦
    Yields.bind fun _ ↦ Yields.bind fun _ ↦ Yields.bind fun _ ↦ Yields.bind fun _ ↦
    Yields.bind fun _ ↦ Yields.pure ⟨rfl, by simp [glueLevel]⟩

/-- **The next level**: the `α`s kept, two glued claims more, at most one root more. -/
theorem nextLevelM_facts {index : Nat} {level next : Whir.Level} {mu : Nat} {w w' : WhirStateW}
    {rounds : Array FoldRoundW} {s s' : TState}
    (h : (nextLevelM index level next mu w rounds).run s = some (w', s')) :
    w'.alphas = w.alphas ∧ w'.glued.size = w.glued.size + 2 ∧
      s'.roots.size ≤ s.roots.size + 1 :=
  ⟨(nextLevelM_yields index level next mu w rounds s w' s' h).1,
    (nextLevelM_yields index level next mu w rounds s w' s' h).2,
    (nextLevelM_roots index level next mu w rounds).grows s w' s' h⟩

/-- `next_level` gets the next level as its fold and rate exponent. -/
theorem nextLevelM_next (index : Nat) (level next : Whir.Level) (mu : Nat) (w : WhirStateW)
    (rounds : Array FoldRoundW) :
    nextLevelM index level ⟨next.fold, next.logInvRate, 0⟩ mu w rounds =
      nextLevelM index level next mu w rounds := rfl

/-! ## The levels from `k` -/

variable {logN laneFolds index : Nat} {basis : BasisW} {level : Whir.Level} {s s' : TState}
  {w w' : WhirStateW} {rs : Array FoldRoundW}

/-- Rejected fold rounds reject. -/
theorem run_none {rest : List Whir.Level} (h : (foldRounds level.fold w).run s = none) :
    (whirLevels logN laneFolds basis index (level :: rest) w).run s = none := by
  cases rest with
  | nil => rw [whirLevels_single, StateT.run_bind, h]; rfl
  | cons next rest => rw [whirLevels_cons_cons, StateT.run_bind, h]; rfl

/-- **The last level** after its fold rounds. -/
theorem run_final (h : (foldRounds level.fold w).run s = some ((w', rs), s')) :
    (whirLevels logN laneFolds basis index [level] w).run s =
      (finalLevelM index level (logN - w'.alphas.size) laneFolds basis w' rs).run s' := by
  rw [whirLevels_single, StateT.run_bind, h]; rfl

/-- **A level before the last** after its fold rounds. -/
theorem run_next {next : Whir.Level} {rest : List Whir.Level}
    (h : (foldRounds level.fold w).run s = some ((w', rs), s')) :
    (whirLevels logN laneFolds basis index (level :: next :: rest) w).run s =
      ((nextLevelM index level next (logN - w'.alphas.size) w' rs).run s').bind fun p ↦
        (whirLevels logN laneFolds basis (index + 1) (next :: rest) p.1).run p.2 := by
  rw [whirLevels_cons_cons, StateT.run_bind, h]
  rfl

end

end NativeRustcVmArm.Whir.WhirLevels
