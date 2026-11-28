module

public import NativeRustcVm.Whir.Model
public import NativeRustcVm.Whir.Fold
public import NativeRustcVm.Rodata
public import NativeVm.Math.Whir.Roots

/-!
# `whir_levels`' model, level by level (arch-independent)

The ladder of the window (`ladderW`, `ladder_eq`): inside it (`Whir.Admissible μ r`),
`Whir.ladder μ r` has `nOf μ` levels, level `i` folding `foldAt i` variables at rate `r + 3 i`
with `qAt μ r i` queries, checked on the window by `decide +kernel`. Before level `k` the state
holds `alphasAt k` `α`s and `2 k` glued claims. A run's results: `foldRounds` adds its `n` `α`s and
keeps the glued claims and the roots (`foldRounds_facts`), `nextLevelM` keeps the `α`s, glues two
claims and reads one root (`nextLevelM_facts`). `whirLevels` from level `k` after its fold rounds
(`run_none`, `run_final`, `run_next`). The same facts as the AArch64 proof's
(`NativeRustcVmArm.Layout.Ladder.Table`, `NativeRustcVmArm.Whir.WhirLevels.Model`), restated here
so that the x86-64 proofs import no AArch64 module.
-/

namespace NativeRustcVmX64.Whir.Levels

open NativeVm.Model LeanVM.Parameters NativeRustcVm.Whir NativeVm.Math NativeRustcVm

@[expose] public section

/-- The level count of a `μ`-variable stack. -/
def nOf (μ : Nat) : Nat := if μ < 20 then 3 else if μ < 24 then 4 else if μ < 28 then 5 else 6

/-- `QUERY_TABLE`'s `i`th query count of the entry `(r - 1, μ - 16)`. -/
def qAt (μ r i : Nat) : Nat :=
  Data.queryTable.flatten.flatten.getD (90 * (r - 1) + 6 * (μ - 16) + i) 0

/-- Level `i`'s fold. -/
def foldAt (i : Nat) : Nat := if i = 0 then 6 else 4

/-- The ladder of the window. -/
def ladderW (μ r : Nat) : List Whir.Level :=
  (List.range (nOf μ)).map fun i ↦ ⟨foldAt i, r + 3 * i, qAt μ r i⟩

/-- Level `k` of the ladder `ladderW μ r`. -/
abbrev lvl (μ r k : Nat) : Whir.Level := ⟨foldAt k, r + 3 * k, qAt μ r k⟩

/-- The `α`s before level `k` of a ladder: `6` for level `1`, `4` for each later one. -/
def alphasAt (k : Nat) : Nat := if k = 0 then 0 else 4 * k + 2

/-- A result of a step satisfies `P`. -/
def Yields {α : Type} (P : α → Prop) (m : VM α) : Prop :=
  ∀ s y s', m.run s = some (y, s') → P y

end

public section

theorem ladder_table : ∀ μ < 31, ∀ r < 5, Whir.Admissible μ r →
    Whir.ladder μ r = some (ladderW μ r) := by
  decide +kernel

theorem queries_le : ∀ j < 360, Data.queryTable.flatten.flatten.getD j 0 ≤ 230 := by
  decide +kernel

theorem length_table : Data.queryTable.flatten.flatten.length = 360 := by decide +kernel

theorem admissible_iff {μ r : Nat} : Whir.Admissible μ r ↔ 16 ≤ μ ∧ μ ≤ 30 ∧ 1 ≤ r ∧ r ≤ 4 :=
  Iff.rfl

theorem ladder_eq {μ r : Nat} (h : Whir.Admissible μ r) :
    Whir.ladder μ r = some (ladderW μ r) := by
  have := admissible_iff.mp h
  exact ladder_table μ (by omega) r (by omega) h

theorem ladder_none {μ r : Nat} (h : ¬Whir.Admissible μ r) : Whir.ladder μ r = none := by
  simp [Whir.ladder, h]

theorem qAt_le (μ r i : Nat) : qAt μ r i ≤ 230 := by
  unfold qAt
  rcases Nat.lt_or_ge (90 * (r - 1) + 6 * (μ - 16) + i) 360 with h | h
  · exact queries_le _ h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_table]; exact h)]
    simp

theorem nOf_le (μ : Nat) : 3 ≤ nOf μ ∧ nOf μ ≤ 6 := by
  unfold nOf; split_ifs <;> omega

theorem length_ladderW (μ r : Nat) : (ladderW μ r).length = nOf μ := by
  simp [ladderW]

theorem ladderW_getElem {μ r i : Nat} (h : i < (ladderW μ r).length) :
    (ladderW μ r)[i] = lvl μ r i := by
  simp [ladderW]

theorem drop_cons {α : Type} {l : List α} {k : Nat} (h : k < l.length) :
    l.drop k = l[k] :: l.drop (k + 1) :=
  List.drop_eq_getElem_cons h

theorem alphasAt_succ (k : Nat) : alphasAt k + foldAt k = alphasAt (k + 1) := by
  unfold alphasAt foldAt; split_ifs <;> omega

/-- The variables left at the final level `nOf μ - 1`, after its fold rounds: at most `5`. -/
theorem mu_final {μ : Nat} (h16 : 16 ≤ μ) (h : μ ≤ 30) : μ - alphasAt (nOf μ) ≤ 5 := by
  have h3 := (nOf_le μ).1
  unfold alphasAt
  simp only [show ¬nOf μ = 0 by omega, ↓reduceIte]
  unfold nOf
  split_ifs <;> omega

/-- Before a non-final level's `next_level`, `μ` at most `30` and the `α`s at most `logN`. -/
theorem alphas_le {μ k : Nat} (h16 : 16 ≤ μ) (h : μ ≤ 30) (hk : k + 1 < nOf μ) :
    alphasAt (k + 1) ≤ μ := by
  unfold alphasAt nOf at *
  split_ifs at * <;> omega

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

end NativeRustcVmX64.Whir.Levels
