module

public import LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.Extraction.AS.Lite
import all LeanVM.Protocol.EndToEnd.Sound.SkelPairs
import all LeanVM.Protocol.EndToEnd.Sound.SkelWhir
import all LeanVM.Protocol.EndToEnd.Sound.SkelFront
import all LeanVM.Protocol.EndToEnd.Sound.SkelBus
import all LeanVM.Protocol.EndToEnd.Sound.SkelLeaves
import all LeanVM.Protocol.EndToEnd.Sound.Avail
import all Statement.LeanVmVerifier

/-!
# The replay's roots

The replay of a skeleton records one root per commit, with the commit's height and width
(`roots_skelReplayP`). The body's skeleton commits the stack and then one word per level after the
first (`commitsOf_skBodyL`), so at every admissible stack size and rate there are at most six
roots, each of height at most the stack tree's and width `32` to `64` (`ladderRootsOk`).
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Verifier
open LeanVM.Extraction.AS LeanVM.Extraction.Fast LeanVM.Protocol.Compile

public section

/-- The heights and widths a skeleton commits, in order. -/
@[expose] def commitsOf : List Op → List (ℕ × ℕ)
  | [] => []
  | .commit h w :: sk => (h, w) :: commitsOf sk
  | .read :: sk => commitsOf sk
  | .sample :: sk => commitsOf sk
  | .grind _ :: sk => commitsOf sk
  | .query :: sk => commitsOf sk

theorem commitsOf_append : ∀ (a b : List Op), commitsOf (a ++ b) = commitsOf a ++ commitsOf b
  | [], _ => rfl
  | op :: a, b => by cases op <;> simp [commitsOf, commitsOf_append a b]

theorem commitsOf_eq_nil : ∀ (sk : List Op), (∀ h w, Op.commit h w ∉ sk) → commitsOf sk = []
  | [], _ => rfl
  | op :: sk, hn => by
    have ih := commitsOf_eq_nil sk fun h w hm ↦ hn h w (List.mem_cons_of_mem _ hm)
    cases op with
    | commit h w => exact absurd List.mem_cons_self (hn h w)
    | _ => simpa [commitsOf] using ih

theorem commitsOf_replicate_read (n : ℕ) : commitsOf (List.replicate n .read) = [] :=
  commitsOf_eq_nil _ fun _ _ ↦ by simp

theorem commitsOf_replicate_sample (n : ℕ) : commitsOf (List.replicate n .sample) = [] :=
  commitsOf_eq_nil _ fun _ _ ↦ by simp

/-- **The replay records the skeleton's commits as roots.** -/
theorem roots_skelReplayP (F : Semantics.KeccakState → Option Semantics.KeccakState) :
    ∀ (sk : List Op) (s : VerifierProgramState) (r : List EvP × VerifierProgramState),
      skelReplayP F sk s = some r → r.2.roots.map Prod.snd = s.roots.map Prod.snd ++ commitsOf sk
  | [], s, r, h => by
    simp only [skelReplayP, Option.some.injEq] at h
    subst h
    simp [commitsOf]
  | op :: sk, s, r, h => by
    cases op with
    | read =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨sp, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact (roots_skelReplayP F sk _ r' h').trans (by simp [commitsOf])
      · simp at h
    | sample =>
      simp only [skelReplayP] at h
      obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
      exact (roots_skelReplayP F sk _ r' h').trans (by simp [commitsOf])
    | grind b =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact (roots_skelReplayP F sk _ r' h').trans (by simp [commitsOf])
      · simp at h
    | commit ht w =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨sp0, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨sp1, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact (roots_skelReplayP F sk _ r' h').trans (by simp [commitsOf])
      · simp at h
    | query =>
      simp only [skelReplayP] at h
      split at h
      · obtain ⟨r', h', rfl⟩ := Option.map_eq_some_iff.mp h
        exact (roots_skelReplayP F sk _ r' h').trans (by simp [commitsOf])
      · simp at h

/-! ## The phases that commit nothing -/

section NoCommit

variable {h w : ℕ}

theorem not_commit_skGrind (b : ℕ) : Op.commit h w ∉ skGrind b := by
  unfold skGrind; split <;> simp

theorem not_commit_skRound (c : ℕ) (b : Bool) : Op.commit h w ∉ skRound c b := by
  cases b <;> simp [skRound, not_commit_skGrind]

theorem not_commit_skSum (c : ℕ) (eqs : List Bool) : Op.commit h w ∉ skSum c eqs := by
  simp [skSum, not_commit_skRound]

theorem not_commit_skGkrStep (step : ℕ) (last : Bool) (L : ℕ) :
    Op.commit h w ∉ skGkrStep step last L := by
  simp [skGkrStep, not_commit_skGrind, not_commit_skSum]

theorem not_commit_skGkrLayers : ∀ (n L : ℕ), Op.commit h w ∉ skGkrLayers n L
  | 0, _ => by simp [skGkrLayers]
  | 1, L => by simp [skGkrLayers, not_commit_skGkrStep]
  | n + 2, L => by
    unfold skGkrLayers
    split <;> simp [not_commit_skGkrStep, not_commit_skGkrLayers]

theorem not_commit_skBus (d : ℕ) : Op.commit h w ∉ skBus d := by
  simp [skBus, skBytecodeShare, not_commit_skGrind, not_commit_skSum, not_commit_skGkrLayers]

theorem not_commit_skTablePhaseL (hs : List ℕ) : Op.commit h w ∉ skTablePhaseL hs := by
  simp [skTablePhaseL, skTablesL, not_commit_skGrind, not_commit_skSum]

theorem not_commit_skLayer (L : ℕ) : Op.commit h w ∉ skLayer L := by
  simp [skLayer, not_commit_skGrind, not_commit_skSum]

theorem not_commit_skKeccak (L : ℕ) : Op.commit h w ∉ skKeccak L := by
  simp [skKeccak, skOpen, not_commit_skGrind, not_commit_skSum, not_commit_skLayer]

theorem not_commit_skOod (L : ℕ) : Op.commit h w ∉ skOod L := by
  simp [skOod, not_commit_skGrind]

theorem not_commit_skRing : Op.commit h w ∉ skRing := by
  simp [skRing, not_commit_skGrind]

theorem not_commit_skFoldRounds : ∀ n : ℕ, Op.commit h w ∉ skFoldRounds n
  | 0 => by simp [skFoldRounds]
  | n + 1 => by simp [skFoldRounds, skFoldRound, not_commit_skGrind, not_commit_skFoldRounds n]

end NoCommit

/-! ## The body's commits -/

/-- The commits of the levels after the first, `A` the folds made before the current one. -/
@[expose] def levelCommits (logN : ℕ) : ℕ → List Whir.Level → List (ℕ × ℕ)
  | _, [] => []
  | _, [_] => []
  | A, level :: next :: rest =>
    (logN - (A + level.fold) - next.fold + next.logInvRate, 2 * 2 ^ next.fold) ::
      levelCommits logN (A + level.fold) (next :: rest)

theorem commitsOf_skLevels (logN : ℕ) :
    ∀ (A : ℕ) (cfg : List Whir.Level), commitsOf (skLevels logN A cfg) = levelCommits logN A cfg
  | _, [] => rfl
  | A, [level] => by
    simp only [skLevels, levelCommits, commitsOf_append]
    rw [commitsOf_eq_nil _ fun _ _ ↦ not_commit_skFoldRounds _,
      commitsOf_eq_nil _ fun _ _ ↦ by simp]
    rfl
  | A, level :: next :: rest => by
    simp only [skLevels, levelCommits, commitsOf_append, commitsOf_skLevels logN (A + level.fold)]
    rw [commitsOf_eq_nil _ fun _ _ ↦ not_commit_skFoldRounds _]
    simp [skMidTail, commitsOf_append, commitsOf, commitsOf_eq_nil _ fun _ _ ↦ not_commit_skGrind _,
      commitsOf_replicate_read, commitsOf_replicate_sample]

/-- The commits of the body at a stack size and a rate: the stack's, then the levels'. -/
@[expose] def bodyCommits (logN ρ : ℕ) : List (ℕ × ℕ) :=
  commitsOf (skCommitStack logN ρ) ++
    match Whir.ladder logN ρ with
    | some cfg => levelCommits logN 0 cfg
    | none => []

theorem commitsOf_skBodyL (lay : LayoutLite) (ρ : ℕ) :
    commitsOf (skBodyL lay ρ) = bodyCommits lay.stackLog ρ := by
  simp only [skBodyL, commitsOf_append, bodyCommits]
  rw [commitsOf_eq_nil _ fun _ _ ↦ not_commit_skOod _, commitsOf_eq_nil _ fun _ _ ↦ not_commit_skBus _,
    commitsOf_eq_nil _ fun _ _ ↦ not_commit_skTablePhaseL _,
    commitsOf_eq_nil _ fun _ _ ↦ not_commit_skKeccak _, commitsOf_eq_nil _ fun _ _ ↦ not_commit_skRing]
  simp only [skWhir]
  split <;> rename_i hl <;> simp [hl, commitsOf, commitsOf_skLevels]

/-- The roots' shapes the leaves' bounds assume, at a stack of `2^logN` and rate `ρ`: at most six,
each of height at most the stack's tree's, `logN − 6 + ρ`, and width `8` to `64`, of widths summing
to at most `224`. -/
@[expose] def RootsOk (logN ρ : ℕ) (cs : List (ℕ × ℕ)) : Prop :=
  cs.length ≤ 6 ∧ (∀ c ∈ cs, c.1 ≤ logN - 6 + ρ ∧ 8 ≤ c.2 ∧ c.2 ≤ 64) ∧ (cs.map Prod.snd).sum ≤ 224

/-- **The body's commits at every admissible stack size and rate.** -/
theorem ladderRootsOk : ∀ m < 15, ∀ r < 4,
    ((bodyCommits (m + 16) (r + 1)).length ≤ 6 ∧
      ((bodyCommits (m + 16) (r + 1)).all fun c ↦ c.1 ≤ m + 16 - 6 + (r + 1) ∧ 8 ≤ c.2 ∧ c.2 ≤ 64) ∧
      ((bodyCommits (m + 16) (r + 1)).map Prod.snd).sum ≤ 224) := by
  decide +kernel

/-- **The ladder's levels at every admissible stack size and rate**: at most six, each folding at
most six variables. -/
theorem ladderFoldsOk : ∀ m < 15, ∀ r < 4,
    (((Whir.ladder (m + 16) (r + 1)).getD []).length ≤ 6 ∧
      ((Whir.ladder (m + 16) (r + 1)).getD []).all fun lv ↦ lv.fold ≤ 6) := by
  decide +kernel

theorem ladder_small {logN ρ : ℕ} {cfg : List Whir.Level} (hc : Whir.ladder logN ρ = some cfg)
    (h1 : Whir.minLogStack ≤ logN) (h2 : logN ≤ Whir.maxLogStack) (h3 : 1 ≤ ρ) (h4 : ρ ≤ 4) :
    cfg.length ≤ 6 ∧ ∀ lv ∈ cfg, lv.fold ≤ 6 := by
  have e1 : logN = (logN - 16) + 16 := by
    have : Whir.minLogStack = 16 := rfl
    omega
  have e2 : ρ = (ρ - 1) + 1 := by omega
  have hm : Whir.maxLogStack = 30 := rfl
  obtain ⟨hl, ha⟩ := ladderFoldsOk (logN - 16) (by omega) (ρ - 1) (by omega)
  rw [← e1, ← e2, hc, Option.getD_some] at hl ha
  exact ⟨hl, fun lv hlv ↦ by simpa using List.all_eq_true.mp ha lv hlv⟩

theorem rootsOk_bodyCommits {logN ρ : ℕ} (h1 : Whir.minLogStack ≤ logN) (h2 : logN ≤ Whir.maxLogStack)
    (h3 : 1 ≤ ρ) (h4 : ρ ≤ 4) : RootsOk logN ρ (bodyCommits logN ρ) := by
  have e1 : logN = (logN - 16) + 16 := by
    have : Whir.minLogStack = 16 := rfl
    omega
  have e2 : ρ = (ρ - 1) + 1 := by omega
  have hm : Whir.maxLogStack = 30 := rfl
  obtain ⟨hl, ha, hs⟩ := ladderRootsOk (logN - 16) (by omega) (ρ - 1) (by omega)
  rw [← e1, ← e2] at hl ha hs
  refine ⟨hl, fun c hc ↦ ?_, hs⟩
  simpa using List.all_eq_true.mp ha c hc

end

end LeanVM.Cost.Bounds.AS
