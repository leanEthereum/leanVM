/-
  LeanVM.Protocol.Rpm.Cost

  The permutation calls of the leanVM verifier and of the honest prover: every Keccak-256 input
  has at most `2^39 + 9` bytes, so every query costs at most `2^32` permutation calls.
-/

import LeanVM.Protocol.Verifier.WhirTarget
import LeanVM.Protocol.Verifier.Claims
import LeanVM.Protocol.LeanVM
import Statement.LeanVm
import Common.Transfer
import LeanVM.Facts.Verifier
import Statement.Fast.Keccak
import Statement.Fast.QuadExt
import Statement.Fast.FieldWords
import Common.Prob
import LeanVM.Protocol.WithHash

/-!
# The permutation calls of the verifier and the honest prover

In the random-permutation model a Keccak-256 hash of `n` bytes costs `⌊n / 136⌋ + 1` calls of the
permutation, one per block of the padded message, and a direct permutation call costs one
(`hashBlocks`). Every hash the verifier and the honest prover compute has at most `2^39 + 9`
bytes (`Short`): the IV's preimage (the `9`-byte version tag, then the bytecode, `16 · 2^logSize`
words of `8` bytes, `logSize ≤ 32`), Merkle nodes (`64` bytes) and Merkle leaves (`8 · width`
bytes, every commitment of the leanVM verifier program having width at most `192`, `WidthsLE`).
So every query costs at most `⌊(2^39 + 9) / 136⌋ + 1 ≤ 2^32` calls, and a computation of `N`
queries at most `N · 2^32` (`isWeightBound_of_isTotalQueryBound`):

* `isWeightBound_verifier`: the verifier, `13261` queries, at most `verifierPermCalls`;
* `isWeightBound_honest`: the honest prover then the verifier, `completenessQueries fuel =
  13263 + 53036 · (2^27 + 2·fuel + 2)` queries, at most `completenessPermCalls fuel`.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Prover (Tree buildTreeWithHash leafDigestsWithHash parentsWithHash levelsWithHash searchM findNonceM)
open OracleComp OracleSpec

/-- The permutation calls of a query: a Keccak-256 hash of `n` bytes costs `⌊n / 136⌋ + 1`
(one per block of the padded message), a permutation one. -/
def hashBlocks : KeccakCalls.Domain → ℕ
  | .inl x => x.length / 136 + 1
  | .inr _ => 1

/-- A short query: a hash of at most `2^39 + 9` bytes, or a permutation. -/
def Short : KeccakCalls.Domain → Prop
  | .inl x => x.length ≤ 2 ^ 39 + 9
  | .inr _ => True

/-- A short query costs at most `2^32` permutation calls. -/
theorem hashBlocks_le_of_short {t : KeccakCalls.Domain} (h : Short t) : hashBlocks t ≤ 2 ^ 32 := by
  rcases t with x | s
  · simp only [Short] at h
    simp only [hashBlocks]
    omega
  · simp [hashBlocks]

/-! ## Weights from counts -/

/-- **A count bound and a per-query weight bound give a weight bound.** -/
theorem isWeightBound_of_isTotalQueryBound {ι : Type} {spec : OracleSpec ι} {α : Type}
    (w : ι → ℕ) (B : ℕ) {X : OracleComp spec α} {N : ℕ} (hN : IsTotalQueryBound X N)
    (hX : AllQueriesSatisfy X fun t ↦ w t ≤ B) : Common.QueryCostAtMost X w (N * B) := by
  induction X using OracleComp.inductionOn generalizing N with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at hN
    rw [allQueriesSatisfy_query_bind_iff] at hX
    rw [Common.isWeightBound_query_bind_iff]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have h1 := hX.1
    refine ⟨by rw [Nat.succ_mul]; omega, fun u ↦ (ih u (hN.2 u) (hX.2 u)).mono ?_⟩
    rw [Nat.succ_mul, Nat.add_sub_cancel]
    omega

/-! ## Short queries -/

theorem allQ_queryF (s : KeccakState) : AllQueriesSatisfy (callKeccakF1600 s) Short :=
  (allQueriesSatisfy_query_iff (spec := KeccakCalls) (.inr s) Short).mpr trivial

theorem allQ_queryH {x : Bytes} (hx : x.length ≤ 2 ^ 39 + 9) :
    AllQueriesSatisfy (callKeccak256 x) Short :=
  (allQueriesSatisfy_query_iff (spec := KeccakCalls) (.inl x) Short).mpr hx

theorem allQ_queryH₀ {x : Bytes} (hx : x.length ≤ 2 ^ 39) : AllQueriesSatisfy (callKeccak256 x) Short :=
  allQ_queryH (hx.trans (Nat.le_add_right _ _))

theorem allQ_pure {α : Type} (a : α) : AllQueriesSatisfy (pure a : OracleComp KeccakCalls α) Short :=
  trivial

theorem flatMap_kBytes_length (l : List K) : (l.flatMap K.toBytes).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, kBytes_length, ih]; ring

theorem pair_length (a b : Digest) : (digestBytes a ++ digestBytes b).length ≤ 2 ^ 39 := by
  simp [digestBytes_length]

theorem bytecodeWords_length (prog : LeanIsaProgram) :
    (bytecodeWords prog).length = 16 * 2 ^ prog.logSize := by
  simp [bytecodeWords, List.length_flatMap]
  omega

theorem bytecode_length (prog : LeanIsaProgram) :
    ((bytecodeWords prog).flatMap K.toBytes).length ≤ 2 ^ 39 := by
  rw [flatMap_kBytes_length, bytecodeWords_length]
  have h1 : 2 ^ prog.logSize ≤ 2 ^ 32 :=
    Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have : (2 : ℕ) ^ 39 = 8 * (16 * 2 ^ 32) := by norm_num
  rw [this]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)

/-! ## The widths of the commitments -/

/-- Every commitment of a program has width at most `W`. -/
def WidthsLE (W : ℕ) {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, WidthsLE W (k x)
  | .sample k => ∀ x, WidthsLE W (k x)
  | .grind _ k => WidthsLE W k
  | .commit _ w k => w ≤ W ∧ WidthsLE W k
  | .query _ _ k => ∀ rows, WidthsLE W (k rows)

namespace WidthsLE

variable {W : ℕ} {α β : Type}

theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : WidthsLE W p) (hf : ∀ a,
    WidthsLE W (f a)) :
    WidthsLE W (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ⟨hp.1, ih hp.2⟩
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

theorem seq {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : WidthsLE W p) (hf : ∀ a,
    WidthsLE W (f a)) :
    WidthsLE W (p >>= f) :=
  bind hp hf

/-- A program without commitments. -/
theorem of_moves {g : ℕ → Prop} {Q G : α → Prop} {p : VerifierProgram α}
    (h : Moves g False Q G p) : WidthsLE W p := by
  induction p with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (h x)
  | sample k ih => exact fun x ↦ ih x (h x)
  | grind b k ih => exact ih h.2.2
  | commit ht w k ih => exact h.1.elim
  | query i ps k ih => exact fun rows ↦ ih rows (h rows)

theorem fail : WidthsLE W (VerifierProgram.fail : VerifierProgram α) := trivial

theorem commitP {ht w : ℕ} (hw : w ≤ W) : WidthsLE W (VerifierProgram.readCommitment ht w) := ⟨hw,
    trivial⟩

/-- A pure step that may fail, then a continuation at its value. -/
theorem liftOption_seq {o : Option α} {f : α → VerifierProgram β} (hf : ∀ a, o = some a → WidthsLE W
    (f a)) :
    WidthsLE W (liftOption o >>= f) := by
  cases o with
  | none => trivial
  | some a => exact hf a rfl

end WidthsLE

/-- Every level of an admissible ladder folds at most `6` variables; decided over the 56
admissible pairs. -/
theorem ladder_folds (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) : ∀ l ∈ levels, l.fold ≤ 6 := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels →
          (levels.all fun l ↦ decide (l.fold ≤ 6)) = true := by
      decide +kernel
    have hk := key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
    simpa using hk
  · simp [Whir.ladder, hadm] at h

/-- The width bound of the leanVM verifier program's commitments: `2 · 2^6`, the two limbs of a
level's folded lanes. -/
def maxWidth : ℕ := 128

theorem two_pow_le {f : ℕ} (h : f ≤ 6) : 2 * 2 ^ f ≤ maxWidth := by
  have : 2 ^ f ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h
  unfold maxWidth; omega

theorem pow_le {f : ℕ} (h : f ≤ 6) : 2 ^ f ≤ maxWidth := by
  have : 2 ^ f ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h
  unfold maxWidth; omega

section Phases

attribute [local irreducible] WidthsLE Moves

theorem widthsLE_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState), (∀ l ∈ levels, l.fold ≤ 6) →
      WidthsLE maxWidth (whirLevels logN laneFolds evaluateBasis index levels s)
  | [], _, _, _ => by unfold whirLevels; exact WidthsLE.fail
  | [level], index, s, _ => by
    refine WidthsLE.seq (WidthsLE.of_moves (moves_foldRounds level.fold s)) fun r ↦ ?_
    obtain ⟨s', rounds⟩ := r
    exact WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True)
      (G := fun _ ↦ False) (Moves.readN _)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (Q := fun _ ↦ True) (G := fun _ ↦ True)
        (Moves.grindP (g := fun _ ↦ True) fun _ ↦ trivial)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (moves_sampleQueriesAux _ _ _)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True) (Q := fun _ ↦ True)
        (G := fun _ ↦ False) (Moves.queryP _ _)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True) (G := fun _ ↦ False)
        (Moves.require _)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (moves_sumcheck (by norm_num) _ _)) fun r ↦ by
        obtain ⟨tail, claim⟩ := r
        exact WidthsLE.of_moves (g := fun _ ↦ True) (G := fun _ ↦ False) (Moves.require _)
  | level :: next :: rest, index, s, hf => by
    have hn : next.fold ≤ 6 := hf next (by simp)
    refine WidthsLE.seq (WidthsLE.of_moves (moves_foldRounds level.fold s)) fun r ↦ ?_
    obtain ⟨s', rounds⟩ := r
    exact WidthsLE.seq (WidthsLE.commitP (two_pow_le hn))
      fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True)
        (G := fun _ ↦ False) (Moves.readN _)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (moves_sampleOodPoints _ _)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True)
        (G := fun _ ↦ False) (Moves.readN _)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (Q := fun _ ↦ True) (G := fun _ ↦ True)
        (Moves.grindP (g := fun _ ↦ True) fun _ ↦ trivial)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (moves_sampleQueriesAux _ _ _)) fun queries ↦
      WidthsLE.seq (WidthsLE.of_moves (Q := fun _ ↦ True) (G := fun _ ↦ True)
        (Moves.grindP (g := fun _ ↦ True) fun _ ↦ trivial)) fun _ ↦
      WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True) (G := fun _ ↦ False)
        Moves.sampleE) fun lam ↦
      WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True) (Q := fun _ ↦ True)
        (G := fun _ ↦ False) (Moves.queryP index queries)) fun words ↦
        widthsLE_whirLevels logN laneFolds evaluateBasis (next :: rest) (index + 1) _
          fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)

theorem widthsLE_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) :
    WidthsLE maxWidth (verifyWhir logN logInvRate target evaluateBasis) :=
  WidthsLE.liftOption_seq fun config hc ↦
    widthsLE_whirLevels logN _ evaluateBasis config 0 _ (ladder_folds _ _ _ hc)

theorem widthsLE_commitStack (logN logInvRate : ℕ) :
    WidthsLE maxWidth (commitStack logN logInvRate) :=
  WidthsLE.liftOption_seq fun config hc ↦ by
    cases config with
    | nil => exact WidthsLE.fail
    | cons level rest =>
      exact WidthsLE.commitP (pow_le (ladder_folds _ _ _ hc level (by simp)))

/-- The commitment's out-of-domain sample commits nothing. -/
theorem widthsLE_readOod (n : ℕ) : WidthsLE maxWidth (readOod n) :=
  WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True) (Q := fun _ ↦ True) (G := fun _ ↦ True)
    (Moves.grindP fun _ ↦ trivial)) fun _ ↦
    WidthsLE.of_moves (g := fun _ ↦ True) (G := fun _ ↦ False)
      (Moves.seq' (Moves.sampleN _) fun _ _ ↦ Moves.seq' Moves.readE fun _ _ ↦
        Moves.pure (Q := fun _ ↦ True) trivial)

theorem widthsLE_verifyExecution (bytecode : List K) (publicInput : Digest) :
    WidthsLE maxWidth (verifyExecution computedBytecodeValue bytecode publicInput) := by
  refine WidthsLE.seq (WidthsLE.of_moves (moves_readSizes bytecode)) fun p ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := p
  refine WidthsLE.seq (widthsLE_commitStack _ _) fun _ ↦
    WidthsLE.seq (widthsLE_readOod _) fun _ ↦
    WidthsLE.seq (WidthsLE.of_moves (moves_verifyBusBalance moves_computedBytecodeValue layout))
      fun bus ↦
      WidthsLE.seq (WidthsLE.of_moves (moves_tablePhase layout bus)) fun _ ↦
        WidthsLE.seq (WidthsLE.of_moves (moves_publicInputPhase layout publicInput)) fun _ ↦
          WidthsLE.seq (WidthsLE.of_moves (moves_keccakPhase _ _)) fun r ↦ ?_
  obtain ⟨claims, keccakPoint, keccakSlices⟩ := r
  refine WidthsLE.seq (WidthsLE.of_moves (moves_ringSwitch keccakPoint keccakSlices)) fun r ↦ ?_
  obtain ⟨ringTarget, ringWeight⟩ := r
  dsimp only
  rw [verifyStackedOpening_eq]
  exact WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True) (G := fun _ ↦ False)
    (Moves.require _)) fun _ ↦
    WidthsLE.seq (WidthsLE.of_moves (g := fun _ ↦ True) (G := fun _ ↦ False) Moves.sampleE)
      fun _ ↦ widthsLE_verifyWhir _ _ _ _

end Phases

/-- **Every commitment of the leanVM verifier program has width at most `128`.** -/
theorem widthsLE_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    WidthsLE maxWidth (leanVmVerifierProgram bytecode publicInput) :=
  WidthsLE.seq (widthsLE_verifyExecution bytecode publicInput) fun _ ↦ trivial

/-! ## The verifier's queries -/

section Verifier

theorem allQ_duplex (sp : Sponge) : AllQueriesSatisfy (duplex callKeccakF1600 sp) Short :=
  allQueriesSatisfy_bind (allQ_queryF _) fun _ ↦ allQ_pure _

theorem allQ_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    AllQueriesSatisfy (Compile.absorb callKeccakF1600 sp x tag) Short := by
  unfold Compile.absorb
  split
  · exact allQueriesSatisfy_bind (allQ_duplex sp) fun _ ↦ allQ_pure _
  · exact allQueriesSatisfy_bind (allQ_pure _) fun _ ↦ allQ_pure _

theorem allQ_squeeze (sp : Sponge) : AllQueriesSatisfy (squeeze callKeccakF1600 sp) Short := by
  unfold squeeze
  split
  · exact allQ_pure _
  · exact allQueriesSatisfy_bind (allQ_duplex sp) fun _ ↦ allQ_pure _

theorem allQ_absorbNonce (sp : Sponge) (n : E) :
    AllQueriesSatisfy (absorbNonce callKeccakF1600 sp n) Short :=
  allQueriesSatisfy_bind (allQ_absorb _ _ _) fun _ ↦
    allQueriesSatisfy_bind (allQ_duplex _) fun _ ↦ allQ_pure _

theorem allQ_climb : ∀ (node : Digest) (q : ℕ) (ss : List Digest),
    AllQueriesSatisfy (climbWithHash callKeccak256 node q ss) Short
  | _, _, [] => trivial
  | node, q, s :: ss => by
    simp only [climbWithHash]
    split <;>
      exact allQueriesSatisfy_bind (allQ_queryH₀ (pair_length _ _)) fun _ ↦ allQ_climb _ _ ss

theorem allQ_openOne (root : Digest) (height width q : ℕ) (o : Opening)
    (hw : width ≤ maxWidth) : AllQueriesSatisfy (openOneWithHash callKeccak256 root height width q o) Short := by
  unfold openOneWithHash
  split
  · rename_i h
    refine allQueriesSatisfy_bind (allQ_queryH ?_) fun _ ↦
      allQueriesSatisfy_bind (allQ_climb _ _ _) fun _ ↦ trivial
    rw [flatMap_kBytes_length, h.1]
    unfold maxWidth at hw
    omega
  · trivial

theorem allQ_openAll (root : Digest) (height width : ℕ) (hw : width ≤ maxWidth) :
    ∀ (ps : List ℕ) (os : List Opening),
      AllQueriesSatisfy (openAllWithHash callKeccak256 root height width ps os) Short
  | [], _ => trivial
  | _ :: _, [] => trivial
  | q :: qs, o :: os => by
    simp only [openAllWithHash]
    refine allQueriesSatisfy_bind (allQ_openOne _ _ _ _ _ hw) fun b ↦ ?_
    split
    · exact allQueriesSatisfy_bind (allQ_openAll root height width hw qs os) fun _ ↦ trivial
    · trivial

theorem allQ_openPhase (root : Digest) (height width : ℕ) (hw : width ≤ maxWidth) (ps : List ℕ)
    (phase : List Opening) :
    AllQueriesSatisfy (openPhaseWithHash callKeccak256 root height width ps phase) Short := by
  unfold openPhaseWithHash
  split
  · exact allQueriesSatisfy_bind (allQ_openAll root height width hw ps phase) fun _ ↦ by
      split <;> trivial
  · trivial

theorem allQ_run {α : Type} : ∀ (P : VerifierProgram α) (s : VerifierProgramState), WidthsLE
    maxWidth P →
    (∀ r ∈ s.roots, r.2.2 ≤ maxWidth) → AllQueriesSatisfy (Compile.runWithHash callKeccak256 callKeccakF1600 P s) Short
  | .ret _, _, _, _ => trivial
  | .fail, _, _, _ => trivial
  | .read k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · exact allQueriesSatisfy_bind (allQ_absorb _ _ _) fun sp ↦ allQ_run _ _ (hP _) hr
    · trivial
  | .sample k, s, hP, hr => by
    simp only [Compile.runWithHash]
    refine allQueriesSatisfy_bind (allQ_squeeze _) fun r ↦ ?_
    obtain ⟨c, sp⟩ := r
    exact allQ_run _ _ (hP _) hr
  | .grind bits k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · refine allQueriesSatisfy_bind (allQ_absorbNonce _ _) fun r ↦ ?_
      obtain ⟨c, sp'⟩ := r
      split
      · exact allQ_run _ _ hP hr
      · trivial
    · trivial
  | .commit height width k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · refine allQueriesSatisfy_bind (allQ_absorb _ _ _) fun sp ↦
        allQueriesSatisfy_bind (allQ_absorb _ _ _) fun sp' ↦ ?_
      refine allQ_run _ _ hP.2 fun r hr' ↦ ?_
      rcases List.mem_append.mp hr' with h | h
      · exact hr r h
      · simp only [List.mem_singleton] at h
        subst h
        exact hP.1
    · trivial
  | .query i ps k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · rename_i root height width phase rest hi _
      refine allQueriesSatisfy_bind (allQ_openPhase root height width
        (hr _ (List.mem_of_getElem? hi)) ps phase) fun o ↦ ?_
      split
      · exact allQ_run _ _ (hP _) hr
      · trivial
    · trivial

theorem allQ_runProof (P : VerifierProgram Bool) (seed : KeccakState) (π : Proof) (hP : WidthsLE
    maxWidth P) :
    AllQueriesSatisfy (runProofWithHash callKeccak256 callKeccakF1600 P seed π) Short := by
  unfold runProofWithHash
  refine allQueriesSatisfy_bind (allQ_run P _ hP fun r hr ↦ by simp at hr) fun o ↦ ?_
  split <;> trivial

theorem allQ_hsRun : ∀ (fs : List (List Digest → Bytes)) (ds : List Digest),
    (∀ f ∈ fs, ∀ ds, (f ds).length ≤ 2 ^ 39 + 9) →
      AllQueriesSatisfy (Seed.hsRun callKeccak256 fs ds) Short
  | [], _, _ => trivial
  | f :: fs, ds, h => by
    simp only [Seed.hsRun]
    exact allQueriesSatisfy_bind (allQ_queryH (h f (by simp) ds)) fun d ↦
      allQ_hsRun fs _ fun g hg ↦ h g (List.mem_cons_of_mem _ hg)

/-- `TAG` is nine bytes. -/
theorem versionTag_length : versionTag.length = 9 := by decide +kernel

theorem allQ_seedRun (prog : LeanIsaProgram) (input : PublicInput) :
    AllQueriesSatisfy ((leanVmSeed (bytecodeWords prog) (publicInputDigest input)).run callKeccak256 callKeccakF1600)
      Short := by
  refine allQueriesSatisfy_bind (allQ_hsRun _ _ fun f hf ds ↦ ?_) fun _ ↦ allQ_queryF _
  simp only [leanVmSeed, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  rw [List.length_append, versionTag_length]
  have := bytecode_length prog
  omega

/-- The verifier of the statement is the seeded verifier at the leanVM seed and program. -/
theorem verifier_eq (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    verifierWithHash callKeccak256 callKeccakF1600 prog input proof =
      verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) proof :=
  (verifierComp_leanVm _ _ _).symm

theorem allQ_verifier (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    AllQueriesSatisfy (verifierWithHash callKeccak256 callKeccakF1600 prog input proof) Short := by
  rw [verifier_eq]
  exact allQueriesSatisfy_bind (allQ_seedRun prog input) fun seed ↦
    allQ_runProof _ seed proof (widthsLE_leanVmProgram _ _)

/-- **The verifier makes at most `verifierPermCalls` permutation calls** on every statement and
proof. -/
theorem isWeightBound_verifier (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    Common.QueryCostAtMost (verifierWithHash callKeccak256 callKeccakF1600 prog input proof) hashBlocks
      verifierPermCalls := by
  have hN := isTotalQueryBound_leanVm (bytecodeWords prog) (publicInputDigest input) proof
  rw [leanVmQueryBound_eq, ← verifier_eq] at hN
  exact isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) hN
    ((allQ_verifier prog input proof).mono fun _ h ↦ hashBlocks_le_of_short h)

end Verifier

/-! ## The honest prover's queries -/

section Prover

theorem allQ_mapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) :
    ∀ l : List β, (∀ a ∈ l, AllQueriesSatisfy (f a) Short) →
      AllQueriesSatisfy (l.mapM f) Short
  | [], _ => by rw [List.mapM_nil]; exact allQ_pure _
  | a :: l, h => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (h a (by simp)) fun b ↦
      allQueriesSatisfy_bind (allQ_mapM f l fun a' ha' ↦ h a' (List.mem_cons_of_mem _ ha'))
        fun _ ↦ allQ_pure _

theorem allQ_arrayMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (xs : Array β)
    (h : ∀ a ∈ xs.toList, AllQueriesSatisfy (f a) Short) :
    AllQueriesSatisfy (xs.mapM f) Short := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQ_mapM f _ h) fun _ ↦ allQ_pure _

theorem allQ_parentsM (level : Array Digest) (n : ℕ) :
    AllQueriesSatisfy (parentsWithHash callKeccak256 level n) Short :=
  allQ_arrayMapM _ _ fun _ _ ↦ allQ_queryH₀ (pair_length _ _)

theorem allQ_levelsM : ∀ (k : ℕ) (level : Array Digest),
    AllQueriesSatisfy (levelsWithHash callKeccak256 k level) Short
  | 0, _ => allQ_pure _
  | k + 1, level => by
    simp only [levelsWithHash]
    exact allQueriesSatisfy_bind (allQ_parentsM _ _) fun _ ↦
      allQueriesSatisfy_bind (allQ_levelsM k _) fun _ ↦ allQ_pure _

/-- Rows of at most `maxWidth` words. -/
def RowsLE (word : Word) : Prop := ∀ p, (word p).length ≤ maxWidth

theorem row_length {word : Word} (hw : RowsLE word) (p : ℕ) :
    ((word p).flatMap K.toBytes).length ≤ 2 ^ 39 := by
  rw [flatMap_kBytes_length]
  have := hw p
  unfold maxWidth at this
  omega

theorem allQ_leafDigestsM (height : ℕ) {word : Word} (hw : RowsLE word) :
    AllQueriesSatisfy (leafDigestsWithHash callKeccak256 height word) Short :=
  allQ_arrayMapM _ _ fun i _ ↦ allQ_queryH₀ (row_length hw i)

theorem allQ_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), AllQueriesSatisfy (searchM callKeccakF1600 bits sp n count) Short
  | 0, _ => allQ_pure _
  | count + 1, n => by
    simp only [searchM]
    refine allQueriesSatisfy_bind (allQ_absorbNonce _ _) fun r ↦ ?_
    split
    · exact allQ_pure _
    · exact allQ_searchM bits sp count (n + 1)

theorem allQ_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    AllQueriesSatisfy (findNonceM callKeccakF1600 bits sp fuel) Short := by
  unfold findNonceM
  exact allQ_searchM _ _ _ _

/-- **Locality**: the words a strategy commits along the run from `h` depend on the challenges
only at the histories extending `h`. -/
theorem shapedFrom_congr (S : Strategy) {chal₁ chal₂ : List Ev → E} {α : Type} :
    ∀ (P : VerifierProgram α) (h : List Ev), (∀ h', h <+: h' → chal₁ h' = chal₂ h') →
      (S.ShapedFrom chal₁ P h ↔ S.ShapedFrom chal₂ P h)
  | .ret _, _, _ => Iff.rfl
  | .fail, _, _ => Iff.rfl
  | .read k, h, hc => by
    simp only [Strategy.ShapedFrom]
    exact shapedFrom_congr S _ _ fun h' hh' ↦ hc h' ((List.prefix_append _ _).trans hh')
  | .sample k, h, hc => by
    simp only [Strategy.ShapedFrom]
    rw [hc h (List.prefix_refl h)]
    exact shapedFrom_congr S _ _ fun h' hh' ↦ hc h' ((List.prefix_append _ _).trans hh')
  | .grind _ k, h, hc => by
    simp only [Strategy.ShapedFrom]
    exact shapedFrom_congr S _ _ fun h' hh' ↦ hc h' ((List.prefix_append _ _).trans hh')
  | .commit _ _ k, h, hc => by
    simp only [Strategy.ShapedFrom]
    exact and_congr_right fun _ ↦
      shapedFrom_congr S _ _ fun h' hh' ↦ hc h' ((List.prefix_append _ _).trans hh')
  | .query i ps k, h, hc => by
    simp only [Strategy.ShapedFrom]
    split
    · exact shapedFrom_congr S _ _ fun h' hh' ↦ hc h' ((List.prefix_append _ _).trans hh')
    · exact Iff.rfl

/-- After a sample, the run from the extended history is shaped for every challenge. -/
theorem shaped_sample (S : Strategy) {α : Type} {k : E → VerifierProgram α} {h : List Ev}
    (hG : ∀ chal, S.ShapedFrom chal (.sample k) h) (c : E) (chal : List Ev → E) :
    S.ShapedFrom chal (k c) (h ++ [Ev.sample c]) := by
  classical
  let chal' : List Ev → E := fun h' ↦ if h' = h then c else chal h'
  have h1 := hG chal'
  simp only [Strategy.ShapedFrom] at h1
  have hc : chal' h = c := by simp [chal']
  rw [hc] at h1
  refine (shapedFrom_congr S _ _ fun h' hh' ↦ ?_).mp h1
  have hne : h' ≠ h := by
    rintro rfl
    have := hh'.length_le
    simp at this
  simp [chal', hne]

/-- Every word committed in a history has rows of at most `maxWidth` words. -/
def HistOK (h : List Ev) : Prop := ∀ c ∈ commits h, RowsLE c.2.2

theorem histOK_append_of_nil {h : List Ev} (e : Ev) (he : commits [e] = []) (hh : HistOK h) :
    HistOK (h ++ [e]) := by
  intro c hc
  rw [commits_append, he, List.append_nil] at hc
  exact hh c hc

/-- The trees the prover carries are those of the history's commitments: the same heights and
words, in order. -/
def TreesOK (cs : List Tree) (h : List Ev) : Prop :=
  cs.map (fun t ↦ (t.height, t.word)) = (commits h).map fun c ↦ (c.1, c.2.2)

theorem treesOK_append_of_nil {cs : List Tree} {h : List Ev} (e : Ev) (he : commits [e] = [])
    (hT : TreesOK cs h) : TreesOK cs (h ++ [e]) := by
  unfold TreesOK
  rw [commits_append, he, List.append_nil]
  exact hT

theorem treesOK_commit {cs : List Tree} {h : List Ev} (hT : TreesOK cs h) (ht w : ℕ) (W : Word)
    (lv : Array (Array Digest)) : TreesOK (cs ++ [⟨ht, W, lv⟩]) (h ++ [Ev.commit ht w W]) := by
  unfold TreesOK at hT ⊢
  rw [commits_append, List.map_append, List.map_append, hT]
  rfl

/-- An opening the prover reads off a tree is the history's answer. -/
theorem answer_of_treesOK {cs : List Tree} {h : List Ev} (hT : TreesOK cs h) {i : ℕ}
    {tree : Tree} (hc : cs[i]? = some tree) (ps : List ℕ) :
    answer h i ps = some (ps.map fun q ↦ tree.word (q % 2 ^ tree.height)) := by
  have e := congrArg (·[i]?) hT
  simp only [List.getElem?_map, hc, Option.map_some] at e
  unfold answer
  rcases hci : (commits h)[i]? with _ | ⟨a, b, c⟩
  · rw [hci] at e
    cases e
  · rw [hci] at e
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl

theorem allQ_proveFromM (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (P : VerifierProgram α) (sp : Sponge) (h : List Ev) (cs : List Tree), WidthsLE maxWidth P →
      (∀ chal, S.ShapedFrom chal P h) → HistOK h → TreesOK cs h →
      AllQueriesSatisfy (proveFromM callKeccak256 callKeccakF1600 S fuel P sp h cs) Short
  | .ret _, _, _, _, _, _, _, _ => allQ_pure _
  | .fail, _, _, _, _, _, _, _ => allQ_pure _
  | .read k, sp, h, cs, hP, hG, hh, hT => by
    simp only [proveFromM]
    exact allQueriesSatisfy_bind (allQ_absorb _ _ _) fun sp' ↦
      allQueriesSatisfy_bind (allQ_proveFromM S fuel _ sp' _ cs (hP _) (fun chal ↦ hG chal)
        (histOK_append_of_nil _ rfl hh) (treesOK_append_of_nil _ rfl hT)) fun _ ↦ allQ_pure _
  | .sample k, sp, h, cs, hP, hG, hh, hT => by
    simp only [proveFromM]
    exact allQueriesSatisfy_bind (allQ_squeeze _) fun r ↦
      allQ_proveFromM S fuel _ r.2 _ cs (hP _) (shaped_sample S hG r.1)
        (histOK_append_of_nil _ rfl hh) (treesOK_append_of_nil _ rfl hT)
  | .grind bits k, sp, h, cs, hP, hG, hh, hT => by
    simp only [proveFromM]
    refine allQueriesSatisfy_bind (allQ_findNonceM _ _ _) fun o ↦ ?_
    split
    · exact allQ_pure _
    · exact allQueriesSatisfy_bind (allQ_absorbNonce _ _) fun r ↦
        allQueriesSatisfy_bind (allQ_proveFromM S fuel k r.2 _ cs hP (fun chal ↦ hG chal)
          (histOK_append_of_nil _ rfl hh) (treesOK_append_of_nil _ rfl hT)) fun _ ↦ allQ_pure _
  | .commit ht w k, sp, h, cs, hP, hG, hh, hT => by
    simp only [proveFromM, buildTreeWithHash, bind_assoc, pure_bind]
    have hs : WellShaped w (S.word h) := (hG fun _ ↦ 0).1
    have hrows : RowsLE (S.word h) := fun p ↦ (hs p).symm ▸ hP.1
    have hh' : HistOK (h ++ [Ev.commit ht w (S.word h)]) := by
      intro c hc
      rw [commits_append] at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hh c hc
      · simp only [commits, List.mem_singleton] at hc
        subst hc
        exact hrows
    exact allQueriesSatisfy_bind (allQ_leafDigestsM _ hrows) fun _ ↦
      allQueriesSatisfy_bind (allQ_levelsM _ _) fun lv ↦
      allQueriesSatisfy_bind (allQ_absorb _ _ _) fun _ ↦
        allQueriesSatisfy_bind (allQ_absorb _ _ _) fun _ ↦
          allQueriesSatisfy_bind (allQ_proveFromM S fuel k _ _ _ hP.2 (fun chal ↦ (hG chal).2)
            hh' (treesOK_commit hT ht w (S.word h) lv.toArray)) fun _ ↦ allQ_pure _
  | .query i ps k, sp, h, cs, hP, hG, hh, hT => by
    simp only [proveFromM]
    split
    · exact allQ_pure _
    · rename_i tree hi
      have ha := answer_of_treesOK hT hi ps
      have hG' : ∀ chal, S.ShapedFrom chal (k (ps.map fun q ↦ tree.word (q % 2 ^ tree.height)))
          (h ++ [Ev.query (ps.map fun q ↦ tree.word (q % 2 ^ tree.height))]) := fun chal ↦ by
        have := hG chal
        simp only [Strategy.ShapedFrom, ha] at this
        exact this
      exact allQueriesSatisfy_bind (allQ_proveFromM S fuel _ sp _ cs (hP _) hG'
          (histOK_append_of_nil _ rfl hh) (treesOK_append_of_nil _ rfl hT)) fun _ ↦ allQ_pure _

theorem allQ_proveM (P : VerifierProgram Bool) (S : Strategy) (seed : KeccakState) (fuel : ℕ)
    (hP : WidthsLE maxWidth P) (hs : ∀ chal, shapedI P S chal) :
    AllQueriesSatisfy (proveM callKeccak256 callKeccakF1600 P S seed fuel) Short :=
  allQueriesSatisfy_bind (allQ_proveFromM S fuel P _ [] [] hP hs
    (fun _ hc ↦ by simp [commits] at hc) rfl) fun _ ↦ allQ_pure _

theorem allQ_romHonestComp (prog : LeanIsaProgram) (input : PublicInput) (S : Strategy) (fuel : ℕ)
    (hs : ∀ chal, shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S
        chal) :
    AllQueriesSatisfy (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S fuel) Short := by
  unfold Rom.honestComp
  exact allQueriesSatisfy_bind (allQ_seedRun prog input) fun seed ↦
    allQueriesSatisfy_bind (allQ_proveM _ _ seed fuel (widthsLE_leanVmProgram _ _) hs)
      fun _ ↦ allQ_pure _

-- Comparing the honest strategy's `shapedI` with itself unfolds the strategy; the default budget
-- does not cover it.
set_option maxHeartbeats 1000000 in
/-- The honest strategy of a witness commits well-shaped words. -/
theorem shaped_of (hW : Whir.Complete.OpeningComplete) {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ} {s : LeanIsa.Sizes}
    {w : Air.Flat.EnsembleWitness (Arithmetization.leanIsaEnsemble prog t.logMemorySize)}
    (hw : Complete.HonestFor prog input t ρ w s) (chal : List Ev → E) :
    shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
      (Complete.leanVmProver prog s ρ (LeanIsa.stackOf prog s w)) chal := by
  obtain ⟨hρ', hw', hs', hadm', -⟩ := hw
  with_reducible exact
    (Complete.runI_leanVmProgram hW (input := input) hadm' hρ' (LeanIsa.m3Honest_stackOf hw' hs') chal).2

-- As for `shaped_of`.

/-- The honest prover's queries: the seed's four, and `leanVmCost = 53036` quarters at the
prover's factor. -/
theorem isTotalQueryBound_honestComp' (prog : LeanIsaProgram) (input : PublicInput) (t :
    Execution prog)
    (ρ fuel : ℕ) :
    IsTotalQueryBound (Complete.honestComp prog input t ρ fuel)
      (2 + 53036 * (2 ^ 27 + 2 * fuel + 2)) := by
  by_cases hex : ∃ w s, Complete.HonestFor prog input t ρ w s
  · unfold Complete.honestComp
    simp only [hex, ↓reduceDIte]
    have h := Rom.isTotalQueryBound_honestComp
      (costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input)) (Complete.leanVmProver
        prog hex.choose_spec.choose ρ (LeanIsa.stackOf prog hex.choose_spec.choose hex.choose))
      fuel (σ := leanVmSeed (bytecodeWords prog) (publicInputDigest input))
    have hc : leanVmCost = 53036 := by decide
    rw [hc] at h
    exact h
  · unfold Complete.honestComp
    simp only [hex, ↓reduceDIte]
    trivial

end Prover

/-- **A prover of at most `2 + 53036 · (2^27 + 2·fuel + 2)` short queries and the verifier make
at most `completenessPermCalls fuel` permutation calls.** -/
theorem isWeightBound_proverVerifier {X : OracleComp KeccakCalls Proof} (prog : LeanIsaProgram)
    (input : PublicInput) {fuel : ℕ}
    (hX : IsTotalQueryBound X (2 + 53036 * (2 ^ 27 + 2 * fuel + 2)))
    (hXq : AllQueriesSatisfy X Short) :
    Common.QueryCostAtMost (X >>= fun proof ↦ verifierWithHash callKeccak256 callKeccakF1600 prog input proof) hashBlocks
      (completenessPermCalls fuel) := by
  have hN : IsTotalQueryBound (X >>= fun proof ↦ verifierWithHash callKeccak256 callKeccakF1600 prog input proof)
      (completenessQueries fuel) := by
    have h := isTotalQueryBound_bind hX fun proof ↦ by
        have := isTotalQueryBound_leanVm (bytecodeWords prog) (publicInputDigest input) proof
        rw [leanVmQueryBound_eq, ← verifier_eq] at this
        exact this
    refine h.mono ?_
    unfold completenessQueries
    omega
  exact isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) hN
    ((allQueriesSatisfy_bind hXq fun proof ↦
      allQ_verifier prog input proof).mono fun _ h ↦ hashBlocks_le_of_short h)

/-- The specification's honest prover of any strategy makes at most
`2 + 53036 · (2^27 + 2·fuel + 2)` queries. -/
theorem isTotalQueryBound_romHonestComp (prog : LeanIsaProgram) (input : PublicInput) (S : Strategy)
    (fuel : ℕ) :
    IsTotalQueryBound (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S fuel)
      (2 + 53036 * (2 ^ 27 + 2 * fuel + 2)) := by
  have h := Rom.isTotalQueryBound_honestComp
    (costLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input)) S fuel
    (σ := leanVmSeed (bytecodeWords prog) (publicInputDigest input))
  have hc : leanVmCost = 53036 := by decide
  rw [hc] at h
  exact h

-- As for `shaped_of`.
set_option maxHeartbeats 1000000 in
/-- **The specification's honest prover at an honest witness, then the verifier, make at most
`completenessPermCalls fuel` permutation calls.** -/
theorem isWeightBound_romHonest (hW : Whir.Complete.OpeningComplete) {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {ρ : ℕ}
    {s : LeanIsa.Sizes} {w : Air.Flat.EnsembleWitness (Arithmetization.leanIsaEnsemble prog t.logMemorySize)}
    (hw : Complete.HonestFor prog input t ρ w s) (fuel : ℕ) :
    Common.QueryCostAtMost
      (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (Complete.leanVmProver prog s ρ (LeanIsa.stackOf prog s w)) fuel >>= fun proof ↦
          verifierWithHash callKeccak256 callKeccakF1600 prog input proof) hashBlocks (completenessPermCalls fuel) :=
  isWeightBound_proverVerifier prog input (isTotalQueryBound_romHonestComp prog input _ fuel)
    (allQ_romHonestComp prog input _ fuel (shaped_of hW hw))

end LeanVM.Rpm
