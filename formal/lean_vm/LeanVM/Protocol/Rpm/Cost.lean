/-
  LeanVM.Protocol.Rpm.Cost

  The permutation calls of a verifier program's queries: every hash it computes is short, so each
  query costs a bounded number of calls of the permutation.
-/

module

import LeanVM.Facts.Verifier
import LeanVM.Protocol.KeccakHash
import Common.Prob
import Common.ByteArray
import Statement.Fast.Keccak
import FastFields.QuadExt
import FastFields.FieldWords
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.Compile.Moves
public import LeanVM.Protocol.Compile.Rom.Bridge

@[expose] public section

/-!
# The permutation calls of a verifier program

In the random-permutation model a Keccak-256 hash of `n` bytes costs `⌊n / 136⌋ + 1` calls of the
permutation, one per block of the padded message, and a direct permutation call costs one
(`hashBlocks`). A query is `Short` when it hashes at most `2^37 + 9` bytes: the IV's preimage
(the `9`-byte version tag, then a bytecode of at most `2^30` instructions), Merkle nodes (`64`
bytes) and Merkle leaves (`8 · width` bytes, for commitments of width at most `maxWidth`,
`WidthsLE`). So every short query costs at most `⌊(2^37 + 9) / 136⌋ + 1 ≤ 2^30` calls, and a
computation of `N` queries at most `N · 2^30` (`isWeightBound_of_isTotalQueryBound`).
`allQ_run`: every query of the compiled run of a program whose commitments are at most `maxWidth`
wide is short. The bus era's instances on leanVM's verifier and honest prover are archived at tag
`formal-bus-archive`.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

open OracleComp OracleSpec

/-- The permutation calls of a query: a Keccak-256 hash of `n` bytes costs `⌊n / 136⌋ + 1`
(one per block of the padded message), a permutation one. -/
def hashBlocks : KeccakCalls.Domain → ℕ
  | .inl x => x.length / 136 + 1
  | .inr _ => 1

/-- A short query: a hash of at most `2^37 + 9` bytes, or a permutation. -/
def Short : KeccakCalls.Domain → Prop
  | .inl x => x.length ≤ 2 ^ 37 + 9
  | .inr _ => True

/-- A short query costs at most `2^30` permutation calls. -/
theorem hashBlocks_le_of_short {t : KeccakCalls.Domain} (h : Short t) : hashBlocks t ≤ 2 ^ 30 := by
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

theorem allQ_queryH {x : Bytes} (hx : x.length ≤ 2 ^ 37 + 9) :
    AllQueriesSatisfy (callKeccak256 x) Short :=
  (allQueriesSatisfy_query_iff (spec := KeccakCalls) (.inl x) Short).mpr hx

theorem allQ_queryH₀ {x : Bytes} (hx : x.length ≤ 2 ^ 37) : AllQueriesSatisfy (callKeccak256 x) Short :=
  allQ_queryH (hx.trans (Nat.le_add_right _ _))

theorem allQ_pure {α : Type} (a : α) : AllQueriesSatisfy (pure a : OracleComp KeccakCalls α) Short :=
  allQueriesSatisfy_pure _ _

theorem flatMap_kBytes_length (l : List K) : (l.flatMap K.toBytes).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, kBytes_length, ih]; ring

theorem pair_length (a b : Digest) : (digestBytes a ++ digestBytes b).length ≤ 2 ^ 37 := by
  simp [digestBytes_length]

theorem bytecodeWords_length (prog : LeanIsaProgram) :
    (bytecodeWords prog).length = 16 * 2 ^ prog.logSize := by
  simp [bytecodeWords, List.length_flatMap]
  omega

theorem bytecode_length (prog : LeanIsaProgram) :
    ((bytecodeWords prog).flatMap K.toBytes).length ≤ 2 ^ 37 := by
  rw [flatMap_kBytes_length, bytecodeWords_length]
  have h1 : 2 ^ prog.logSize ≤ 2 ^ 30 :=
    Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  have : (2 : ℕ) ^ 37 = 8 * (16 * 2 ^ 30) := by norm_num
  rw [this]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)

/-! ## The widths of the commitments -/

/-- Every commitment of a program has width at most `W`. -/
def WidthsLE (W : ℕ) {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, WidthsLE W (k x)
  | .sample k => ∀ x, WidthsLE W (k x)
  | .readPacked _ k => ∀ xs, WidthsLE W (k xs)
  | .samplePacked _ k => ∀ xs, WidthsLE W (k xs)
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
  | readPacked n k ih => exact fun xs ↦ ih xs (hp xs)
  | samplePacked n k ih => exact fun xs ↦ ih xs (hp xs)
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
  | readPacked n k ih => exact fun xs ↦ ih xs (h xs)
  | samplePacked n k ih => exact fun xs ↦ ih xs (h xs)
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

/-- The width bound of the leanVM verifier program's commitments: `2 · 2^6`, the two limbs of a
level's folded lanes. -/
def maxWidth : ℕ := 128

theorem two_pow_le {f : ℕ} (h : f ≤ 6) : 2 * 2 ^ f ≤ maxWidth := by
  have : 2 ^ f ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h
  unfold maxWidth; omega

theorem pow_le {f : ℕ} (h : f ≤ 6) : 2 ^ f ≤ maxWidth := by
  have : 2 ^ f ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h
  unfold maxWidth; omega

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

theorem allQ_absorbPackedChunks : ∀ (fuel : ℕ) (state : KeccakState) (values : List E),
    AllQueriesSatisfy (absorbPackedChunks callKeccakF1600 fuel state values) Short
  | 0, _, _ => allQ_pure _
  | _ + 1, _, [] => allQ_pure _
  | fuel + 1, _, _ :: _ => by
    simp only [absorbPackedChunks]
    exact allQueriesSatisfy_bind (allQ_queryF _) fun _ ↦ allQ_absorbPackedChunks fuel _ _

theorem allQ_observePacked (sp : Sponge) (values : List E) :
    AllQueriesSatisfy (observePacked callKeccakF1600 sp values) Short := by
  simp only [observePacked]
  split
  · simp only [pure_bind]
    exact allQueriesSatisfy_bind (allQ_absorbPackedChunks _ _ _) fun _ ↦ allQ_pure _
  · exact allQueriesSatisfy_bind (allQ_duplex _) fun _ ↦
      allQueriesSatisfy_bind (allQ_absorbPackedChunks _ _ _) fun _ ↦ allQ_pure _

theorem allQ_squeezePackedChunks : ∀ (fuel : ℕ) (sp : Sponge) (missing : ℕ),
    AllQueriesSatisfy (squeezePackedChunks callKeccakF1600 fuel sp missing) Short
  | 0, _, _ => allQ_pure _
  | _ + 1, _, 0 => allQ_pure _
  | fuel + 1, _, _ + 1 => by
    simp only [squeezePackedChunks]
    exact allQueriesSatisfy_bind (allQ_duplex _) fun _ ↦
      allQueriesSatisfy_bind (allQ_squeezePackedChunks fuel _ _) fun _ ↦ allQ_pure _

theorem allQ_samplesPacked (sp : Sponge) (count : ℕ) :
    AllQueriesSatisfy (samplesPacked callKeccakF1600 sp count) Short := by
  simp only [samplesPacked]
  exact allQueriesSatisfy_bind (allQ_squeezePackedChunks _ _ _) fun _ ↦ allQ_pure _

theorem allQ_climb : ∀ (node : Digest) (q : ℕ) (ss : List Digest),
    AllQueriesSatisfy (climbWithHash callKeccak256 node q ss) Short
  | _, _, [] => allQueriesSatisfy_pure _ _
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
      allQueriesSatisfy_bind (allQ_climb _ _ _) fun _ ↦ allQueriesSatisfy_pure _ _
    rw [flatMap_kBytes_length, h.1]
    unfold maxWidth at hw
    omega
  · exact allQueriesSatisfy_pure _ _

theorem allQ_openAll (root : Digest) (height width : ℕ) (hw : width ≤ maxWidth) :
    ∀ (ps : List ℕ) (os : List Opening),
      AllQueriesSatisfy (openAllWithHash callKeccak256 root height width ps os) Short
  | [], _ => allQueriesSatisfy_pure _ _
  | _ :: _, [] => allQueriesSatisfy_pure _ _
  | q :: qs, o :: os => by
    simp only [openAllWithHash]
    refine allQueriesSatisfy_bind (allQ_openOne _ _ _ _ _ hw) fun b ↦ ?_
    split
    · exact allQueriesSatisfy_bind (allQ_openAll root height width hw qs os) fun _ ↦ allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_pure _ _

theorem allQ_openPhase (root : Digest) (height width : ℕ) (hw : width ≤ maxWidth) (ps : List ℕ)
    (phase : List Opening) :
    AllQueriesSatisfy (openPhaseWithHash callKeccak256 root height width ps phase) Short := by
  unfold openPhaseWithHash
  split
  · exact allQueriesSatisfy_bind (allQ_openAll root height width hw ps phase) fun _ ↦ by
      split <;> exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _

theorem allQ_run {α : Type} : ∀ (P : VerifierProgram α) (s : VerifierProgramState), WidthsLE
    maxWidth P →
    (∀ r ∈ s.roots, r.2.2 ≤ maxWidth) → AllQueriesSatisfy (Compile.runWithHash callKeccak256 callKeccakF1600 P s) Short
  | .ret _, _, _, _ => allQueriesSatisfy_pure _ _
  | .fail, _, _, _ => allQueriesSatisfy_pure _ _
  | .read k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · exact allQueriesSatisfy_bind (allQ_absorb _ _ _) fun sp ↦ allQ_run _ _ (hP _) hr
    · exact allQueriesSatisfy_pure _ _
  | .sample k, s, hP, hr => by
    simp only [Compile.runWithHash]
    refine allQueriesSatisfy_bind (allQ_squeeze _) fun r ↦ ?_
    obtain ⟨c, sp⟩ := r
    exact allQ_run _ _ (hP _) hr
  | .readPacked n k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · exact allQueriesSatisfy_bind (allQ_observePacked _ _) fun sp ↦ allQ_run _ _ (hP _) hr
    · exact allQueriesSatisfy_pure _ _
  | .samplePacked n k, s, hP, hr => by
    simp only [Compile.runWithHash]
    refine allQueriesSatisfy_bind (allQ_samplesPacked _ _) fun r ↦ ?_
    obtain ⟨cs, sp⟩ := r
    exact allQ_run _ _ (hP _) hr
  | .grind bits k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · refine allQueriesSatisfy_bind (allQ_absorbNonce _ _) fun r ↦ ?_
      obtain ⟨c, sp'⟩ := r
      split
      · exact allQ_run _ _ hP hr
      · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_pure _ _
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
    · exact allQueriesSatisfy_pure _ _
  | .query i ps k, s, hP, hr => by
    simp only [Compile.runWithHash]
    split
    · rename_i root height width phase rest hi _
      refine allQueriesSatisfy_bind (allQ_openPhase root height width
        (hr _ (List.mem_of_getElem? hi)) ps phase) fun o ↦ ?_
      split
      · exact allQ_run _ _ (hP _) hr
      · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_pure _ _

theorem allQ_runProof (P : VerifierProgram Bool) (seed : KeccakState) (π : Proof) (hP : WidthsLE
    maxWidth P) :
    AllQueriesSatisfy (runProofWithHash callKeccak256 callKeccakF1600 P seed π) Short := by
  unfold runProofWithHash
  refine allQueriesSatisfy_bind (allQ_run P _ hP fun r hr ↦ by simp at hr) fun o ↦ ?_
  split <;> exact allQueriesSatisfy_pure _ _

theorem allQ_hsRun : ∀ (fs : List (List Digest → Bytes)) (ds : List Digest),
    (∀ f ∈ fs, ∀ ds, (f ds).length ≤ 2 ^ 37 + 9) →
      AllQueriesSatisfy (Seed.hsRun callKeccak256 fs ds) Short
  | [], _, _ => allQueriesSatisfy_pure _ _
  | f :: fs, ds, h => by
    simp only [Seed.hsRun]
    exact allQueriesSatisfy_bind (allQ_queryH (h f (by simp) ds)) fun d ↦
      allQ_hsRun fs _ fun g hg ↦ h g (List.mem_cons_of_mem _ hg)

end Verifier

end LeanVM.Rpm

end
