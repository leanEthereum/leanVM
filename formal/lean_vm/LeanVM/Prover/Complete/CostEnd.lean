/-
  LeanVM.Prover.Complete.CostEnd

  The honest prover's and the verifier's queries, and their permutation calls: `HonestCosts`.
-/

module

public import LeanVM.Prover.Complete.CostRun
public import LeanVM.Prover.Complete.CostWalk
public import LeanVM.Prover.Complete.End
public import LeanVM.Protocol.Rpm.Cost
public import LeanVM.Wire.HonestScript

/-!
# The honest prover's costs

* `qb_honestComp`, `qb_verifierComp` (`CostRun`) on the leanVM verifier program, which is `Wired`
  with `leanVmStream` stream elements and `wireMaxPhases` openings (`wired_leanVmProgram`) and of
  `leanVmSamples` other events (`sampLE_leanVmProgram`): the prover makes at most `QA`, the verifier
  at most `QV` queries, `QA + QV ≤ 2^120`.
* Every query is short (`Short`): the verifier's (`allQ_run`, its commitments at most `128` wide),
  the seed's (the bytecode's hash), and the prover's (`allQ_runFrom`: its trees' leaves are rows of
  at most `wireMaxLeafWords` words, `WordsOK`, `wordsOK_honestScript`). So each costs at most
  `2^30` permutation calls, and the two together at most `(QA + QV) · 2^30 ≤ 2^125`.

`honestCosts : HonestCosts`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Wire LeanVM.Rpm
open OracleComp OracleSpec

variable {α β : Type}

/-! ## Every query is short -/

theorem widthsLE_of_sampLE : ∀ {p : VerifierProgram α} {n : ℕ}, SampLE p n → WidthsLE maxWidth p
  | .ret _, _, _ => trivial
  | .fail, _, _ => trivial
  | .read k, _, h => fun x ↦ widthsLE_of_sampLE (p := k x) (h.2 x)
  | .sample k, _, h => fun x ↦ widthsLE_of_sampLE (p := k x) (h.2 x)
  | .readPacked _ k, _, h => fun x ↦ widthsLE_of_sampLE (p := k x) (h.2 x)
  | .samplePacked _ k, _, h => fun x ↦ widthsLE_of_sampLE (p := k x) (h.2 x)
  | .grind _ k, _, h => widthsLE_of_sampLE (p := k) h.2
  | .commit _ _ k, _, h => ⟨h.2.1, widthsLE_of_sampLE (p := k) h.2.2.2⟩
  | .query _ _ k, _, h => fun x ↦ widthsLE_of_sampLE (p := k x) (h.2 x)

theorem versionTag_length : versionTag.length = 9 := by decide +kernel

theorem allQ_leanVmSeed (prog : LeanIsaProgram) (publicInput : Digest) :
    AllQueriesSatisfy ((leanVmSeed (bytecodeWords prog) publicInput).run callKeccak256
      callKeccakF1600) Short := by
  unfold Seed.run
  refine allQueriesSatisfy_bind (allQ_hsRun _ _ fun f hf ds ↦ ?_) fun _ ↦ allQ_queryF _
  simp only [leanVmSeed, List.mem_singleton] at hf
  subst hf
  simp only [List.length_append, versionTag_length]
  have := bytecode_length prog
  omega

theorem allQ_verifierComp (prog : LeanIsaProgram) (publicInput : Digest) (π : Proof) :
    AllQueriesSatisfy (verifierComp (leanVmSeed (bytecodeWords prog) publicInput)
      (leanVmVerifierProgram (bytecodeWords prog) publicInput) π) Short :=
  allQueriesSatisfy_bind (allQ_leanVmSeed prog publicInput) fun seed ↦
    allQ_runProof _ seed π (widthsLE_of_sampLE (sampLE_leanVmProgram _ _))

theorem allQ_listMapM {γ δ : Type} (f : γ → OracleComp KeccakCalls δ)
    (hf : ∀ a, AllQueriesSatisfy (f a) Short) :
    ∀ l : List γ, AllQueriesSatisfy (l.mapM f) Short
  | [] => allQueriesSatisfy_pure _ _
  | a :: l => by
    simp only [List.mapM_cons]
    exact allQueriesSatisfy_bind (hf a) fun _ ↦ allQueriesSatisfy_bind (allQ_listMapM f hf l)
      fun _ ↦ allQueriesSatisfy_pure _ _

theorem allQ_arrayMapM {γ δ : Type} (f : γ → OracleComp KeccakCalls δ)
    (hf : ∀ a, AllQueriesSatisfy (f a) Short) (xs : Array γ) :
    AllQueriesSatisfy (xs.mapM f) Short := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (allQ_listMapM f hf _) fun _ ↦ allQueriesSatisfy_pure _ _

theorem allQ_levels : ∀ (k : ℕ) (level : Array Digest),
    AllQueriesSatisfy (levelsWithHash callKeccak256 k level) Short
  | 0, _ => allQueriesSatisfy_pure _ _
  | k + 1, level => by
    simp only [levelsWithHash]
    exact allQueriesSatisfy_bind (allQ_arrayMapM _ (fun _ ↦ allQ_queryH₀ (pair_length _ _)) _)
      fun up ↦ allQueriesSatisfy_bind (allQ_levels k up) fun _ ↦ allQueriesSatisfy_pure _ _

/-- A tree of a word whose rows have at most `wireMaxLeafWords` words is built with short
queries. -/
theorem allQ_buildTree (height : ℕ) {word : Word} {L : ℕ} (hL : L ≤ wireMaxLeafWords)
    (hw : ∀ p, (word p).length = L) :
    AllQueriesSatisfy (buildTreeWithHash callKeccak256 height word) Short := by
  unfold buildTreeWithHash leafDigestsWithHash
  refine allQueriesSatisfy_bind (allQ_arrayMapM _ (fun i ↦ allQ_queryH₀ ?_) _) fun l ↦
    allQueriesSatisfy_bind (allQ_levels height l) fun _ ↦ allQueriesSatisfy_pure _ _
  rw [flatMap_kBytes_length, hw]
  unfold wireMaxLeafWords at hL
  omega

theorem allQ_searchM (bits : ℕ) (o : Bool) (sp : Sponge) :
    ∀ (count n : ℕ), AllQueriesSatisfy (searchM callKeccakF1600 bits o sp n count) Short
  | 0, _ => allQueriesSatisfy_pure _ _
  | count + 1, n => by
    simp only [searchM]
    refine allQueriesSatisfy_bind (allQ_absorbNonce _ _) fun r ↦ ?_
    split
    · exact allQueriesSatisfy_pure _ _
    · exact allQ_searchM bits o sp count (n + 1)

/-- **The prover's run asks short queries only**, from a script whose committed words are well
shaped. -/
theorem allQ_runFrom (fuel : ℕ) : ∀ (p : VerifierProgram α) (S : Option (Script β)) (sp : Sponge)
    (cs : List Tree), ScriptOK S →
      AllQueriesSatisfy (runFromWithHash callKeccak256 callKeccakF1600 fuel p S sp cs) Short
  | .ret _, _, _, _, _ => allQueriesSatisfy_pure _ _
  | .fail, _, _, _, _ => allQueriesSatisfy_pure _ _
  | .read k, S, sp, cs, hS => by
    simp only [runFromWithHash]
    exact allQueriesSatisfy_bind (allQ_absorb _ _ _) fun sp' ↦ allQueriesSatisfy_bind
      (allQ_runFrom fuel _ _ sp' cs (scriptOK_afterSend hS)) fun _ ↦ allQueriesSatisfy_pure _ _
  | .sample k, S, sp, cs, hS => by
    simp only [runFromWithHash]
    exact allQueriesSatisfy_bind (allQ_squeeze _) fun r ↦
      allQ_runFrom fuel _ _ r.2 cs (scriptOK_afterSample _ hS)
  | .readPacked m k, S, sp, cs, hS => by
    simp only [runFromWithHash]
    exact allQueriesSatisfy_bind (allQ_observePacked _ _) fun sp' ↦ allQueriesSatisfy_bind
      (allQ_runFrom fuel _ _ sp' cs (scriptOK_afterSendPacked hS)) fun _ ↦
        allQueriesSatisfy_pure _ _
  | .samplePacked m k, S, sp, cs, hS => by
    simp only [runFromWithHash]
    exact allQueriesSatisfy_bind (allQ_samplesPacked _ _) fun r ↦
      allQ_runFrom fuel _ _ r.2 cs (scriptOK_afterSamplePacked _ hS)
  | .grind bits k, S, sp, cs, hS => by
    simp only [runFromWithHash]
    refine allQueriesSatisfy_bind (allQ_searchM _ _ _ _ _) fun o ↦ ?_
    split
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_bind (allQ_absorbNonce _ _) fun r ↦ allQueriesSatisfy_bind
        (allQ_runFrom fuel k _ r.2 cs (scriptOK_afterGrind hS)) fun _ ↦ allQueriesSatisfy_pure _ _
  | .commit ht w k, S, sp, cs, hS => by
    simp only [runFromWithHash]
    obtain ⟨L, hL, hw⟩ := wordOf_ok hS
    exact allQueriesSatisfy_bind (allQ_buildTree ht hL hw) fun tree ↦ allQueriesSatisfy_bind
      (allQ_absorb _ _ _) fun sp0 ↦ allQueriesSatisfy_bind (allQ_absorb _ _ _) fun sp1 ↦
        allQueriesSatisfy_bind (allQ_runFrom fuel k _ sp1 _ (scriptOK_afterCommit hS)) fun _ ↦
          allQueriesSatisfy_pure _ _
  | .query i ps k, S, sp, cs, hS => by
    simp only [runFromWithHash]
    split
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_bind (allQ_runFrom fuel _ _ sp cs (scriptOK_afterQuery _ hS))
        fun _ ↦ allQueriesSatisfy_pure _ _

theorem allQ_honestComp (prog : LeanIsaProgram) (publicInput : Digest) {S : Script β}
    (hS : WordsOK S) (fuel : ℕ) :
    AllQueriesSatisfy (honestComp (leanVmSeed (bytecodeWords prog) publicInput)
      (leanVmVerifierProgram (bytecodeWords prog) publicInput) S fuel) Short := by
  unfold honestComp runScriptWithHash
  exact allQueriesSatisfy_bind (allQ_leanVmSeed prog publicInput) fun seed ↦
    allQueriesSatisfy_bind (allQueriesSatisfy_bind (allQ_runFrom fuel _ _ _ _ hS) fun _ ↦
      allQueriesSatisfy_pure _ _) fun _ ↦ allQueriesSatisfy_pure _ _

/-! ## The counts -/

/-- The honest prover's queries, at most. -/
def proverQueries : ℕ := 1 + 1 + (leanVmStream + leanVmSamples) * proverK commitMaxHeight (2 ^ 35)

/-- The verifier's queries, at most. -/
def verifierQueries : ℕ := 1 + 1 + (leanVmStream + leanVmSamples + wireMaxPhases * openBound)

theorem leanVmSamples_le : leanVmSamples ≤ 2 ^ 14 := by
  unfold leanVmSamples keccakSamples keccakLayerSamples whirSamplesBound
  simp only [keccakLocalBits]
  norm_num

theorem queries_le : proverQueries + verifierQueries ≤ 2 ^ 72 := by
  have h1 := leanVmStream_lt
  have h2 := leanVmSamples_le
  unfold proverQueries verifierQueries proverK commitMaxHeight openBound wireMaxQueries
    wireMaxHeight wireMaxPhases
  generalize leanVmStream = a at *
  generalize leanVmSamples = b at *
  have : (a + b) * (2 ^ (32 + 1) + 2 * 2 ^ 35 + 2) ≤ (2 ^ 32 + 2 ^ 14) * (2 ^ 33 + 2 * 2 ^ 35 + 2) :=
    Nat.mul_le_mul (by omega) le_rfl
  norm_num at this ⊢
  omega

/-- **The honest prover's costs are bounded.** -/
theorem honestCosts : HonestCosts := by
  intro prog input t ρ W _ _ _ _ _ _
  have hw := wired_leanVmProgram (bytecodeWords prog) (publicInputDigest input)
  have hs := sampLE_leanVmProgram (bytecodeWords prog) (publicInputDigest input)
  have hA := qb_honestComp hw hs (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
    (honestScript W ρ (publicInputDigest input)) (2 ^ 35)
  have hV := qb_verifierComp hw hs (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
  have hlen : (leanVmSeed (bytecodeWords prog) (publicInputDigest input)).hs.length = 1 := rfl
  rw [hlen] at hA hV
  refine ⟨proverQueries, verifierQueries, (proverQueries + verifierQueries) * 2 ^ 30, ?_, ?_,
    hA, hV, ?_⟩
  · exact queries_le.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  · have := Nat.mul_le_mul_right (2 ^ 30) queries_le
    exact this.trans (by norm_num)
  · refine isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 30)
      (isTotalQueryBound_bind hA fun π ↦ ?_) ?_
    · rw [← verifierComp_leanVm]
      exact hV π
    · refine (allQueriesSatisfy_bind (allQ_honestComp prog _
        (wordsOK_honestScript W ρ (publicInputDigest input)) _) fun π ↦ ?_).mono
        fun _ h ↦ hashBlocks_le_of_short h
      rw [← verifierComp_leanVm]
      exact allQ_verifierComp prog _ π

end LeanVM.Prover.Complete.Cost

end
