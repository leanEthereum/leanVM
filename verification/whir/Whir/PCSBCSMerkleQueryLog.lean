import Whir.MerkleQueryLogExtractionRows
import Whir.PublicMerkleProbability

/-! PCS-only deterministic Merkle slice. Runtime input is the ordinary public
compression trace, not a whole-hash oracle. Probability is the existing shared
256-bit random-compression game, with actual root policy and compression budget.
This module makes no claim about real BLAKE2s or whole-system Fiat-Shamir. -/
namespace Whir.PCSBCSMerkleQueryLog
open Concrete FiatShamirGame DuplexModeGame PublicMerkleLog PublicMerkleBinding
open MerkleTransport MerkleTransport.Commitments MerkleBinding
open MerkleQueryLogExtraction PublicMerkleProbability PublicCompressionProgram
open DuplexFraming TypedOracleCompiler

/-- Saturate the frozen public compression trace once, preindex the completed
ordinary hash records once, then traverse the fixed-depth tree once. -/
def fromPublic (log : PublicLog) (root : Digest32) (height : Nat) : Tree :=
  extract canonicalCodec (build (records log)) height root

/-- Literal raw occupied leaves, prepared for the source decoder. Its
`receivedLane`/`fullRow` perform the source lane reversal themselves. Passing
the coefficient-order or padded first-fold table instead would double reverse. -/
def rawRoot0 (log : PublicLog) (root : Digest32) (height occupied : Nat) : Array (Array K) :=
  extractRows canonicalCodec (build (records log)) occupied (Array.replicate occupied 0) height root #[]

theorem rawRoot0_eq_fullRows (log : PublicLog) (root : Digest32) (height occupied : Nat) :
    rawRoot0 log root height occupied = fullRows occupied height (fromPublic log root height) := by
  exact extractRows_eq_emit canonicalCodec (build (records log)) occupied
    (Array.replicate occupied 0) height root #[]

theorem rawRoot0_shape (log : PublicLog) (root : Digest32) (height occupied : Nat) :
    (rawRoot0 log root height occupied).size = 2^height ∧
      ∀ row ∈ (rawRoot0 log root height occupied).toList, row.size = occupied := by
  rw [rawRoot0_eq_fullRows]
  exact ⟨fullRows_size occupied height _,fullRows_width occupied height _⟩

/-- Collision exclusion is the concrete observed compression event. It is
DERIVED into whole-hash preimage uniqueness rather than assumed as a field. -/
theorem public_eq_snapshot (C : PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (clean : ¬ OutputCollision log)
    (root : Digest32) (fallback : List K) (address : List Bool) :
    (fromPublic log root address.length).row fallback address =
      idealRow (hashing (hash C)) (recordDomain (records log)) root fallback address :=
  extract_eq_ideal canonicalCodec (hash C) (records log) (records_authentic C log auth)
    (fun bad => clean (reconstructed_collision C log auth bad)) root fallback address

/-- Full-height accepted raw rows agree with the executable frozen tree, or
expose the existing collision/fresh-target compression witness. The statement
also covers absence and malformed preimages: they cannot pass silently. -/
theorem opened_rows (C : PrimitiveOracle) (log : PublicLog) (auth : AuthenticLog C log)
    (root : Digest32) (height : Nat) (output : List RawPath)
    (depth : ∀ p ∈ output, p.path.length = height)
    (accepted : ∀ p ∈ output, p.root (hash C) = root)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    (∀ p ∈ output, (fromPublic log root height).get
      (addressAbove p.leafIndex height []) = some p.leafData) ∨
      OpenPrimitiveBad C log root output := by
  classical
  by_cases collision : OutputCollision log
  · exact Or.inr (Or.inl collision)
  have clean : ¬ Collision (hashing (hash C)) (recordDomain (records log)) :=
    fun bad => collision (reconstructed_collision C log auth bad)
  by_cases fresh : ∃ p ∈ output, FreshHit (hashing (hash C)) (recordDomain (records log)) root
      (p.opening.inputs (hashing (hash C)))
  · obtain ⟨p,hp,hfresh⟩ := fresh
    rcases freshHit_primitive C log auth root _ (bounds p hp) hfresh with hc | hf
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr ⟨p,hp,hf⟩)
  · left
    intro p hp
    have noFresh : ¬ FreshHit (hashing (hash C)) (recordDomain (records log)) root
        (p.opening.inputs (hashing (hash C))) := fun bad => fresh ⟨p,hp,bad⟩
    have recorded := (recorded_or_fresh (hashing (hash C)) (recordDomain (records log)) root
      p.opening (Or.inl ((p.opening_digest (hash C)).trans (accepted p hp)))).resolve_right noFresh
    have result := extract_complete canonicalCodec (hash C) (records log)
      (records_authentic C log auth) clean p.opening recorded
    simpa only [fromPublic,RawPath.opening_digest,accepted p hp,RawPath.opening_row,
      addressAbove_length,List.length_nil,Nat.add_zero,depth p hp] using result

/-- A single causal terminal event covers ANY freeze/configuration/extraction
in the one actual trace. There is no union factor for rows or clones, and no
assumed multi-extractability interface. -/
def FrozenExtractionBad (C : PrimitiveOracle) (roots : RootPolicy) (trace : PublicLog) : Prop :=
  ∃ (before after oldLog : PublicLog) (root : Digest32) (height : Nat) (output : List RawPath),
    trace = before ++ after ∧
    (∀ e ∈ oldLog, e ∈ before) ∧
    (∀ n d, (n,d) ∈ before → tag n = 0 → (n,d) ∈ oldLog) ∧
    root ∈ roots before.reverse ∧
    (∀ p ∈ output, p.path.length = height) ∧
    (∀ p ∈ output, p.root (hash C) = root) ∧
    (∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^56) ∧
    (∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)),
      ∀ e ∈ PublicMerkleLog.plan C bytes, e ∈ trace) ∧
    ∃ p ∈ output, (fromPublic oldLog root height).get
      (addressAbove p.leafIndex height []) ≠ some p.leafData

theorem extraction_bad_opening_bad (C : PrimitiveOracle) (roots : RootPolicy)
    (trace : PublicLog) (auth : AuthenticLog C trace) (bad : FrozenExtractionBad C roots trace) :
    FrozenOpeningBad C roots trace := by
  obtain ⟨before,after,oldLog,root,height,output,he,sub,ordinary,registered,
    depth,accepted,bounds,plans,p,hp,mismatch⟩ := bad
  have oldAuth : AuthenticLog C oldLog := by
    intro n d hm
    apply auth n d
    rw [he]
    exact List.mem_append_left _ (sub _ hm)
  have wider : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64 := by
    intro p hp bytes hb
    exact lt_of_lt_of_le (bounds p hp bytes hb) (by norm_num)
  have primitive : OpenPrimitiveBad C oldLog root output := by
    rcases opened_rows C oldLog oldAuth root height output depth accepted wider with good | bad
    · exact (mismatch (good p hp)).elim
    · exact bad
  exact ⟨before,after,oldLog,root,output,he,sub,ordinary,registered,bounds,plans,primitive⟩

noncomputable def extractionProbability {T : Type} (roots : RootPolicy) {Q : Nat}
    (p : Computation T Q) : ℚ := by
  classical
  exact average (fun C : PrimitiveOracle =>
    if FrozenExtractionBad C roots (toLog (Sampling.execute C p).2) then 1 else 0)

/-- Q counts actual shared compression calls. M is the independently checked
target-admission cap; it must not be inferred from distinct commitment CVs or
from a whole-construction cost when the source made primitive requests. -/
theorem multi_extraction_probability {T : Type} (roots : RootPolicy) (Q M : Nat)
    (rootCap : ∀ log, log.length ≤ Q → (roots log).card ≤ M)
    (grow : RootsGrow roots) (p : Computation T Q) :
    extractionProbability roots p ≤ bound Q M := by
  classical
  apply le_trans _ (opening_probability_bound roots Q M rootCap grow p)
  apply average_mono
  intro C
  by_cases bad : FrozenExtractionBad C roots (toLog (Sampling.execute C p).2)
  · have covered := extraction_bad_opening_bad C roots _ (execute_authentic C p) bad
    simp only [bad,covered,↓reduceIte,le_refl]
  · simp only [bad,↓reduceIte]
    split <;> norm_num

end Whir.PCSBCSMerkleQueryLog
