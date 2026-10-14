import Whir.PCSBCSMerkleQueryLog
import Whir.PCSBCSMerkleLeafImages
import Whir.MerkleQueryLogExtractionRowsAgreement
import Whir.WHIRPhysicalRows
import Whir.SupportedCandidateExtraction

/-! PR600 12ee source-width boundary: the authenticated image has leafWords
words, including a checked leading zero prefix; occupied words are obtained by
draining leafWords-occupied. The rectangular compact oracle retains literal
suffixes even for invalid padding, independently of availability/padding status.
Only accepted-query transport authenticates these suffixes. Decoder lane access
reverses internally; verifier coefficient/fold order remains separate. Checked
Lean codecs do not claim a complete Rust scalar/assembly refinement. -/
namespace Whir.PCSBCSMerkleSourceRows
open Concrete FiatShamirGame MerkleTransport MerkleTransport.Commitments
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PublicMerkleLog PublicMerkleBinding
open PCSBCSMerkleLeafImages

/-- Full image agreement needs no honest-padding or availability assumption. -/
theorem imageRoot0_eq_baseOracle (C : DuplexModeGame.PrimitiveOracle)
    (log : PublicLog) (auth : AuthenticLog C log) (clean : ¬ OutputCollision log)
    (root : Digest32) (height leafWords occupied : Nat) :
    imageTable (sourceCells log root height leafWords occupied) =
      baseOracle (hash C) ⟨recordDomain (records log),[]⟩ root height (2^height) leafWords := by
  rw [imageTable_eq_full,rawRoot0_eq_fullRows]
  exact fullRows_eq_empty_snapshot canonicalCodec (hash C) (records log)
    (records_authentic C log auth) (fun bad => clean (reconstructed_collision C log auth bad))
    root height leafWords

/-- This is the literal suffix oracle, not a claim that every prefix is valid
or that default rows are authenticated. No all-valid-root premise is imposed. -/
theorem compactRoot0_eq_compactBaseOracle (C : DuplexModeGame.PrimitiveOracle)
    (log : PublicLog) (auth : AuthenticLog C log) (clean : ¬ OutputCollision log)
    (root : Digest32) (height leafWords occupied : Nat) :
    compactTable (sourceCells log root height leafWords occupied) =
      WHIRPhysicalRows.compactBaseOracle (hash C)
        ⟨recordDomain (records log),[]⟩ root height (2^height) leafWords occupied := by
  rw [compactTable_eq_drop,← imageTable_eq_full log root height leafWords occupied,
    imageRoot0_eq_baseOracle C log auth clean]
  simp [baseOracle,WHIRPhysicalRows.compactBaseOracle,WHIRPhysicalRows.compactBaseRow,
    Array.map_ofFn,Function.comp_def]

theorem prepared_source_shape (log : PublicLog) (root : Digest32)
    (height leafWords occupied rows : Nat) (fits : occupied ≤ leafWords) (count : rows = 2^height) :
    (compactTable (sourceCells log root height leafWords occupied)).size = rows ∧
    ∀ row ∈ (compactTable (sourceCells log root height leafWords occupied)).toList,
      row.size = occupied := by
  subst rows
  exact compactTable_shape log root height leafWords occupied fits

/-- A coefficient-ascending view agrees with the decoder's intrinsic raw-row
lane access. This theorem does not reverse the oracle supplied to the decoder. -/
theorem coefficient_lane (raw : Array (Array K)) (occupied index lane : Nat)
    (inside : index < raw.size) (shape : raw[index].size = occupied) (live : lane < occupied) :
    ((root0CoefficientOrder raw)[index]!)[lane]! =
      SupportedCandidateExtraction.recordLane occupied raw[index] lane := by
  rw [show (root0CoefficientOrder raw)[index]! = raw[index].reverse by
    simpa only [getElem!_pos (root0CoefficientOrder raw) index (by simpa [root0CoefficientOrder_size] using inside)]
      using root0CoefficientOrder_raw raw index inside]
  simp only [SupportedCandidateExtraction.recordLane,live,↓reduceIte]
  rw [getElem!_pos _ lane (by simpa [shape] using live),Array.getElem_reverse]
  have reverseInside : occupied-1-lane < raw[index].size := by rw [shape]; omega
  simp only [shape]
  rw [getElem!_pos (raw[index]) (occupied-1-lane) reverseInside]

/-- Actual accepted flat transport supplies the fixed-depth Root0 paths.
The only failure branch is the existing observed compression game event. -/
theorem pruned_opened_rows (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (root : Digest32) (proof : PrunedMerklePaths)
    (numLeaves leafWords occupied : Nat) (queries : List Nat) (output : List RawPath)
    (accepted : proof.open (hash C) root numLeaves queries occupied leafWords = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    (∀ p ∈ output, (fromPublic log root numLeaves.log2).get
      (addressAbove p.leafIndex numLeaves.log2 []) = some p.leafData) ∨
      OpenPrimitiveBad C log root output := by
  have refined := open_refines (hash C) proof root numLeaves queries occupied leafWords output accepted
  apply opened_rows C log auth root numLeaves.log2 output
  · intro p hp
    obtain ⟨q,hq,row,hr,hw,hi,hd,hl,hdepth,hroot⟩ := forall₂_mem_right refined hp
    exact hdepth
  · intro p hp
    obtain ⟨q,hq,row,hr,hw,hi,hd,hl,hdepth,hroot⟩ := forall₂_mem_right refined hp
    exact hroot
  · exact bounds

end Whir.PCSBCSMerkleSourceRows
