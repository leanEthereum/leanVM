import Whir.PCSBCSMerkleRootCache
import Whir.PCSBCSMerkleOpenedTable
import Whir.PCSBCSMerkleFullSourceTransport

/-! Cache transport retains full images and literal compact suffixes separately.
Lookup supplies height, full image width and occupied width. Availability and
zero-prefix authentication are concluded only from accepted source openings. -/
namespace Whir.PCSBCSMerkleRootCache
open Concrete FiatShamirGame PublicMerkleLog PublicMerkleBinding MerkleTransport
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PCSBCSMerkleLeafImages

theorem cached_opened_table (C : DuplexModeGame.PrimitiveOracle) (registry : Registry)
    (valid : WellFormed registry) (root : Digest32) (frozen : Frozen)
    (proof : PrunedMerklePaths) (numLeaves leafWords occupied : Nat)
    (queries : List Nat) (output : List RawPath)
    (known : registry[cacheKey root ⟨numLeaves.log2,leafWords,occupied⟩]? = some frozen)
    (auth : AuthenticLog C frozen.queryPrefix)
    (accepted : proof.open (hash C) root numLeaves queries occupied leafWords = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    List.Forall₂ (fun q p => frozen.raw[q]! =
      (p.leafData.drop (leafWords-occupied)).toArray ∧
      (frozen.cells[q]?).map (fun cell => (cell.available,cell.paddingValid)) = some (true,true))
      queries output ∨ OpenPrimitiveBad C frozen.queryPrefix root output := by
  have provenance := valid root ⟨numLeaves.log2,leafWords,occupied⟩ frozen known
  have rows : frozen.raw = compactTable
      (sourceCells frozen.queryPrefix root numLeaves.log2 leafWords occupied) :=
    congrArg Frozen.raw provenance
  have cells : frozen.cells = sourceCells frozen.queryPrefix root numLeaves.log2 leafWords occupied :=
    congrArg Frozen.cells provenance
  rcases PCSBCSMerkleSourceRows.pruned_opened_compact C frozen.queryPrefix auth root
      proof numLeaves leafWords occupied queries output accepted bounds with good | bad
  · left
    simpa only [rows,cells] using good
  · exact Or.inr bad

/-- Successful full-wire source semantics includes the checked zero prefix
before compacting; invalid padding is a local rejection, not a bad hash event. -/
theorem cached_opened_source (C : DuplexModeGame.PrimitiveOracle) (registry : Registry)
    (valid : WellFormed registry) (root : Digest32) (frozen : Frozen)
    (fullProof : PrunedMerklePaths) (numLeaves leafWords occupied : Nat)
    (queries : List Nat) (output : List RawPath)
    (known : registry[cacheKey root ⟨numLeaves.log2,leafWords,occupied⟩]? = some frozen)
    (auth : AuthenticLog C frozen.queryPrefix)
    (accepted : PCSBCSMerkleFullSourceTransport.openSource (hash C) fullProof root
      numLeaves queries leafWords occupied = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    List.Forall₂ (fun q p => frozen.raw[q]! =
      (p.leafData.drop (leafWords-occupied)).toArray ∧
      (frozen.cells[q]?).map (fun cell => (cell.available,cell.paddingValid)) = some (true,true))
      queries output ∨ OpenPrimitiveBad C frozen.queryPrefix root output := by
  obtain ⟨compact,_decoded,opened⟩ := PCSBCSMerkleFullSourceTransport.openSource_refines
    (hash C) fullProof root numLeaves queries leafWords occupied output accepted
  exact cached_opened_table C registry valid root frozen compact numLeaves leafWords occupied
    queries output known auth opened bounds

end Whir.PCSBCSMerkleRootCache
