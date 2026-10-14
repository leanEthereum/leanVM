import Whir.PCSBCSMerkleSourceRows

/-! Full images remain in the Merkle relation. Compact suffix authentication is
established only for accepted source openings with their zero-prefix image;
absence defaults and arbitrary committed padding are not authenticated. -/
namespace Whir.PCSBCSMerkleSourceRows
open Concrete FiatShamirGame MerkleTransport MerkleTransport.Commitments
open MerkleBinding
open MerkleQueryLogExtraction PCSBCSMerkleQueryLog PublicMerkleLog PublicMerkleBinding
open PCSBCSMerkleLeafImages

theorem pruned_opened_table (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (root : Digest32) (proof : PrunedMerklePaths)
    (numLeaves leafWords occupied : Nat) (queries : List Nat) (output : List RawPath)
    (accepted : proof.open (hash C) root numLeaves queries occupied leafWords = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    List.Forall₂ (fun q p => (rawRoot0 log root numLeaves.log2 leafWords)[q]! = p.leafData.toArray)
      queries output ∨ OpenPrimitiveBad C log root output := by
  have refined := open_refines (hash C) proof root numLeaves queries occupied leafWords output accepted
  have conditions := ((open_spec (hash C) proof root numLeaves queries occupied leafWords output).mp accepted).1
  rcases pruned_opened_rows C log auth root proof numLeaves leafWords occupied queries output accepted bounds with good | bad
  · left
    apply List.forall₂_of_length_eq_of_get refined.length_eq
    intro i hi ho
    obtain ⟨stored,hs,hw,hindex,hdata,hlen,hdepth,hroot⟩ := refined.get hi ho
    have hq := conditions.range (queries.get ⟨i,hi⟩) (List.get_mem _ _)
    have inside : queries.get ⟨i,hi⟩ < 2^numLeaves.log2 := by simpa only [conditions.power] using hq
    have tree := good (output.get ⟨i,ho⟩) (List.get_mem _ _)
    rw [hindex] at tree
    have table := fullRows_get leafWords numLeaves.log2 (fromPublic log root numLeaves.log2)
      (queries.get ⟨i,hi⟩) inside
    simp only [Tree.row,tree,Option.getD_some,MerkleQueryLogExtraction.normalize,hlen,↓reduceIte] at table
    have bound : queries.get ⟨i,hi⟩ <
        (fullRows leafWords numLeaves.log2 (fromPublic log root numLeaves.log2)).size := by
      simpa only [fullRows_size] using inside
    rw [Array.getElem?_eq_getElem bound] at table
    have result := Option.some.inj table
    rw [rawRoot0_eq_fullRows]
    simpa only [getElem!_pos
      (fullRows leafWords numLeaves.log2 (fromPublic log root numLeaves.log2))
      (queries.get ⟨i,hi⟩) bound] using result
  · exact Or.inr bad

/-- Both status bits are proved, independently of numerical zero defaults. -/
theorem pruned_opened_compact (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (auth : AuthenticLog C log) (root : Digest32) (proof : PrunedMerklePaths)
    (numLeaves leafWords occupied : Nat) (queries : List Nat) (output : List RawPath)
    (accepted : proof.open (hash C) root numLeaves queries occupied leafWords = some output)
    (bounds : ∀ p ∈ output, ∀ bytes ∈ p.opening.inputs (hashing (hash C)), bytes.length < 2^64) :
    List.Forall₂ (fun q p =>
      (compactTable (sourceCells log root numLeaves.log2 leafWords occupied))[q]! =
        (p.leafData.drop (leafWords-occupied)).toArray ∧
      ((sourceCells log root numLeaves.log2 leafWords occupied)[q]?).map
        (fun cell => (cell.available,cell.paddingValid)) = some (true,true)) queries output ∨
      OpenPrimitiveBad C log root output := by
  have refined := open_refines (hash C) proof root numLeaves queries occupied leafWords output accepted
  have conditions := ((open_spec (hash C) proof root numLeaves queries occupied leafWords output).mp accepted).1
  rcases pruned_opened_rows C log auth root proof numLeaves leafWords occupied queries output accepted bounds with good | bad
  · left
    apply List.forall₂_of_length_eq_of_get refined.length_eq
    intro i hi ho
    obtain ⟨stored,hs,hw,hindex,hdata,hlen,hdepth,hroot⟩ := refined.get hi ho
    have hq := conditions.range (queries.get ⟨i,hi⟩) (List.get_mem _ _)
    have inside : queries.get ⟨i,hi⟩ < 2^numLeaves.log2 := by simpa only [conditions.power] using hq
    have tree := good (output.get ⟨i,ho⟩) (List.get_mem _ _)
    rw [hindex] at tree
    have cell := sourceCells_get log root numLeaves.log2 leafWords occupied (queries.get ⟨i,hi⟩) inside
    simp only [cellAt,tree] at cell
    have admitted := leafCell_admitted leafWords occupied stored hw conditions.fits
    have drop : ((output.get ⟨i,ho⟩).leafData.drop (leafWords-occupied)).toArray = stored.toArray := by
      rw [hdata]
      simp [leafImage,hw]
    rw [hdata] at cell
    refine ⟨?_,?_⟩
    · rw [drop]
      simp only [compactTable,getElem!_def,Array.getElem?_map,cell,Option.map_some,admitted.2.2]
    · rw [cell]
      simp only [Option.map_some,admitted.1,admitted.2.1]
  · exact Or.inr bad

end Whir.PCSBCSMerkleSourceRows
