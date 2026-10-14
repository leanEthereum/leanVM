import Whir.MerkleTransport

/-! The native opening verifier hashes the full padded leaf, removes its leading
absent lanes, and leaves the occupied row in raw descending order. The WHIR
base-row fold performs the one reversal; extraction must not reverse twice. -/
namespace Whir.WHIRPhysicalRows
open Concrete FiatShamirGame MerkleTransport MerkleTransport.Commitments MerkleBinding

noncomputable def compactBaseRow (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index leafWords lanes : Nat) : List K :=
  (baseRow hash snapshot root height index leafWords).drop (leafWords - lanes)

noncomputable def compactBaseOracle (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows leafWords lanes : Nat) : Array (Array K) :=
  Array.ofFn (fun q : Fin numRows =>
    (compactBaseRow hash snapshot root height q.val leafWords lanes).toArray)

theorem compactBaseRow_length (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index leafWords lanes : Nat) (fits : lanes ≤ leafWords) :
    (compactBaseRow hash snapshot root height index leafWords lanes).length = lanes := by
  simp only [compactBaseRow,List.length_drop,baseRow_length]
  omega

theorem compactBaseOracle_size (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows leafWords lanes : Nat) :
    (compactBaseOracle hash snapshot root height numRows leafWords lanes).size = numRows := by
  simp [compactBaseOracle]

theorem compactBaseOracle_get (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows leafWords lanes index : Nat) (bound : index < numRows) :
    (compactBaseOracle hash snapshot root height numRows leafWords lanes)[index]! =
      (compactBaseRow hash snapshot root height index leafWords lanes).toArray := by
  simp [compactBaseOracle,bound]

theorem compactBaseOracle_row_size (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows leafWords lanes index : Nat) (fits : lanes ≤ leafWords) (bound : index < numRows) :
    ((compactBaseOracle hash snapshot root height numRows leafWords lanes)[index]!).size = lanes := by
  rw [compactBaseOracle_get _ _ _ _ _ _ _ _ bound]
  simpa using compactBaseRow_length hash snapshot root height index leafWords lanes fits

theorem compactBaseRow_of_leaf (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height index leafWords lanes : Nat) (stored : List K)
    (width : stored.length = lanes) (fits : lanes ≤ leafWords)
    (extracted : row hash snapshot root height index = leafImage 0 leafWords stored) :
    compactBaseRow hash snapshot root height index leafWords lanes = stored := by
  have full : (leafImage (0 : K) leafWords stored).length = leafWords :=
    leafImage_length 0 leafWords stored (width ▸ fits)
  unfold compactBaseRow baseRow
  rw [extracted,ite_eq_left full]
  simpa only [leafImage,width,List.length_replicate] using
    (List.drop_left : (List.replicate (leafWords-lanes) (0 : K) ++ stored).drop
      (List.replicate (leafWords-lanes) (0 : K)).length = stored)

theorem compactBaseOracle_locality (hash other : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows leafWords lanes : Nat) (agree : ∀ x ∈ snapshot.table, hash x = other x) :
    compactBaseOracle hash snapshot root height numRows leafWords lanes =
      compactBaseOracle other snapshot root height numRows leafWords lanes := by
  simp only [compactBaseOracle,compactBaseRow,baseRow,row,
    oracle_locality hash other snapshot root agree]
  rfl

theorem compactBaseOracle_eq_recorded (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows leafWords lanes : Nat) (records : Records) (absent : Digest32)
    (authentic : Authentic hash records) (covered : snapshot.table ⊆ recordDomain records) :
    compactBaseOracle hash snapshot root height numRows leafWords lanes =
      compactBaseOracle (recordedHash records absent) snapshot root height numRows leafWords lanes :=
  compactBaseOracle_locality hash _ snapshot root height numRows leafWords lanes
    (recordedHash_agrees_on_snapshot hash records absent snapshot authentic covered)

/-- Accepted native padded paths give the same occupied rows, in original query
order, once the public primitive binding theorem supplies its non-bad branch. -/
theorem open_compact_rows (hash : Primitive) (snapshot : Snapshot)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (lanes leafWords : Nat) (output : List RawPath)
    (accepted : proof.open hash root numLeaves queries lanes leafWords = some output)
    (bound : ∀ path ∈ output,
      path.leafData = row hash snapshot root numLeaves.log2 path.leafIndex) :
    List.Forall₂ (fun q path => (path.leafData.drop (leafWords-lanes)).toArray =
      (compactBaseOracle hash snapshot root numLeaves.log2 numLeaves leafWords lanes)[q]!)
      queries output := by
  have refined := open_refines _ _ _ _ _ _ _ _ accepted
  have conditions := ((open_spec _ _ _ _ _ _ _ _).mp accepted).1
  apply List.forall₂_of_length_eq_of_get refined.length_eq
  intro i hi ho
  obtain ⟨stored,hs,hw,hindex,hdata,hlen,hdepth,hroot⟩ := refined.get hi ho
  have hq := conditions.range (queries.get ⟨i,hi⟩) (List.get_mem _ _)
  have hraw := bound (output.get ⟨i,ho⟩) (List.get_mem _ _)
  rw [compactBaseOracle_get _ _ _ _ _ _ _ _ hq]
  congr 1
  rw [← hindex]
  simp only [compactBaseRow,baseRow,← hraw,hlen,↓reduceIte]

end Whir.WHIRPhysicalRows
