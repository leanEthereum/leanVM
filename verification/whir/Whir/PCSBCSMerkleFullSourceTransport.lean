import Whir.PCSBCSMerkleLeafImages

/-! Acceptance-side source boundary: read full leafWords images, check their
leading zeros, drain leafWords-occupied, then use the existing compact octopus
transport which reconstitutes the identical full hashed image. This models
successful output semantics, not the order/trace of rejected Rust executions. -/
namespace Whir.PCSBCSMerkleFullSourceTransport
open Concrete FiatShamirGame MerkleTransport MerkleBinding PCSBCSMerkleLeafImages

private theorem zeroPrefix_image (n : Nat) (row : List K)
    (checked : zeroPrefix n row = true) : row = List.replicate n 0 ++ row.drop n := by
  induction n generalizing row with
  | zero => simp
  | succ n ih =>
    cases row with
    | nil => simp [zeroPrefix] at checked
    | cons x xs =>
      simp only [zeroPrefix,Bool.and_eq_true,beq_iff_eq] at checked
      obtain ⟨rfl,tail⟩ := checked
      simpa only [List.replicate_succ,List.cons_append,List.drop_succ_cons] using
        congrArg (List.cons (0 : K)) (ih xs tail)

def compactLeaf (leafWords occupied : Nat) (image : List K) : Option (List K) :=
  if occupied ≤ leafWords ∧ image.length = leafWords ∧ zeroPrefix (leafWords-occupied) image = true
  then some (image.drop (leafWords-occupied)) else none

theorem compactLeaf_spec (leafWords occupied : Nat) (image compact : List K)
    (accepted : compactLeaf leafWords occupied image = some compact) :
    occupied ≤ leafWords ∧ compact.length = occupied ∧
      image = leafImage 0 leafWords compact := by
  unfold compactLeaf at accepted
  split at accepted
  next guard =>
    cases Option.some.inj accepted
    obtain ⟨fits,width,padding⟩ := guard
    have suffix : (image.drop (leafWords-occupied)).length = occupied := by
      simp only [List.length_drop,width]
      omega
    refine ⟨fits,suffix,?_⟩
    simpa only [leafImage,suffix] using zeroPrefix_image (leafWords-occupied) image padding
  next => contradiction

def compactProof (proof : PrunedMerklePaths) (leafWords occupied : Nat) : Option PrunedMerklePaths := do
  let rows ← collect (compactLeaf leafWords occupied) proof.leafData
  pure ⟨rows,proof.siblingHashes⟩

def openSource (hash : Primitive) (proof : PrunedMerklePaths) (root : Digest32)
    (numLeaves : Nat) (queries : List Nat) (leafWords occupied : Nat) : Option (List RawPath) := do
  let compact ← compactProof proof leafWords occupied
  compact.open hash root numLeaves queries occupied leafWords

theorem openSource_refines (hash : Primitive) (proof : PrunedMerklePaths) (root : Digest32)
    (numLeaves : Nat) (queries : List Nat) (leafWords occupied : Nat) (output : List RawPath)
    (accepted : openSource hash proof root numLeaves queries leafWords occupied = some output) :
    ∃ compact, compactProof proof leafWords occupied = some compact ∧
      compact.open hash root numLeaves queries occupied leafWords = some output := by
  simpa only [openSource,Option.bind_eq_bind,Option.bind_eq_some_iff] using accepted

/-- Invalid padding cannot be accepted, even when its full bytes hash to root. -/
theorem compactLeaf_reject_padding (leafWords occupied : Nat) (image : List K)
    (invalid : zeroPrefix (leafWords-occupied) image ≠ true) :
    compactLeaf leafWords occupied image = none := by
  simp [compactLeaf,invalid]

end Whir.PCSBCSMerkleFullSourceTransport
