import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.EncodingSelectionCache
import SphincsSecurity.Proof.Base.FirstSuccessTable
import SphincsSecurity.Proof.Hypertree.FrontierSigningEvaluation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def decodeEncodingOutput (output : HashOutput) : Option Encoding := TargetSum.decodeDigest (truncateHash output)

theorem decodeEncodingOutput_invalid_nonempty : (FirstSuccessTable.invalid decodeEncodingOutput).Nonempty := by
  refine ⟨0, (FirstSuccessTable.mem_invalid _ _).mpr ?_⟩
  decide

def referenceEncodingTable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (attempts start : Nat) : Fin attempts → HashOutput :=
  fun index => f (encodingRetryInput parameter position message (start + index.val))

def encodingTableResult {n : Nat} (table : Fin n → HashOutput) (start : Nat) : Option (Counter × Encoding) × Nat :=
  let result := FirstSuccessTable.select decodeEncodingOutput table
  (result.map (fun result => (BitVec.ofNat counterBits (start + result.1.val), result.2)),
    result.elim n (fun result => result.1.val + 1))

theorem eval_encode_eq_decodeEncodingOutput (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (counter : Nat) :
    evalWithAnswerFn f (encode parameter position.lay position.tree position.leafIdx message
      (BitVec.ofNat counterBits counter)) =
        decodeEncodingOutput (f (encodingRetryInput parameter position message counter)) := by
  simp only [encode, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure]
  rfl

theorem referenceEncodingSearch_eq_table (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (position : EncodingPosition) (message : Digest) (attempts start : Nat) :
    referenceEncodingSearch parameter f position.lay position.tree position.leafIdx message attempts start =
      encodingTableResult (referenceEncodingTable parameter f position message attempts start) start := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      have htail :
          (fun i : Fin attempts => referenceEncodingTable parameter f position message (attempts + 1) start i.succ) =
            referenceEncodingTable parameter f position message attempts (start + 1) := by
        funext i
        change f (encodingRetryInput parameter position message (start + (i.val + 1))) =
          f (encodingRetryInput parameter position message (start + 1 + i.val))
        rw [show start + (i.val + 1) = start + 1 + i.val by omega]
      rw [referenceEncodingSearch, eval_encode_eq_decodeEncodingOutput,
        encodingTableResult, FirstSuccessTable.select]
      have hzero : referenceEncodingTable parameter f position message (attempts + 1) start 0 =
          f (encodingRetryInput parameter position message start) := by simp [referenceEncodingTable]
      rw [hzero]
      cases hdecode : decodeEncodingOutput (f (encodingRetryInput parameter position message start)) with
      | some word => simp
      | none =>
          rw [htail, ih]
          unfold encodingTableResult
          cases hselected : FirstSuccessTable.select decodeEncodingOutput
              (referenceEncodingTable parameter f position message attempts (start + 1)) with
          | none => simp [Nat.add_comm]
          | some result =>
              rcases result with ⟨index, word⟩
              simp [Nat.add_comm, Nat.add_left_comm]

end SphincsSecurity.Concrete
