import Whir.MerkleQueryLogExtractionSaturationCost
import Whir.PCSBCSMerkleQueryLog

/-! End-to-end resource contract in the explicit public-log data-operation
model. Hash-map insertion/lookup invocations are stated separately from the
standard library's internal bucket/instruction costs. Worst-case bucket work
is bounded by resident Q fixed-32-byte keys, not an assumed random digest hash.
No claim is made about wall-clock timings or a Rust allocator refinement. -/
namespace Whir.MerkleQueryLogExtraction
open Concrete FiatShamirGame PublicMerkleLog MerkleTransport.Commitments PCSBCSMerkleQueryLog

def countedBuild : Records → Index × Nat
  | [] => (∅,0)
  | (bytes,d)::rest =>
    let previous := countedBuild rest
    (previous.1.insert (key d) bytes,previous.2+1)

theorem countedBuild_value (records : Records) : (countedBuild records).1 = build records := by
  induction records with
  | nil => rfl
  | cons e rest ih => rcases e with ⟨bytes,d⟩; simp only [countedBuild,build,ih]

theorem countedBuild_steps (records : Records) : (countedBuild records).2 = records.length := by
  induction records with
  | nil => rfl
  | cons e rest ih => rcases e with ⟨bytes,d⟩; simp only [countedBuild,List.length_cons,ih]

theorem rawRoot0_word_slots (log : PublicLog) (root : Digest32) (height width : Nat) :
    ((rawRoot0 log root height width).toList.map Array.size).sum ≤ 2^height*width := by
  have shape := rawRoot0_shape log root height width
  have bound := List.sum_le_length_nsmul
    ((rawRoot0 log root height width).toList.map Array.size) width (by
      intro size member
      obtain ⟨row,hr,rfl⟩ := List.mem_map.mp member
      exact le_of_eq (shape.2 row hr))
  simpa only [List.length_map,Array.length_toList,shape.1,smul_eq_mul] using bound

/-- Cubic one-time compression-log saturation; Q preindex insertions; fewer
than 2N digest lookups/codec invocations; N row pushes; at most N*width occupied
word slots. These are ACTUAL counted computations or actual output sizes. -/
theorem actual_resource_contract (log : PublicLog) (root : Digest32) (height width Q N : Nat)
    (queries : log.length ≤ Q) (rows : N = 2^height) :
    (PublicCost.recordsFrom log log).2 ≤ Q*(20000*(Q+2)*(Q+2)+1) ∧
    (countedBuild (records log)).2 ≤ Q ∧
    (build (records log)).size ≤ Q ∧
    ((records log).map (fun record => record.1.length)).sum ≤ Q*(64*(Q+2)) ∧
    (countedRows canonicalCodec (build (records log)) width (Array.replicate width 0)
      height root #[]).2 < 2*N ∧
    (rawRoot0 log root height width).size = N ∧
    ((rawRoot0 log root height width).toList.map Array.size).sum ≤ N*width := by
  have saturation := PublicCost.actual_saturation_steps log
  have saturationCap : log.length*(20000*(log.length+2)*(log.length+2)+1) ≤
      Q*(20000*(Q+2)*(Q+2)+1) := by gcongr
  have inserts : (countedBuild (records log)).2 ≤ Q := by
    rw [countedBuild_steps]
    exact (PublicMerkleProbability.records_length log).trans queries
  have storage := public_payload_bytes log
  have storageCap : log.length*(64*(log.length+2)) ≤ Q*(64*(Q+2)) := by gcongr
  have visits := fused_visit_budget canonicalCodec (build (records log)) width height root #[]
  have shape := rawRoot0_shape log root height width
  have words := rawRoot0_word_slots log root height width
  rw [← rows] at visits shape words
  exact ⟨saturation.trans saturationCap,inserts,(public_index_size log).trans queries,
    storage.trans storageCap,visits,shape.1,words⟩

end Whir.MerkleQueryLogExtraction
