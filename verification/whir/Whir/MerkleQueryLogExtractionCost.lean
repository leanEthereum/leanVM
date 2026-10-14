import Whir.MerkleQueryLogExtractionRows
import Whir.PublicMerkleProbability

/-! Structural resource certificates. A visit is one preindexed digest lookup
and at most one codec invocation. This is not a unit-cost cryptographic/hash
assumption: hash-table bucket comparisons and public-log saturation are separate.
Record byte lengths are bounded from actual public recovery fuel. -/
namespace Whir.MerkleQueryLogExtraction
open Concrete FiatShamirGame MerkleTransport.Commitments PublicMerkleLog

/-- Instrument the same descent, without per-row log scans. -/
def countedExtract (codec : Codec) (index : Index) : Nat → Digest32 → Tree × Nat
  | 0, d => (extract codec index 0 d,1)
  | h+1, d => match index[key d]? with
    | none => (.absent,1)
    | some bytes => match codec.pair bytes with
      | none => (.absent,1)
      | some (l,r) =>
        let left := countedExtract codec index h l
        let right := countedExtract codec index h r
        (.branch left.1 right.1,1+left.2+right.2)

theorem countedExtract_value (codec : Codec) (index : Index) (height : Nat) (root : Digest32) :
    (countedExtract codec index height root).1 = extract codec index height root := by
  induction height generalizing root with
  | zero => rfl
  | succ h ih =>
    simp only [countedExtract,extract]
    cases hi : index[key root]? with
    | none => rfl
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp only [hp]
      | some pair => rcases pair with ⟨l,r⟩; simp only [hp,ih]

theorem countedExtract_visits (codec : Codec) (index : Index) (height : Nat) (root : Digest32) :
    (countedExtract codec index height root).2 + 1 ≤ 2^(height+1) := by
  induction height generalizing root with
  | zero => simp [countedExtract]
  | succ h ih =>
    simp only [countedExtract]
    cases hi : index[key root]? with
    | none =>
      have positive : 0 < 2^(h+1) := by positivity
      simp only [pow_succ]
      omega
    | some bytes =>
      cases hp : codec.pair bytes with
      | none =>
        have positive : 0 < 2^(h+1) := by positivity
        simp only [hp,pow_succ]
        omega
      | some pair =>
        rcases pair with ⟨l,r⟩
        have hl := ih l
        have hr := ih r
        simp only [hp]
        rw [pow_succ]
        omega

/-- No extracted tree contains more live nodes than this exact full-depth
visit bound. Missing/malformed nodes short-circuit, not scan additional rows. -/
theorem fixed_depth_visit_budget (codec : Codec) (index : Index) (height : Nat) (root : Digest32)
    (N : Nat) (shape : N = 2^height) :
    (countedExtract codec index height root).2 < 2*N := by
  have h := countedExtract_visits codec index height root
  rw [pow_succ,← shape] at h
  omega

theorem build_size (records : Records) : (build records).size ≤ records.length := by
  induction records with
  | nil => simp [build]
  | cons e rest ih =>
    rcases e with ⟨bytes,d⟩
    have h := Std.ExtHashMap.size_insert_le (m := build rest) (k := key d) (v := bytes)
    simp only [build,List.length_cons]
    omega

theorem public_index_size (log : PublicLog) : (build (records log)).size ≤ log.length :=
  (build_size (records log)).trans (PublicMerkleProbability.records_length log)

theorem public_record_bytes (log : PublicLog) (bytes : List Byte) (d : Digest32)
    (hm : (bytes,d) ∈ records log) : bytes.length ≤ 64*(log.length+2) := by
  obtain ⟨n,_,hp⟩ := PublicMerkleBinding.records_origin hm
  exact PublicMerkleLog.parse_resource_bound hp

/-- Actual retained reconstructed payload, not a guessed width budget. -/
theorem public_payload_bytes (log : PublicLog) :
    ((records log).map (fun record => record.1.length)).sum ≤
      log.length * (64*(log.length+2)) := by
  have sum := List.sum_le_length_nsmul
    ((records log).map (fun record => record.1.length)) (64*(log.length+2)) (by
      intro size hm
      obtain ⟨⟨bytes,d⟩,member,rfl⟩ := List.mem_map.mp hm
      exact public_record_bytes log bytes d member)
  have count := PublicMerkleProbability.records_length log
  simp only [List.length_map,smul_eq_mul] at sum
  exact sum.trans (Nat.mul_le_mul_right _ count)

theorem public_selected_bytes (log : PublicLog) (root : Digest32) (bytes : List Byte)
    (hit : (build (records log))[key root]? = some bytes) :
    bytes.length ≤ 64*(log.length+2) := public_record_bytes log bytes root (build_mem hit)


def countedFill (default : Array K) : Nat → Array (Array K) × Nat → Array (Array K) × Nat
  | 0, state => state
  | n+1, state => countedFill default n (state.1.push default,state.2+1)

theorem countedFill_value (default : Array K) (n : Nat) (state : Array (Array K) × Nat) :
    (countedFill default n state).1 = fill default n state.1 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simpa only [countedFill,fill] using ih (state.1.push default,state.2+1)

theorem countedFill_pushes (default : Array K) (n : Nat) (state : Array (Array K) × Nat) :
    (countedFill default n state).2 = state.2+n := by
  induction n generalizing state with
  | zero => simp [countedFill]
  | succ n ih => simp [countedFill,ih,Nat.add_comm,Nat.add_left_comm]

def countedEmit (width : Nat) (default : Array K) :
    Nat → Tree → Array (Array K) × Nat → Array (Array K) × Nat
  | 0, .leaf row, state =>
    (state.1.push (if row.length = width then row.toArray else default),state.2+1)
  | h+1, .branch l r, state =>
    countedEmit width default h r (countedEmit width default h l state)
  | h, _, state => countedFill default (2^h) state

theorem countedEmit_value (width : Nat) (default : Array K) (height : Nat) (tree : Tree)
    (state : Array (Array K) × Nat) :
    (countedEmit width default height tree state).1 = emit width default height tree state.1 := by
  induction height generalizing tree state with
  | zero => cases tree <;> simp only [countedEmit,emit,countedFill_value]
  | succ h ih => cases tree <;> simp only [countedEmit,emit,countedFill_value,ih]

theorem countedEmit_pushes (width : Nat) (default : Array K) (height : Nat) (tree : Tree)
    (state : Array (Array K) × Nat) :
    (countedEmit width default height tree state).2 = state.2+2^height := by
  induction height generalizing tree state with
  | zero => cases tree <;> simp [countedEmit,countedFill_pushes]
  | succ h ih => cases tree <;>
      simp only [countedEmit,countedFill_pushes,ih,pow_succ,Nat.mul_two,Nat.add_assoc]

/-- Exact N output pushes, even for missing subtrees; shared default rows are
allocated once by the wrapper rather than copying a width-sized row N times. -/
theorem full_materialization_pushes (width height : Nat) (tree : Tree) :
    (countedEmit width (Array.replicate width 0) height tree (#[],0)).2 = 2^height := by
  simpa only [Nat.zero_add] using countedEmit_pushes width (Array.replicate width 0)
    height tree (#[],0)

def countedRows (codec : Codec) (index : Index) (width : Nat) (default : Array K) :
    Nat → Digest32 → Array (Array K) → Array (Array K) × Nat
  | 0, root, out => (extractRows codec index width default 0 root out,1)
  | h+1, root, out => match index[key root]? with
    | none => (fill default (2^(h+1)) out,1)
    | some bytes => match codec.pair bytes with
      | none => (fill default (2^(h+1)) out,1)
      | some (l,r) =>
        let left := countedRows codec index width default h l out
        let right := countedRows codec index width default h r left.1
        (right.1,1+left.2+right.2)

theorem countedRows_value (codec : Codec) (index : Index) (width : Nat) (default : Array K)
    (height : Nat) (root : Digest32) (out : Array (Array K)) :
    (countedRows codec index width default height root out).1 =
      extractRows codec index width default height root out := by
  induction height generalizing root out with
  | zero => rfl
  | succ h ih =>
    cases hi : index[key root]? with
    | none => simp [countedRows,extractRows,hi]
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp [countedRows,extractRows,hi,hp]
      | some pair => rcases pair with ⟨l,r⟩; simp only [countedRows,extractRows,hi,hp,ih]

theorem countedRows_visits (codec : Codec) (index : Index) (width : Nat) (default : Array K)
    (height : Nat) (root : Digest32) (out : Array (Array K)) :
    (countedRows codec index width default height root out).2 =
      (countedExtract codec index height root).2 := by
  induction height generalizing root out with
  | zero => rfl
  | succ h ih =>
    cases hi : index[key root]? with
    | none => simp [countedRows,countedExtract,hi]
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp [countedRows,countedExtract,hi,hp]
      | some pair => rcases pair with ⟨l,r⟩; simp only [countedRows,countedExtract,hi,hp,ih]

theorem fused_visit_budget (codec : Codec) (index : Index) (width height : Nat) (root : Digest32)
    (out : Array (Array K)) :
    (countedRows codec index width (Array.replicate width 0) height root out).2 < 2*2^height := by
  rw [countedRows_visits]
  exact fixed_depth_visit_budget codec index height root (2^height) rfl

end Whir.MerkleQueryLogExtraction
