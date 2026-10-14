import Whir.PCSBCSMerkleLeafImages
import Whir.MerkleQueryLogExtractionResourceContract

/-! Instrumented fused image/suffix extraction, with the same shared default
cell as production. No counter is executed by the production cache. -/
namespace Whir.PCSBCSMerkleLeafImages
open Concrete FiatShamirGame PublicMerkleLog MerkleQueryLogExtraction PCSBCSMerkleQueryLog

def countedCells (codec : Codec) (index : Index) (leafWords occupied : Nat) (default : ImageCell) :
    Nat → Digest32 → Array ImageCell → Array ImageCell × Nat
  | 0, root, out => (extractCells codec index leafWords occupied default 0 root out,1)
  | h+1, root, out => match index[key root]? with
    | none => (fillCells default (2^(h+1)) out,1)
    | some bytes => match codec.pair bytes with
      | none => (fillCells default (2^(h+1)) out,1)
      | some (l,r) =>
        let left := countedCells codec index leafWords occupied default h l out
        let right := countedCells codec index leafWords occupied default h r left.1
        (right.1,1+left.2+right.2)

theorem countedCells_value (codec : Codec) (index : Index) (leafWords occupied : Nat)
    (default : ImageCell) (height : Nat) (root : Digest32) (out : Array ImageCell) :
    (countedCells codec index leafWords occupied default height root out).1 =
      extractCells codec index leafWords occupied default height root out := by
  induction height generalizing root out with
  | zero => rfl
  | succ h ih =>
    cases hi : index[key root]? with
    | none => simp [countedCells,extractCells,hi]
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp [countedCells,extractCells,hi,hp]
      | some pair => rcases pair with ⟨l,r⟩; simp only [countedCells,extractCells,hi,hp,ih]

theorem countedCells_visits (codec : Codec) (index : Index) (leafWords occupied : Nat)
    (default : ImageCell) (height : Nat) (root : Digest32) (out : Array ImageCell) :
    (countedCells codec index leafWords occupied default height root out).2 =
      (countedExtract codec index height root).2 := by
  induction height generalizing root out with
  | zero => rfl
  | succ h ih =>
    cases hi : index[key root]? with
    | none => simp [countedCells,countedExtract,hi]
    | some bytes =>
      cases hp : codec.pair bytes with
      | none => simp [countedCells,countedExtract,hi,hp]
      | some pair => rcases pair with ⟨l,r⟩; simp only [countedCells,countedExtract,hi,hp,ih]

theorem source_visit_budget (log : PublicLog) (root : Digest32) (height leafWords occupied : Nat) :
    (countedCells canonicalCodec (build (records log)) leafWords occupied
      (defaultCell leafWords occupied) height root #[]).2 < 2*(2^height) := by
  rw [countedCells_visits]
  exact fixed_depth_visit_budget _ _ _ _ _ rfl

theorem compact_word_slots (log : PublicLog) (root : Digest32)
    (height leafWords occupied : Nat) (fits : occupied ≤ leafWords) :
    ((compactTable (sourceCells log root height leafWords occupied)).toList.map Array.size).sum ≤
      2^height*occupied := by
  have shape := compactTable_shape log root height leafWords occupied fits
  have bound := List.sum_le_length_nsmul
    ((compactTable (sourceCells log root height leafWords occupied)).toList.map Array.size) occupied (by
      intro size member
      obtain ⟨row,inside,rfl⟩ := List.mem_map.mp member
      exact le_of_eq (shape.2 row inside))
  simpa only [List.length_map,Array.length_toList,shape.1,smul_eq_mul] using bound

theorem image_word_slots (log : PublicLog) (root : Digest32)
    (height leafWords occupied : Nat) :
    ((imageTable (sourceCells log root height leafWords occupied)).toList.map Array.size).sum ≤
      2^height*leafWords := by
  rw [imageTable_eq_full]
  exact rawRoot0_word_slots log root height leafWords

/-- Actual byte volume supplied to leaf/pair codecs at visited preimages.
This is a data-operation metric, not a machine-instruction claim. -/
def inputByteVolume (codec : Codec) (index : Index) : Nat → Digest32 → Nat
  | 0, root => match index[key root]? with
    | none => 0
    | some bytes => bytes.length
  | h+1, root => match index[key root]? with
    | none => 0
    | some bytes => match codec.pair bytes with
      | none => bytes.length
      | some (l,r) => bytes.length + inputByteVolume codec index h l + inputByteVolume codec index h r

theorem inputByteVolume_bound (codec : Codec) (index : Index) (height : Nat)
    (root : Digest32) (B : Nat)
    (cap : ∀ d bytes, index[key d]? = some bytes → bytes.length ≤ B) :
    inputByteVolume codec index height root ≤ (countedExtract codec index height root).2*B := by
  induction height generalizing root with
  | zero =>
    cases hit : index[key root]? with
    | none => simp [inputByteVolume,hit,countedExtract]
    | some bytes => simpa [inputByteVolume,hit,countedExtract] using cap root bytes hit
  | succ h ih =>
    cases hit : index[key root]? with
    | none => simp [inputByteVolume,hit,countedExtract]
    | some bytes =>
      have size := cap root bytes hit
      cases parsed : codec.pair bytes with
      | none => simpa [inputByteVolume,countedExtract,hit,parsed] using size
      | some pair =>
        rcases pair with ⟨l,r⟩
        have left := ih l
        have right := ih r
        simp only [inputByteVolume,countedExtract,hit,parsed]
        nlinarith

theorem public_input_byte_volume (log : PublicLog) (root : Digest32) (height Q N : Nat)
    (queryCap : log.length ≤ Q) (rowCap : 2^height ≤ N) :
    inputByteVolume canonicalCodec (build (records log)) height root ≤ 2*N*(64*(Q+2)) := by
  have bytes := inputByteVolume_bound canonicalCodec (build (records log)) height root
    (64*(log.length+2)) (public_selected_bytes log)
  have visits := fixed_depth_visit_budget canonicalCodec (build (records log)) height root (2^height) rfl
  have count : (countedExtract canonicalCodec (build (records log)) height root).2 ≤ 2*N := by omega
  exact bytes.trans (Nat.mul_le_mul count (by omega))

end Whir.PCSBCSMerkleLeafImages
