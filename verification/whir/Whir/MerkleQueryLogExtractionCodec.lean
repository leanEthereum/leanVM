import Whir.MerkleQueryLogExtraction

/-! Canonical untagged Merkle byte parsing. These inverse proofs concern the
Lean byte codec; they are not a new Rust parser refinement claim. -/
namespace Whir.MerkleQueryLogExtraction
open Concrete FiatShamirGame

/-- Decode eight bytes at a time. Any non-word-aligned input is rejected. -/
def decodeWords : List Byte → Option (List K)
  | [] => some []
  | a :: b :: c :: d :: e :: f :: g :: h :: rest =>
    (decodeWords rest).map (ByteCodec.decodeK (fun i =>
      (#[a,b,c,d,e,f,g,h])[i.val]!) :: ·)
  | _ => none

private theorem word_array (x : K) :
    (fun i : Fin 8 => (#[ByteCodec.encodeK x 0,ByteCodec.encodeK x 1,
      ByteCodec.encodeK x 2,ByteCodec.encodeK x 3,ByteCodec.encodeK x 4,
      ByteCodec.encodeK x 5,ByteCodec.encodeK x 6,ByteCodec.encodeK x 7])[i.val]!) =
      ByteCodec.encodeK x := by
  funext i
  fin_cases i <;> rfl

theorem decodeWords_complete (row : List K) :
    decodeWords (ByteCodec.wordsBytes row) = some row := by
  induction row with
  | nil => rfl
  | cons x xs ih =>
    change decodeWords (List.ofFn (ByteCodec.encodeK x) ++ ByteCodec.wordsBytes xs) = _
    have first : List.ofFn (ByteCodec.encodeK x) =
        [ByteCodec.encodeK x 0,ByteCodec.encodeK x 1,ByteCodec.encodeK x 2,
          ByteCodec.encodeK x 3,ByteCodec.encodeK x 4,ByteCodec.encodeK x 5,
          ByteCodec.encodeK x 6,ByteCodec.encodeK x 7] := by rfl
    rw [first]
    change (decodeWords (ByteCodec.wordsBytes xs)).map
      (ByteCodec.decodeK (fun i : Fin 8 => (#[ByteCodec.encodeK x 0,ByteCodec.encodeK x 1,
        ByteCodec.encodeK x 2,ByteCodec.encodeK x 3,ByteCodec.encodeK x 4,
        ByteCodec.encodeK x 5,ByteCodec.encodeK x 6,ByteCodec.encodeK x 7])[i.val]!) :: ·) = _
    rw [ih,word_array,ByteCodec.decodeK_encodeK]
    rfl

private theorem bytes_array (a b c d e f g h : Byte) :
    List.ofFn (fun i : Fin 8 => (#[a,b,c,d,e,f,g,h])[i.val]!) = [a,b,c,d,e,f,g,h] := by
  rfl

theorem decodeWords_sound (bytes : List Byte) (row : List K)
    (decoded : decodeWords bytes = some row) : ByteCodec.wordsBytes row = bytes := by
  induction bytes using decodeWords.induct generalizing row with
  | case1 =>
    have eq : row = [] := Option.some.inj decoded.symm
    subst row
    rfl
  | case2 a b c d e f g h rest ih =>
    simp only [decodeWords,Option.map_eq_some_iff] at decoded
    obtain ⟨tail,ht,eq⟩ := decoded
    subst row
    change List.ofFn (ByteCodec.encodeK (ByteCodec.decodeK
      (fun i : Fin 8 => (#[a,b,c,d,e,f,g,h])[i.val]!))) ++ ByteCodec.wordsBytes tail = _
    rw [ByteCodec.encodeK_decodeK,bytes_array,ih tail ht]
    rfl
  | case3 bytes he => simp [decodeWords] at decoded

/-- Convert once to an array. The final equality guard rejects wrong lengths
and guarantees exact canonical bytes without a choice of digest halves. -/
def parsePair (bytes : List Byte) : Option (Digest32 × Digest32) :=
  let array := bytes.toArray
  let pair : Digest32 × Digest32 :=
    (fun i => array[i.val]?.getD 0, fun i => array[32+i.val]?.getD 0)
  if List.ofFn (ByteCodec.pairBytes pair) = bytes then some pair else none

theorem parsePair_sound (bytes : List Byte) (pair : Digest32 × Digest32)
    (decoded : parsePair bytes = some pair) : List.ofFn (ByteCodec.pairBytes pair) = bytes := by
  dsimp only [parsePair] at decoded
  split at decoded
  next he => cases Option.some.inj decoded; exact he
  next => contradiction

theorem parsePair_complete (pair : Digest32 × Digest32) :
    parsePair (List.ofFn (ByteCodec.pairBytes pair)) = some pair := by
  have eq : ((fun i : Fin 32 =>
      (List.ofFn (ByteCodec.pairBytes pair)).toArray[i.val]?.getD 0),
      (fun i : Fin 32 =>
      (List.ofFn (ByteCodec.pairBytes pair)).toArray[32+i.val]?.getD 0)) = pair := by
    apply Prod.ext
    · funext i
      have bound : i.val < 64 := by omega
      simp only [List.getElem?_toArray,List.getElem?_ofFn,dite_eq_left bound,Option.getD_some,
        ByteCodec.pairBytes,dite_eq_left i.isLt]
    · funext i
      have bound : 32+i.val < 64 := by omega
      have above : ¬32+i.val < 32 := by omega
      simp only [List.getElem?_toArray,List.getElem?_ofFn,dite_eq_left bound,Option.getD_some,
        ByteCodec.pairBytes,dite_eq_right above]
      apply congrArg pair.2
      apply Fin.ext
      change 32+i.val-32 = i.val
      omega
  dsimp only [parsePair]
  rw [eq]
  simp

def canonicalCodec : Codec where
  leaf := decodeWords
  pair := parsePair
  leaf_sound := decodeWords_sound
  leaf_complete := decodeWords_complete
  pair_sound := parsePair_sound
  pair_complete := parsePair_complete

end Whir.MerkleQueryLogExtraction
