module

public import NativeVm.Equiv.Transcript
public import NativeVm.Model.Verify
public import Statement.Verifier.Lib
import Mathlib.Tactic.IntervalCases

/-!
# The model's verifier is the statement's

`Model.verify bytecode publicInput stream openings` is `verifyWith keccakF1600` of the bytecode's
`K` words, the public input and the proof the decoded stream and openings denote (`verify_eq`),
given that the model's walk simulates the statement's (`Sim (Model.verifyExecution …)
(verifyExecution computedBytecodeValue …)`, which the phases' modules prove).

* **The IV.** `ivWords` holds the tag's first eight bytes, then words shifted up a byte (`shiftWord`:
  `(a >>> 56) ||| (b <<< 8)` has the bytes `a`'s top byte, then `b`'s low seven), so its bytes are
  the tag, the bytecode's bytes and seven zeros; the first `9 + 8n` are `versionTag` then the
  bytecode's bytes (`ivBytes`), and `fiatShamirIv` is the statement's (`fiatShamirIv_eq`).
* **The seed** is then the statement's `spongeSeedWith` (`seed_eq`), and the start states related.
* **The end.** The walk's final states are related, so the stream is consumed exactly when the
  cursor reaches its end (the cursor never passes it), and so for the openings: `runProof`'s check.
-/

@[expose] public section

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

attribute [local irreducible] keccakF1600

/-! ## The IV's bytes -/

/-- A word of `ivWords`: `a`'s top byte, then `b`'s low seven. -/
abbrev shiftWord (a b : UInt64) : UInt64 := (a >>> 56) ||| (b <<< 8)

theorem shiftWord_byte_succ (a b : UInt64) (k : ℕ) (hk : k < 7) :
    (shiftWord a b >>> (8 * (k + 1)).toUInt64).toUInt8 = (b >>> (8 * k).toUInt64).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  interval_cases k <;> (
    ext i hi
    simp [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    rw [BitVec.getLsbD_of_ge _ _ (by omega)]
    simp (disch := omega) only [Bool.false_or, decide_eq_true, decide_eq_false, Bool.true_and,
      Bool.not_false])
  all_goals (congr 1; omega)

theorem shiftWord_byte_zero (a b : UInt64) :
    (shiftWord a b >>> (8 * 0).toUInt64).toUInt8 = (a >>> (8 * 7).toUInt64).toUInt8 := by
  apply UInt8.toBitVec_inj.mp
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]

/-- A word's top byte. -/
abbrev topByte (a : UInt64) : UInt8 := (a >>> (8 * 7).toUInt64).toUInt8

theorem wordBytes_eq (w : UInt64) :
    wordBytes w = (w >>> (8 * 0).toUInt64).toUInt8 ::
      (List.range 7).map fun k ↦ (w >>> (8 * (k + 1)).toUInt64).toUInt8 := rfl

theorem take_seven_wordBytes (w : UInt64) :
    (wordBytes w).take 7 = (List.range 7).map fun k ↦ (w >>> (8 * k).toUInt64).toUInt8 := rfl

theorem take_seven_append_top (b : UInt64) : (wordBytes b).take 7 ++ [topByte b] = wordBytes b :=
  rfl

theorem wordBytes_shiftWord (a b : UInt64) :
    wordBytes (shiftWord a b) = topByte a :: (wordBytes b).take 7 := by
  rw [wordBytes_eq, shiftWord_byte_zero, take_seven_wordBytes]
  exact congrArg _ (List.map_congr_left fun k hk ↦ shiftWord_byte_succ a b k (List.mem_range.mp hk))

/-- The shifted words of `a`, then `L` and a zero word, against `L` and a zero word: `a`'s top byte,
`L`'s bytes, seven zeros. -/
theorem wordsBytes_shift : ∀ (a : UInt64) (L : List UInt64),
    Native.Keccak.wordsBytes (List.zipWith shiftWord (a :: (L ++ [0])) (L ++ [0])) =
      topByte a :: Native.Keccak.wordsBytes L ++ List.replicate 7 0
  | a, [] => by
    simp only [List.nil_append, List.zipWith_cons_cons, List.zipWith_nil_right,
      Native.Keccak.wordsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      wordBytes_shiftWord]
    rfl
  | a, b :: L => by
    simp only [List.cons_append, List.zipWith_cons_cons]
    have ih := wordsBytes_shift b L
    simp only [List.cons_append] at ih
    simp only [Native.Keccak.wordsBytes, List.flatMap_cons] at ih ⊢
    rw [ih, wordBytes_shiftWord]
    conv_rhs => rw [← take_seven_append_top b]
    simp

theorem range_map_getD {E : List UInt64} {m : ℕ} (hE : E.length = m + 1) :
    (List.range m).map (fun k ↦ (E.getD k 0 >>> 56) ||| (E.getD (k + 1) 0 <<< 8)) =
      List.zipWith shiftWord E E.tail := by
  apply List.ext_getElem
  · simp [hE]
  · intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < E.length),
      List.getElem?_eq_getElem (by omega : k + 1 < E.length)]

theorem ivWords_toList (bytecode : Array UInt64) :
    (ivWords bytecode).toList =
      tagLow :: List.zipWith shiftWord (tagLast <<< 56 :: (bytecode.toList ++ [0]))
        (bytecode.toList ++ [0]) := by
  have hE : ((tagLast <<< 56) :: (bytecode.toList ++ [0])).length = bytecode.size + 1 + 1 := by
    simp
  rw [ivWords, Array.toList_append, Array.toList_map, Array.toList_range]
  simp only [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, Array.toList_append,
    ← List.getD_eq_getElem?_getD, List.cons_append, List.nil_append]
  rw [range_map_getD hE]
  rfl

/-- The version tag's bytes, `"leanvm-v1"`. -/
theorem versionTag_eq : versionTag = [108, 101, 97, 110, 118, 109, 45, 118, 49] := by
  unfold versionTag
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
  have hc : "leanvm-v1".toList = [Char.ofNat 108, Char.ofNat 101, Char.ofNat 97, Char.ofNat 110,
      Char.ofNat 118, Char.ofNat 109, Char.ofNat 45, Char.ofNat 118, Char.ofNat 49] := by
    simp
  rw [hc]
  simp [List.utf8Encode, String.utf8EncodeChar]
  have hb : ([108, 101, 97, 110, 118, 109, 45, 118, 49] : List UInt8).toByteArray =
      ⟨#[108, 101, 97, 110, 118, 109, 45, 118, 49]⟩ := by
    cases h : ([108, 101, 97, 110, 118, 109, 45, 118, 49] : List UInt8).toByteArray with
    | mk d => rw [← List.data_toByteArray, h]
  rw [hb]
  decide +kernel

/-- **The IV's bytes**: the first `9 + 8n` bytes of `ivWords` are the tag's, then the bytecode's. -/
theorem ivBytes (bytecode : Array UInt64) :
    (Native.Keccak.wordsBytes (ivWords bytecode).toList).take (9 + 8 * bytecode.size) =
      versionTag ++ (bytecode.toList.map K.ofLane).flatMap K.toBytes := by
  have htag : versionTag = wordBytes tagLow ++ [topByte (tagLast <<< 56)] := by
    rw [versionTag_eq]
    decide
  have hlen : (Native.Keccak.wordsBytes bytecode.toList).length = 8 * bytecode.size := by
    simp [Native.Keccak.wordsBytes, wordBytes, List.length_flatMap, mul_comm]
  have hfl : (bytecode.toList.map K.ofLane).flatMap K.toBytes =
      Native.Keccak.wordsBytes bytecode.toList := by
    simp [Native.Keccak.wordsBytes, List.flatMap_map, K.toBytes]
  rw [ivWords_toList, Native.Keccak.wordsBytes, List.flatMap_cons, ← Native.Keccak.wordsBytes,
    wordsBytes_shift, htag, hfl,
    show wordBytes tagLow ++ (topByte (tagLast <<< 56) :: Native.Keccak.wordsBytes bytecode.toList ++
      List.replicate 7 (0 : UInt8)) = (wordBytes tagLow ++ [topByte (tagLast <<< 56)] ++
        Native.Keccak.wordsBytes bytecode.toList) ++ List.replicate 7 (0 : UInt8) by simp,
    List.take_left' (by simp [hlen, wordBytes]; omega)]

/-! ## The seed -/

theorem fiatShamirIv_eq (bytecode : Array UInt64) :
    Model.fiatShamirIv bytecode =
      Id.run (fiatShamirIvWith (m := Id) keccakF1600 (bytecode.toList.map K.ofLane)) := by
  rw [Model.fiatShamirIv, ivBytes]
  rfl

theorem seed_eq (bytecode : Array UInt64) (publicInput : Vector UInt64 4) :
    seed bytecode publicInput =
      Id.run (spongeSeedWith (m := Id) keccakF1600 (bytecode.toList.map K.ofLane) publicInput) := by
  rw [seed, fiatShamirIv_eq]
  rfl

/-! ## The end -/

/-- The stream is consumed exactly when the cursor is at its end. -/
theorem _root_.NativeVm.Model.TState.Rel.stream_consumed {t : TState} {s : VerifierProgramState}
    (h : t.Rel s) : (t.cursor == t.stream.size) = s.stream.isEmpty := by
  have := h.cursor_le
  rw [← h.stream, Bool.eq_iff_iff, beq_iff_eq, List.isEmpty_iff, List.map_eq_nil_iff,
    List.drop_eq_nil_iff, Array.length_toList]
  omega

/-- The openings are consumed exactly when the phase cursor is at their end. -/
theorem _root_.NativeVm.Model.TState.Rel.openings_consumed {t : TState}
    {s : VerifierProgramState} (h : t.Rel s) : (t.phase == t.openings.size) = s.openings.isEmpty := by
  have := h.phase_le
  rw [← h.openings, Bool.eq_iff_iff, beq_iff_eq, List.isEmpty_iff, List.map_eq_nil_iff,
    List.drop_eq_nil_iff, Array.length_toList]
  omega

/-- **The model's verifier is the statement's**, given that the model's walk simulates the
statement's. -/
theorem verify_eq_of_sim (bytecode : Array UInt64) (publicInput : Vector UInt64 4)
    (stream : Array EW) (openings : Array (Array OpeningW))
    (hwalk : Sim (Model.verifyExecution bytecode publicInput)
      (Verifier.verifyExecution computedBytecodeValue (bytecode.toList.map K.ofLane) publicInput)
      fun _ _ ↦ True) :
    Model.verify bytecode publicInput stream openings =
      Id.run (verifyWith (m := Id) keccakF1600 (bytecode.toList.map K.ofLane) publicInput
        ⟨stream.toList.map EW.toE, openings.toList.map phaseOpenings⟩) := by
  let start : TState := ⟨⟨seed bytecode publicInput, #[], none⟩, stream, 0, openings, 0, #[]⟩
  let s0 : VerifierProgramState :=
    ⟨⟨Id.run (spongeSeedWith (m := Id) keccakF1600 (bytecode.toList.map K.ofLane) publicInput),
      [], none⟩, stream.toList.map EW.toE, openings.toList.map phaseOpenings, []⟩
  have hstart : start.Rel s0 :=
    ⟨⟨seed_eq bytecode publicInput, rfl, rfl⟩, Nat.zero_le _, by simp [start, s0], Nat.zero_le _,
      by simp [start, s0], rfl⟩
  have hrun : Id.run (verifyWith (m := Id) keccakF1600 (bytecode.toList.map K.ofLane) publicInput
      ⟨stream.toList.map EW.toE, openings.toList.map phaseOpenings⟩) =
      match runSpec (leanVmVerifierProgram (bytecode.toList.map K.ofLane) publicInput) s0 with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false := rfl
  have hverify : Model.verify bytecode publicInput stream openings =
      match (Model.verifyExecution bytecode publicInput).run start with
      | some ((), s) => s.cursor == s.stream.size && s.phase == s.openings.size
      | none => false := rfl
  rw [hrun, hverify, leanVmVerifierProgram, runSpec_bind]
  have hw := hwalk start s0 hstart
  revert hw
  generalize (Model.verifyExecution bytecode publicInput).run start = x
  generalize runSpec (Verifier.verifyExecution computedBytecodeValue
    (bytecode.toList.map K.ofLane) publicInput) s0 = y
  rintro (⟨⟨-, hrel⟩⟩ | _)
  · exact (congrArg₂ (· && ·) hrel.stream_consumed hrel.openings_consumed)
  · rfl

end NativeVm.Equiv
