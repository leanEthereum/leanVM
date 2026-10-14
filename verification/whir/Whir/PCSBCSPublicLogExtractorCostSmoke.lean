import Whir.PCSBCSPublicLogExtractorCost

/-! Scoped execution checks use actual BLAKE2s. They exercise the concrete
source interpreter and frozen image statuses, not a mocked security game. -/
namespace Whir.PCSBCSPublicLogExtractorCostSmoke
open Whir Concrete Protocol FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicMerkleLog AnchoredHeaderCodec PCSBCSPublicLogExtractorCost

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

private def digest (n : Nat) : Digest32 :=
  fun i => ⟨(n / 256^i.val)%256,Nat.mod_lt _ (by decide)⟩

private def publicPath (cv : Digest32) (log : PublicLog) :
    List DuplexEncoding.Instruction → Option (PublicLog × Node)
  | [] => none
  | [(block,tweak)] => some (log,⟨cv,block,tweak,true⟩)
  | (block,tweak)::next::rest =>
    let input : Node := ⟨cv,block,tweak,true⟩
    let stored := Array.ofFn (blake2sOracle input)
    let answer : Digest32 := fun i => stored[i.val]'(by simp [stored])
    publicPath answer (Whir.DuplexPublicSimulator.observe log input answer) (next::rest)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def p : ParameterBounds.Profile := (⟨0,by decide⟩,⟨0,by decide⟩)
private def prices : MetadataCosts :=
  { shape := 31, originalFamily := 53, originalSlice := 59 }

private def imageView (frozen : PCSBCSMerkleRootCache.Frozen) :=
  frozen.cells.map fun cell => (cell.image,cell.compact,cell.available,cell.paddingValid)

private def tree (words : List (List K)) : Digest32 × PublicLog :=
  let bytes := words.map ByteCodec.wordsBytes
  let leaves := bytes.map hashBlake2s
  let left := List.ofFn (ByteCodec.pairBytes (leaves[0]!,leaves[1]!))
  let right := List.ofFn (ByteCodec.pairBytes (leaves[2]!,leaves[3]!))
  let top := List.ofFn (ByteCodec.pairBytes (hashBlake2s left,hashBlake2s right))
  (hashBlake2s top,(bytes.map (plan blake2sOracle)).flatten ++
    plan blake2sOracle left ++ plan blake2sOracle right ++ plan blake2sOracle top)

def smoke : IO Unit := do
  let words : List (List K) := [[0,3],[0,5],[0,7],[0,11]]
  let bytes := words.map ByteCodec.wordsBytes
  let leaves := bytes.map hashBlake2s
  let left := List.ofFn (ByteCodec.pairBytes (leaves[0]!,leaves[1]!))
  let right := List.ofFn (ByteCodec.pairBytes (leaves[2]!,leaves[3]!))
  let top := List.ofFn (ByteCodec.pairBytes (hashBlake2s left,hashBlake2s right))
  let root := hashBlake2s top
  let incomplete := ((bytes.drop 1).map (plan blake2sOracle)).flatten ++
    plan blake2sOracle left ++ plan blake2sOracle right ++ plan blake2sOracle top
  let shape : Shape := ⟨2,1,1,1⟩
  let imageShape := PCSBCSSourceRootReferences.initialShape shape
  let domain := digest 7
  let statement := digest 9
  let iv := PCSBCSSourceCoordinateDecoder.seedIV
  let history : FramedHistory := ⟨domain,statement,
    [.absorb 0 (WHIRHistory.scalarBytes (headerScalars shape root))]⟩
  let key : Coordinate := ⟨history,.output 0⟩
  let some (capturedPrefix,input) := publicPath iv incomplete (DuplexEncoding.plan key)
    | throw (IO.userError "empty actual source path")
  let target : Record := ⟨shape,root,⟨digest 41,fun _ => none,0,true,0,0⟩,[0,0],0⟩
  let registry :=
    (⟨iv,domain,fun s => if s = statement then some shape else none⟩ : AnchoredHeaderRoots.Public)
  let received := Whir.DuplexPublicSimulator.observe capturedPrefix input (blake2sOracle input)
  let changed := Whir.DuplexPublicSimulator.observe capturedPrefix input (digest 123)
  let later := plan blake2sOracle bytes[0]! ++ received
  let foreign := {target with root := digest 42}
  let recovery := recoverCount 64 iv capturedPrefix input
  require (decide (recovery.1 = PCSBCSSourceCoordinateDecoder.recover 64 iv capturedPrefix input))
    "counted recovery differs from actual linear decoder"
  for (name,selectedTarget,log) in [("captured",target,received),("tampered",target,changed),
      ("future",target,later),("missing",foreign,received)] do
    let extracted := extractCount p 64 0 registry selectedTarget prices
      1 (fun j : Fin 0 => nomatch j) #[] #[] 0 log
    let counted := extracted.2.1
    let actual := PCSBCSPublicLogExtractor.selectPrefix p 64 0 registry selectedTarget log
    require (decide (counted.value = actual)) (name ++ " selection erasure")
    if name == "missing" then
      require counted.value.isNone "missing capture invented"
    else
      require (decide (counted.value = some capturedPrefix)) (name ++ " first prefix changed")
    let uncounted := PCSBCSPublicLogExtractor.extract p 64 0 registry selectedTarget
      1 (fun j : Fin 0 => nomatch j) #[] #[] 0 log
    require (extracted.1.isSome == uncounted.isSome) (name ++ " extraction erasure")
    let allowance := originalAccessorAllowance extracted.2.2 prices
    let outerCharge := counted.callbacks.cost prices
    let declaredCharge := counted.operations+outerCharge+extracted.2.2+allowance
    IO.println s!"{name}: scanner_source_operations={counted.operations}, public_shape_lookup_calls={repr counted.callbacks}, public_shape_lookup_charge={outerCharge}, raw_backend_units={extracted.2.2}, original_input_allowance={allowance}, declared_logical_total={declaredCharge}"
  let decoded := rootCount p 1 (fun j : Fin 0 => nomatch j) #[] #[] 0 capturedPrefix target
  let uncountedRoot := PCSBCSPublicRootExtractor.extract p 1 (fun j : Fin 0 => nomatch j)
    #[] #[] 0 capturedPrefix target
  require (decoded.1.isSome == uncountedRoot.isSome) "one-freeze full-root helper erasure"
  require decoded.1.isNone "tiny tree unexpectedly fits production profile"
  let header := headerCount registry history
  require header.1.isSome "valid BLAKE2s root header rejected"
  require (header.1.isSome ==
    (AnchoredHeaderRoots.fromHistory registry history).isSome) "header parser erasure"
  let brokenHistory := {history with frames := [.absorb 0 ([⟨1,by decide⟩] : List Byte)]}
  let brokenHeader := headerCount registry brokenHistory
  require brokenHeader.1.isNone "bad public header padding accepted"
  require (brokenHeader.1.isSome ==
    (AnchoredHeaderRoots.fromHistory registry brokenHistory).isSome) "bad header parser erasure"
  IO.println s!"full_root_freeze_source_operations={decoded.2.1}; raw_kernel_field_resource_operations={decoded.2.2}; header_source_operations={header.2.1}; shapes_invocations={header.2.2}; rejected_header_operations={brokenHeader.2.1}"
  let opening := openingReferencesCount p 0 key
  require (decide (opening.1 = PCSBCSSourcePrimitiveRootBudget.openingReferences p 0 key))
    "literal public-opening scanner erasure"
  require opening.1.isNone "header-only history invented a saved opening"
  let frozen := freezeCount capturedPrefix root imageShape
  let actualFrozen := PCSBCSMerkleRootCache.freeze capturedPrefix root imageShape
  require (imageView frozen.1 == imageView actualFrozen) "counted frozen cells differ"
  require (((frozen.1.cells[0]?).map (fun c => c.available)) == some false &&
    ((frozen.1.cells[1]?).map (fun c => c.available)) == some true)
    "unavailable captured cell confused with missing capture"
  let bad := tree [[1,3],[0,5],[0,7],[0,11]]
  let badFrozen := freezeCount bad.2 bad.1 imageShape
  require (imageView badFrozen.1 == imageView (PCSBCSMerkleRootCache.freeze bad.2 bad.1 imageShape))
    "bad-padding freeze erasure"
  require (((badFrozen.1.cells[0]?).map (fun c => c.available)) == some true &&
    ((badFrozen.1.cells[0]?).map (fun c => c.paddingValid)) == some false)
    "available bad padding silently became authenticated zero or unavailable"
  let config := ParameterBounds.config p
  let decodedShape : Shape := ⟨config.logN,config.folds[0]!,config.rates[0]!,1⟩
  let decodedTarget : Record :=
    ⟨decodedShape,root,⟨digest 41,fun _ => none,0,true,0,0⟩,
      List.replicate config.logN 0,0⟩
  let decodedEntry := WHIRHistory.encodeHistory
    ⟨domain,statement,[.absorb 0 (openingScalars decodedTarget)]⟩
  let openingKey := WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth config)
    decodedEntry [WHIRHistoryKey.initialPending] 0
  let some (openingPrefix,openingInput) := publicPath iv incomplete (DuplexEncoding.plan openingKey)
    | throw (IO.userError "empty literal saved-opening path")
  let boundary := decodedEntry.frames.length
  let openingCount := openingReferencesCount p boundary openingKey
  require (decide (openingCount.1 =
    PCSBCSSourcePrimitiveRootBudget.openingReferences p boundary openingKey))
    "accepted literal opening erasure"
  require (openingCount.1.isSome) "valid literal saved opening rejected"
  let refsCount := referencesCount p 64 boundary registry prices openingPrefix openingInput
  require (decide (refsCount.1 = PCSBCSSourcePrimitiveRootBudget.references p 64 boundary
    registry openingPrefix openingInput)) "public-byte reference scanner erasure"
  require (refsCount.1.length == 1 && refsCount.1.all (fun r => decide
    (r = ⟨root,PCSBCSSourceRootReferences.initialShape decodedShape⟩)))
    "public scanner invented a root or shape"
  let openingLog := Whir.DuplexPublicSimulator.observe openingPrefix openingInput
    (blake2sOracle openingInput)
  let selectedOpening := selectPrefixCount p 64 boundary registry decodedTarget prices openingLog
  require (decide (selectedOpening.value =
    PCSBCSPublicLogExtractor.selectPrefix p 64 boundary registry decodedTarget openingLog))
    "decoded opening selector erasure"
  require (selectedOpening.value == some openingPrefix) "literal opening capture included its reply"
  let W := 1024
  let P := PCSBCSPublicLogParserCost.framesSize openingKey.history.frames
  let S := PCSBCSSourceSavedRecordDecoderCost.physicalSize decodedEntry
  require (decide (openingCount.2 ≤ openingReferencePolynomial p W P S))
    "literal opening decoder cost exceeded public-volume polynomial"
  IO.println s!"literal_opening_operations={openingCount.2}; physical_saved_entry={S}; saved_decoder_polynomial={PCSBCSSourceSavedRecordDecoderCost.physicalPolynomial S}; opening_reference_bound={openingReferencePolynomial p W P S}"
  IO.println "counted PCS public-log smoke PASS (real BLAKE2s; public-byte scanner; missing/captured/tampered; unavailable versus bad padding; no FS endpoint)"

end Whir.PCSBCSPublicLogExtractorCostSmoke

def main : IO Unit := Whir.PCSBCSPublicLogExtractorCostSmoke.smoke
