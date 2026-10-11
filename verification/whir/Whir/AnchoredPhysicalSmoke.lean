import Whir.AnchoredSourcePacket
import Lean.Util.CollectAxioms
import Whir.WHIRNativeErasure

/-! Executable smoke of the native commit/open record boundary with the real BLAKE2s primitive. These tests do not claim an honest complete WHIR opening fixture or a concrete BLAKE2s security bound. -/
namespace Whir.AnchoredPhysicalSmoke
open Concrete FiatShamirGame DuplexModeGame AnchoredHeaderCodec AnchoredPhysicalTranscript
open WHIRSourceChronology

local instance : Add E := ⟨E.add⟩
local instance : Mul E := ⟨E.mul⟩
local instance : Zero E := ⟨E.zero⟩
local instance : One E := ⟨E.one⟩
local instance (n : Nat) : OfNat E n := ⟨FieldModel.instCommRingE.natCast n⟩

private def iv : Digest32 := DuplexCompression.parameterIV
private def digest (x : Nat) : Digest32 :=
  fun i => ⟨(x / 256 ^ i.val) % 256, Nat.mod_lt _ (by decide)⟩

private theorem digest_exact (x : Nat) : digest x = ByteCodec.encodeNat 32 x := by
  funext i
  apply Fin.ext
  exact (ByteCodec.encodeNat_byte 32 x i).symm
private def shape : Shape := ⟨15,6,1,3⟩
private def original : DuplexRefinement.State :=
  DuplexRefinement.absorb (compressionOf blake2sOracle)
    (DuplexRefinement.seed (compressionOf blake2sOracle) iv (digest 7) (digest 9))
    (List.ofFn (ByteCodec.encodeNat 13 0x0102030405060708090a0b0c0d))
private def fresh : DuplexRefinement.State :=
  DuplexRefinement.seed (compressionOf blake2sOracle) iv (digest 11) (digest 13)

def smoke : List (String × Bool) :=
  match (runReal blake2sOracle iv (compile
    (receiveSource (cap := 32) shape original (headerScalars shape (digest 17)) (fun _ => 23)))).view.result.value with
  | .error _ => [("original commitment received",false)]
  | .ok (_,record) =>
    let frame := openingScalars record
    let foreign := {record with root := digest 19}
    let context := {record with context := {record.context with previous := record.context.previous+1}}
    let point := {record with point := (record.point.headD 0+1)::record.point.drop 1}
    let value := {record with value := record.value+1}
    let honest := (runReal blake2sOracle iv (compile
      (bindingSource (cap := 32) shape record fresh frame))).view.result.value
    [("original commitment received",true),
      ("derived anchor has exact dimension",record.point.length == shape.logN),
      ("normalized native snapshot valid",decide record.context.Valid),
      ("honest fresh-session record accepted",match honest with | .ok (_,[]) => true | _ => false),
      ("foreign record rejected",verifyBinding shape record (openingScalars foreign) == .error .commitmentMismatch),
      ("tampered original context rejected",verifyBinding shape record (openingScalars context) == .error .commitmentMismatch),
      ("tampered original point rejected",verifyBinding shape record (openingScalars point) == .error .commitmentMismatch),
      ("tampered advertised value rejected",verifyBinding shape record (openingScalars value) == .error .commitmentMismatch),
      ("truncated frame errors",verifyBinding shape record (frame.drop 1) == .error .malformedTranscript)]


/-- A complete native arithmetic opening with omitted lanes, after an honest record binding in a different session. Dense prover weights are test data only; the executable verifier uses the prefix DP. Merkle authentication of the erased physical fixture is not claimed. -/
def nativeSmoke : IO Unit := do
  for (label,passed) in smoke do
    unless passed do throw (IO.userError s!"record smoke failed: {label}")
  let c : Protocol.Config := ⟨3,#[1,1],#[1,1],#[2,2],#[0,1]⟩
  let sh : Shape := ⟨3,1,1,1⟩
  let witness : Array K := #[1,7,19,5]
  let padded : Array E := witness.map E.ofK ++ #[0,0,0,0]
  let result := (runReal blake2sOracle iv (compile (receiveSource (cap := 32) sh original
    (headerScalars sh (digest 17)) (fun point => Concrete.mle padded point.toArray)))).view.result.value
  let record ← match result with
    | .ok (_,record) => pure record
    | .error _ => throw (IO.userError "native fixture original commitment rejected")
  match (runReal blake2sOracle iv (compile (bindingSource (cap := 32) sh record fresh
      (openingScalars record)))).view.result.value with
  | .error _ => throw (IO.userError "native fixture fresh record binding rejected")
  | .ok _ => pure ()
  let ch : Protocol.Challenges :=
    ⟨#[⟨#[2],#[#[13,17]],#[43],7⟩,⟨#[3],#[],#[47],11⟩],#[5]⟩
  let beta : E := 41
  let weight := (CommitmentAnchor.weight c 1 record.point.toArray).map (beta*·)
  let target := beta*record.value
  let proof ← match Protocol.prove c ch witness weight target with
    | .ok (_,proof) => pure proof
    | .error message => throw (IO.userError s!"native fixture honest prover: {message}")
  let family : Fin 0 → RingPCSGame.FamilyClaim := Fin.elim0
  let seed : RingPCSGame.Prefix := (⟨3,1,0⟩,fun _ => 0)
  match AnchoredPhysicalAnchor.sourceVerify record family #[] seed beta c ch
      (WHIRPhysicalErasure.eraseOracles proof) with
  | .ok () => IO.println "honest fresh-session occupied-prefix native opening accepted"
  | .error message => throw (IO.userError s!"native fixture honest verifier: {message}")

#print axioms AnchoredHeaderCodec.verifyBinding_sound
#print axioms digest_exact
#print axioms AnchoredHeaderRoots.rawHeader_exact
#print axioms AnchoredSourceRegistry.first_query_freezes
#print axioms AnchoredPhysicalTranscript.absorbSource_real
#print axioms AnchoredPhysicalDriver.honest_anchor_selects

end Whir.AnchoredPhysicalSmoke

def main : IO Unit := Whir.AnchoredPhysicalSmoke.nativeSmoke
