import Whir.PCSBCSRoundsAdapter
import Whir.PCSBCSRoundsByteHistory
import Whir.DuplexCompression

/-! Actual compiled field/byte/sampler smoke for the modeled PCS adapter. It does
not use a mock transcript oracle or claim Merkle authentication/Rust refinement. -/
namespace Whir.PCSBCSRoundsSmoke
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def toy : Config := ⟨3, #[1,1], #[2,2], #[16,8], #[0,1]⟩
def e (n : Nat) : E := ⟨UInt64.ofNat n,UInt64.ofNat (n+100),UInt64.ofNat (n+200)⟩

def draw (s : DuplexRefinement.State) (n : Nat) :
    IO (DuplexRefinement.State × List FiatShamirGame.Byte) :=
  match DuplexRefinement.squeeze DuplexCompression.compress s n with
  | .ok result => pure result
  | .error _ => throw (IO.userError "native duplex squeeze unexpectedly rejected")

/-- Uses actual BLAKE2s compression, not a mock transcript oracle. Within one
group the 8 cached bytes after a 24-byte E remain usable; across each absorbed
reply or bits-zero nonce they are not used by the next group's squeeze. -/
def cacheBoundarySmoke : IO Unit := do
  let initial := DuplexRefinement.seed DuplexCompression.compress DuplexCompression.parameterIV
    DuplexRefinement.zeroDigest DuplexRefinement.zeroDigest
  let prior ← draw initial 24
  check (prior.1.consumed == 24) "E must consume exactly 24 bytes"
  let tail ← draw prior.1 8
  check (tail.2 == (List.ofFn prior.1.output).drop 24)
    "within-group unused 8 bytes were incorrectly discarded"
  let changed : FiatShamirGame.Digest32 := fun i =>
    ⟨((prior.1.output i).val+1)%256,Nat.mod_lt _ (by decide)⟩
  for (name,reply) in [("fold",[e 131,e 132]),("OOD",[e 133,e 134,e 135]),
      ("query intro",[e 136,e 137]),("nonfinal tail",[e 138,e 139])] do
    let bytes := scalarBytes reply
    let left := DuplexRefinement.absorb DuplexCompression.compress prior.1 bytes
    let right := DuplexRefinement.absorb DuplexCompression.compress
      {prior.1 with output := changed} bytes
    check (left.consumed == 0 && right.consumed == 0) s!"{name} did not reset cursor"
    let leftDraw ← draw left 24
    let rightDraw ← draw right 24
    check (leftDraw.2 == rightDraw.2) s!"{name} reused prior unused cache bytes"
  let nonce := ByteCodec.encodeE E.zero
  let checked := DuplexRefinement.verifyNonce DuplexCompression.compress DuplexCompression.powOK
    prior.1 nonce 0
  match checked with
  | .error _ => throw (IO.userError "canonical bits-zero nonce rejected")
  | .ok (bound,ok) =>
    check (ok && bound.consumed == 0) "bits-zero nonce did not bind/reset"
    let leftDraw ← draw bound 24
    let rightDraw ← draw {bound with output := changed} 24
    check (leftDraw.2 == rightDraw.2) "bits-zero nonce reused old cache"
  check ((WHIRHistory.executeEvent DuplexCompression.compress DuplexCompression.powOK
    prior.1 (.nonce 0 E.one)).isNone) "malformed bits-zero nonce did not reject"
  IO.println "PCS byte boundary PASS: E=24/32, within-group tail8 retained; fold/OOD/query-intro/nonfinal-tail reply absorbs and canonical nonce(bits=0) reset old-cache use"

def smoke : IO Unit := do
  let gamma := e 1
  let maps : Fin 6 → E := fun i => e (i.val+2)
  let lambda := e 8
  let first := stackSampleScalars (c := toy) .initial ((gamma,maps),lambda)
  check (first == (List.range 8).map (fun i => e (i+1)))
    "gamma/six-maps/lambda source order mismatch"
  check (List.ofFn (initialEight (c := toy) ((gamma,maps),lambda)) == first)
    "literal Fin8 source ordering mismatch"
  check (parseExact 8 (scalarBytes first) == some first)
    "joint 8E byte codec order mismatch"
  check ((parseExact 8 ((scalarBytes first).dropLast)).isNone)
    "truncated initial bytes accepted"
  let squeezes : Fin (queryChunks toy 0) → E := fun i => e (i.val+21)
  let query := stackSampleScalars (.query (⟨0,by decide⟩ : Fin toy.folds.size)) (squeezes,lambda)
  check (query == List.ofFn squeezes ++ [lambda]) "query lambda was reordered"
  check (parseExact (queryChunks toy 0+1) (scalarBytes query) == some query)
    "fullE query vector lost unused bits"
  let raw : Array E := #[⟨0xfedcba9876543210,0x0123456789abcdef,0x9988776655443322⟩,
    ⟨0x55aa33cc77ee11ff,0x123456789abcdef0,0xf0e1d2c3b4a59687⟩]
  for depth in [13,26,63] do
    let count := 192/depth+1
    let actual := deriveQueries depth count raw
    let expected := some (tab count fun i => SamplingProbability.concretePlace count depth i
      (Layout.rawQuery depth (fun j => raw[j]!.toNat) i))
    check (actual == expected) s!"cross-limb/stratum query mismatch at depth {depth}"
  let tape : Tape toy := (lambda,fun i =>
    (fun j => e (40+i.val+j.val),fun j k => e (60+i.val+j.val+k.val),
      fun j => e (80+i.val+j.val),e (100+i.val)),fun j => e (120+j.val))
  let source : SourceTape toy := ((gamma,maps),tape)
  let restored := (tapeAdapter toy).symm (tapeAdapter toy source)
  check (restored.1.1 == gamma && restored.2.1 == lambda)
    "joint initial tape adapter mismatch"
  check (!(CausalGame.opening toy (challenges toy restored.2) #[]).isOk)
    "missing modeled replies accepted"
  check (!(CausalGame.opening toy (challenges toy restored.2) #[.query #[] ⟨0,0⟩]).isOk)
    "malformed initial reply tag accepted"
  cacheBoundarySmoke
  let mut maximumBits := 0
  let mut maximumRounds := 0
  for n in List.finRange 14 do
    for rate in List.finRange 4 do
      let p : ParameterBounds.Profile := (n,rate)
      let c := ParameterBounds.config p
      maximumBits := max maximumBits (rmax c)
      maximumRounds := max maximumRounds (depth c)
      check (c.valid && (schedule c).all (fun q => decide (0 < rawWidth q)))
        "production empty-round edge"
  IO.println s!"PCS grouped smoke PASS: joint 8E, query fullE+lambda, byte order/truncation, cross-limb strata, causal tape regrouping, malformed replies; 56 profiles: max k={maximumRounds}, max rmax={maximumBits} bits"

end Whir.PCSBCSRoundsSmoke

def main : IO Unit := Whir.PCSBCSRoundsSmoke.smoke
