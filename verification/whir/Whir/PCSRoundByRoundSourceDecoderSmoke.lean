import Whir.PCSRoundByRoundSourceDecoder

/-! TOY GENERIC HELPER SMOKE, not a production-profile runtime benchmark.
Runs the exact `runForConfig` helper used by production `run`, with eight
nontrivial words, sixteen full-root rows, all64 slices, an ordinary and a
strided point, and the immutable original anchor. -/
namespace Whir.PCSRoundByRoundSourceDecoderSmoke
open Concrete Protocol CausalGame SupportedCandidateExtraction PCSRoundByRoundSource

def config : Config := ⟨3, #[1, 1], #[2, 2], #[16, 8], #[0, 1]⟩
def words : Array K := #[3, 5, 7, 11, 13, 17, 19, 23]
def witness : Witness config 2 := fun i => words[i.val]!
def anchorPoint : Array E := #[E.ofK 29, E.ofK 31, E.ofK 37]
def family : Fin 1 → RingPCSGame.FamilyClaim := fun _ =>
  ⟨0, #[], fun bit => if RingPCSGame.wordBit 3 bit then 1 else 0⟩
def points : Array RingPCSGame.PointClaim :=
  #[.point 1 #[] (E.ofK 5), .strided 0 1 1 #[] (E.ofK 5)]
def root : BaseOracle :=
  let encoded := encodedLanes config (paddedWitness config 2 witness)
  Array.ofFn fun q : Fin 16 => #[(encoded[1]!)[q.val]!.c0, (encoded[0]!)[q.val]!.c0]

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def smoke : IO Unit := do
  let anchorValue := CommitmentAnchor.value config 2 witness anchorPoint
  let extract := fun original root =>
    (runForConfig config (by decide) 2 original points anchorPoint anchorValue root).map Array.ofFn
  check (extract family root == some words) "toy full-root same-word extraction failed"
  let corrupt := root.set! 0 ((root[0]!).map fun x => x + 1)
  check (extract family corrupt == some words) "toy heavy-corrupted root recovery failed"
  check ((matchingRows ⟨config, 2, corrupt, #[]⟩ witness).card == 15)
    "toy common-support guard did not count actual corrupted rows"
  let wrong : Fin 1 → RingPCSGame.FamilyClaim := fun j =>
    { family j with slices := fun bit => (family j).slices bit + 1 }
  check ((extract wrong root).isNone) "toy wrong original slices accepted"
  check ((extract family (root.pop)).isNone) "toy malformed root length accepted"
  check ((extract family (root.set! 0 #[3])).isNone) "toy malformed root lane width accepted"
  check ((runForConfig config (by decide) 2 family points #[] anchorValue root).isNone)
    "toy malformed anchor metadata accepted"
  check ((runForConfig config (by decide) 2 family points anchorPoint (anchorValue + 1) root).isNone)
    "toy changed saved anchor accepted"
  IO.println "TOY GENERIC HELPER SMOKE: 8 nontrivial words, 16 directly indexed rows; same word recovered with 1 corrupted row (15 common matches); malformed root/metadata, wrong originals and changed anchor rejected"

end Whir.PCSRoundByRoundSourceDecoderSmoke

def main : IO Unit := Whir.PCSRoundByRoundSourceDecoderSmoke.smoke
