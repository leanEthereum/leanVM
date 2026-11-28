/-
  LeanVM.Protocol.Relation.ExtractorDef

  The agreement-set extractor of the leanVM verifier: the cut verifier it replays, and the
  extractor on the adversary's answers and on its transcript.
-/

module

public import LeanVM.Protocol.Relation.Walk
public import LeanVM.Protocol.Relation.Link.Rel
public import LeanVM.Protocol.Whir.Sound.Cut
public import LeanVM.Protocol.Whir.Sound.DescentC
public import LeanVM.Protocol.Whir.Sound.StackA
public import LeanVM.Protocol.Compile.Rom.Replay
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Extraction.Defs
public import LeanVM.Protocol.Extraction.Extractor
public import LeanVM.Protocol.Rpm.ExtractF

/-!
# The agreement-set extractor

**The cut verifier** (`leanVmProgramCut`): the ghost verifier `leanVmProgramG` with the stacked
opening cut right after the final polynomial (`Whir.Sound.verifyStackedOpeningCut`), returning the
verdict, the announced sizes and the opening's trace. An honest prover need not query the
permutation past the final polynomial, so the extractor replays only the cut.

**The extractor** (`extractAS program input H keys F π`), from the adversary's Keccak-256 answers
`H` (with `keys`, the inputs they answer), its permutation answers `F` and the proof `π`:

1. the seed (`leanVmSeed`), on `H` and `F`;
2. the replay of the cut verifier on `F` (`Rom.replayU`, the openings unverified), which returns
   the announced layout and rate and the opening's trace, at a state holding the roots read;
3. every root's word, inverted through `H` (`Extraction.committedWordC`), as arrays of each
   leaf's lanes (`wordArrays`);
4. the compiled descent from the final polynomial (`Whir.Sound.descendTraceC`: one-error Newton
   decoding on the agreement sets), ending on level 0's lanes;
5. the stack read off them (`Whir.Sound.stackA`), and its execution (`candidate`: the memory
   read off the stack, run to the first cycle in the final state).

No halting search, no list decoding. **On a transcript** (`transcriptExtractor`): `H` the
Keccak-256 evaluations of the adversary's permutation queries, `F` the answers of its first
forward queries (`Rpm.firstForward`). It has the type of `Statement`'s straight-line extractors.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.Whir.Params LeanVM.Protocol.EndToEnd

@[expose] public section

/-! ## The cut verifier -/

/-- `veBodyG` cut at the final polynomial. -/
def veBodyCut (layout : Layout) (ρ : ℕ) (input : PublicInput) : VerifierProgram WhirTrace := do
  commitStack layout.stackLog ρ
  let ood ← readOod layout.stackLog
  let (link, pub, outs, keccakPoint, keccakSlices) ← frontProg layout input
  let qk ← liftOption (layout.placements.getD qkeccak none)
  let (ring, batching) ← ringSwitch [keccakRingClaim qk keccakPoint keccakSlices, link.ring]
  let memoryTerm ← memoryTermClaim layout link
  verifyStackedOpeningCut layout.stackLog ρ (ring :: openOthers layout memoryTerm link pub outs ood)
    batching

/-- **The leanVM verifier cut at the final polynomial**, returning the verdict and the data. -/
def leanVmProgramCut (bytecode : List K) (input : PublicInput) :
    VerifierProgram (Bool × ((Layout × ℕ) × WhirTrace)) :=
  (readAnnouncedSizes bytecode).bind fun a ↦
    (veBodyCut a.1 a.2 input).bind fun tr ↦ VerifierProgram.ret (true, (a, tr))

/-- The state the verifier starts from on the proof `π`, at the seed. -/
def startState (π : Proof) (seed : KeccakState) : VerifierProgramState :=
  ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩

/-! ## The extractor -/

/-- **The committed words as arrays**: for commitment `i`, the lanes of each of its leaves, one
per column of level `i`'s code. -/
def wordArrays (μ R : ℕ) (cs : List (ℕ × ℕ × Word)) : List AV :=
  (List.range cs.length).map fun i ↦
    Array.ofFn fun v : Fin (codesOf μ R i).n ↦ (lanesOf i (wordOf cs i v)).toArray

/-- The extractor after the replay: the roots' words, the descent, level 0's stack and its
execution, from the replay's value and state. -/
def finishAS (program : LeanIsaProgram) (H : Bytes → Option Digest) (keys : List Bytes)
    (r : (Bool × ((Layout × ℕ) × WhirTrace)) × VerifierProgramState) : Option (Execution program) :=
  let layout := r.1.2.1.1
  let cs := r.2.roots.map fun x ↦ (x.2.1, x.2.2, Extraction.committedWordC H keys x.1 x.2.1 x.2.2)
  (descendTraceC layout.stackLog r.1.2.1.2 (wordArrays layout.stackLog r.1.2.1.2 cs) r.1.2.2 0).bind
    fun T ↦ if T.1 = laneBits then
      some (candidate program layout (⟨stackA layout.stackLog T.2⟩ : Column layout.stackLog))
    else none

/-- **The agreement-set extractor**: from the adversary's Keccak-256 answers `H` (`keys` the
inputs they answer), its permutation answers `F` and the proof `π`, the seed and the cut
verifier's replay on them, then `finishAS`. -/
def extractAS (program : LeanIsaProgram) (input : PublicInput) (H : Bytes → Option Digest)
    (keys : List Bytes) (F : KeccakState → Option KeccakState) (π : Proof) :
    Option (Execution program) :=
  ((leanVmSeed (bytecodeWords program) (publicInputDigest input)).run H F).bind fun seed ↦
  (replayU F (leanVmProgramCut (bytecodeWords program) input) (startState π seed)).bind
    (finishAS program H keys)

/-- **The extractor on a transcript of permutation queries**: on its Keccak-256 evaluations and
the answers of its first forward queries. -/
def transcriptExtractorWithHash (program : LeanIsaProgram) (input : PublicInput)
    (T : PermutationTranscript) (proof : Proof) : Option (Execution program) :=
  extractAS program input (lookupEvaluation (keccakEvaluationsOfTranscript T))
    ((keccakEvaluationsOfTranscript T).map (·.1)) (Rpm.firstForward T) proof

/-- **The leanVM knowledge extractor**, a straight-line extractor: the agreement-set extractor on
the adversary's permutation queries, its coins left out. -/
def transcriptExtractor : StraightLineExtractor :=
  fun program input T proof ↦ transcriptExtractorWithHash program input (permutationQueries T) proof

end
end LeanVM.Protocol.Relation
