import LeanVM.Protocol.Extraction.Fast.Transcript
import LeanVMTests.Extraction.Toy

/-!
# Tests: the fast extractor's decoder

* Roth–Ruckenstein's substitution `Y := a + X·Y`: `substituteFast` (proved equal to CompPoly's
  `substituteYRootPlusXY`) agrees with it on pseudo-random polynomials over `K`;
* `decodeStacksAtFast` (proved equal to `decodeStacksAt`) decodes a toy word of `Toy.lean`;
* the indexed replay (`keccakEvaluationsFast`, proved equal to the statement's evaluations of at
  most `L` bytes) on a transcript holding the sponge paths of three messages, and inverse queries;
* the address table (`powTable`, `gLogTable`): the index of `g^i` by binary search, `none` off
  the addresses;
* the sorted map (`SortedMap`, the replay's and the lookups' index): after 300 insertions with
  repeated keys, every key reads its newest value, as a scan of the insertions does;
* the restated lane-decoder steps (`Fast/RootFinder.lean`, `Fast/RootSteps.lean`,
  `Fast/LeeRows.lean`, `Fast/DecoderFast.lean`), each proved equal to the statement's or
  CompPoly's, run against them on small inputs;
* the axiom footprint of `transcriptExtractorFast_eq`.
-/

namespace LeanVMTests.Extraction

open CompPoly CompPoly.GuruswamiSudan LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast

/-- A pseudo-random bivariate polynomial over `K` of `Y`-degree `< ny` and `X`-degree `< nx`. -/
def randomBivariate (seed nx ny : ℕ) : CBivariate K :=
  let r := randoms seed (nx * ny)
  CPolynomial.ofArray (Array.ofFn fun y : Fin ny ↦
    CPolynomial.ofArray (Array.ofFn fun x : Fin nx ↦ K.ofBits (r.getD (y.val * nx + x.val) 0)))

#guard (List.range 4).all fun s ↦
  let Q := randomBivariate s 12 9
  let a := K.ofBits (lcg (s + 77))
  substituteFast Q a == substituteYRootPlusXY Q a

-- A larger one, fast only (CompPoly's takes `|Q|²·ℓ/2` steps).
#guard (substituteFast (randomBivariate 9 200 40) (K.ofBits 5)).val.size = 40

/-- `decodes`, fast. -/
def decodesFast {μ : ℕ} (R A : ℕ) (q : Vector K (2 ^ μ)) (w : Array (List K)) : Bool × ℕ :=
  let l := decodeStacksAtFast μ R A fun v ↦ w.getD v []
  (l.any fun d ↦ d.toList == q.toList, l.length)

#guard decodesFast 1 3 (randomStack 1 7) (corrupt 1 [2] (wordOf 1 (randomStack 1 7))) = (true, 1)

/-! ## The restated decoder steps, run -/

/-- `(X − 3)(X − 5)(X − 7)(X² + X + 1)`: five roots in `K` (`X² + X + 1` splits: `GF(4) ⊆ K`). -/
def rootPoly : CPolynomial K :=
  CPolynomial.linearFactor (K.ofBits 3) * CPolynomial.linearFactor (K.ofBits 5) *
    CPolynomial.linearFactor (K.ofBits 7) *
    (CPolynomial.X * CPolynomial.X + CPolynomial.X + CPolynomial.C 1)

#guard (rootsInFieldFast rootPoly).size = 5
#guard rootsInFieldFast rootPoly == fieldRootCtx.rootsInField rootPoly
#guard (List.range 4).all fun s ↦
  let Q := randomBivariate (s + 11) 6 5
  initialCoeffFast Q == initialCoefficientPolynomial Q &&
    divXPowerFast Q 2 == CBivariate.divXPower Q 2
#guard (List.range 3).all fun s ↦
  let Q := randomBivariate (s + 21) 7 4
  let params : GSInterpParams := ⟨3, 2, 9⟩
  normalizeLeeFast params Q == LeeOSullivan.normalizeLeeCandidate? params Q
#guard
  let R := (randomBivariate 31 5 1).val.getD 0 0
  let G := (randomBivariate 32 6 1).val.getD 0 0
  let params : GSInterpParams := ⟨3, 2, 9⟩
  leeRowsFast R G params == leeOSullivanBasisRowsWithRG R G params

/-! ## The replay -/

open LeanVM LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash Common in
/-- The forward queries of the sponge path of `m`, from the zero state. -/
def spongeQueries (m : List UInt8) : List (PermutationQuery KeccakState × KeccakState) :=
  let bs := keccakPadded m
  ((List.range (bs.length / rate)).foldl (fun (acc : _ × _) j ↦
    let blk := (bs.drop (rate * j)).take rate
    let x : KeccakState := Vector.ofFn fun i ↦
      if i.val < 17 then Keccak.lane acc.1 i ^^^ littleEndianLane blk i else Keccak.lane acc.1 i
    let y := keccakF1600 x
    (y, acc.2 ++ [(.forward x, y)])) (Vector.replicate 25 0, [])).2

/-- Messages of `64`, `512` and `1000` bytes. -/
def message (n seed : ℕ) : List UInt8 := (randoms seed n).toList.map (·.toUInt8)

open LeanVM.Semantics LeanVM.Protocol Common in
/-- Their paths, interleaved with inverse queries and repeated queries. -/
def toyTranscript : List (PermutationQuery KeccakState × KeccakState) :=
  let junk : KeccakState := Vector.ofFn fun i ↦ (i.val * 77).toUInt64
  spongeQueries (message 64 1) ++ [(.inverse junk, keccakF1600 junk)] ++
    spongeQueries (message 512 2) ++ spongeQueries (message 64 1) ++ spongeQueries (message 1000 3)

-- The statement's replay finds the three evaluations, with the right digests.
#guard (LeanVM.keccakEvaluationsOfTranscript toyTranscript).map (·.1.length) = [1000, 512, 64]
#guard (LeanVM.keccakEvaluationsOfTranscript toyTranscript).all fun e ↦
  e.2 == LeanVM.Protocol.KeccakHash.keccak256 e.1

-- The indexed replay keeps those of at most `L` bytes.
#guard keccakEvaluationsFast toyTranscript 600 ==
  (LeanVM.keccakEvaluationsOfTranscript toyTranscript).filter (·.1.length ≤ 600)
#guard (keccakEvaluationsFast toyTranscript 600).map (·.1.length) = [512, 64]
#guard (keccakEvaluationsFast toyTranscript 64).map (·.1.length) = [64]

/-! ## The address table -/

#guard (List.range 1024).all fun i ↦
  (gLogTable (powTable 10) 10 (addressOfIndex i)).map (·.val) == some i
#guard gLogTable (powTable 10) 10 (addressOfIndex 1024) == none
#guard gLogTable (powTable 10) 10 0 == none

/-! ## The sorted map -/

/-- 300 insertions, `(lcg-derived key mod 97, index)`: keys repeat. -/
def sortedMapInserts : List (ℕ × ℕ) :=
  (List.range 300).map fun i ↦ (lcg (i + 5) % 97, i)

#guard
  let m := sortedMapInserts.foldl (fun m e ↦ m.insert e.1 e.2) (SortedMap.empty : SortedMap ℕ ℕ)
  (List.range 100).all fun k ↦ m.get? k == lookup sortedMapInserts.reverse k
-- 300 insertions leave at most `log₂ 300 + 1` levels.
#guard (sortedMapInserts.foldl (fun m e ↦ m.insert e.1 e.2)
  (SortedMap.empty : SortedMap ℕ ℕ)).levels.length ≤ 9

/-- info: 'LeanVM.Extraction.Fast.transcriptExtractorFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transcriptExtractorFast_eq

end LeanVMTests.Extraction
