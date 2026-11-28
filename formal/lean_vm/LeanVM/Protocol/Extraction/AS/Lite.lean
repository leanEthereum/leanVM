/-
  LeanVM.Protocol.Extraction.AS.Lite

  The agreement-set extractor the cost machine runs: the replay along the cut verifier's
  skeleton, the trace read off it, the descent, and the candidate execution, on the layout's sizes.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.SkelDefs
public import LeanVM.Protocol.Extraction.AS.Forward
public import LeanVM.Protocol.Extraction.Fast.Transcript

/-!
# The lite extractor

`extractL prog input qs π`, on the transcript's permutation queries `qs`:

1. the permutation answered by the transcript's first forward answers, indexed (`fwdIndex`,
   `fwdF`), and the seed through it;
2. the replay of the announced sizes' skeleton (`skelReplayP`, the history reduced to each event's
   read and sampled values), the sizes decoded (`decSizesL`, a `LayoutLite`);
3. the replay of the body's skeleton (`skBody`), the cut opening's trace decoded (`decBodyL`);
4. every root's word read through one index of the transcript's evaluations (`wordsGo`,
   `transcriptIndex`), the compiled descent (`descendTraceC`), the stack read off level 0's lanes
   (`stackA`), and the candidate execution on the sizes (`candidateL`).

No verifier arithmetic is computed and no table is built. `transcriptExtractorL` is it on the
adversary's transcript. It returns every execution `Relation.transcriptExtractor` returns.
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Relation LeanVM.Extraction.Fast Common
open LeanVM.Protocol.Whir.Params LeanVM.Protocol.EndToEnd

@[expose] public section

attribute [local instance] lexOrd

/-! ## The replay on values -/

/-- An event's values: the scalar of a read, the challenge of a sample. -/
abbrev EvP : Type := Option E × Option E

section Replay

variable (F : KeccakState → Option KeccakState)

/-- **The replay of a skeleton, on values**: `skelReplay` with each event reduced to its read
and sampled values. A packed read checks the stream holds its `n` scalars on their prefix, not on
the stream's length, so that its price does not grow with the proof. -/
def skelReplayP : List Op → VerifierProgramState → Option (List EvP × VerifierProgramState)
  | [], s => some ([], s)
  | .read :: sk, s => match s.stream, s.sponge.ground with
    | x :: xs, none => (absorb (m := Option) F s.sponge x dsObserve).bind fun sp ↦
      (skelReplayP sk { s with sponge := sp, stream := xs }).map fun r ↦ ((some x, none) :: r.1, r.2)
    | _, _ => none
  | .sample :: sk, s => (squeeze (m := Option) F s.sponge).bind fun c ↦
      (skelReplayP sk { s with sponge := c.2 }).map fun r ↦ ((none, some c.1) :: r.1, r.2)
  | .readPacked n :: sk, s =>
    if s.sponge.ground.isNone ∧ (s.stream.take n).length = n then
      (observePacked (m := Option) F s.sponge (s.stream.take n)).bind fun sp ↦
        (skelReplayP sk { s with sponge := sp, stream := s.stream.drop n }).map fun r ↦
          ((none, none) :: r.1, r.2)
    else none
  | .samplePacked n :: sk, s => (samplesPacked (m := Option) F s.sponge n).bind fun c ↦
      (skelReplayP sk { s with sponge := c.2 }).map fun r ↦ ((none, none) :: r.1, r.2)
  | .grind _ :: sk, s => match s.stream, s.sponge.ground with
    | n :: xs, none => (absorbNonce (m := Option) F s.sponge n).bind fun c ↦
      (skelReplayP sk { s with sponge := c.2, stream := xs }).map fun r ↦ ((none, none) :: r.1, r.2)
    | _, _ => none
  | .commit height width :: sk, s => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => (absorb (m := Option) F s.sponge x0 dsObserve).bind fun sp0 ↦
      (absorb (m := Option) F sp0 x1 dsObserve).bind fun sp1 ↦
      let roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)]
      (skelReplayP sk { s with sponge := sp1, stream := xs, roots := roots }).map fun r ↦
        ((none, none) :: r.1, r.2)
    | _, _ => none
  | .query :: sk, s => match s.openings with
    | _ :: rest => (skelReplayP sk { s with openings := rest }).map fun r ↦ ((none, none) :: r.1, r.2)
    | [] => none

end Replay

/-! ## The decoders -/

/-- A fold round's challenges. -/
def decRoundP (h : List EvP) : Option FoldRound :=
  let h' := h.drop (4 + (skGrind Whir.foldGrindingBits).length)
  (h'.head?.bind (fun p : EvP ↦ p.2)).bind fun alpha ↦
    ((h'.drop 1).head?.bind (fun p : EvP ↦ p.2)).map fun beta ↦ ⟨alpha, beta⟩

/-- The fold rounds. -/
def decRoundsP : ℕ → List EvP → Option (List FoldRound)
  | 0, _ => some []
  | n + 1, h => (decRoundP (h.take skFoldRound.length)).bind fun r ↦
      (decRoundsP n ((h.drop skFoldRound.length).take (skFoldRounds n).length)).map fun rs ↦ r :: rs

/-- A level's high part, after the next level's commitment. -/
def decHighP (fold : ℕ) (h : List EvP) : Option (List E) :=
  ((h.drop 1).take fold).mapM (fun p : EvP ↦ p.1)

/-- The cut levels' trace, `A` the folds made before them. -/
def decLevelsP (logN : ℕ) : ℕ → List Whir.Level → List EvP → Option WhirTrace
  | _, [], _ => none
  | A, [level], h =>
    (decRoundsP level.fold (h.take (skFoldRounds level.fold).length)).bind fun rounds ↦
      (((h.drop (skFoldRounds level.fold).length).take
        (2 ^ (logN - (A + level.fold)) + level.fold)).mapM (fun p : EvP ↦ p.1)).map
          (WhirTrace.final rounds)
  | A, level :: next :: rest, h =>
    (decRoundsP level.fold (h.take (skFoldRounds level.fold).length)).bind fun rounds ↦
      let h' := h.drop (skFoldRounds level.fold).length
      let Lm := (skMidTail logN (A + level.fold) level next).length
      (decHighP level.fold (h'.take Lm)).bind fun high ↦
        (decLevelsP logN (A + level.fold) (next :: rest) ((h'.drop Lm).take
          (skLevels logN (A + level.fold) (next :: rest)).length)).map fun tr ↦
          WhirTrace.mid rounds high tr

/-- The cut opening's trace. -/
def decWhirCutP (logN ρ : ℕ) (h : List EvP) : Option WhirTrace :=
  (Whir.ladder logN ρ).bind fun config ↦ decLevelsP logN 0 config h

/-- The cut body's trace, after the body's head. -/
def decBodyL (lay : LayoutLite) (ρ : ℕ) (h : List EvP) : Option WhirTrace :=
  decWhirCutP lay.stackLog ρ (h.drop (skBodyHead lay ρ).length)

/-! ## The announced sizes -/

/-- `columnKappas tables` on the tables' widths. -/
def columnKappasL (logMemory : ℕ) (tableLogHeights : List ℕ) : List ℕ :=
  [logMemory, logMemory, tableLogHeights.getD opKeccak 0 + qkeccakSlotBits] ++
    (List.range nTables).flatMap fun t ↦
      List.replicate (tableWidthsL.getD t 0) (tableLogHeights.getD t 0)

/-- `buildLayout` on the sizes. -/
def buildLayoutLite (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) :
    Option LayoutLite :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if minLogMemory ≤ logMemory ∧ logMemory ≤ maxLogMemory ∧
        tableRows.all (· ≤ 2 ^ maxTableLog) ∧ bytecodeSlotBits ≤ logLength ∧
        logLength ≤ Verifier.maxLogBytecode + bytecodeSlotBits ∧ tableRows.length = nTables then
      let logBytecode := logLength - bytecodeSlotBits
      let tableLogHeights :=
        List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows tableLogFloors
      let kappas := columnKappasL logMemory tableLogHeights
      let (offsets, stackLog) := stack kappas
      let placements := kappas.zipIdx.map fun (kappa, column) ↦
        let index := match qkeccakSlot column with
          | some slot => (offsets.lookup qkeccak).map (· + (slot <<< kappa))
          | none => offsets.lookup column
        index.map fun index ↦ ({ variableCount := kappa, index := index } : Placement)
      some ⟨logMemory, logBytecode, tableRows, placements, stackLog, tableLogHeights⟩
    else none

/-- `readAnnouncedSizes`'s checks on the announced values, on the sizes. -/
def sizesOfL (bytecode : List K) (announced : List E) : Option (LayoutLite × ℕ) :=
  if (announced.all fun value ↦ value.limb 1 = 0) then
    let logMemory := kToNat ((announced.headD 0).limb 0)
    let tableRows := ((announced.drop 1).take nTables).map fun value ↦ kToNat (value.limb 0)
    let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
    if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
      (buildLayoutLite bytecode logMemory tableRows).bind fun lay ↦
        if Whir.minLogStack ≤ lay.stackLog ∧ lay.stackLog ≤ Whir.maxLogStack then
          some (lay, logInverseRate)
        else none
    else none
  else none

/-- The announced sizes, decoded off their history. -/
def decSizesL (bytecode : List K) (h : List EvP) : Option (LayoutLite × ℕ) :=
  (h.mapM (fun p : EvP ↦ p.1)).bind (sizesOfL bytecode)

/-! ## The committed words -/

/-- Column `v`'s lanes of commitment `i`, from its leaves. -/
def laneRow (i : ℕ) (lv : Array (List K)) (h w v : ℕ) : Array E :=
  (lanesOf i (leafAt lv h w v)).toArray

/-- The `n` columns' lanes of commitment `i`, from its leaves. -/
def laneRows (n i : ℕ) (lv : Array (List K)) (h w : ℕ) : AV :=
  Array.ofFn fun v : Fin n ↦ laneRow i lv h w v

/-- The longest lookup of the roots' leaves: a node's `64` bytes, a leaf's `8w`. -/
def capOf : List (Digest × ℕ × ℕ) → ℕ
  | [] => 64
  | x :: xs => max (8 * x.2.2) (capOf xs)

/-- A root's leaves, read through the roots' shared index `I`. -/
def leavesAt (I : SortedMap (List UInt64 × ℕ) Hits) (x : Digest × ℕ × ℕ) : Array (List K) :=
  leavesIn I x.2.2 x.2.1 x.1

/-- Root `i`'s word, column by column. -/
def wordArrOf (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) (i : ℕ) (x : Digest × ℕ × ℕ) : AV :=
  laneRows (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) i (leavesAt I x) x.2.1 x.2.2

/-- Every root's word from root `i` on. -/
def wordsGo (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) :
    ℕ → List (Digest × ℕ × ℕ) → List AV
  | _, [] => []
  | i, x :: xs => wordArrOf μ R I i x :: wordsGo μ R I (i + 1) xs

/-! ## The candidate execution on the sizes -/

/-- Each table's cycle pointer column (its state link's `cycle`; every table's `pc` is local
column `0`, its `fp` column `1`). -/
def stateCyclesL : List ℕ := [6, 8, 4, 9, 13, 67]

/-- Row `i` of the global column `c`, on the sizes (`columnRow`). -/
def columnRowL (lay : LayoutLite) {μ : ℕ} (q : Column μ) (c i : ℕ) : K :=
  match lay.placements.getD c none with
  | some placement => cell q (placement.index + i)
  | none => 0

/-- Table `t`'s local column `c` at row `u`, on the sizes (`tableWord`). -/
def tableWordL (lay : LayoutLite) {μ : ℕ} (q : Column μ) (t c u : ℕ) : K :=
  columnRowL lay q (globalColumnBases.getD t 0 + c) u

/-- The cycles of the executed rows in the final state, on the sizes (`finalCycles`). -/
def finalCyclesL (lay : LayoutLite) {μ : ℕ} (q : Column μ) (chunks : Chunks) : List ℕ :=
  (List.range nTables).flatMap fun t ↦ (List.range (lay.tableRows.getD t 0)).filterMap fun u ↦
    if tableWordL lay q t 0 u = g ^ (2 ^ lay.logBytecode - 1) ∧ tableWordL lay q t 1 u = 1 then
      some (ptrIndex chunks (tableWordL lay q t (stateCyclesL.getD t 0) u) % 2 ^ chunks.width)
    else none

/-- The cycle the run halts at, on the sizes (`firstFinal`). -/
def firstFinalL (lay : LayoutLite) {μ : ℕ} (q : Column μ) : ℕ :=
  match chunksL lay with
  | some chunks => (finalCyclesL lay q chunks).foldl min (lay.tableRows.foldl (· + ·) 0)
  | none => lay.tableRows.foldl (· + ·) 0

/-- The memory read off a stack, on the sizes (`memoryImage`). -/
def memoryImageL (lay : LayoutLite) {μ : ℕ} (q : Column μ) : MemoryImage lay.logMemory :=
  fun i ↦ E.ofLimbs (columnRowL lay q memory0 i) (columnRowL lay q memory1 i)

/-- **The execution a stack gives, on the sizes** (`candidate`). -/
def candidateL (program : LeanIsaProgram) (lay : LayoutLite) {μ : ℕ} (q : Column μ) :
    Execution program :=
  ⟨lay.logMemory, memoryImageL lay q, firstFinalL lay q⟩

/-! ## The extractor -/

/-- **The finish**: the roots' words through one index, the descent, level 0's stack and its
execution. -/
def finishL (prog : LeanIsaProgram) (qs : List (PermutationQuery KeccakState × KeccakState))
    (lay : LayoutLite) (ρ : ℕ) (tr : WhirTrace) (roots : List (Digest × ℕ × ℕ)) :
    Option (Execution prog) :=
  (descendTraceC lay.stackLog ρ (wordsGo lay.stackLog ρ (transcriptIndex qs (capOf roots)) 0 roots)
    tr 0).bind fun T ↦
  if T.1 = laneBits then
    some (candidateL prog lay (⟨stackA lay.stackLog T.2⟩ : Column lay.stackLog))
  else none

/-- **The lite extractor** on the transcript's permutation queries. -/
def extractL (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) :=
  let M := fwdIndex qs
  let F := fwdF M
  (seedWithHash (keccak256With F) F (bytecodeWords prog) (publicInputDigest input)).bind fun seed ↦
  (skelReplayP F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizesL (bytecodeWords prog) r₁.1).bind fun a ↦
  (skelReplayP F (skBody a.1 a.2) r₁.2).bind fun r₂ ↦
  (decBodyL a.1 a.2 r₂.1).bind fun tr ↦
  finishL prog qs a.1 a.2 tr r₂.2.roots

/-- **The lite extractor on the adversary's transcript.** -/
def transcriptExtractorL : StraightLineExtractor :=
  fun prog input T π ↦ extractL prog input (permutationQueries T) π

end
end LeanVM.Extraction.AS
