/-
  LeanVM.Protocol.EndToEnd.Sound.SkelDefs

  The skeletons of the cut verifier's phases, on the layout's sizes.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Skeleton

/-!
# The cut verifier's skeleton

The transcript operations of the cut verifier (`Relation.leanVmProgramCut`), phase by phase, as
functions of the announced sizes only: the layout's fields the phases' skeletons read are a
`LayoutLite` (`Layout.lite`), which holds no table. The tables' counts the link reads
(`nAccessesL`, `nPointersL`, `nValuesL`) and their widths (`tableWidthsL`) are constants.

* the announced sizes: `skSizes`;
* the body (`Relation.veBodyCut`): the stack's commitment (`skCommitStack`), its out-of-domain
  sample (`skOod`), the link (`skLink`), the public input (`[.sample]`), the Keccak reduction
  (`skKeccak`), ring switching (`skRing`), then the cut opening (`skWhir`): `skBody`, and
  `skBodyHead` before the opening.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound

@[expose] public section

/-! ## The layout's sizes -/

/-- The layout's fields the extractor reads: no bytecode, no table. -/
structure LayoutLite where
  logMemory : ℕ
  logBytecode : ℕ
  tableRows : List ℕ
  placements : List (Option Placement)
  stackLog : ℕ
  tableLogHeights : List ℕ
  deriving Inhabited

/-- A layout's sizes. -/
def _root_.LeanVM.Protocol.Verifier.Layout.lite (layout : Layout) : LayoutLite :=
  ⟨layout.logMemory, layout.logBytecode, layout.tableRows, layout.placements, layout.stackLog,
    layout.tableLogHeights⟩

/-- The tables' widths, in opcode order. -/
def tableWidthsL : List ℕ := [7, 9, 5, 10, 14, 68]

/-- The tables' memory accesses. -/
def nAccessesL : ℕ := 39

/-- The tables' pointer columns. -/
def nPointersL : ℕ := 33

/-- The tables' columns that are not pointers, whose values the link reads. -/
def nValuesL : ℕ := 80

/-- `packedChallenges tables nRows width` on the constants. -/
def packedChallengesL (nRows width : ℕ) : ℕ :=
  (nTables - 1) + 5 + nAccessesL + bytecodeSlotBits + 2 + nPointersL + nRows + width +
    ((Chunks.new width).map Chunks.d).getD 0

/-- The link's chunks at the sizes. -/
def chunksL (lay : LayoutLite) : Option Chunks :=
  Chunks.new (pointerWidth lay.logMemory lay.logBytecode (lay.tableRows.foldl (· + ·) 0))

/-! ## The leaves -/

/-- The skeleton of a proof of work of `bits` bits: none when `bits = 0`. -/
def skGrind (bits : ℕ) : List Op := if bits = 0 then [] else [.grind bits]

/-- The skeleton of one sumcheck round of `count` coefficients, with an equality factor or
without. -/
def skRound (count : ℕ) : Bool → List Op
  | false => .read :: List.replicate (count - 2) .read ++ skGrind (grindingBits (count - 1))
  | true => List.replicate (count - 1) .read ++ skGrind (grindingBits (count - 1 + 1))

/-- The skeleton of a sumcheck of `count` coefficients a round, its rounds' equality factors
present or absent as `eqs`. -/
def skSum (count : ℕ) (eqs : List Bool) : List Op :=
  eqs.flatMap fun b ↦ skRound count b ++ [.sample]

/-- The samples of the query positions' loop. -/
def sqSamples (depth : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, remaining =>
    if remaining = 0 then 0 else 1 + sqSamples depth fuel (remaining - min (128 / depth) remaining)

/-! ## The opening -/

/-- The skeleton of a fold round. -/
def skFoldRound : List Op :=
  List.replicate 4 .read ++ skGrind Whir.foldGrindingBits ++ [.sample, .sample]

/-- The skeleton of `n` fold rounds. -/
def skFoldRounds : ℕ → List Op
  | 0 => []
  | n + 1 => skFoldRound ++ skFoldRounds n

/-- The skeleton of a level with a next one, after its folds, `A` the folds made. -/
def skMidTail (logN A : ℕ) (level next : Whir.Level) : List Op :=
  [.commit (logN - A - next.fold + next.logInvRate) (2 * 2 ^ next.fold)] ++
    List.replicate level.fold .read ++ skGrind Whir.oodGrindingBits ++
    List.replicate (logN - A) .sample ++ [.read] ++ skGrind Whir.queryGrindingBits ++
    List.replicate (sqSamples (logN - A + level.logInvRate) level.queries level.queries) .sample ++
    [.sample, .query]

/-- The skeleton of the levels, cut, `A` the folds made before them. -/
def skLevels (logN : ℕ) : ℕ → List Whir.Level → List Op
  | _, [] => []
  | A, [level] => skFoldRounds level.fold ++
      List.replicate (2 ^ (logN - (A + level.fold)) + level.fold) .read
  | A, level :: next :: rest => skFoldRounds level.fold ++
      skMidTail logN (A + level.fold) level next ++ skLevels logN (A + level.fold) (next :: rest)

/-- The skeleton of the cut opening at the stack's size and the rate. -/
def skWhir (logN logInvRate : ℕ) : List Op :=
  match Whir.ladder logN logInvRate with
  | some config => skLevels logN 0 config
  | none => []

/-- The skeleton of the stack's commitment. -/
def skCommitStack (logN logInvRate : ℕ) : List Op :=
  match Whir.ladder logN logInvRate with
  | some (level :: _) => [.commit (levelShape logN level (2 ^ level.fold)).1
      (levelShape logN level (2 ^ level.fold)).2]
  | _ => []

/-- The skeleton of the stack's out-of-domain sample. -/
def skOod (stackLog : ℕ) : List Op :=
  skGrind Whir.oodGrindingBits ++ List.replicate stackLog .sample ++ [.read]

/-! ## The front phases -/

/-- The skeleton of the link at the layout's sizes. -/
def skLink (lay : LayoutLite) : List Op :=
  match chunksL lay with
  | none => []
  | some chunks =>
    let nRows := lay.tableLogHeights.foldl max 0
    skGrind (grindingBits (max (nRows + 3 + bytecodeSlotBits) (chunks.width + 1))) ++
      [.sample, .samplePacked (packedChallengesL nRows chunks.width)] ++
      skSum 3 (List.replicate chunks.width false) ++ [.read, .samplePacked 5] ++
      skSum (roundCoefficients chunks.d).1 (List.replicate nRows false) ++
      skSum (roundCoefficients chunks.d).2 (List.replicate (log2Ceil nPointersL) false) ++
      [.readPacked (nValuesL + kBits)]

/-- The skeleton of a layer of the Keccak reduction, its claim's point of `L` coordinates. -/
def skKeccakLayer (L : ℕ) : List Op :=
  List.replicate productBits .read ++ skGrind (grindingBits (productBits - 1)) ++ [.sample] ++
    skSum 3 (List.replicate L true) ++ skSum 4 (List.replicate keccakLocalBits false) ++
    List.replicate 3 .read ++ skGrind (grindingBits 2) ++ [.sample]

/-- The skeleton of an opening of `q_keccak`'s slots. -/
def skKeccakOpen : List Op := skSum 3 (List.replicate qkeccakSlotBits false)

/-- The skeleton of the Keccak reduction over `2^logSteps` steps (two segments: the first one's
outputs committed). -/
def skKeccak (logSteps : ℕ) : List Op :=
  skGrind (grindingBits (keccakSegmentBits + keccakLaneBits)) ++
    List.replicate keccakSegmentBits .sample ++ List.replicate keccakLaneBits .sample ++ [.read] ++
    (List.range keccakDepth).flatMap (fun _ ↦ skKeccakLayer (logSteps - 4 + keccakSegmentBits)) ++
    skKeccakOpen ++ [.read] ++ skSum 3 (List.replicate 4 false) ++ skKeccakOpen ++
    List.replicate kBits .read

/-- The skeleton of ring switching, its two claims merged. -/
def skRing : List Op :=
  skGrind Whir.batchGrindingBits ++ [.samplePacked (2 * ringMapWidth + 1 + 1)]

/-! ## The cut verifier -/

/-- The skeleton of the announced sizes. -/
def skSizes : List Op := List.replicate (2 + nTables) .read

/-- The skeleton of the cut body before the opening. -/
def skBodyHead (lay : LayoutLite) (ρ : ℕ) : List Op :=
  skCommitStack lay.stackLog ρ ++ skOod lay.stackLog ++ skLink lay ++ [.sample] ++
    skKeccak (lay.tableLogHeights.getD opKeccak 0) ++ skRing

/-- The skeleton of the cut body at the layout's sizes and the rate. -/
def skBody (lay : LayoutLite) (ρ : ℕ) : List Op :=
  skBodyHead lay ρ ++ skWhir lay.stackLog ρ

end
end LeanVM.Protocol.EndToEnd.Sound
