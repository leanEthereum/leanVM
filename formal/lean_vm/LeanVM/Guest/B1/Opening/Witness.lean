/-
  LeanVM.Guest.B1.Opening.Witness

  `opening_queries`' witness read off its frames: each query's position, row and siblings below
  the cap, as functions of the valuations (the witness convention, `B1/Main/Frames.lean`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesRow
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.AcceptableChild

/-!
# `opening_queries`' witness, named

The witness convention: a witness is a function of the function's own valuation and the frame map
`V`, reading words only (no hash, no verifier function, no choice).

**A query's witness** (`QW`, `Interface.lean`): its position, its row and its siblings below the
cap.

* `winPosOf rd bp D cd`: the position whose windows `g^v` the run at `bp` holds (`memRead`, the
  memory's word, `0` where it has none; `gLog7`, the exponent of a small power of `g`), bit `l`
  read from the window holding it (`qwAt`);
* `oqSibsOf pd ch q σ`: the siblings below the cap, read off the children cells `ch ..` of a
  frame: at level `l` the pair off the walk's side;
* `oqQueryW s rd bp cap flags b emit σ V`: the query hinted at `b`, its window pointer `bp`
  (`oqRow` its row), its siblings off its `walk_path` call's frame;
* `oqIterOf s rd σ V`: a loop iteration's queries (two at level 0, one deeper), from its frame;
* `oqsOf s odd loop N rd σ V`: the function's queries, from its frame `σ` (the odd first query at
  level 0) and the frames `V loop (g^j :: oqLoopArgs σ) []` of its `N` iterations.

`opening_queries_sound_w_Spec`: under a call relation `C ≤ Rel` that unfolds at `V`
(`UnfoldsV`), a valuation `σ` holding the body of a deployed specialization, its positions and
window pointers naming positions (`QueryPosOk`), gives `MeaningOpeningQueriesW` at
`oqsOf … σ V`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Reading words -/

/-- The memory's word at `p·g^off` (`0` where it has none). -/
def memRead (rd : Reader) (p : E) (off : ℕ) : E := (rd (p.limb 0 * Parameters.addressOfIndex
    off)).getD 0

/-- The `n` words of the run at `p`. -/
def readN (rd : Reader) (p : E) (n : ℕ) : List E := (List.range n).map (memRead rd p)

/-- The digest of two cells. -/
def digestOfCells (a b : E) : Digest := digestFromHalves (a, b)

/-- The exponent `n < 128` of `x = g^n` (`0` for any other word). -/
def gLog7 (x : E) : ℕ := ((List.range 128).find? fun n ↦ decide (gen ^ n = x)).getD 0

/-- The window of a position of depth `d`, cap depth `cd`, holding its bit `l` (`qwWin`). -/
def qwAt (d cd l : ℕ) : ℕ :=
  if l < d - cd then l / 6 else if l = d - cd then qwNp d cd else qwNp d cd + 1

/-- The position whose windows `g^v` the run at `bp` holds: bit `l` from the window holding it. -/
def winPosOf (rd : Reader) (bp : E) (d cd : ℕ) : ℕ :=
  bitsVal (fun l ↦ (gLog7 (memRead rd bp (qwAt d cd l))).testBit (l - (qwWin d cd (qwAt d cd l)).1)) d

/-! ## A query's witness -/

/-- The siblings below the cap of the query at `q`, read off the children cells `ch ..`: at
level `l` the pair off the walk's side (the left at bit `1`, the right at bit `0`). -/
def oqSibsOf (pd ch q : ℕ) (σ : Val) : List Digest :=
  (List.range pd).map fun l ↦
    digestOfCells (σ (.n (ch + 4 * l + (if q.testBit l then 0 else 2))))
      (σ (.n (ch + 4 * l + (if q.testBit l then 0 else 2) + 1)))

/-- The arguments of a query's `walk_path` call (`oqQueryT`): the leaf digest's cells, the window
pointer, the cap and the flags. -/
def oqWalkArgs (s : Oq) (b : ℕ) (emit : Bool) (bp cap flags : E) (σ : Val) : List E :=
  [σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 1)), bp, cap,
    flags]

/-- The query hinted at `b` (window pointer `bp`, cap `cap`, flags `flags`), from its frame `σ`
and its walk's frame (`V (oqWalkOf s) (oqWalkArgs …) []`, whose children cells hold the
siblings). -/
def oqQueryW (s : Oq) (rd : Reader) (bp cap flags : E) (b : ℕ) (emit : Bool) (σ : Val)
    (V : FrameMap) : QW :=
  (winPosOf rd bp (s.pd + s.cd) s.cd, oqRow s b σ,
    oqSibsOf s.pd wpCh (winPosOf rd bp (s.pd + s.cd) s.cd)
      (V (oqWalkOf s) (oqWalkArgs s b emit bp cap flags σ) []))

/-- A loop iteration's queries, from its frame: two at level 0 (`base = 1`), one deeper. -/
def oqIterOf (s : Oq) (rd : Reader) (σ : Val) (V : FrameMap) : List QW :=
  if s.base = 1 then
    [oqQueryW s rd (σ (.n 15)) (σ (.n 4)) (σ (.n 5)) 16 true σ V,
      oqQueryW s rd (σ (.n (oqE1 s + 1))) (σ (.n 4)) (σ (.n 5)) (oqE1 s + 2) false σ V]
  else [oqQueryW s rd (σ (.n 13)) (σ (.n 4)) (σ (.n 5)) 14 true σ V]

/-- The loop's arguments after its counter (`oqMainT`'s call). -/
def oqLoopArgs (σ : Val) : List E :=
  [σ (.n 7), σ (.n 5), σ (.n 6), σ (.n 0), σ (.n 1), σ (.n 3), σ (.n 4), σ (.n 10), σ (.n 2)]

/-- **The queries of `opening_queries`**, from its frame `σ` and its `N` iterations' frames. -/
def oqsOf (s : Oq) (odd : ℕ) (loop : String) (N : ℕ) (rd : Reader) (σ : Val) (V : FrameMap) :
    List QW :=
  (if odd = 1 then [oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V] else []) ++
    (List.range N).flatMap fun j ↦ oqIterOf s rd (V loop (gen ^ j :: oqLoopArgs σ) []) V

/-! ## The specializations -/

/-- The deployed specializations with their loop helpers (read off their bodies' `callIf`) and
shapes: `(name, loop, shape)`, in the order of `openingQueriesShapes`. -/
def openingQueriesLoops : List (String × String × OqShape) :=
  [("opening_queries__L0_L1_L6_L32_L17_L8_L0_L0_L0_L0_L0", "__loop340",
      ⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L6_L0_L0_L0_L0_L0", "__loop341",
      ⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L5_L0_L0_L0_L0_L0", "__loop342",
      ⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L14_L5_L4_L39_L20_L5_L1", "__loop343",
      ⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L1_L1_L6_L32_L18_L8_L0_L0_L0_L0_L0", "__loop344",
      ⟨1, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0", "__loop345",
      ⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0", "__loop346",
      ⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1", "__loop347",
      ⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L1_L6_L32_L19_L8_L0_L0_L0_L0_L0", "__loop348",
      ⟨1, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0", "__loop349",
      ⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0", "__loop350",
      ⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1", "__loop351",
      ⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L1_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0", "__loop352",
      ⟨1, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0", "__loop353",
      ⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0", "__loop354",
      ⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1", "__loop355",
      ⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩),
    ("opening_queries__L1_L1_L6_L32_L21_L8_L0_L0_L0_L0_L0", "__loop356",
      ⟨1, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0", "__loop357",
      ⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0", "__loop358",
      ⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1", "__loop359",
      ⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L1_L1_L6_L32_L22_L8_L0_L0_L0_L0_L0", "__loop360",
      ⟨1, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0", "__loop361",
      ⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0", "__loop362",
      ⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1", "__loop363",
      ⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L1_L6_L32_L23_L8_L0_L0_L0_L0_L0", "__loop364",
      ⟨1, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0", "__loop365",
      ⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0", "__loop366",
      ⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1", "__loop367",
      ⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L1_L1_L6_L32_L18_L7_L0_L0_L0_L0_L0", "__loop368",
      ⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1", "__loop369",
      ⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0", "__loop370",
      ⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1", "__loop371",
      ⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L1_L6_L32_L20_L7_L0_L0_L0_L0_L0", "__loop372",
      ⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1", "__loop373",
      ⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0", "__loop374",
      ⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1", "__loop375",
      ⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩),
    ("opening_queries__L1_L1_L6_L32_L22_L7_L0_L0_L0_L0_L0", "__loop376",
      ⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1", "__loop377",
      ⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0", "__loop378",
      ⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1", "__loop379",
      ⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L1_L6_L32_L24_L7_L0_L0_L0_L0_L0", "__loop380",
      ⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0", "__loop381",
      ⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0", "__loop382",
      ⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L4_L0_L0_L0_L0_L0", "__loop383",
      ⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L4_L2_L1089_L8_L3_L1", "__loop384",
      ⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L0_L0_L4_L16_L16_L5_L4_L1131_L20_L5_L1", "__loop385",
      ⟨0, 0, 4, 16, 16, 5, 4, 1131, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1", "__loop386",
      ⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1", "__loop387",
      ⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L4_L3_L1382_L12_L4_L1", "__loop388",
      ⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L4_L4_L1464_L20_L5_L1", "__loop389",
      ⟨0, 0, 4, 16, 19, 4, 4, 1464, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1", "__loop390",
      ⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0", "__loop391",
      ⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0", "__loop392",
      ⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0", "__loop393",
      ⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0", "__loop394",
      ⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1", "__loop395",
      ⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L1_L1_L6_L32_L20_L6_L0_L0_L0_L0_L0", "__loop396",
      ⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L17_L5_L4_L1677_L20_L5_L1", "__loop397",
      ⟨0, 0, 4, 16, 17, 5, 4, 1677, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0", "__loop398",
      ⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1", "__loop399",
      ⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L1_L6_L32_L22_L6_L0_L0_L0_L0_L0", "__loop400",
      ⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L18_L4_L2_L1846_L8_L3_L1", "__loop401",
      ⟨0, 0, 4, 16, 18, 4, 2, 1846, 8, 3, 1, [1, 6]⟩),
    ("opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0", "__loop402",
      ⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1", "__loop403",
      ⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩),
    ("opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0", "__loop404",
      ⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L20_L4_L4_L2010_L20_L5_L1", "__loop405",
      ⟨0, 0, 4, 16, 20, 4, 4, 2010, 20, 5, 1, [1, 6, 360, 18245760]⟩),
    ("opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0", "__loop406",
      ⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0", "__loop407",
      ⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L4_L5_L2092_L36_L6_L1", "__loop408",
      ⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩),
    ("opening_queries__L1_L1_L6_L32_L26_L6_L0_L0_L0_L0_L0", "__loop409",
      ⟨1, 1, 6, 32, 26, 6, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0", "__loop410",
      ⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0", "__loop411",
      ⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩),
    ("opening_queries__L0_L0_L4_L16_L21_L4_L2_L2181_L8_L3_L1", "__loop412",
      ⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩)]

/-- The table's specializations are the deployed ones. -/
theorem openingQueriesLoops_shapes :
    openingQueriesLoops.map (fun p ↦ (p.1, p.2.2)) = openingQueriesShapes := rfl

/-- **`opening_queries` is sound with its queries named** at the specialization `name` (loop
helper `loop`, shape `sh`): under a call relation `C ≤ Rel` unfolding at `V`, a valuation `σ`
holding its body on `args` returning `rets`, `N` iterations (`args[7] = g^N`) and the positions
and window pointers naming positions, its meaning holds with the queries
`oqsOf sh.oq sh.odd loop N rd σ V`. -/
def opening_queries_sound_w_Spec (name loop : String) (sh : OqShape) : Prop :=
  ∀ (rd : Reader) (C : CallRel) (V : FrameMap), UnfoldsV rd C V →
    CallRel.Le C (coreProgram.Rel rd) →
    ∀ (fm : Fn) (σ : Val) (args rets : List E) (N : ℕ), coreProgram.find? name = some fm →
      fm.params.map σ = args → Stmt.HoldsList C rd σ fm.body False (fun rs ↦ rs = rets) →
      args.getD 7 0 = gen ^ N → N < ordG →
      QueryPosOk rd (args.getD 5 0) (args.getD 6 0) (oqCount sh.odd sh.base N) sh.depth sh.cd →
      MeaningOpeningQueriesW sh rd (oqsOf sh.oq sh.odd loop N rd σ V) args rets

/-- Every deployed specialization of `opening_queries` is sound with its queries named. -/
def opening_queries_all_sound_w_Spec : Prop :=
  ∀ p ∈ openingQueriesLoops, opening_queries_sound_w_Spec p.1 p.2.1 p.2.2

end
end LeanVM.Guest.B1
