/-
  LeanVM.Guest.B1.Opening.Witness

  `opening_queries`' witness read off its frames: each query's position, row and siblings below
  the cap, as functions of the valuations (the witness convention, `B1/Main/Frames.lean`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesRow
public import LeanVM.Guest.B1.Main.FramesP
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.B1.Opening.QueriesLoops

/-!
# `opening_queries`' witness, named

The witness convention: a witness is a function of the function's own valuation and the frame map
`V`, reading words only (no hash, no verifier function, no choice).

**A query's witness** (`QW`, `Interface.lean`): its position, its row and its siblings below the
cap.

* `winPosOf rd bp D cd`: the position whose windows `g^v` the run at `bp` holds (`memRead`, the
  memory's word, `0` where it has none; `gLog7`, the exponent of a small power of `g`), bit `l`
  read from the window holding it (`qwAt`);
* `oqSibsOf pd ch σ`: the siblings below the cap, read off the hinted cells `ch ..` of a frame;
* `oqQueryW s cd rd bp b emit σ`: the query hinted at `b`, its window pointer `bp` (`oqRow` its
  row), its siblings off its inline path's hinted cells;
* `oqIterOf s cd rd σ`: a loop iteration's queries (two at level 0, one deeper), from its frame;
* `oqsOf s cd odd loop N rd σ V`: the function's queries, from its frame `σ` (the odd first query
  at level 0) and the frames `V loop (g^j :: oqLoopArgs s σ) []` of its `N` iterations.

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

/-- The siblings below the cap, read off the hinted cells `ch ..` (`walk_path`, inline): level `l`'s
at `ch + 2l`, `ch + 2l + 1`. -/
def oqSibsOf (pd ch : ℕ) (σ : Val) : List Digest :=
  (List.range pd).map fun l ↦ digestOfCells (σ (.n (ch + 2 * l))) (σ (.n (ch + 2 * l + 1)))

/-- The query hinted at `b` (window pointer `bp`) of a level of cap depth `cd`, from its frame `σ`:
its position off its windows, its row, its siblings off its path's hinted cells. -/
def oqQueryW (s : Oq) (cd : ℕ) (rd : Reader) (bp : E) (b : ℕ) (emit : Bool) (σ : Val) : QW :=
  (winPosOf rd bp (s.pd + cd) cd, oqRow s b σ, oqSibsOf s.pd (oqCh s b emit) σ)

/-- A loop iteration's queries, from its frame: two at level 0 (`base = 1`), one deeper. -/
def oqIterOf (s : Oq) (cd : ℕ) (rd : Reader) (σ : Val) : List QW :=
  if s.base = 1 then
    [oqQueryW s cd rd (σ (.n 14)) 15 true σ, oqQueryW s cd rd (σ (.n (oqE1 s + 1))) (oqE1 s + 2) false σ]
  else [oqQueryW s cd rd (σ (.n 13)) 14 true σ]

/-- The loop's arguments after its counter (`oqMainT`'s call). -/
def oqLoopArgs (s : Oq) (σ : Val) : List E :=
  [σ (.n oqMN), σ (.n (if s.base = 1 then oqMK s - 2 else oqMPos)),
    σ (.n (if s.base = 1 then oqMK s - 1 else oqMQp)), σ (.n oqMCap), σ (.n oqMFlags), σ (.n oqMCoefs),
    σ (.n oqMHs), σ (.n 11), σ (.n oqMLamInv)]

/-- **The queries of `opening_queries`** of a level of cap depth `cd`, from its frame `σ` (the odd
first query at level 0 when `odd = 1`) and its `N` iterations' frames. -/
def oqsOf (s : Oq) (cd odd : ℕ) (loop : String) (N : ℕ) (rd : Reader) (σ : Val) (V : FrameMap) :
    List QW :=
  (if odd = 1 then [oqQueryW s cd rd (σ (.n 16)) 17 true σ] else []) ++
    (List.range N).flatMap fun j ↦ oqIterOf s cd rd (V loop (gen ^ j :: oqLoopArgs s σ) [])


/-- **`opening_queries` is sound with its queries named**, in the program `P`, at the specialization
`name` (loop helper `loop`, shape `sh`) at a cap depth `1 ≤ cd ≤ 8`: under a call relation
`C ≤ Rel` unfolding at `V`, a valuation `σ` holding its body on `args` returning `rets`, `N`
iterations (`args[7] = g^N`), the odd first query `args[8] = g^odd`, `odd ≤ base`, and the positions
and window pointers naming positions of depth `pd + cd`, its meaning holds with the queries
`oqsOf sh.oq cd odd loop N rd σ V`. -/
def opening_queries_sound_w_SpecP (P : Program) (name loop : String) (sh : OqShape) : Prop :=
  ∀ (cd : ℕ), 1 ≤ cd → cd ≤ 8 → ∀ (rd : Reader) (C : CallRel) (V : FrameMap),
    UnfoldsVP P rd C V → CallRel.Le C (P.Rel rd) →
    ∀ (fm : Fn) (σ : Val) (args rets : List E) (N odd : ℕ), P.find? name = some fm →
      fm.params.map σ = args → Stmt.HoldsList C rd σ fm.body False (fun rs ↦ rs = rets) →
      args.getD 7 0 = gen ^ N → N < ordG → args.getD 8 0 = gen ^ odd → odd ≤ sh.base →
      QueryPosOk rd (args.getD 5 0) (args.getD 6 0) (oqCount odd sh.base N) (sh.pd + cd) cd →
      MeaningOpeningQueriesW sh cd rd (oqsOf sh.oq cd odd loop N rd σ V) args rets

/-- Every deployed specialization of `opening_queries` is sound with its queries named. -/
def opening_queries_all_sound_w_SpecP (P : Program) : Prop :=
  ∀ p ∈ openingQueriesLoops, opening_queries_sound_w_SpecP P p.1 p.2.1 p.2.2

end
end LeanVM.Guest.B1
