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

The witness convention (G6, 2026-10-23): a witness is a function of the function's own valuation
and the frame map `V`, reading words only (no hash, no verifier function, no choice).

**A query's witness** (`QW`): its position, its row and its siblings below the cap.

* `winPosOf rd bp D cd`: the position whose windows `g^v` the run at `bp` holds (`memRead`, the
  memory's word, `0` where it has none; `gLog7`, the exponent of a small power of `g`), bit `l`
  read from the window holding it (`qwAt`);
* `oqSibsOf pd ch q σ`: the siblings below the cap, read off the children cells `ch ..` of a
  frame: at level `l` the pair off the walk's side (`sibOff`);
* `oqQueryW s rd bp cap flags b emit σ V`: the query hinted at `b`, its window pointer `bp` (`oqRow`
  its row), its siblings off its `walk_path` call's frame (40f877dc: the walk is a function);
* `oqIterOf s rd σ V`: a loop iteration's queries (two at level 0, one deeper), from its frame;
* `oqsOf s odd loop N rd σ V`: the function's queries, from its frame `σ` (the odd first query at
  level 0) and the frames `V loop (g^j :: ps) []` of its `N` iterations, `ps` the loop's other
  arguments (`oqLoopArgs σ`).

**What the witness satisfies.** `QueryOpensS` is `QueryOpens` with the siblings named;
`MeaningOpeningQueriesW … ws` is `MeaningOpeningQueries` with the queries' positions, rows and
siblings those of `ws`. `opening_queries_sound_w_Spec`: under a call relation `C ≤ Rel` that
unfolds at `V` (`UnfoldsV`), a valuation `σ` holding the body of a deployed specialization, its
window pointers naming positions' windows, gives `MeaningOpeningQueriesW` at `oqsOf … σ V`.
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

/-- The digest of two cells (the zero digest when they are not one's). -/
def digestOfCells (a b : E) : Digest := (digestFromHalves (a, b)).getD (Vector.replicate 4 0)

/-- The exponent `n < 128` of `x = g^n` (`0` for any other word). -/
def gLog7 (x : E) : ℕ := ((List.range 128).find? fun n ↦ decide (gen ^ n = x)).getD 0

/-- The window of a position of depth `d`, cap depth `cd`, holding its bit `l` (`qwWin`). -/
def qwAt (d cd l : ℕ) : ℕ :=
  if l < d - cd then l / 6 else if l = d - cd then qwNp d cd else qwNp d cd + 1

/-- The position whose windows `g^v` the run at `bp` holds: bit `l` from the window holding it. -/
def winPosOf (rd : Reader) (bp : E) (d cd : ℕ) : ℕ :=
  bitsVal (fun l ↦ (gLog7 (memRead rd bp (qwAt d cd l))).testBit (l - (qwWin d cd (qwAt d cd l)).1)) d

/-! ## A query's witness -/

/-- A query's witness: its position, its row and its siblings below the cap. -/
abbrev QW : Type := ℕ × List K × List Digest

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
  (winPosOf rd bp (s.pd + s.cd) s.cd, oqRow b s.R σ,
    oqSibsOf s.pd wpCh (winPosOf rd bp (s.pd + s.cd) s.cd)
      (V (oqWalkOf s) (oqWalkArgs s b emit bp cap flags σ) []))

/-- A loop iteration's queries, from its frame: two at level 0 (`base = 1`), one deeper. -/
def oqIterOf (s : Oq) (rd : Reader) (σ : Val) (V : FrameMap) : List QW :=
  if s.base = 1 then
    [oqQueryW s rd (σ (.n 10)) (σ (.n 3)) (σ (.n 4)) 11 true σ V,
      oqQueryW s rd (σ (.n (oqE1 s))) (σ (.n 3)) (σ (.n 4)) (oqE1 s + 1) false σ V]
  else [oqQueryW s rd (σ (.n 9)) (σ (.n 3)) (σ (.n 4)) 10 true σ V]

/-- The loop's arguments after its counter (`oqMainT`'s call). -/
def oqLoopArgs (σ : Val) : List E :=
  [σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1), σ (.n 5), σ (.n 11), σ (.n 8)]

/-- **The queries of `opening_queries`**, from its frame `σ` and its `N` iterations' frames. -/
def oqsOf (s : Oq) (odd : ℕ) (loop : String) (N : ℕ) (rd : Reader) (σ : Val) (V : FrameMap) :
    List QW :=
  (if odd = 1 then [oqQueryW s rd (σ (.n 12)) (σ (.n 0)) (σ (.n 1)) 13 true σ V] else []) ++
    (List.range N).flatMap fun j ↦ oqIterOf s rd (V loop (gen ^ j :: oqLoopArgs σ) []) V

/-! ## What the witness satisfies -/

/-- **`QueryOpens` with the siblings below the cap named.** -/
def QueryOpensS (rd : Reader) (base I depth cd : ℕ) (cap flags wp : E) (q : ℕ) (row : List K)
    (sibs : List Digest) (d : E) : Prop :=
  row.length = (if base = 1 then I else 3 * I) ∧ sibs.length = depth - cd ∧
    ∃ w : ℕ → E,
      (∀ l < rowLo I + I / rowLo I, LoadHolds rd wp l (w l)) ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)))
        (digestHalves (climbD (merkleLeafDigest row) q sibs)).1 ∧
      LoadHolds rd cap (2 * (2 ^ cd + q / 2 ^ (depth - cd)) + 1)
        (digestHalves (climbD (merkleLeafDigest row) q sibs)).2 ∧
      LoadHolds rd flags (2 ^ (cd - 1) + q / 2 ^ (depth - cd + 1)) 1 ∧
      d = rowDot base I row w

/-- **`opening_queries`' meaning, its queries those of `ws`**: as `MeaningOpeningQueries`, query
`k` at the position `ws[k].1`, opening the row `ws[k].2.1` with the siblings `ws[k].2.2`. -/
def MeaningOpeningQueriesW (odd base I depth cd : ℕ) (rd : Reader) (ws : List QW) :
    List E → List E → Prop
  | [cap, flags, lam, lamN, qptrs, wp, nG], rets =>
      ∃ N < ordG, nG = gen ^ N ∧ lam ≠ 0 ∧ ws.length = oqCount odd base N ∧
        ∃ (bps : ℕ → E) (ds : ℕ → E),
          (∀ k < oqCount odd base N, LoadHolds rd qptrs k (bps k) ∧
            (ws.getD k default).1 < 2 ^ depth ∧
            (∀ i < qwN depth cd,
              LoadHolds rd (bps k) i (gen ^ qwVal depth cd (ws.getD k default).1 i)) ∧
            QueryOpensS rd base I depth cd cap flags wp (ws.getD k default).1
              (ws.getD k default).2.1 (ws.getD k default).2.2 (ds k)) ∧
          ∃ ch : E, (∀ i ≤ N, LoadHolds rd ch i (oqChain odd base lam⁻¹ ds i)) ∧
            rets = [oqChain odd base lam⁻¹ ds N * lamN]
  | _, _ => False

/-- The deployed specializations with their loop helpers and shapes: `(name, loop, shape, odd)`. -/
def openingQueriesLoops : List (String × String × Oq × ℕ) :=
  [("opening_queries__L0_L1_L64_L32_L17_L8", "__loop103", ⟨1, 64, 9, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L19_L8", "__loop375", ⟨1, 64, 11, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L21_L6", "__loop110", ⟨1, 64, 15, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L22_L7", "__loop397", ⟨1, 64, 15, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L24_L7", "__loop400", ⟨1, 64, 17, 7⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L20_L7", "__loop405", ⟨1, 64, 13, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L23_L7", "__loop408", ⟨1, 64, 16, 7⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L14_L5", "__loop106", ⟨0, 16, 9, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L16_L6", "__loop104", ⟨0, 16, 10, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L18_L4", "__loop390", ⟨0, 16, 14, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L19_L5", "__loop383", ⟨0, 16, 14, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L20_L6", "__loop382", ⟨0, 16, 14, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L22_L4", "__loop696", ⟨0, 16, 18, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L23_L6", "__loop401", ⟨0, 16, 17, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L18_L7", "__loop391", ⟨1, 64, 11, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L20_L6", "__loop109", ⟨1, 64, 14, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L21_L7", "__loop395", ⟨1, 64, 14, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L23_L6", "__loop112", ⟨1, 64, 17, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L25_L6", "__loop114", ⟨1, 64, 19, 6⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L21_L7", "__loop406", ⟨1, 64, 14, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L23_L8", "__loop387", ⟨1, 64, 15, 8⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L15_L5", "__loop105", ⟨0, 16, 10, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L17_L4", "__loop396", ⟨0, 16, 13, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L18_L5", "__loop380", ⟨0, 16, 13, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L19_L6", "__loop379", ⟨0, 16, 13, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L21_L4", "__loop108", ⟨0, 16, 17, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L22_L5", "__loop402", ⟨0, 16, 17, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L24_L5", "__loop115", ⟨0, 16, 19, 5⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L18_L8", "__loop107", ⟨1, 64, 10, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L20_L7", "__loop393", ⟨1, 64, 13, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L21_L8", "__loop381", ⟨1, 64, 13, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L23_L7", "__loop398", ⟨1, 64, 16, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L26_L6", "__loop116", ⟨1, 64, 20, 6⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L22_L7", "__loop407", ⟨1, 64, 15, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L24_L7", "__loop409", ⟨1, 64, 17, 7⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L16_L4", "__loop394", ⟨0, 16, 12, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L17_L5", "__loop377", ⟨0, 16, 12, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L18_L6", "__loop376", ⟨0, 16, 12, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L20_L4", "__loop403", ⟨0, 16, 16, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L21_L5", "__loop389", ⟨0, 16, 16, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L22_L6", "__loop388", ⟨0, 16, 16, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L24_L6", "__loop411", ⟨0, 16, 18, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L19_L7", "__loop392", ⟨1, 64, 12, 7⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L20_L8", "__loop378", ⟨1, 64, 12, 8⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L22_L6", "__loop111", ⟨1, 64, 16, 6⟩, 0),
    ("opening_queries__L0_L1_L64_L32_L24_L6", "__loop113", ⟨1, 64, 18, 6⟩, 0),
    ("opening_queries__L1_L1_L64_L32_L19_L7", "__loop404", ⟨1, 64, 12, 7⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L22_L8", "__loop384", ⟨1, 64, 14, 8⟩, 1),
    ("opening_queries__L1_L1_L64_L32_L25_L7", "__loop410", ⟨1, 64, 18, 7⟩, 1),
    ("opening_queries__L0_L0_L16_L24_L16_L5", "__loop374", ⟨0, 16, 11, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L17_L6", "__loop373", ⟨0, 16, 11, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L19_L4", "__loop399", ⟨0, 16, 15, 4⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L20_L5", "__loop386", ⟨0, 16, 15, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L21_L6", "__loop385", ⟨0, 16, 15, 6⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L23_L5", "__loop412", ⟨0, 16, 18, 5⟩, 0),
    ("opening_queries__L0_L0_L16_L24_L25_L5", "__loop117", ⟨0, 16, 20, 5⟩, 0)]

/-- The loop helper of a specialization. -/
def oqLoopOf (name : String) : String :=
  ((openingQueriesLoops.find? (·.1 = name)).map (·.2.1)).getD ""

/-- **`opening_queries` is sound with its queries named** at the specialization `name` (loop
helper `loop`, shape `s`, `odd`): under a call relation `C ≤ Rel` unfolding at `V`, a valuation
`σ` holding its body on `args` returning `rets`, `N` iterations (`args[6] = g^N`) and the window
pointers naming positions' windows, its meaning holds with the queries `oqsOf s odd loop N rd σ V`. -/
def opening_queries_sound_w_Spec (name loop : String) (s : Oq) (odd : ℕ) : Prop :=
  ∀ (rd : Reader) (C : CallRel) (V : FrameMap), UnfoldsV rd C V →
    CallRel.Le C (coreProgram.Rel rd) →
    ∀ (fm : Fn) (σ : Val) (args rets : List E) (N : ℕ), coreProgram.find? name = some fm →
      fm.params.map σ = args → Stmt.HoldsList C rd σ fm.body False (fun rs ↦ rs = rets) →
      args.getD 6 0 = gen ^ N → N < ordG →
      QueryWinsOk rd (args.getD 4 0) (oqCount odd s.base N) (s.pd + s.cd) s.cd →
      MeaningOpeningQueriesW odd s.base s.I (s.pd + s.cd) s.cd rd (oqsOf s odd loop N rd σ V)
        args rets

/-- Every deployed specialization of `opening_queries` is sound with its queries named. -/
def opening_queries_all_sound_w_Spec : Prop :=
  ∀ p ∈ openingQueriesLoops, opening_queries_sound_w_Spec p.1 p.2.1 p.2.2.1 p.2.2.2

end
end LeanVM.Guest.B1
