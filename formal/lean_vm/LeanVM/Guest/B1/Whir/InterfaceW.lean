/-
  LeanVM.Guest.B1.Whir.InterfaceW

  `open_stacked`'s soundness with its witness named: the stream words and the openings it reads,
  as functions of its valuation and the frame map.
-/

module

public import LeanVM.Guest.B1.Whir.RateCfg
public import LeanVM.Guest.B1.Whir.Folds
public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Opening.Witness

/-!
# `open_stacked`, its witness named

The witness convention (G6, 2026-10-23, `B1/Main/Frames.lean`): a witness is a function of the
function's own valuation `σ` and the frame map `V`, reading words only.

**The witness** `open_stacked_osW rd m r σ V` of the size `m` at the rate `r`, its levels that
rate's rows (`osCfgR m (r - 1)`):

* the stream words: the `osWordsLen c` words at the cursor `σ 9` (`readN`), as many as the size
  reads at the rate: the first quadratic's two, each level's rounds (`roundLen` words a round: the
  nonce of its proof of work, if any, and two), its next commitment's six (root, out-of-domain
  value, intro, nonce) or the final message and its nonce, its intro's two, and the tail's
  `2·(yrLog - 1)`;
* the openings, one phase per level: the queries of the `opening_queries` call in the level's
  `level_queries` call (`osQCalls`, the dispatches the template makes, its words values of `σ`;
  `lqCall`, the call in the callee's frame `V name args rets`), read off that callee's frame and
  its loop's frames (`oqsOf`), each with the cap's siblings from the memory (`capSibsOf`, the
  cells `verify_merkle_cap` checks): `⟨position, row, below-cap ++ cap siblings⟩`.

`OpenOutW` is `OpenOut` at given words and openings. `open_stacked_sound_w_Spec osW`: under a call
relation `C ≤ Rel` unfolding at `V`, a valuation `σ` holding the body of `openName μ` on the
arguments `rateSel r :: fs ++ [target, root0, root1, cur]` gives `OpenOutW` at
`osW rd (μ - minOpenLog) r σ V`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `OpenOut` at given words and openings -/

/-- **`OpenOut` at the words `xs` and the openings `os`.** -/
def OpenOutW (rd : Reader) (μ r : ℕ) (root : Digest) (fs : List E) (target cur : E)
    (rets : List E) (xs : List E) (os : List (List Opening)) : Prop :=
  ∃ (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
    ReadsAt rd cur xs ∧
    RunsWith (whirOpen μ r target) ⟨fs, []⟩ xs os [(root, stackShape μ r)] w s' roots' ∧
    w.point.length = μ ∧
    ∃ pt pt1 : E, rets = [w.target, pt, pt1, w.inner, w.residual] ∧
      ReadsAt rd pt (w.point ++ List.replicate (pointCap - μ) 0) ∧
      ReadsAt rd pt1 (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)

theorem OpenOutW.openOut {rd : Reader} {μ r : ℕ} {root : Digest} {fs : List E} {target cur : E}
    {rets xs : List E} {os : List (List Opening)} (h : OpenOutW rd μ r root fs target cur rets xs os) :
    OpenOut rd μ r root fs target cur rets := by
  obtain ⟨w, s', roots', h1, h2, h3, h4⟩ := h
  exact ⟨xs, os, w, s', roots', h1, h2, h3, h4⟩

/-! ## The witness -/

/-- The stream words the levels `lvl ..` read: each its rounds', its next commitment's six or the
final message and its nonce, and its intro's two. -/
def lvsWords (c : OsCfg) : ℕ → List OsLv → ℕ
  | _, [] => 0
  | lvl, lv :: rest =>
    roundLen lv.foldGrind * lv.folds + (if lvl = c.yrLevel then c.yrLen + 1 else 6) + 2 +
      lvsWords c (lvl + 1) rest

/-- The stream words a size reads at a rate's levels: the first quadratic's two, the levels', the
tail's. -/
def osWordsLen (c : OsCfg) : ℕ := 2 + lvsWords c 0 c.levels + 2 * (c.yrLog - 1)

/-- The name of the `opening_queries` specialization a level's `level_queries` calls. -/
def oqNameOf (lvl : ℕ) (lv : OsLv) : String :=
  oqName lv.queries (if lvl = 0 then 1 else 0) lv.interleave lv.leafCells lv.depth lv.capDepth

/-- The `opening_queries` call in `level_queries`' body (`lqBody`): its name, arguments and
returns. -/
def lqCall (lvl : ℕ) (lv : OsLv) : String × List V × List V :=
  let pw := osPowSteps 0 (osPowDigits lv.queries) 0 9
  let k := 9 + osPowLen lv.queries
  (oqNameOf lvl lv, [.n 4, .n 6, .n 0, .n pw.2, .n 1, .n 2, .n k], [.n (k + 1)])

/-- The dispatch into `level_queries` of `osQueries _ lvl lv lam s`: the rate's name, the
arguments and the returns. -/
def osQueriesDisp (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam : ℕ) (s : OsSt) :
    String × List V × List V :=
  let k := s.k
  let P := c.plan
  let m0 := s.mats
  let fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  let bp := osMatP P m1 osQbp lv.posOff fp.2.2
  (osQueriesName lvl lv, [.n lam, .n bp.2.1, .n (k + 1)], osRun bp.2.2 4)

/-- The `level_queries` dispatch of a level's template (`osLevel`, `osQueries`). -/
def osQCall (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : String × List V × List V :=
  let f := osFolds (osFoldNames c lvl lv) osFch lv.foldsOff lv.folds s
  let m := if lvl = c.yrLevel then osFinal c f.2 else osCommit c.plan lvl lv f.2
  let sq := osPositions c lvl lv m.2.1
  let lam := sq.2.k - 1
  let mu := osMu lvl lam sq.2.k
  osQueriesDisp c lvl lv lam { sq.2 with k := mu.2 }

/-- The levels' `level_queries` dispatches, with each level's index and configuration. -/
def osQCalls (c : OsCfg) : ℕ → List OsLv → OsSt → List (ℕ × OsLv × String × List V × List V)
  | _, [], _ => []
  | lvl, lv :: rest, s => (lvl, lv, osQCall c lvl lv s) :: osQCalls c (lvl + 1) rest (osLevel c lvl lv s).2

/-- The sibling of the cap's node `capNode D p j` (the ancestor `j` levels up of the cap's leaf
`p`, `2^(D - j) + p / 2^j`). -/
def capSib (D p j : ℕ) : ℕ :=
  if p / 2 ^ j % 2 = 0 then 2 ^ (D - j) + p / 2 ^ j + 1 else 2 ^ (D - j) + p / 2 ^ j - 1

/-- **The cap's siblings** of its leaf `p` (of `2^D`), from the cap's cells at `cap` (node `v`'s
cells `2v`, `2v + 1`). -/
def capSibsOf (rd : Reader) (cap : E) (D p : ℕ) : List Digest :=
  (List.range D).map fun j ↦
    digestOfCells (memRead rd cap (2 * capSib D p j)) (memRead rd cap (2 * capSib D p j + 1))

/-- A query's opening: its position, its row, its siblings below the cap, then the cap's. -/
def toOpening (rd : Reader) (cap : E) (cd depth : ℕ) (w : QW) : Opening :=
  ⟨w.1, w.2.1, w.2.2 ++ capSibsOf rd cap cd (w.1 / 2 ^ (depth - cd))⟩

/-- The `opening_queries` shape of a level. -/
def lvOq (lvl : ℕ) (lv : OsLv) : Oq :=
  ⟨if lvl = 0 then 1 else 0, lv.interleave, lv.depth - lv.capDepth, lv.capDepth⟩

/-- **A level's openings** from its `opening_queries` call `call` (words values of `σ`) and the
queries' witness `W` at the call's words: each with the cap's siblings from the memory. -/
def lvOpenings (rd : Reader) (σ : Val) (lv : OsLv) (W : List E → List E → List QW)
    (call : String × List Core.V × List Core.V) : List Opening :=
  (W (call.2.1.map σ) (call.2.2.map σ)).map
    (toOpening rd ((call.2.1.map σ).headD 0) lv.capDepth lv.depth)

/-- The queries' witness of level `lvl`'s `opening_queries` call `name`: read off the callee's frame
and its loop's frames. -/
def lvW (rd : Reader) (Fr : FrameMap) (lvl : ℕ) (lv : OsLv) (name : String) :
    List E → List E → List QW := fun args rets ↦
  oqsOf (lvOq lvl lv) (lv.queries % 2 * (if lvl = 0 then 1 else 0)) (oqLoopOf name)
    (lv.queries / (1 + if lvl = 0 then 1 else 0)) rd (Fr name args rets) Fr

/-- **A level's openings** from its `level_queries` call on `args`, returning `rets`: those of the
`opening_queries` call in the callee's frame `Fr name args rets`, read off that frame and its
loop's frames. -/
def lqOpenings (rd : Reader) (Fr : FrameMap) (lvl : ℕ) (lv : OsLv) (args rets : List E) :
    List Opening :=
  lvOpenings rd (Fr (osQueriesName lvl lv) args rets) lv (lvW rd Fr lvl lv (oqNameOf lvl lv))
    (lqCall lvl lv)

/-- **A level's openings**, from its `level_queries` dispatch's words in `σ` and the frames `Fr`. -/
def osLevelOs (rd : Reader) (σ : Val) (Fr : FrameMap) :
    ℕ × OsLv × String × List Core.V × List Core.V → List Opening
  | (lvl, lv, _, args, rets) => lqOpenings rd Fr lvl lv (args.map σ) (rets.map σ)

/-- **`open_stacked`'s witness** at the size `m` and the rate `r`, from its valuation `σ` and the
frames `V`: the stream words at the cursor and the levels' openings, one phase per level, at the
rate's levels (`osCfgR m (r - 1)`). -/
def open_stacked_osW (rd : Reader) (m r : ℕ) (σ : Val) (V : FrameMap) :
    List E × List (List Opening) :=
  (readN rd (σ (.n 9)) (osWordsLen (osCfgR m (r - 1))),
    (osQCalls (osCfgR m (r - 1)) 0 (osCfgR m (r - 1)).levels
      (osHead (osCfgR m (r - 1))).2).map (osLevelOs rd σ V))

/-! ## The statement -/

/-- **`open_stacked` is sound with its witness `osW`**: under a call relation `C ≤ Rel` unfolding
at the frame map `V`, a valuation `σ` holding the body of the specialization of `μ` on the rate's
selector, the capacity cells `fs`, the claim `target`, the root's two cells and the cursor,
returning `rets`, on a memory image of at most `2^32` words (the query windows' range checks),
gives `OpenOutW` at the words and openings `osW L.read (μ - minOpenLog) r σ V`. Proved as
`open_stacked_sound_w` for `open_stacked_osW`. -/
def open_stacked_sound_w_Spec
    (osW : Reader → ℕ → ℕ → Val → FrameMap → List E × List (List Opening)) :
    Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ) (C : CallRel) (V : FrameMap), UnfoldsV L.read C V →
    CallRel.Le C (coreProgram.Rel L.read) →
    ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 32 → 1 ≤ r → r ≤ 4 →
      ∀ (root : Digest) (fs : List E) (target root0 root1 cur : E) (rets : List E) (fn : Fn)
        (σ : Val), fs.length = 5 → (root0, root1) = digestHalves root →
        coreProgram.find? (openName μ) = some fn →
        fn.params.map σ = rateSel r :: fs ++ [target, root0, root1, cur] →
        Stmt.HoldsList C L.read σ fn.body False (fun rs ↦ rs = rets) →
        OpenOutW L.read μ r root fs target cur rets (osW L.read (μ - minOpenLog) r σ V).1
          (osW L.read (μ - minOpenLog) r σ V).2

end
end LeanVM.Guest.B1.Whir
