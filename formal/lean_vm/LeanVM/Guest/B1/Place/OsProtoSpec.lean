/-
  LeanVM.Guest.B1.Place.OsProtoSpec

  What the placed lift of an opening arm takes of the body's completeness at honest values: the
  honest data of every accepting run, in the lift's own terms (the statement; the body's
  completeness, `Whir/C*`, proves it).
-/

module

public import LeanVM.Guest.B1.Place.OsSpec
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Opening.QueriesPlacedD1
public import LeanVM.Guest.B1.Whir.LrSound
public import LeanVM.Guest.B1.Whir.FinishSplit
public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.B1.Whir.CVal
public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# The body at honest values, as the lift takes it

An arm `open_stacked__L{m}` at the rate `ri` runs the body `osBody (osCfgR m ri)` (its levels the
rate's rows). Each level dispatches on the rate's selector into three helpers, which the lift
places by their own placed statements: `level_positions` (the first word and the sponge's
capacity, the positions and window pointers' slots, the window table), `level_queries` (`λ` and
`1/λ`, `0, 0` at the final level, the round coefficients, the high part, the positions and window
pointers), and, at a non-final level, `level_residual` (the positions, the row of `basis_d`, the
high part, `μ`). `osLpCallOf c l`, `osLqCallOf c l`, `osLrCalls c`: those dispatches' arguments
and returns, in the template's values.

`OsHonestA c args cur tabs xs tgt inn res pt pt1`: the honest data of an accepting run at the
configuration `c`:

* `own`: the buffers' words in allocation order, of their sizes (`osSizesL`), the point buffers'
  `pt`, `pt1`; `query_win_ptrs`' words (index `osIxQbpA`) are not read (the decoders write them);
* per level `l`: `level_positions`' first word `w0 l` and capacity `capL l`, the positions the
  decoders store (`posW`); `level_queries`' `λ`, `1/λ`, its hinted cap and flags (`capW`, `flW`)
  checked to the level's root (`caps`), the queries' data (S1b's `OqStatic`: the rounds, the final
  lane, the positions `qs`, the rows and siblings) and its returned chain (`batched_eq`); a
  non-final level's `μ` and `level_residual`'s chains over the stored words (`res`);
* on every memory holding the buffers at the base `b` (`OsMemA`): the rounds and the high part
  where the queries read them (`qMem`);
* **the body**: at every base, values on which the body before its return holds for every callee
  relation `C` and memory satisfying `OsHA` (the words at the cursor, the window table, the
  buffers, every named callee's meaning on loads fixed by those memories, `C` true on the
  helpers), returning `[tgt, PT, PT1, inn, res]`, allocating the buffers at their bases, the
  helpers' dispatches at their honest values (`OsHelperVals`).

`os_honest_Spec`: every accepting run of `whirOpen μ r target` from `⟨capOf S, []⟩` with no zero
challenge and openings agreeing in the caps has `OsHonestA` at the arm of `μ` and the rate `r`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The buffers -/

/-- The head's buffers' indices in `osSizesL`. -/
abbrev osIxFmsgA : ℕ := 0
abbrev osIxRootsA : ℕ := 1
abbrev osIxFchA : ℕ := 2
abbrev osIxCoefsA : ℕ := 3
abbrev osIxBetasA : ℕ := 4
abbrev osIxMusA : ℕ := 5
abbrev osIxHsA : ℕ := 6
abbrev osIxOodzA : ℕ := 7
abbrev osIxOodScA : ℕ := 8
abbrev osIxQposA : ℕ := 9
abbrev osIxQbpA : ℕ := 10

/-- A non-final level's message `sent`. -/
def osIxSentA (l : ℕ) : ℕ := 11 + l

/-- The final level's normalized lane, the tail's challenges, the point, `point1`, `basis_d`. -/
def osIxLaneA (c : OsCfg) : ℕ := 11 + c.yrLevel
def osIxTchA (c : OsCfg) : ℕ := 12 + c.yrLevel
def osIxPtA (c : OsCfg) : ℕ := 13 + c.yrLevel
def osIxPt1A (c : OsCfg) : ℕ := 14 + c.yrLevel
def osIxBdA (c : OsCfg) : ℕ := 15 + c.yrLevel

/-- Buffer `j`'s pointer, the buffers from `b`. -/
def osPtrA (c : OsCfg) (b j : ℕ) : E := ofK (addressOfIndex ((bases b (osSizesL c)).getD j 0))

/-- Buffer `j`'s words. -/
def osOwnA (own : List (List E)) (j : ℕ) : List E := own.getD j []

/-- The high part level `l`'s queries read: the final lane, or the level's row of `level_hs`. -/
def osHsPtrA (c : OsCfg) (b l : ℕ) : E :=
  if l = c.yrLevel then osPtrA c b (osIxLaneA c) else osPtrA c b osIxHsA * gen ^ (l * hsStride)

/-! ## The helpers' dispatches -/

/-- Level `l`'s row. -/
abbrev osLvA (c : OsCfg) (l : ℕ) : OsLv := c.levels.getD l default

/-- The state entering level `l`. -/
def osLvSt (c : OsCfg) (l : ℕ) : OsSt := (osLevels c 0 (c.levels.take l) (osHead c).2).2

/-- The state before level `l`'s positions. -/
def osPosSt (c : OsCfg) (l : ℕ) : OsSt :=
  let lv := osLvA c l
  let f := osRounds c.plan lv.foldsOff lv.folds (osLvSt c l)
  (if l = c.yrLevel then osFinalMsg c lv f.2 else osCommit c l lv f.2).2

/-- Level `l`'s dispatch into `level_positions`: its arguments and returns. -/
def osLpCallOf (c : OsCfg) (l : ℕ) : List V × List V :=
  let lv := osLvA c l
  let s := osPosSt c l
  let qp := osMatS c.plan osQpos lv.posOff s
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  ((s.word0 :: s.fs ++ [qp.2.1, wp.2.1, osTabs]).map V.n, osRun wp.2.2.k 5)

/-- Level `l`'s dispatch into `level_queries`: its arguments and returns. -/
def osLqCallOf (c : OsCfg) (l : ℕ) : List V × List V :=
  osQCallOf c l (osLvA c l) (osPreQ c l (osLvA c l) (osLvSt c l))

/-- The non-final levels' dispatches into `level_residual` from level `lvl`, in order. -/
def osResCallsL (c : OsCfg) (ich bd ls la : ℕ) : ℕ → List OsLv → List OsMat → ℕ →
    List (List V × List V)
  | _, [], _, _ => []
  | lvl, lv :: rest, mats, k =>
    let qp := osMatP c.plan mats osQpos lv.posOff k
    let m1 := osMatsAfter c.plan mats osQpos lv.posOff k
    let bp := osMatP c.plan m1 bd (lvl * ligColsCap) qp.2.2
    let m2 := osMatsAfter c.plan m1 bd (lvl * ligColsCap) qp.2.2
    let hp := osMatP c.plan m2 osHs (lvl * hsStride) bp.2.2
    ([.n qp.2.1, .n bp.2.1, .n hp.2.1, .n hp.2.2], osRun (hp.2.2 + 1) 2) ::
      osResCallsL c ich bd ls la (lvl + 1) rest (osResidual c ich bd ls la lvl lv mats k).2.1
        (osResidual c ich bd ls la lvl lv mats k).2.2

/-- The non-final levels' dispatches into `level_residual` (`osFinishA`'s), in order. -/
def osLrCalls (c : OsCfg) : List (List V × List V) :=
  let tl := osTail c (osLevels c 0 c.levels (osHead c).2).2
  let st := tl.2.1
  let pt := st.k + 1
  let pts := osPtBlks c pt (pt + 1) tl.2.2 0 pointCap (pt + 2)
  let bs := osBases c tl.2.2 (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel)
    (pts.2 + 6)
  osResCallsL c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel) st.mats
    (bs.2 + 3)

/-! ## The honest data -/

/-- Level `l`'s `opening_queries` shape, odd count, pairs and queries. -/
def oqSA (c : OsCfg) (l : ℕ) : Oq := (oqShapeOf (osOqName c l (osLvA c l))).oq
def oqOddA (c : OsCfg) (l : ℕ) : ℕ := (oqShapeOf (osOqName c l (osLvA c l))).odd
def oqNA (c : OsCfg) (l : ℕ) : ℕ := (osLvA c l).queries / (1 + lvBase l)
def oqQA (c : OsCfg) (l : ℕ) : ℕ := oqCount (oqOddA c l) (oqSA c l).base (oqNA c l)

/-- The positions a level's squeezes decode per squeeze. -/
abbrev osPerA (c : OsCfg) (l : ℕ) : ℕ := 128 / (osLvA c l).depth

/-- Level `l`'s root, its two cells in `level_roots`. -/
def osRootA (own : List (List E)) (l : ℕ) : E × E :=
  ((osOwnA own osIxRootsA).getD (2 * l) 0, (osOwnA own osIxRootsA).getD (2 * l + 1) 0)

/-- **`level_residual`'s chains** at a non-final level `l`, `μ = mu`, over the stored words: the
positions from the level's offset of `query_positions`, its row of `basis_d`, its row of
`level_hs`. -/
def osLrRetA (c : OsCfg) (own : List (List E)) (l : ℕ) (mu : E) : E × E :=
  let lv := osLvA c l
  resFold (lrP lv.logCols fun s ↦ (osOwnA own (osIxBdA c)).getD (l * ligColsCap + s) 0)
    (lrH lv.logCols lv.folds lv.highBits
      ((List.range lv.folds).map fun i ↦ (osOwnA own osIxHsA).getD (l * hsStride + i) 0))
    mu (0, 0) ((List.range lv.queries).map fun k ↦ (osOwnA own osIxQposA).getD (lv.posOff + k) 0)

/-- **The memory holds the buffers** at the base `b`, but `query_win_ptrs`. -/
def OsMemA (rd : Reader) (c : OsCfg) (b : ℕ) (own : List (List E)) : Prop :=
  ∀ j < (osSizesL c).length, j ≠ osIxQbpA → ReadsAt rd (osPtrA c b j) (osOwnA own j)

/-- A named callee's loads, fixed on every memory holding the caller's words. -/
def OsFixedA (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E) (xs : List E) (K : OsKind)
    (a : List E) : Prop :=
  ∀ q ∈ K.spec, ∃ ws : List E, ws.length = q.2 ∧ ∀ rd', ReadsAt rd' cur xs → WinTabs rd' tabs →
    OsMemA rd' c b own → ReadsAt rd' (a.getD q.1 0) ws

/-- **The callee relation and memory the body holds on.** -/
def OsHA (C : CallRel) (rd : Reader) (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E)
    (xs : List E) : Prop :=
  ReadsAt rd cur xs ∧ WinTabs rd tabs ∧ OsMemA rd c b own ∧
    (∀ f K, osKindOf f = some K → ∀ a r, K.Pre rd a r → OsFixedA c b own cur tabs xs K a → C f a r) ∧
    ∀ f a r, osKindOf f = none → C f a r

/-- The per-level data the helpers' dispatches carry. -/
structure OsLvData where
  w0 : E
  capL : List E
  lam : E
  lamInv : E
  batched : E
  mu : E

/-- **The helpers' dispatches at their honest values** under `σ'`, the buffers at `b`. -/
def OsHelperVals (c : OsCfg) (b : ℕ) (tabs : E) (own : List (List E)) (D : ℕ → OsLvData)
    (σ' : Val) : Prop :=
  ∀ l < c.levels.length,
    (osLpCallOf c l).1.map σ' = (D l).w0 :: (D l).capL ++
      [osPtrA c b osIxQposA * gen ^ (osLvA c l).posOff,
        osPtrA c b osIxQbpA * gen ^ (osLvA c l).posOff, tabs] ∧
    (osLpCallOf c l).2.map σ' = ((⟨(D l).capL, []⟩ : Fs).squeezeN ((osLvA c l).squeezes - 1)).2.cap ∧
    (osLqCallOf c l).1.map σ' =
      [if l = c.yrLevel then 0 else (D l).lam, if l = c.yrLevel then 0 else (D l).lamInv,
        osPtrA c b osIxCoefsA * gen ^ (2 * (osLvA c l).foldsOff), osHsPtrA c b l,
        osPtrA c b osIxQposA * gen ^ (osLvA c l).posOff,
        osPtrA c b osIxQbpA * gen ^ (osLvA c l).posOff] ∧
    (osLqCallOf c l).2.map σ' =
      [(osRootA own l).1, (osRootA own l).2, (D l).batched,
        (if l = c.yrLevel then 0 else (D l).lam) ^ (osLvA c l).queries] ∧
    (l < c.yrLevel →
      ((osLrCalls c).getD l ([], [])).1.map σ' =
        [osPtrA c b osIxQposA * gen ^ (osLvA c l).posOff,
          osPtrA c b (osIxBdA c) * gen ^ (l * ligColsCap),
          osPtrA c b osIxHsA * gen ^ (l * hsStride), (D l).mu] ∧
      ((osLrCalls c).getD l ([], [])).2.map σ' =
        [(osLrRetA c own l (D l).mu).1, (osLrRetA c own l (D l).mu).2])

/-- **What the body returns and allocates** under `σ'`, the buffers at `b`. -/
def OsOutA (c : OsCfg) (b : ℕ) (tabs tgt inn res : E) (own : List (List E)) (D : ℕ → OsLvData)
    (σ' : Val) : Prop :=
  (osBodyRet c).map σ' = [tgt, osPtrA c b (osIxPtA c), osPtrA c b (osIxPt1A c), inn, res] ∧
  ((osBodyA c).filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ' s)) =
    osSizesL c ∧
  (((osBodyA c).filterMap Main.Stmt.allocSz).map Prod.fst).map σ' =
    (bases b (osSizesL c)).map (fun e ↦ ofK (addressOfIndex e)) ∧
  OsHelperVals c b tabs own D σ'

/-- **The body's completeness at honest values**, as the placed lift takes it. -/
structure OsHonestA (c : OsCfg) (args : List E) (cur tabs : E) (xs : List E) (tgt inn res : E)
    (pt pt1 : List E) where
  own : List (List E)
  own_len : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesL c)
  own_pt : osOwnA own (osIxPtA c) = pt
  own_pt1 : osOwnA own (osIxPt1A c) = pt1
  D : ℕ → OsLvData
  capL_len : ∀ l < c.levels.length, (D l).capL.length = 5
  /-- The positions the decoders store: squeeze `j`'s position `i`. -/
  posW : ∀ l < c.levels.length, ∀ j < (osLvA c l).squeezes, ∀ i < osPerA c l,
    (osOwnA own osIxQposA).getD ((osLvA c l).posOff + j * osPerA c l + i) 0 =
      eOfNat (qwPosOf (osLvA c l).depth (sqSample (D l).w0 (D l).capL j) i)
  lam_inv : ∀ l < c.yrLevel, (D l).lam * (D l).lamInv = 1
  capW : ℕ → List E
  flW : ℕ → List E
  rounds : ℕ → List FoldRound
  hsv : ℕ → List E
  qs : ℕ → ℕ → ℕ
  rows : ℕ → ℕ → List K
  sibs : ℕ → ℕ → List Digest
  rounds_len : ∀ l < c.levels.length, (rounds l).length = (oqSA c l).folds
  hsv_len : ∀ l < c.levels.length, (oqSA c l).final = 1 → (hsv l).length = (oqSA c l).nHs
  static : ∀ l < c.levels.length,
    OqStatic (oqSA c l) (rounds l) (hsv l) (qs l) (rows l) (sibs l) (oqQA c l)
  qs_eq : ∀ l < c.levels.length, ∀ k < oqQA c l,
    qs l k = qwPosOf (osLvA c l).depth (sqSample (D l).w0 (D l).capL (k / osPerA c l))
      (k % osPerA c l)
  batched_eq : ∀ l < c.levels.length, (D l).batched = if (oqSA c l).final = 1 then 0 else
    oqChain (oqOddA c l) (oqSA c l).base (D l).lamInv
      (fun k ↦ foldRow (lanesOf (oqSA c l).base (rows l k)) (K.ofBits (qs l k)) (rounds l)) (oqNA c l)
  /-- The hinted cap and flags, checked to the level's root, each query's leaf climbed to them. -/
  caps : ∀ l < c.levels.length,
    (capW l).length = 4 * 2 ^ (oqSA c l).cd ∧ (flW l).length = 2 ^ (oqSA c l).cd ∧
    (∀ (rd : Reader) (CAP FL : E), ReadsAt rd CAP (capW l) → ReadsAt rd FL (flW l) →
      MeaningVerifyMerkleCap (oqSA c l).cd rd [CAP, FL] [(osRootA own l).1, (osRootA own l).2]) ∧
    ∀ k < oqQA c l,
      (capW l).getD (2 * (2 ^ (oqSA c l).cd + qs l k / 2 ^ (oqSA c l).pd)) 0 =
        (digestHalves (climbD (merkleLeafDigest (rows l k)) (qs l k) (sibs l k))).1 ∧
      (capW l).getD (2 * (2 ^ (oqSA c l).cd + qs l k / 2 ^ (oqSA c l).pd) + 1) 0 =
        (digestHalves (climbD (merkleLeafDigest (rows l k)) (qs l k) (sibs l k))).2 ∧
      (flW l).getD (2 ^ ((oqSA c l).cd - 1) + qs l k / 2 ^ ((oqSA c l).pd + 1)) 0 = 1
  qMem : ∀ b rd, OsMemA rd c b own → ∀ l < c.levels.length,
    RoundsAt rd (osPtrA c b osIxCoefsA * gen ^ (2 * (osLvA c l).foldsOff)) (rounds l) ∧
    ((oqSA c l).final = 1 → WordsAt rd (osHsPtrA c b l) (hsv l))
  body : ∀ b, ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader),
    OsHA C rd c b own cur tabs xs →
      BlkF C rd (Val.ofArgs args) 11 kEnd f (osBodyA c) (OsOutA c b tabs tgt inn res own D)

/-- **The honest data of every accepting run** at its arm and rate. -/
def os_honest_Spec : Prop :=
  ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
      (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
      NoZeroChallenge μ r target S xs os root →
      CapsAgree μ r target S xs os root →
      Nonempty (OsHonestA (osCfgR (μ - minOpenLog) (r - 1))
        (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
        cur tabs xs w.target w.inner w.residual (w.point ++ List.replicate (pointCap - μ) 0)
        (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1))

end
end LeanVM.Guest.B1
