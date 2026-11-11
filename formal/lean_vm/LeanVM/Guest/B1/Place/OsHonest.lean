/-
  LeanVM.Guest.B1.Place.OsHonest

  What the placed lift of f128's `open_stacked` takes of the body's completeness at honest
  values, in the lift's own terms.
-/

module

public import LeanVM.Guest.B1.Place.OsLayF
public import LeanVM.Guest.B1.Place.OsQPlace
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Whir.FinishSplit
public import LeanVM.Guest.B1.Whir.Witness
public import LeanVM.Guest.B1.Whir.CVal

/-!
# The body at honest values, as the lift takes it

`OsHonest c args cur tabs xs tgt inn res pt pt1`: the honest data of an accepting run at the
configuration `c` (the body's completeness, `Whir/C*`, gives it):

* the buffers' words `own` in allocation order, of their sizes (`osSizesF`), the point buffers'
  `pt`, `pt1`; `query_win_ptrs`' entry is not read (the decoders write it);
* each level's squeezes' capacities `cap l j` and decoded words `word l j`, and its
  `opening_queries` data (S1b-2's `OqStatic`, `OqLinMem` but the windows): the rounds'
  challenges, the final coefficients, the positions `qs`, the rows and siblings, `λ⁻¹`, the
  returned chain;
* on every memory holding the buffers at the base `b` (`OsMemF`): the squeeze rows, the decoded
  positions, the queries' words, the residual loops' runs;
* **the body**: at every base, values on which the body before its return holds for every
  callee relation `C` and memory satisfying `OsH` (the words at the cursor, the window table, the
  buffers, every named callee's meaning on loads fixed by those memories, `C` true on unnamed
  callees), returning `[tgt, PT, PT1, inn, res]`, allocating the buffers at their bases, the
  special calls at their honest values (`OsSpecVals`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## Indices and pointers -/

/-- Level `l`'s squeeze run's index among the buffers. -/
def osIxSqz (c : OsCfg) (l : ℕ) : ℕ := 13 + 2 * l + (if l = c.yrLevel then 0 else 1)

/-- The final level's normalized lane's index. -/
def osIxHsF (c : OsCfg) : ℕ := 14 + 2 * c.yrLevel

/-- The finish's buffers' indices: the tail challenges, the point, `point1`, `basis_d`, … -/
def osIxPT (c : OsCfg) : ℕ := 14 + 2 * c.levels.length
def osIxPT1 (c : OsCfg) : ℕ := 15 + 2 * c.levels.length
def osIxBD (c : OsCfg) : ℕ := 16 + 2 * c.levels.length
def osIxRC (c : OsCfg) (l : ℕ) : ℕ := 20 + 2 * c.levels.length + l

/-- The high part a level's queries read: the final lane, or the level's row of `level_hs`. -/
def osHsPtr (c : OsCfg) (b l : ℕ) : E :=
  if l = c.yrLevel then osPtrF c b (osIxHsF c) else osPtrF c b 8 * gen ^ (l * hsStride)

/-- Level `l`'s `opening_queries` shape. -/
def oqS (c : OsCfg) (l : ℕ) : Oq := (oqShapeOf (osQueriesName c l (osLvAt c l))).oq

/-- Level `l`'s `opening_queries` odd count. -/
def oqOdd (c : OsCfg) (l : ℕ) : ℕ := (oqShapeOf (osQueriesName c l (osLvAt c l))).odd

/-- Level `l`'s query pairs (`g^N`). -/
def oqN (c : OsCfg) (l : ℕ) : ℕ := (osLvAt c l).queries / (1 + if l = 0 then 1 else 0)

/-- Level `l`'s queries. -/
def oqQ (c : OsCfg) (l : ℕ) : ℕ := oqCount (oqOdd c l) (oqS c l).base (oqN c l)

/-! ## The memory and the callee relation -/

/-- **The memory holds the buffers** at the base `b`, but `query_win_ptrs`. -/
def OsMemF (rd : Reader) (c : OsCfg) (b : ℕ) (own : List (List E)) : Prop :=
  ∀ j < (osSizesF c).length, j ≠ osIxQbp → ReadsAt rd (osPtrF c b j) (own.getD j [])

/-- A named callee's loads, fixed on every memory holding the caller's words. -/
def OsFixedF (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E) (xs : List E) (K : OsKind)
    (a : List E) : Prop :=
  ∀ q ∈ K.spec, ∃ ws : List E, ws.length = q.2 ∧ ∀ rd', ReadsAt rd' cur xs → WinTabs rd' tabs →
    OsMemF rd' c b own → ReadsAt rd' (a.getD q.1 0) ws

/-- **The callee relation and memory the body holds on.** -/
def OsH (C : CallRel) (rd : Reader) (c : OsCfg) (b : ℕ) (own : List (List E)) (cur tabs : E)
    (xs : List E) : Prop :=
  ReadsAt rd cur xs ∧ WinTabs rd tabs ∧ OsMemF rd c b own ∧
    (∀ f K, osKindOf f = some K → ∀ a r, K.Pre rd a r → OsFixedF c b own cur tabs xs K a → C f a r) ∧
    ∀ f a r, osKindOf f = none → C f a r

/-! ## The special calls' values -/

/-- **The special calls' values** under `σ'`, the buffers at `b`: each level's first decoder, its
squeeze loop, its `opening_queries`, each non-final level's residual loop. -/
def OsSpecVals (c : OsCfg) (b : ℕ) (tabs : E) (word : ℕ → ℕ → E) (lamInv batched mu : ℕ → E)
    (σ' : Val) : Prop :=
  (∀ l < c.levels.length,
    (osDecCall c l).2.2.1.map σ' = [word l 0, osPtrF c b 11 * gen ^ (osLvAt c l).posOff,
      osPtrF c b osIxQbp * gen ^ (osLvAt c l).posOff, tabs] ∧
    (osSqCall c l).1.map σ' = some (gen + gen ^ (osLvAt c l).squeezes) ∧
    (osSqCall c l).2.2.1.map σ' = [gen, gen ^ (osLvAt c l).squeezes, osPtrF c b (osIxSqz c l),
      osPtrF c b 11, osPtrF c b osIxQbp, tabs] ∧
    (osQCall c l).2.2.1.map σ' = [osPtrF c b 0 * gen ^ (4 * (osLvAt c l).capOff),
      osPtrF c b 1 * gen ^ (osLvAt c l).capOff, lamInv l,
      osPtrF c b 5 * gen ^ (2 * (osLvAt c l).foldsOff), osHsPtr c b l,
      osPtrF c b 11 * gen ^ (osLvAt c l).posOff, osPtrF c b osIxQbp * gen ^ (osLvAt c l).posOff,
      gen ^ oqN c l] ∧
    (osQCall c l).2.2.2.map σ' = [batched l]) ∧
  ∀ l < c.yrLevel,
    (osResCall c l).1.map σ' = some (1 + gen ^ ((osLvAt c l).queries / resBatch)) ∧
    (osResCall c l).2.2.1.map σ' = [1, gen ^ ((osLvAt c l).queries / resBatch), osPtrF c b 11,
      osPtrF c b (osIxBD c), osPtrF c b 8, osPtrF c b (osIxRC c l), mu l]

/-- **What the body returns and allocates** under `σ'`, the buffers at `b`. -/
def OsOutF (c : OsCfg) (b : ℕ) (tabs tgt inn res : E) (word : ℕ → ℕ → E) (lamInv batched mu : ℕ → E)
    (σ' : Val) : Prop :=
  (osBodyRet c).map σ' = [tgt, osPtrF c b (osIxPT c), osPtrF c b (osIxPT1 c), inn, res] ∧
  ((osBodyA c).filterMap Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ' s)) = osSizesF c ∧
  (((osBodyA c).filterMap Stmt.allocSz).map Prod.fst).map σ' =
    (bases b (osSizesF c)).map (fun e ↦ ofK (addressOfIndex e)) ∧
  OsSpecVals c b tabs word lamInv batched mu σ'

/-! ## The honest data -/

/-- **The body's completeness at honest values**, as the placed lift takes it. -/
structure OsHonest (c : OsCfg) (args : List E) (cur tabs : E) (xs : List E) (tgt inn res : E)
    (pt pt1 : List E) where
  own : List (List E)
  own_len : List.Forall₂ (fun w s ↦ w.length = s) own (osSizesF c)
  own_pt : own.getD (osIxPT c) [] = pt
  own_pt1 : own.getD (osIxPT1 c) [] = pt1
  word : ℕ → ℕ → E
  cap : ℕ → ℕ → List E
  cap_len : ∀ l j, (cap l j).length = 5
  cap_word : ∀ l j, 1 ≤ j → (⟨cap l j, []⟩ : Fs).squeeze.1 = word l j
  lamInv : ℕ → E
  rounds : ℕ → List FoldRound
  hsv : ℕ → List E
  qs : ℕ → ℕ → ℕ
  rows : ℕ → ℕ → List K
  sibs : ℕ → ℕ → List Digest
  batched : ℕ → E
  mu : ℕ → E
  rounds_len : ∀ l < c.levels.length, (rounds l).length = (oqS c l).folds
  hsv_len : ∀ l < c.levels.length, (oqS c l).final = 1 → (hsv l).length = (oqS c l).nHs
  static : ∀ l < c.levels.length,
    OqStatic (oqS c l) (rounds l) (hsv l) (qs l) (rows l) (sibs l) (oqQ c l)
  qs_eq : ∀ l < c.levels.length, ∀ k < oqQ c l,
    qs l k = qwPosOf (osLvAt c l).depth (word l (k / sqPer (osLvAt c l))) (k % sqPer (osLvAt c l))
  batched_eq : ∀ l < c.levels.length, batched l = if (oqS c l).final = 1 then 0 else
    oqChain (oqOdd c l) (oqS c l).base (lamInv l)
      (fun k ↦ foldRow (lanesOf (oqS c l).base (rows l k)) (K.ofBits (qs l k)) (rounds l)) (oqN c l)
  rowsMem : ∀ b rd, OsMemF rd c b own → ∀ l < c.levels.length, ∀ j, 1 ≤ j →
    j < (osLvAt c l).squeezes →
    (∀ i < 5, LoadHolds rd (osPtrF c b (osIxSqz c l) * (gen ^ j) ^ 5) i ((cap l j).getD i 0)) ∧
    ∀ i < 5, LoadHolds rd (osPtrF c b (osIxSqz c l) * (gen ^ j) ^ 5) (5 + i)
      (((⟨cap l j, []⟩ : Fs).squeeze.2.cap).getD i 0)
  posMem : ∀ b rd, OsMemF rd c b own → ∀ l < c.levels.length, ∀ j < (osLvAt c l).squeezes,
    ∀ i < sqPer (osLvAt c l),
      LoadHolds rd (osPtrF c b 11 * gen ^ (osLvAt c l).posOff * (gen ^ j) ^ sqPer (osLvAt c l)) i
        (eOfNat (qwPosOf (osLvAt c l).depth (word l j) i))
  qMem : ∀ b rd, OsMemF rd c b own → ∀ l < c.levels.length,
    RoundsAt rd (osPtrF c b 5 * gen ^ (2 * (osLvAt c l).foldsOff)) (rounds l) ∧
    ((oqS c l).final = 1 → WordsAt rd (osHsPtr c b l) (hsv l)) ∧
    ∀ k < oqQ c l,
      LoadHolds rd (osPtrF c b 0 * gen ^ (4 * (osLvAt c l).capOff))
        (2 * (2 ^ (oqS c l).cd + qs l k / 2 ^ (oqS c l).pd))
        (digestHalves (climbD (merkleLeafDigest (rows l k)) (qs l k) (sibs l k))).1 ∧
      LoadHolds rd (osPtrF c b 0 * gen ^ (4 * (osLvAt c l).capOff))
        (2 * (2 ^ (oqS c l).cd + qs l k / 2 ^ (oqS c l).pd) + 1)
        (digestHalves (climbD (merkleLeafDigest (rows l k)) (qs l k) (sibs l k))).2 ∧
      LoadHolds rd (osPtrF c b 1 * gen ^ (osLvAt c l).capOff)
        (2 ^ ((oqS c l).cd - 1) + qs l k / 2 ^ ((oqS c l).pd + 1)) 1
  resRel : ∀ b rd, OsMemF rd c b own → ∀ l < c.yrLevel,
    coreProgram.Rel rd (c.resLoop l) [1, gen ^ ((osLvAt c l).queries / resBatch), osPtrF c b 11,
      osPtrF c b (osIxBD c), osPtrF c b 8, osPtrF c b (osIxRC c l), mu l] []
  body : ∀ b, ∃ (kEnd : ℕ) (f : ℕ → E), ∀ (C : CallRel) (rd : Reader),
    OsH C rd c b own cur tabs xs →
      BlkF C rd (Val.ofArgs args) 10 kEnd f (osBodyA c)
        (OsOutF c b tabs tgt inn res word lamInv batched mu)

end
end LeanVM.Guest.B1
