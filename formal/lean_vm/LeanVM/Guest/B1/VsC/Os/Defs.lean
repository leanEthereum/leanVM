/-
  LeanVM.Guest.B1.VsC.Os.Defs

  The definitions the honest data of `open_stacked` takes from the bus era's placed lift.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Whir.IsZeroDef
public import LeanVM.Guest.B1.Fs.Message
public import LeanVM.Guest.B1.Fs.TailRoundP
public import LeanVM.Guest.B1.Merkle.Meaning
public import LeanVM.Guest.B1.Eq.MeaningP
public import LeanVM.Guest.B1.VsC.Oq.PlacedL

/-!
# The honest data's definitions

Restored from `formal-bus-archive`'s `Place/OsMean.lean`, `Place/OsBos.lean`,
`Lift/OsCallees.lean` and `Opening/QueriesPlacedD1.lean`, without the bus era's placement (its
allocator is not Hotwire's):

* `OsKind`, `OsKind.Pre`, `OsKind.spec`, `osKindOf`: `open_stacked`'s named callees, their meanings
  and the words they load. The table is read off the deployed specializations (`omDeployed`,
  `spfDeployed`, `merkleCapNames`, `foldFinalMsgNames`), not listed by hand: the archive's list
  missed Hotwire's `opening_message__L1_L1` and `squeeze_point_from__L25 .. L30`.
* `osPosTotal`, `osSizesL`: the body's `HeapBuf`s' sizes, in allocation order.
* `oqW`, `OqStatic`: a level's `opening_queries` witnesses and their static facts.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The named callees -/

/-- `opening_message__L{n}_L{nonce}`'s loads: `n + nonce` words at the cursor (argument 5), `n` at
its output (argument 6). -/
def msgSpec (n nonce : ℕ) : List (ℕ × ℕ) := [(5, n + nonce), (6, n)]

/-- `squeeze_point_from__L{n}`'s: the `n` words at its point (argument 6). -/
def spfSpec (n : ℕ) : List (ℕ × ℕ) := [(6, n)]

/-- `opening_tail_round`'s: the two words at the cursor (argument 5). -/
def tailSpec : List (ℕ × ℕ) := [(5, 2)]

/-- `verify_merkle_cap__L{D}`'s: the cap and the flags. -/
def merkleCapSpec (D : ℕ) : List (ℕ × ℕ) := [(0, 2 ^ (D + 2)), (1, 2 ^ D)]

/-- `fold_final_msg__L{n}`'s: the message and the point. -/
def foldFinalSpec (n : ℕ) : List (ℕ × ℕ) := [(0, 2 ^ n), (1, n)]

/-- The kinds of `open_stacked`'s named callees. -/
inductive OsKind where
  | tail
  | msg (n nonce : ℕ)
  | spf (n : ℕ)
  | cap (d : ℕ)
  | ffm (n : ℕ)
  | iz
  deriving DecidableEq

/-- A kind's meaning. -/
def OsKind.Pre : OsKind → Reader → List E → List E → Prop
  | .tail => MeaningOpeningTailRound
  | .msg n nonce => MeaningOpeningMessage n nonce
  | .spf n => MeaningSqueezePointFrom n
  | .cap d => MeaningVerifyMerkleCap d
  | .ffm n => MeaningFoldFinalMsg n
  | .iz => fun _ ↦ MeaningIsZero

/-- A kind's loads. -/
def OsKind.spec : OsKind → List (ℕ × ℕ)
  | .tail => tailSpec
  | .msg n nonce => msgSpec n nonce
  | .spf n => spfSpec n
  | .cap d => merkleCapSpec d
  | .ffm n => foldFinalSpec n
  | .iz => []

/-- The named callees and their kinds. -/
def osKindTable : List (String × OsKind) :=
  [("is_zero", .iz), ("opening_tail_round", .tail)] ++
  omDeployed.map (fun p ↦ (omName p, .msg p.1 p.2)) ++
  spfDeployed.map (fun n ↦ (spfName n, .spf n)) ++
  merkleCapNames.map (fun p ↦ (p.1, .cap p.2)) ++
  foldFinalMsgNames.map (fun p ↦ (p.1, .ffm p.2))

/-- The kind a name names. -/
def osKindOf (f : String) : Option OsKind := osKindTable.lookup f

theorem os_mem_of_lookup {f : String} {K : OsKind} :
    ∀ (l : List (String × OsKind)), l.lookup f = some K → (f, K) ∈ l
  | [], h => by simp [List.lookup] at h
  | (a, b) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq] at h
      subst h
      have : f = a := by simpa using hb
      subst this
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (os_mem_of_lookup l h)

/-- An entry names a deployed specialization of its kind. -/
def osKindEntryOk : String × OsKind → Bool
  | (f, .tail) => f == "opening_tail_round"
  | (f, .msg n nonce) => decide ((n, nonce) ∈ omDeployed) && f == omName (n, nonce)
  | (f, .spf n) => decide (n ∈ spfDeployed) && f == spfName n
  | (f, .cap d) => decide ((f, d) ∈ merkleCapNames)
  | (f, .ffm n) => decide ((f, n) ∈ foldFinalMsgNames)
  | (f, .iz) => f == "is_zero"

set_option maxRecDepth 100000 in
theorem osKindTable_ok : osKindTable.all osKindEntryOk = true := by decide +kernel

theorem osKindOf_isZero : osKindOf "is_zero" = some .iz := by decide +kernel

theorem osKindEntry_ok {f : String} {K : OsKind} (hK : osKindOf f = some K) :
    osKindEntryOk (f, K) = true :=
  List.all_eq_true.mp osKindTable_ok _ (os_mem_of_lookup osKindTable hK)

/-! ## The buffers -/

/-- The query positions of every level at the levels' rate (`LIG_POS_TOTAL`): each level's squeezes
times the positions a squeezed word carries. -/
def osPosTotal (c : OsCfg) : ℕ := (c.levels.map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum

/-- **`open_stacked`'s heap buffers' sizes**, in allocation order (`Whir.osHead`, `osLevel`,
`osTail`, `osFinish`): the head's twelve (`final_msg`, `level_roots`, `fold_challenges`,
`round_coefs`, `level_scales`, `level_lam_invs`, `level_hs`, `ood_z`, `ood_scalars`, `pos_totals`,
`query_positions`, `query_win_ptrs`); each non-final level's message `sent`; the final level's
normalized lane `hs`; `tail_challenges`, `point`, `point1`, `basis_d`, `level_scale`, `level_after`,
`inner_chain`. -/
def osSizesL (c : OsCfg) : List ℕ :=
  let n := c.levels.length
  let lane := c.yrLen + (c.levels.getD c.yrLevel default).folds
  [lane, 2 * n, c.nFolds, 2 * c.nFolds, n, n, n * hsStride, n * ligColsCap, n, ligNRates,
    osPosTotal c, osPosTotal c] ++
  ((c.levels.take c.yrLevel).map fun lv ↦ 2 + lv.folds) ++
  [lane, yrLogCap, pointCap, pointCap, n * ligColsCap, n, n, 2 * n]

theorem osLvR_eq_getD {m r l : ℕ} (h : l < osNLevels m) :
    osLvR m r l = (osCfgR m r).levels.getD l default := by
  simp [osCfgR, osLevelsR, List.getD_eq_getElem?_getD, h]

/-- `osCfgR m r` has `osNLevels m` levels. -/
theorem osCfgR_levels_length (m r : ℕ) : (osCfgR m r).levels.length = osNLevels m := by
  simp [osCfgR, osLevelsR]

/-! ## A level's queries -/

/-- A query's witness from the call's data: its position, its row, its siblings below the cap. -/
def oqW (qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest) (k : ℕ) : QW :=
  (qs k, rows k, sibs k)

/-- **The opening's static facts** of the queries `k < Q`: the position below `2^(pd + cd)`, the
row's and the siblings' lengths, and (final level) the fold the final polynomial at the point. -/
def OqStatic (s : Oq) (cd : ℕ) (rounds : List FoldRound) (hsv : List E) (qs : ℕ → ℕ)
    (rows : ℕ → List K) (sibs : ℕ → List Digest) (Q : ℕ) : Prop :=
  ∀ k < Q, qs k < 2 ^ (s.pd + cd) ∧ (rows k).length = rowLen s.base s.folds ∧
    (sibs k).length = s.pd ∧
    (s.final = 1 → foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds =
      novelSum hsv (wsChain (s.vs.map K.ofBits) (eOfNat (qs k))) s.nHs s.hsBits)

end
end LeanVM.Guest.B1
