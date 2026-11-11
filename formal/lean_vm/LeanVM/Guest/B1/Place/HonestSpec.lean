/-
  LeanVM.Guest.B1.Place.HonestSpec

  The honest trace's facts that open_stacked's helpers' placed statements take: the statement.
-/

module

public import LeanVM.Guest.B1.Place.OsCallsOk
public import LeanVM.Guest.B1.Place.Lq
public import LeanVM.Guest.B1.Place.Lr
public import LeanVM.Guest.B1.Whir.Facts

/-!
# The helpers' honest data

The arm places its helpers by their placed statements (`Place/Lp.lean`, `Lq.lean`, `Lr.lean`) at
the honest trace `tr` of `osBodyA_honest`. Their hypotheses on the arm's own buffers (where the
words lie, what memory holds) the lift discharges from the layout; what they say of the data is
`OsHelperFacts c tr`, level by level:

* `level_positions` (`LpAtO`): the level's capacity `(tr.L i).F2.cap` is five canonical cells and
  the decoded positions in `query_positions` (`posAt`) are those of the squeeze challenges
  `sqChal cap j` (`qwPosOf`); the call returns `sqLast`, `sqCaps cap sq` by definition.
* `level_queries` (`LqAtO`): `λ ≠ 0`; the hinted cap and flags, the queried positions, rows and
  siblings (`LqCaps` at the level's root), the positions those the decoders give (query `k` is
  word `k / (192/d)`'s position `k % (192/d)`), and the level's enforced sum the queries' chain at
  the honest row weights `wpC c tr i`, times `λ^q`.
* `level_residual` (`LrAtO`): `finH c tr i` is the chain `lrAcc` over the level's positions in
  `query_positions` and its row of `basis_d`, at `μ = finM tr i`.

`os_helper_facts_Spec`: on every accepting run with no zero challenge and openings that agree in
the caps, every trace fitting the configuration and the run (`TrFit`, `TrRun`) has them.

**Design note for the proof.** Build on the trace's bridges (`Whir/Br*.lean`, `Whir/Spec*.lean`):
`BrCaps`' `capsL`, `flagsL`, `cap_meaning_at` (the cap and flags, with `CapsAgree` and
`TrRun.qs`), the level's openings `(tr.L i).qs`, `(tr.L i).os` (rows and siblings), `SpLv.enforced`;
`CPrim`'s `squeezeN_sqCaps` (the challenges); `BrCont`'s `finH`, `finD`, `qposC`, `bdC` and
`CLr`'s `lrAcc` (`resFoldC` is the soundness side's `resFold`); the old `Place/OsKidsSp1..5` did
this for the old callees (`opening_queries` directly, the residual loop).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- The base of level `i`'s queries: `1` at level `0`. -/
def lvBase (i : ℕ) : ℕ := if i = 0 then 1 else 0

/-- **Level `i`'s honest data the helpers' statements take.** -/
structure LvHelperFacts (c : OsCfg) (tr : OsTr) (i : ℕ) : Prop where
  cap5 : (tr.L i).F2.cap.length = 5
  capCan : AllCanonical (tr.L i).F2.cap
  pos : ∀ j < (lvAt c i).squeezes, ∀ t < 192 / (lvAt c i).depth,
    posAt c tr i (j * (192 / (lvAt c i).depth) + t) =
      eOfNat (qwPosOf (lvAt c i).depth (sqChal (tr.L i).F2.cap j) t)
  lam : (tr.L i).lam ≠ 0
  queries : ∃ (capW flW : List E) (qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest),
    LqCaps (lqShape (lvBase i) (lvAt c i).interleave (lvAt c i).depth (lvAt c i).capDepth)
      (lvAt c i).queries capW flW (digestHalves (tr.L i).root).1 (digestHalves (tr.L i).root).2
      qs rows sibs ∧
    (∀ k < (lvAt c i).queries, qs k = qwPosOf (lvAt c i).depth
      (sqChal (tr.L i).F2.cap (k / (192 / (lvAt c i).depth))) (k % (192 / (lvAt c i).depth))) ∧
    (tr.L i).enforced = oqChain ((lvAt c i).queries % 2 * lvBase i) (lvBase i) (tr.L i).lam⁻¹
      (fun k ↦ rowDot (lvBase i) (lvAt c i).interleave (rows k) fun l ↦ (wpC c tr i).getD l 0)
      (lqIters (lvAt c i).queries (lvBase i)) * (tr.L i).lam ^ (lvAt c i).queries
  res : finH c tr i = lrAcc (fun s ↦ (bdC c tr).getD (i * ligColsCap + s) 0) (lvAt c i).logCols
    (finM tr i) (fun k ↦ (qposC c tr).getD ((lvAt c i).posOff + k) 0) (lvAt c i).queries

/-- The honest data of every level. -/
def OsHelperFacts (c : OsCfg) (tr : OsTr) : Prop := ∀ i < c.levels.length, LvHelperFacts c tr i

/-- **The honest trace has the helpers' data**, at every arm and rate. -/
def os_helper_facts_Spec : Prop :=
  ∀ m < osArms, ∀ ri < 4, ∀ cfg : List Whir.Level,
    CandFacts (osCfgR m ri) (m + minOpenLog) (ri + 1) cfg →
    ∀ (S : KeccakState) (root : Digest) (target : E) (xs : List E) (os : List (List Opening))
      (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      RunsWith (whirOpen (m + minOpenLog) (ri + 1) target) ⟨capOf S, []⟩ xs os
        [(root, stackShape (m + minOpenLog) (ri + 1))] w s' roots' →
      NoZeroChallenge (m + minOpenLog) (ri + 1) target S xs os root →
      CapsAgree (m + minOpenLog) (ri + 1) target S xs os root →
      ∀ tr : OsTr, TrFit (osCfgR m ri) tr →
        TrRun (osCfgR m ri) (m + minOpenLog) (ri + 1) target S xs os root tr →
        OsHelperFacts (osCfgR m ri) tr

end
end LeanVM.Guest.B1
