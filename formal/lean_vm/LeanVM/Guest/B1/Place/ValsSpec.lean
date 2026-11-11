/-
  LeanVM.Guest.B1.Place.ValsSpec

  The honest valuation of open_stacked's body at the values its placed lift reads: the statement.
-/

module

public import LeanVM.Guest.B1.Place.OsCallsOk
public import LeanVM.Guest.B1.Place.OsCalls
public import LeanVM.Guest.B1.Whir.CVal

/-!
# The body's values the lift reads

The arm's honest valuation `osSigma c tr σ0 c0 c2 b0` is the caller's `σ0` below `10` and the
body's values `osBodyF c tr σ0 c0 c2 (osAtOf c b0)` from `10` to the body's end (what
`osBodyA_honest`'s `BlkF` makes hold). The placed lift (`os_completeAt_placeJF`, the kids lemma)
reads, of it, only pointers:

* `sizes`, `bufs`: the `HeapBuf` hints' sizes are `osSizesL c` (all but the point buffers are
  dynamic, `osHeapA k`, of the values `g^n`) and their pointers the bump allocator's, the buffers
  from `b0` (`bases`);
* `lp`: level `i`'s `level_positions` call's positions pointer (argument `5`) is
  `query_positions·g^posOff`, so that the call is level `i`'s (`osSp` gives some level's);
* `lq`: level `i`'s `level_queries` call's row weights (argument `2`) are level `i`'s buffer.

`OsCallVals c tr σ0 c0 c2 b0`: those three; `os_call_vals_Spec`: at every arm and rate, every
trace, caller valuation, coefficients and base.

**Design note for the proof.** Build on the body's value function: `osBodyF` (`Whir/BrBody.lean`)
is `bodyF`, a sequence of segments (`seqF`, `lvsF`, the levels' `posSegs`, `osQueries`' heap and
materializations); `fill_in` (`Whir/CVal.lean`) reads it. The old `Whir/CVals.lean` and
`Place/OsVals*.lean`, `Place/OsAllocs.lean` (the squeeze loop's template, deleted in 45c43698d) walked
the same segments for the old body: `lvsF_bufs`, `osVal_*`. The positions pointer is the
materialization `osMatP` of `osQpos` at `posOff` (`posSegs`' first segment, or an earlier
materialization `MatsOk` names); the row weights are `osQueries`' `osHeap c.maxIl k`, value `k + 1`.
Nothing here depends on the trace's data, only on `c` and `b0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **The arm's honest valuation**: the caller's below `10`, the body's values above. -/
noncomputable def osSigma (c : OsCfg) (tr : OsTr) (σ0 : Val) (c0 c2 : E) (b0 : ℕ) : Val :=
  fill σ0 10 (osFinEnd c (osTlSt c).2.1 (osTlSt c).2.2) (osBodyF c tr σ0 c0 c2 (osAtOf c b0))

/-- **The values the placed lift reads**, of the honest valuation. -/
structure OsCallVals (c : OsCfg) (tr : OsTr) (σ0 : Val) (c0 c2 : E) (b0 : ℕ) : Prop where
  sizes : ((osBodyAc c).filterMap Main.Stmt.allocSz).map
    (fun x ↦ x.2.elim id fun s ↦ logG (osSigma c tr σ0 c0 c2 b0 s)) = osSizesL c
  bufs : (((osBodyAc c).filterMap Main.Stmt.allocSz).map Prod.fst).map (osSigma c tr σ0 c0 c2 b0) =
    (bases b0 (osSizesL c)).map fun b ↦ ofK (addressOfIndex b)
  lp : ∀ i (h : i < (osLvKOf (osSigma c tr σ0 c0 c2 b0) c 0 c.levels (osHead c).2).length),
    (((osLvKOf (osSigma c tr σ0 c0 c2 b0) c 0 c.levels (osHead c).2)[i]).sq.args.map
      (osSigma c tr σ0 c0 c2 b0)).getD 5 0 = (osAtOf c b0).P.qpos * gen ^ (lvAt c i).posOff
  lq : ∀ i (h : i < (osLvKOf (osSigma c tr σ0 c0 c2 b0) c 0 c.levels (osHead c).2).length),
    ∀ c' ∈ ((osLvKOf (osSigma c tr σ0 c0 c2 b0) c 0 c.levels (osHead c).2)[i]).B,
      osKindOf c'.f = none → (c'.args.map (osSigma c tr σ0 c0 c2 b0)).getD 2 0 = (osAtOf c b0).wp i

/-- **The values hold at every arm and rate.** -/
def os_call_vals_Spec : Prop :=
  ∀ m < osArms, ∀ ri < 4, ∀ (tr : OsTr) (σ0 : Val) (c0 c2 : E) (b0 : ℕ),
    tr.Ls.length = (osCfgR m ri).levels.length → OsCallVals (osCfgR m ri) tr σ0 c0 c2 b0

end
end LeanVM.Guest.B1
