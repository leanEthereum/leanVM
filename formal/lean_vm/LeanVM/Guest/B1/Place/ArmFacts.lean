/-
  LeanVM.Guest.B1.Place.ArmFacts

  open_stacked's per-arm, per-rate decided facts the placed lift uses: the statement.
-/

module

public import LeanVM.Guest.B1.Place.OsCallsOk
public import LeanVM.Guest.B1.Place.OsCalls
public import LeanVM.Guest.B1.Place.Lp
public import LeanVM.Guest.B1.Place.Lq
public import LeanVM.Guest.B1.Place.Lr
public import LeanVM.Guest.B1.Whir.Facts
public import LeanVM.Guest.B1.Whir.Interface

/-!
# The arms' decided facts

`OsArmFacts m ri`, of the arm `m` (stack log `m + minOpenLog`) at the rate `ri`, its levels
`osCfgR m ri`:

* `fn`: the arm's function is `osBody (osCfg m)` on ten parameters, not a loop;
* `names`: `OsNames (osCfgR m ri) ri` (the named callees' kinds, the helpers outside the table, the
  rate's rows);
* `sizes`, `pos`, `tot`: `OsSizes`, the buffers' sizes positive, their total below `2^64 - 1`;
* `allocs`: the body has no `frameAddr` (its `HeapBuf`s' sizes are values, `OsCallVals.sizes`);
* `disp`: its dispatches name fewer than `2^64 - 1` callees (`DispShort`);
* `lp`, `lq`, `lr`: each level's helper names are table entries at the level's shape;
* `lpNodup`: `lpTable`'s names are distinct (the decoders' frame pointers are chosen by name).

`os_arm_facts_Spec`: every arm below `osArms` at every rate below `4`. With `candB_sound`
(`Whir/Facts.lean`, `CandFacts`), what the lift decides per arm.

**Design note for the proof.** Everything is decidable on the generated data: write a `Bool` check
per arm and rate (as `candB`, `Whir/Facts.lean`) and its soundness, then `decide +kernel` (or
`by decide` per arm) over `m < osArms`, `ri < 4`; after the data is regenerated (12 arms) only the
check is re-run. `fn` is `Whir/Data*.lean`'s check of the core IR against `osBody`
(`osBody_rate` moves it to any rate). If a field is false for some arm (for instance a
`grind_check` or `opening_row_weights` specialization outside `osKindTable`), report it: the kind
table (`Place/OsMean.lean`) then grows.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The arm `m`'s decided facts at the rate `ri`.** -/
structure OsArmFacts (m ri : ℕ) : Prop where
  fn : ∃ fn : Fn, coreProgram.find? (openName (m + minOpenLog)) = some fn ∧ fn.params = osParams 10 ∧
    fn.body = osBody (osCfg m) ∧ coreProgram.loop (openName (m + minOpenLog)) = false
  names : OsNames (osCfgR m ri) ri
  sizes : OsSizes (osCfgR m ri)
  pos : ∀ x ∈ osSizesL (osCfgR m ri), 0 < x
  tot : (osSizesL (osCfgR m ri)).sum < 2 ^ 64 - 1
  allocs : (osBodyAc (osCfgR m ri)).filterMap Main.Stmt.addrS = []
  disp : DispShort (osBodyAc (osCfgR m ri))
  lp : ∀ i < (osCfgR m ri).levels.length, ∃ loop : String,
    (osPositionsName (lvAt (osCfgR m ri) i), (lvAt (osCfgR m ri) i).squeezes, loop,
      (lvAt (osCfgR m ri) i).depth, (lvAt (osCfgR m ri) i).capDepth) ∈ lpTable
  lq : ∀ i < (osCfgR m ri).levels.length,
    (osQueriesName i (lvAt (osCfgR m ri) i), (lvAt (osCfgR m ri) i).queries,
      (if i = 0 then 1 else 0), (lvAt (osCfgR m ri) i).interleave,
      (lvAt (osCfgR m ri) i).leafCells, (lvAt (osCfgR m ri) i).depth,
      (lvAt (osCfgR m ri) i).capDepth) ∈ lqTable
  lr : ∀ i < (osCfgR m ri).levels.length, ∃ l1 l2 : String,
    (osResidualName (lvAt (osCfgR m ri) i), (lvAt (osCfgR m ri) i).queries,
      (lvAt (osCfgR m ri) i).logCols, l1, l2) ∈ lrTable
  lpNodup : (lpTable.map (·.1)).Nodup

/-- **Every arm's decided facts, at every rate.** -/
def os_arm_facts_Spec : Prop := ∀ m < osArms, ∀ ri < 4, OsArmFacts m ri

end
end LeanVM.Guest.B1
