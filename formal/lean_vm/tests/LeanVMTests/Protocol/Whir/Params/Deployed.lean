/-
  LeanVMTests.Protocol.Whir.Params.Deployed

  Controls for the deployed WHIR parameters' check: level 0's list bound and threshold, the
  query rows are tight, and the interface is filled.
-/

import LeanVM.Protocol.Whir.Params.Iface

/-!
# Deployed WHIR parameter controls

* **Level 0.** The largest list bound is `166`, at `(19, 4)`; the extractor's threshold at
  `(15, 1)` is level 0's `A₀ = 744 − 6 = 738`.
* **Queries.** Level 0 of `(15, 1)` passes its checks, and with one query fewer, as at `(28, 4)`,
  its query row fails: the Rust's query counts are the smallest that pass.
* **Use.** `openingIface` fills the soundness assembly's interface.
-/

namespace LeanVMTests.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Whir.Params

#guard listMax₀ 19 4 = 166
#guard (List.range 14).all fun i ↦ (List.range 4).all fun r ↦ listMax₀ (15 + i) (r + 1) ≤ 166
#guard LeanVM.Extraction.johnsonThreshold 15 1 = 738
#guard thr0Of 15 1 = 738

/-- Level 0's checks with one query fewer. -/
def dropOne (μ R : ℕ) : Bool :=
  match Whir.ladder μ R, levelsOf μ R with
  | some (c :: _), lv :: _ => levelChecks μ lv { c with queries := c.queries - 1 }
  | _, _ => true

#guard !dropOne 15 1
#guard !dropOne 28 4

#guard match Whir.ladder 15 1, levelsOf 15 1 with
  | some (c :: _), lv :: _ => levelChecks 15 lv c
  | _, _ => false

noncomputable example : LeanVM.Protocol.EndToEnd.Sound.OpeningIface := openingIface

end LeanVMTests.Protocol.Whir.Params
