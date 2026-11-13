/-
  LeanVMTests.Protocol.Whir.Params.Deployed

  Controls for the deployed WHIR parameters' check: level 0's list bound and threshold, the
  query rows are tight, and the interface is filled.
-/

import LeanVM.Protocol.Whir.Params.Iface

/-!
# Deployed WHIR parameter controls

* **Level 0.** The largest list bound is `127`, first at `(18, 4)` and at most shapes from there
  on, below the extractor's bound `166`; the extractor's threshold at `(16, 1)` is level 0's
  `A₀ = 1478 − 6 = 1472`.
* **Queries.** Level 0 of `(16, 1)` passes its checks, and with one query fewer, as at `(30, 4)`,
  its query row fails: the Rust's query counts are the smallest that pass.
* **Use.** `openingIface` fills the soundness assembly's interface.
-/

namespace LeanVMTests.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Whir.Params

#guard listMax₀ 18 4 = 127
#guard (List.range 15).all fun i ↦ (List.range 4).all fun r ↦ listMax₀ (16 + i) (r + 1) ≤ 127
#guard LeanVM.Extraction.johnsonThreshold 16 1 = 1472
#guard thr0Of 16 1 = 1472

/-- Level 0's checks with one query fewer. -/
def dropOne (μ R : ℕ) : Bool :=
  match Whir.ladder μ R, levelsOf μ R with
  | some (c :: _), lv :: _ => levelChecks μ lv { c with queries := c.queries - 1 }
  | _, _ => true

#guard !dropOne 16 1
#guard !dropOne 30 4

#guard match Whir.ladder 16 1, levelsOf 16 1 with
  | some (c :: _), lv :: _ => levelChecks 16 lv c
  | _, _ => false

noncomputable example : LeanVM.Protocol.EndToEnd.Sound.OpeningIface := openingIface

end LeanVMTests.Protocol.Whir.Params
