module

public import LeanVM.Cost.Extractor.Top
public import LeanVM.Guest.Fast.DiscreteLog

/-!
# The guest decoder's compiled chain: the exponent of a power of `g`

The guest decoder's readers read counts and positions as exponents (`B1.Main.gLog`: the `i < 2^34`
with `g^i` the word's low limb, `0` otherwise). Compiled here through a discrete logarithm
(`gLog_discreteLog`: `Located.gLogWith Extraction.Fast.discreteLog`, Pohlig–Hellman over the
factors of `2^64 − 1`, `Guest/Fast/DiscreteLog.lean`'s `gLog_eq_discreteLog`). This module is the
decoder chain's one point of contact with the logarithm.

Every module of the chain imports `LeanVM.Cost.Extractor.Top` first, through this one: the
compiler allocates function indices from its imports, so the decoder's functions follow the
extractor's and share its compiled library.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.B1 LeanVM.Guest.B1.Main

@[expose] public section

/-- `gLog` through the discrete logarithm. -/
theorem gLog_discreteLog (x : E) :
    gLog x = LeanVM.Guest.Located.gLogWith LeanVM.Extraction.Fast.discreteLog x :=
  congrFun LeanVM.Guest.Fast.gLog_eq_discreteLog x

cost_rewrite gLog_discreteLog

/-! ## The logarithm, its tables given

`discreteLog x` builds its baby-step tables (`discreteLogTables`, about `7.8·10^7` on the cost
machine) at every call. The chain's functions take them built, `D`, from the decoder's top level,
and read an exponent by `gLogD D` (`gLogD_tables`: at `D = discreteLogTables` it is `gLog`), the
logarithm passed as a value to `gLogAt`. (`cost_rewrite gLog_discreteLog` stays for a `gLog` not
yet given its tables: it prices the tables at every call.) -/

open LeanVM.Extraction.Fast in
/-- The exponent below `2^34` of a logarithm `o`, `0` if none (`Located.gLogWith`). -/
def gLogAt (o : Option ℕ) : ℕ :=
  match o with
  | some n => if n < 2 ^ 34 then n else 0
  | none => 0

open LeanVM.Extraction.Fast in
/-- **`gLog`, the logarithm's tables `D` given.** -/
def gLogD (D : DiscreteLogTables) (x : E) : ℕ := gLogAt (discreteLogWith D (x.limb 0))

open LeanVM.Extraction.Fast in
/-- At the tables built, `gLogD` is `gLog`. -/
theorem gLogD_tables : gLogD discreteLogTables = gLog := by
  funext x
  rw [gLog_discreteLog]
  rfl

cost_compile gLogAtC := gLogAt
-- the logarithm at the tables, under a name of its own (the bounds name it, not an index)
/-! The discrete logarithm's parts, each under a name of its own (stable across the chain's
reallocations of on-demand indices). -/
open LeanVM.Extraction.Fast in
cost_compile giantStepsC measure fun _ _ _ n _ _ ↦ n := giantSteps
open LeanVM.Extraction.Fast in
cost_compile phResidueC := phResidue
open LeanVM.Extraction.Fast in
cost_compile crtCombineC := crtCombine
open LeanVM.Extraction.Fast in
cost_compile phCandidateC := phCandidate
open LeanVM.Extraction.Fast in
cost_compile logCheckC := logCheck
open LeanVM.Extraction.Fast in
cost_compile discreteLogWithC := discreteLogWith
cost_compile gLogDC := gLogD


end

end LeanVM.Cost.Decoder
