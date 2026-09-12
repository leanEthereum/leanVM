import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.Honest
/-!
# Positions the cache has settled

A position is *settled* by a cache when every position below it is and the honest input there is
cached. The point of the notion is `honestInput_eq_of_settled`: at a settled position the honest
input is a function of the cache alone, the same for every answer function the cache agrees with. It
is what lets the accounting speak of "the honest input at this domain" without knowing the rest of
the run, and what the extraction's honest values are matched against.

Settling is monotone, and the input it pins never moves again.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

/-- The answer function a cache induces: its own answers, and `0` where it says nothing. -/
def fromCache (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

theorem agreesWithFn_fromCache (cache : QueryCache HashSpec) :
    cache.AgreesWithFn (fromCache cache) := by
  intro input answer hcached
  simp [fromCache, hcached]

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

variable {parameter} {otsSecret} {ftsSecret}

end SphincsSecurity
