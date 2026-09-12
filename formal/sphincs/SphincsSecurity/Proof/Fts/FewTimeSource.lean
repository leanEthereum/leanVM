import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeLoop
import SphincsSecurity.Proof.Reference.SigningTrace
import SphincsSecurity.Proof.Scheme.Secrets
/-!
# Sources of previously cached selected digests

If a selected signer digest was already cached when that signer began, the full adversary trace
locates the earlier interval that first inserted it. Key generation is not a possible source.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem sequenceFin_some {alpha : Type} {count : Nat}
    (values : Fin count → alpha) :
    sequenceFin (m := Option) (fun position => some (values position)) = some values := by
  induction count with
  | zero =>
      rw [sequenceFin]
      congr
      funext position
      exact Fin.elim0 position
  | succ count ih =>
      rw [sequenceFin, ih]
      change some (Fin.cases (values 0) (fun position => values position.succ)) = some values
      rw [Option.some.injEq]
      funext position
      cases position using Fin.cases <;> rfl

end SphincsSecurity.Concrete
