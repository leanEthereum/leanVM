/-
  LeanVM.Guest.B1.Place.OsHonestSpec

  The honest data the placed lift of f128's `open_stacked` takes, at every accepting run.
-/

module

public import LeanVM.Guest.B1.Place.OsHonest
public import LeanVM.Guest.B1.Place.OsSpec

/-!
# The honest data of every run

`OsHonestSpec`: every accepting run of `whirOpen μ r target` from `⟨capOf S, []⟩` with no zero
challenge, no combiner vanishing at a queried point and openings agreeing in the caps has the
honest data `OsHonest` at its candidate, the arguments `capOf S ++ [target, root's cells, cur,
tabs]`, returning the run's claim, glued weight and residual, the point buffers the run's point
zero-padded and one plus it one-padded. The body's completeness (`Whir/C*`) proves it;
`Place/OsCandAll` turns it into OsSpec's statements.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The honest data of every accepting run** at its candidate. -/
def OsHonestSpec : Prop :=
  ∀ (μ r : ℕ), 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (S : KeccakState) (root : Digest) (target cur tabs : E) (xs : List E)
      (os : List (List Opening)) (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
      NoZeroChallenge μ r target S xs os root → NoZeroCombiner μ r target S xs os root →
      CapsAgree μ r target S xs os root →
      Nonempty (OsHonest (osCfg (candidate μ r))
        (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs]) cur tabs xs
        w.target w.inner w.residual (w.point ++ List.replicate (pointCap - μ) 0)
        (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1))

end
end LeanVM.Guest.B1
