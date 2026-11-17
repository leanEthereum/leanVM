module

public import Quantum.StdModel.Props

@[expose] public section

/-!
# SM-TCR-C and EncTCR+C with target tweaks restricted to a set

The games `Props.smTcr` and `Props.encTcrCtr` accept a target at any tweak. When a collection's
inputs at some tweaks do not depend on the tweak (leanSPHINCS's `tcrColl` and `encCtr` at tweaks
of another kind or out of range hash `PK.seed` and the message bytes only), targets at such tweaks
share their inputs across tweaks, and the games are broken generically: `v` targets at such tweaks
give a multi-target second-preimage search (success about `v q² / 2^128` with `q` quantum calls),
and two targets with colliding digests already win with no quantum call (about `v² / 2^128`).

The restricted games `smTcrIn` and `encTcrCtrIn` are the same experiments whose judge also
requires every target to be at a tweak of the set `G` (`TcrIn`, `EncIn`), the tweaks where the
inputs determine the tweak.
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Props

variable (W : OracleWorld)

section Tcr

variable {Par Tw Fn Out EFn EOut : Type} {Msg : Fn → Type} {EMsg : EFn → Type}

/-- Every target of the transcript is at a tweak of `G` for its function. -/
def TcrIn (G : Fn → Tw → Prop) (log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) :
    Prop :=
  ∀ e ∈ tcrTargets log, G e.1.1 e.1.2.1

/-- **SM-TCR-C with target tweaks in `G`**: `smTcr`, the judge also requiring every target at a
tweak of `G`. -/
noncomputable def smTcrIn [SampleableType Par] (C : TwColl Par Tw Fn Msg Out)
    (D : TwColl Par Tw EFn EMsg EOut) (G : Fn → Tw → Prop) :
    Experiment W (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) Unit (Σ l, Tw × Msg l) :=
  { smTcr W C D with
    judge := fun P log out ↦ do
      let b ← (smTcr W C D).judge P log out
      pure (holds (TcrIn G log) && b) }

/-- **Restricted SM-TCR-C success probability** at the table `tab`. -/
noncomputable abbrev smTcrInSucc [SampleableType Par] (C : TwColl Par Tw Fn Msg Out)
    (D : TwColl Par Tw EFn EMsg EOut) (G : Fn → Tw → Prop) (tab : W.Tab)
    (A : Adversary W (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) Unit (Σ l, Tw × Msg l)) :
    ENNReal :=
  (smTcrIn W C D G).succAt tab A

end Tcr

section Enc

variable {Par Tw Msg Dig Fn Out : Type} {CMsg : Fn → Type}

/-- Every target of the transcript is at a tweak of `G`. -/
def EncIn (G : Tw → Prop) (log : QueryLog (CtrSpec Par Tw Msg Dig Fn CMsg Out)) : Prop :=
  ∀ e ∈ ctrTargets log, G e.1.1

/-- **EncTCR+C with target tweaks in `G`**: `encTcrCtr`, the judge also requiring every target at
a tweak of `G`. -/
noncomputable def encTcrCtrIn [SampleableType Par] (e : CtrEnc Par Tw Msg Dig)
    (C : TwColl Par Tw Fn CMsg Out) (G : Tw → Prop) :
    Experiment W (CtrSpec Par Tw Msg Dig Fn CMsg Out) Unit (Tw × Msg × ℕ) :=
  { encTcrCtr W e C with
    judge := fun P log out ↦ do
      let b ← (encTcrCtr W e C).judge P log out
      pure (holds (EncIn G log) && b) }

/-- **Restricted EncTCR+C success probability** at the table `tab`. -/
noncomputable abbrev encTcrCtrInSucc [SampleableType Par] (e : CtrEnc Par Tw Msg Dig)
    (C : TwColl Par Tw Fn CMsg Out) (G : Tw → Prop) (tab : W.Tab)
    (A : Adversary W (CtrSpec Par Tw Msg Dig Fn CMsg Out) Unit (Tw × Msg × ℕ)) : ENNReal :=
  (encTcrCtrIn W e C G).succAt tab A

end Enc

end Quantum.StdModel.Props

end
