module

public import Quantum.StdModel.Props.Basic

@[expose] public section

/-!
# SM-TCR-C: single-function, multi-target, distinct-tweak target-collision resistance of a
collection (design D3)

The notion SM-DT-TCR of Bernstein, Hulsing, Kolbl, Niederhagen, Rijneveld, Schwabe (CCS 2019,
Def. 2) for a collection of tweakable hashes sharing the public parameter `P` (SM-DT-TCR-C of
Barbosa, Dupressoir, Hulsing, Meijers, Strub, ASIACRYPT 2024), with the extra phase-1 oracle at
non-target tweaks of Hulsing, Kudinov, Ronen, Yogev (SPHINCS+C, S&P 2023, Section 5.1).

The challenger samples `P` and keeps it hidden in phase 1. The adversary asks targets
`target l T M` of the target collection `C` (answered `Th_l(P, T, M)`), evaluations `eval l T M`
of the evaluation collection `D` (answered `Th'_l(P, T, M)`, at tweaks never used by a target),
and gets `P` from `reveal`. It wins with `(l, T, M')` when a target `(l, T, M)` with `M ≠ M'` has
`Th_l(P, T, M') = Th_l(P, T, M)`. The transcript must have pairwise distinct target tweaks (over
all functions of `C`), no target after the first reveal, and no evaluation at a target tweak.

The evaluation collection holds every function of the scheme sharing `P` (with `C` among them,
or the chain step `F` beside it), so that the honest structure above the targets is computable
at the hidden `P`: this is the family `Th_λ` of HKRY23 Section 5.1, the target functions being
the part that receives targets. A function without targets adds no winning event.

Differences from the published notions: the adversary also has superposition access to the
world's hash (in the standard model it can evaluate Keccak-256 itself; in the QROM this is the
random oracle); the evaluation oracle is available in both phases (after the reveal it gives
nothing new); the collision is a message inequality at a fixed function and tweak, as in BHK+19.

Instance obligation (see `Props.Basic`): the evaluation restriction compares tweaks, so no
function of `D` may produce the bytes of a target input under a tweak other than the target's.
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Props

open HashSig

/-- The classical queries of the SM-TCR-C game: targets of the functions `Fn`, evaluations of
the functions `EFn`. -/
inductive TcrQuery (Tw Fn : Type) (Msg : Fn → Type) (EFn : Type) (EMsg : EFn → Type) where
  /-- A target `(l, T, M)`, phase 1 only, at a fresh tweak. -/
  | target (l : Fn) (t : Tw) (m : Msg l)
  /-- An evaluation `Th'_l(P, T, M)` of the evaluation collection at a tweak no target uses. -/
  | eval (l : EFn) (t : Tw) (m : EMsg l)
  /-- The public parameter. -/
  | reveal

namespace TcrQuery

variable {Tw Fn EFn : Type} {Msg : Fn → Type} {EMsg : EFn → Type}

/-- The answer types: a digest for targets and evaluations, the parameter for `reveal`. -/
def Resp (Par Out EOut : Type) : TcrQuery Tw Fn Msg EFn EMsg → Type
  | .target .. => Out
  | .eval .. => EOut
  | .reveal => Par

/-- Whether a query is `reveal`. -/
def isReveal : TcrQuery Tw Fn Msg EFn EMsg → Bool
  | .reveal => true
  | _ => false

/-- Whether a query is a target. -/
def isTarget : TcrQuery Tw Fn Msg EFn EMsg → Bool
  | .target .. => true
  | _ => false

variable {Par Out EOut : Type}

/-- A transcript entry as a target: its input and the answered digest. -/
def asTarget : ((q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q) →
    Option ((Σ l, Tw × Msg l) × Out)
  | ⟨.target l t m, y⟩ => some (⟨l, t, m⟩, y)
  | _ => none

/-- A transcript entry as an evaluation: its tweak. -/
def evalTweak : ((q : TcrQuery Tw Fn Msg EFn EMsg) × Resp Par Out EOut q) → Option Tw
  | ⟨.eval _ t _, _⟩ => some t
  | _ => none

end TcrQuery

open TcrQuery

/-- The oracle specification of the SM-TCR-C ports. -/
abbrev TcrSpec (Par Tw Fn : Type) (Msg : Fn → Type) (Out EFn : Type) (EMsg : EFn → Type)
    (EOut : Type) : OracleSpec (TcrQuery Tw Fn Msg EFn EMsg) :=
  OracleSpec.ofFn (Resp Par Out EOut)

variable {Par Tw Fn Out EFn EOut : Type} {Msg : Fn → Type} {EMsg : EFn → Type}

/-- The targets of a transcript, in order. -/
def tcrTargets (log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) :
    List ((Σ l, Tw × Msg l) × Out) :=
  log.filterMap asTarget

/-- **The rules of the SM-TCR-C transcript**: pairwise distinct target tweaks, every target before
the first reveal, and no evaluation at a target tweak. -/
def TcrValid (log : QueryLog (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut)) : Prop :=
  ((tcrTargets log).map fun e ↦ e.1.2.1).Nodup ∧
    (∀ e ∈ phaseTwo (fun q ↦ q.isReveal) log, e.1.isTarget = false) ∧
    ∀ t ∈ log.filterMap evalTweak, t ∉ (tcrTargets log).map fun e ↦ e.1.2.1

variable (W : OracleWorld)

/-- **The SM-TCR-C challenger** for the target collection `C` and the evaluation collection `D`:
a uniform hidden `P`; targets answered by `C`, evaluations by `D`; the forgery `(l, T, M')` wins
against a target `(l, T, M)` with `M ≠ M'` and the same digest, on a valid transcript. -/
noncomputable def smTcr [SampleableType Par] (C : TwColl Par Tw Fn Msg Out)
    (D : TwColl Par Tw EFn EMsg EOut) :
    Experiment W (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) Unit (Σ l, Tw × Msg l) where
  State := Par
  setup := sample W Par
  pub _ := ()
  answer P
    | .target l t m => C.eval W l P t m
    | .eval l t m => D.eval W l P t m
    | .reveal => pure P
  judge P log out := do
    let y ← C.eval W out.1 P out.2.1 out.2.2
    pure (holds (TcrValid log ∧ ∃ e ∈ tcrTargets log,
      e.1.1 = out.1 ∧ e.1.2.1 = out.2.1 ∧ e.1 ≠ out ∧ e.2 = y))

/-- **SM-TCR-C success probability** at the table `tab`. -/
noncomputable abbrev smTcrSucc [SampleableType Par] (C : TwColl Par Tw Fn Msg Out)
    (D : TwColl Par Tw EFn EMsg EOut) (tab : W.Tab)
    (A : Adversary W (TcrSpec Par Tw Fn Msg Out EFn EMsg EOut) Unit (Σ l, Tw × Msg l)) :
    ENNReal :=
  (smTcr W C D).succAt tab A

end Quantum.StdModel.Props

end
