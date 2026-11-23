module

public import Quantum.StdModel.Props.Basic

@[expose] public section

/-!
# CPRE: chain preimage resistance with openings (design D4)

Hash chains `C_{j,μ+1} = Th(P, T_{j,μ}, C_{j,μ})` from uniform starts `C_{j,0}`, of length
`len j`, with pairwise distinct step tweaks `T_{j,μ}` (`Chains`). The challenger samples `P` and
the starts. The adversary asks `value j μ` (answered `C_{j,min μ (len j)}`: an opening of chain
`j` at `μ` when `μ < len j`, the chain end otherwise), evaluations `eval l T M` of a collection at
tweaks that are no chain step tweak, and `reveal` for `P`. A chain is adaptive or selective: the
openings of a selective chain must come before the first reveal, those of an adaptive chain may
come at any time. The opened position of chain `j` is its lowest opening. The adversary wins with
`(j, μ', z)`, `μ' < len j`, when walking `z` from position `μ'` reaches the end `C_{j, len j}` and
either `z ≠ C_{j,μ'}` (a second preimage, or a preimage into the honest chain) or no opening of
chain `j` is at or below `μ'` (a preimage of an unopened value).

Published notions it matches or extends:
* For chains of length one with adaptive openings: SM-DT-OpenPRE (Barbosa, Dupressoir, Hulsing,
  Meijers, Strub, ASIACRYPT 2024; the T-openPRE of Bernstein and Hulsing, ASIACRYPT 2019,
  Theorem 38), extended by second preimages of opened targets.
* For WOTS chains with selective openings: the event the WOTS-TW analysis of Hulsing and Kudinov
  (ASIACRYPT 2022), restated in SPHINCS+C (S&P 2023, App. C), bounds by SM-UD, SM-PRE and SM-TCR.
* For chains with adaptive openings and length above one (leanXMSS, length 3): a new notion; no
  tight reduction to textbook notions is known (design, I2).

Differences: the adversary has superposition access to the world's hash; leanXMSS uses all chains
adaptive (an adversary that reveals first has `P` public, as in the design). A selective
opening's value is returned at once, as in the d-EU-naCMA experiment of HK22 (restated in
SPHINCS+C, App. D), where signatures are answered in phase 1; only the chain ends, available in
phase 1 here, go beyond it, and an HK22-style reduction computes them by SM-TCR target queries at
the hidden `P`. Openings may be repeated; only the lowest counts, since it determines the values
above it.

Instance obligation (see `Props.Basic`): the evaluation restriction compares tweaks, so no
function of the evaluation collection may produce the bytes of a chain step input under a tweak
that is no step tweak.
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Props

open HashSig

/-- **A family of hash chains**: the step `Th(P, T, x)`, the length of each chain, the step
tweaks `T_{j,μ}`, and whether openings of chain `j` are adaptive. -/
structure Chains (Par Tw J Val : Type) where
  /-- The chain step. -/
  step : TwHash Par Tw Val Val
  /-- The length of chain `j`. -/
  len : J → ℕ
  /-- The tweak of step `μ` of chain `j`. -/
  tweak : J → ℕ → Tw
  /-- Whether chain `j` may be opened after the reveal. -/
  adaptive : J → Bool

namespace Chains

variable {Par Tw J Val : Type} (ch : Chains Par Tw J Val) (W : OracleWorld)

/-- Walk `n` steps of chain `j` from position `μ` and value `x`. -/
noncomputable def walk (P : Par) (j : J) : ℕ → ℕ → Val → OracleComp W.Oracles Val
  | _, 0, x => pure x
  | μ, n + 1, x => do
    let y ← ch.step.eval W () P (ch.tweak j μ) x
    walk P j (μ + 1) n y

/-- Whether `t` is a step tweak of some chain. -/
def IsStepTweak (t : Tw) : Prop :=
  ∃ j μ, μ < ch.len j ∧ ch.tweak j μ = t

/-- The step tweaks are pairwise distinct, as in every instance of the design; the game is defined
without it. -/
def DistinctTweaks : Prop :=
  ∀ j μ j' μ', μ < ch.len j → μ' < ch.len j' → ch.tweak j μ = ch.tweak j' μ' → j = j' ∧ μ = μ'

end Chains

/-- The classical queries of the CPRE game. -/
inductive CpreQuery (J Tw Fn : Type) (Msg : Fn → Type) where
  /-- The value of chain `j` at position `μ` (an opening when `μ` is below the chain length). -/
  | value (j : J) (μ : ℕ)
  /-- An evaluation `Th_l(P, T, M)` of the collection at a tweak that is no chain step tweak. -/
  | eval (l : Fn) (t : Tw) (m : Msg l)
  /-- The public parameter. -/
  | reveal

namespace CpreQuery

variable {J Tw Fn : Type} {Msg : Fn → Type}

/-- The answer types: a chain value, a digest of the collection, the parameter. -/
def Resp (Par Val Out : Type) : CpreQuery J Tw Fn Msg → Type
  | .value .. => Val
  | .eval .. => Out
  | .reveal => Par

/-- Whether a query is `reveal`. -/
def isReveal : CpreQuery J Tw Fn Msg → Bool
  | .reveal => true
  | _ => false

/-- The chain and position of a value query. -/
def asValue : CpreQuery J Tw Fn Msg → Option (J × ℕ)
  | .value j μ => some (j, μ)
  | _ => none

/-- The tweak of an evaluation. -/
def evalTweak : CpreQuery J Tw Fn Msg → Option Tw
  | .eval _ t _ => some t
  | _ => none

end CpreQuery

open CpreQuery

/-- The oracle specification of the CPRE ports. -/
abbrev CpreSpec (Par Tw J Val Fn : Type) (Msg : Fn → Type) (Out : Type) :
    OracleSpec (CpreQuery J Tw Fn Msg) :=
  OracleSpec.ofFn (Resp Par Val Out)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type}

/-- **The rules of the CPRE transcript**: no evaluation at a chain step tweak, and every opening
of a selective chain before the first reveal. -/
def CpreValid (ch : Chains Par Tw J Val)
    (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) : Prop :=
  (∀ t ∈ log.filterMap fun e ↦ e.1.evalTweak, ¬ ch.IsStepTweak t) ∧
    ∀ e ∈ phaseTwo (fun q ↦ q.isReveal) log, ∀ jμ ∈ e.1.asValue,
      jμ.2 < ch.len jμ.1 → ch.adaptive jμ.1 = true

/-- Chain `j` is opened at or below position `μ` in the transcript. -/
def OpenedAtOrBelow (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (j : J)
    (μ : ℕ) : Prop :=
  ∃ ν ≤ μ, (j, ν) ∈ log.filterMap fun e ↦ e.1.asValue

variable (W : OracleWorld)

/-- **The CPRE challenger** for the chains `ch`, with the collection `C` behind the evaluation
port: a uniform hidden `P` and uniform chain starts; the forgery `(j, μ', z)` wins on a valid
transcript when `μ' < len j`, `z` walks to the end of chain `j`, and `z ≠ C_{j,μ'}` or chain `j`
is not opened at or below `μ'`. -/
noncomputable def cpre [SampleableType Par] [Fintype J] [SampleableType Val]
    (ch : Chains Par Tw J Val) (C : TwColl Par Tw Fn Msg Out) :
    Experiment W (CpreSpec Par Tw J Val Fn Msg Out) Unit (J × ℕ × Val) where
  State := Par × (J → Val)
  setup := do
    let P ← sample W Par
    let s ← sample W (J → Val)
    pure (P, s)
  pub _ := ()
  answer s
    | .value j μ => ch.walk W s.1 j 0 (min μ (ch.len j)) (s.2 j)
    | .eval l t m => C.eval W l s.1 t m
    | .reveal => pure s.1
  judge s log out := do
    let j := out.1
    let μ := out.2.1
    let z := out.2.2
    let e' ← ch.walk W s.1 j μ (ch.len j - μ) z
    let e ← ch.walk W s.1 j 0 (ch.len j) (s.2 j)
    let c ← ch.walk W s.1 j 0 μ (s.2 j)
    pure (holds (CpreValid ch log ∧ μ < ch.len j ∧ e' = e ∧
      (z ≠ c ∨ ¬ OpenedAtOrBelow log j μ)))

/-- **CPRE success probability** at the table `tab`. -/
noncomputable abbrev cpreSucc [SampleableType Par] [Fintype J] [SampleableType Val]
    (ch : Chains Par Tw J Val) (C : TwColl Par Tw Fn Msg Out) (tab : W.Tab)
    (A : Adversary W (CpreSpec Par Tw J Val Fn Msg Out) Unit (J × ℕ × Val)) : ENNReal :=
  (cpre W ch C).succAt tab A

end Quantum.StdModel.Props

end
