module

public import Quantum.SufCma.Game
public import Quantum.Classical
public import Quantum.Par.Spec

@[expose] public section

/-!
# The parallel-query SUF-CMA game in the QRPM

A parallel adversary calls the permutation in rounds: one call of the port `.permPar w dir` acts on
the register `Fin w → S × S`, the slot `i` calling `φ` or `φ⁻¹` as `dir i` says. Its signing
requests stay single classical calls (`.sign r`). A round of width `w` is, by definition, its `w`
calls on the components in the order `0, …, w - 1` (`toSeq`, through `Quantum.Par.seqCalls`): for a
fixed permutation these are basis maps on disjoint registers, so a round is the product unitary
`|x_i, y_i⟩ ↦ |x_i, y_i + φ_{dir i} x_i⟩` in every slot (`run₂_challenged_permRound`). The game of
a parallel adversary is the game `Quantum.SufCma.game` of its serialization (`winProbPar_eq`).

* `widthCharge` counts the calls of a round (`w`), `roundCharge` the rounds (`1` each, so a path
  of `d` rounds has query depth `d`), `signChargePar` the signing requests.
* `QuantumStronglyUnforgeablePar sch e limit bound`: every parallel adversary making at most `q`
  calls in at most `d` rounds and at most `limit` signing requests on every path wins with
  probability at most `bound q d`.

## Main statements

* `isChargeBound_toSeq_perm`, `isChargeBound_toSeq_sign`: the serialized adversary makes at most
  `q` permutation calls when the parallel one has total width at most `q`, and the same signing
  requests.
* `QuantumStronglyUnforgeable.par`: the sequential theorem gives the parallel one with the bound
  `fun q _ ↦ bound q`.
* `QuantumRuntime.roundStep_eq_relabel`, `QuantumRuntime.run₂_seqCalls_eq_relabel`: a round
  against a runtime whose steps are basis relabellings is the relabelling along their product.
* `run₂_challenged_permRound`: fidelity of a round of the game for each permutation.
-/

open IPFunctor
open scoped ENNReal

universe u v

/-! ## Rounds of basis relabellings -/

namespace Quantum.QuantumRuntime

open Quantum.Par (roundIn roundOut RoundResult roundZeroEquiv seqCalls
  relabel_bind_relabel_bind)
open SubInstrument

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)

/-- **A round of relabelling steps.** When the step of every port `f i` relabels its register
along `g i` and reports `r0 i`, the round step relabels along the product of the `g i` and
reports `r0`. -/
theorem roundStep_eq_relabel {w : ℕ} (f : Fin w → spec.Port)
    (g : ∀ i, spec.In (f i) ≃ spec.Out (f i)) (r0 : RoundResult spec f)
    (hR : ∀ i, R.step (f i) = (relabel ((g i).prodCongr (Equiv.refl R.D))).map fun _ ↦ r0 i) :
    R.roundStep f =
      (relabel ((Equiv.piCongrRight g).prodCongr (Equiv.refl R.D))).map fun _ ↦ r0 := by
  induction w with
  | zero =>
    have h1 : (roundZeroEquiv f).prodCongr (Equiv.refl R.D) =
        (Equiv.piCongrRight g).prodCongr (Equiv.refl R.D) :=
      Equiv.ext fun _ ↦ Prod.ext (funext fun i ↦ i.elim0) rfl
    have h2 : (fun _ : Unit ↦ (finZeroElim : RoundResult spec f)) = fun _ ↦ r0 :=
      funext fun _ ↦ funext fun i ↦ i.elim0
    rw [roundStep_zero, h1, h2]
  | succ w ih =>
    rw [roundStep_succ, hR 0, ih (fun i ↦ f i.succ) (fun i ↦ g i.succ) (Fin.tail r0)
      fun i ↦ hR i.succ]
    simp only [map_eq_bind_pure, frame_bind, frame_relabel, frame_pure,
      SubInstrument.bind_assoc, SubInstrument.pure_bind, relabel_bind_relabel_bind,
      Fin.cons_self_tail]
    refine congrArg (fun e ↦ (relabel e).bind fun _ : Unit ↦ SubInstrument.pure r0)
      (Equiv.ext fun x ↦ Prod.ext (funext fun i ↦ ?_) rfl)
    cases i using Fin.cases <;> rfl

/-- **A round of relabelling steps, run**: the calls of the round relabel the exposed register
along the product of the `g i`, then along `post`. -/
theorem run₂_seqCalls_eq_relabel {w : ℕ} (f : Fin w → spec.Port)
    (g : ∀ i, spec.In (f i) ≃ spec.Out (f i)) (r0 : RoundResult spec f)
    (hR : ∀ i, R.step (f i) = (relabel ((g i).prodCongr (Equiv.refl R.D))).map fun _ ↦ r0 i)
    (E : QReg) {A B : QReg} (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    R.run₂ .instruments (seqCalls f E ℓ post) =
      (relabel (((ℓ.trans ((Equiv.piCongrRight g).prodCongr (Equiv.refl E))).trans
        post).prodCongr (Equiv.refl R.D))).map fun _ ↦ r0 := by
  rw [run₂_seqCalls, R.roundStep_eq_relabel f g r0 hR]
  simp only [map_eq_bind_pure, frame_bind, frame_relabel, frame_pure, SubInstrument.bind_assoc,
    SubInstrument.pure_bind, relabel_bind_relabel_bind]
  exact congrArg (fun e ↦ (relabel e).bind fun _ : Unit ↦ SubInstrument.pure r0)
    (Equiv.ext fun _ ↦ rfl)

end Quantum.QuantumRuntime

namespace Quantum.SufCma

open Common Common.SufCma SubInstrument
open Quantum.Par (roundIn roundOut seqCalls seqCalls_succ isChargeBound_seqCalls)
open LeanVM.Semantics (KeccakState)

/-! ## The parallel adversary -/

/-- The parallel adversary's ports: a round of `w` permutation calls with the directions `dir`,
and one classical signing port per request. -/
inductive AdvPortPar (Req : Type) where
  /-- A round of `w` calls, the slot `i` calling `φ` or `φ⁻¹` as `dir i` says. -/
  | permPar (w : ℕ) (dir : Fin w → PermutationPort)
  /-- The signing request `r`. -/
  | sign (r : Req)

variable (PK Req Resp F : Type) (S : Type) [Fintype S] [DecidableEq S]

/-- The parallel adversary's signature: a round of width `w` acts on `Fin w → S × S` (the `w`
query registers, each input then response) and reports nothing; a signing port acts on no register
and reports the signer's answer. -/
@[reducible]
def advSpecPar : QuantumOracleSpec.{0, 0} where
  Port := AdvPortPar Req
  In
    | .permPar w _ => QReg.of (Fin w → S × S)
    | .sign _ => QReg.of Unit
  Out
    | .permPar w _ => QReg.of (Fin w → S × S)
    | .sign _ => QReg.of Unit
  Result
    | .permPar _ _ => Unit
    | .sign _ => Resp

/-- A parallel quantum SUF-CMA adversary: from the public key, a program over `advSpecPar`. -/
abbrev AdversaryPar := PK → QComp (advSpecPar Req Resp S) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F S}

/-- A round costs its width, a signing request nothing: the number of permutation calls. -/
def widthCharge : AdvPortPar Req → ℕ
  | .permPar w _ => w
  | .sign _ => 0

/-- A round costs one, a signing request nothing: the query depth. -/
def roundCharge : AdvPortPar Req → ℕ
  | .permPar _ _ => 1
  | .sign _ => 0

/-- A signing request costs one, a round nothing. -/
def signChargePar : AdvPortPar Req → ℕ
  | .permPar _ _ => 0
  | .sign _ => 1

/-- A charge on the parallel ports as a charge on commands: a call of port `i` costs `c i`, a
local operation nothing. -/
def cmdChargePar {L : LocalSig.{u, v}} (c : AdvPortPar Req → ℕ) (A : QReg) :
    QuantumComp.Cmd L (advSpecPar Req Resp S) A → ℕ
  | .prim _ => 0
  | .query i _ _ => c i

/-! ## Serialization -/

/-- **A round of width `w`** with the adversary's register `A ≃ (Fin w → S × S) × E`: its `w`
permutation calls on the components, in order, slot `i` calling the port `.perm (dir i)`, ending
on the register of the round's output. -/
noncomputable def permRound {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpecPar Req Resp S).In (.permPar w dir) × E) :
    QComp (advSpec Req Resp S) A (QReg.of ((advSpecPar Req Resp S).Out (.permPar w dir) × E))
      (Fin w → Unit) :=
  seqCalls (spec := advSpec Req Resp S) (fun i ↦ AdvPort.perm (dir i)) E ℓ (Equiv.refl _)

/-- **Serialization**: a local operation stays, a round becomes its calls in order
(`permRound`), and a signing request stays. -/
noncomputable def toSeq :
    CommandSubstitution
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpecPar Req Resp S))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec Req Resp S))
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.permPar _ dir) E ℓ =>
      QuantumComp.bind (permRound dir E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩
  | _, .query (.sign r) E ℓ =>
      QuantumComp.queryBind (spec := advSpec Req Resp S) (.sign r) E ℓ fun b ↦
        QuantumComp.pure ⟨ULift.up b, rfl⟩

/-- The serialized adversary: every round replaced by its calls in order. -/
noncomputable def serialize (A : AdversaryPar PK Req Resp F S) : Adversary PK Req Resp F S :=
  fun pk ↦ IFreeM.substitute toSeq (A pk)

/-! ## Budgets of the serialized adversary -/

/-- **Calls of the serialized adversary**: a parallel adversary of total width at most `q` is
serialized to one making at most `q` permutation calls. -/
theorem isChargeBound_toSeq_perm {A B : QReg} {α : Type}
    {x : QComp (advSpecPar Req Resp S) A B α} {q : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdChargePar widthCharge) q) :
    IFreeM.IsChargeBound (IFreeM.substitute toSeq x) (cmdCharge permCharge) q := by
  refine IFreeM.IsChargeBound.substitute toSeq (fun A c ↦ ?_) hx
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind
      (isChargeBound_seqCalls (k := fun _ ↦ 1) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ le_rfl) _ _ _)
      fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp [cmdChargePar, widthCharge]
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨Nat.zero_le _, fun _ ↦ trivial⟩

/-- **Signing requests of the serialized adversary**: the same as the parallel adversary's. -/
theorem isChargeBound_toSeq_sign {A B : QReg} {α : Type}
    {x : QComp (advSpecPar Req Resp S) A B α} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdChargePar signChargePar) n) :
    IFreeM.IsChargeBound (IFreeM.substitute toSeq x) (cmdCharge signCharge) n := by
  refine IFreeM.IsChargeBound.substitute toSeq (fun A c ↦ ?_) hx
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind
      (isChargeBound_seqCalls (k := fun _ ↦ 0) (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ le_rfl) _ _ _)
      fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp [cmdChargePar, signChargePar]
  · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩

/-! ## The game -/

variable {Seed SK : Type} (sch : Scheme Seed PK SK Req Resp F) [AddCommGroup S]
  (e : KeccakState ≃ S)

/-- **The winning probability of a parallel adversary**: that of its serialization in the QRPM
game. -/
noncomputable def winProbPar [Fintype Seed] (A : AdversaryPar PK Req Resp F S) : ℝ≥0∞ :=
  winProb sch e (serialize A)

/-- **Parallel SUF-CMA of `sch` against quantum adversaries in the QRPM**: every parallel adversary
that makes at most `q` permutation calls in at most `d` rounds and at most `limit` signing
requests on every path wins with probability at most `bound q d`. -/
def QuantumStronglyUnforgeablePar [Fintype Seed] (limit : ℕ) (bound : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ q d (A : AdversaryPar PK Req Resp F S),
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar widthCharge) q) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar roundCharge) d) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar signChargePar) limit) →
      winProbPar sch e A ≤ bound q d

/-- **The serialized adversary is an adversary of the sequential game with the same winning
probability.** -/
theorem winProbPar_eq [Fintype Seed] (A : AdversaryPar PK Req Resp F S) :
    winProbPar sch e A = winProb sch e (serialize A) :=
  rfl

/-- **The sequential theorem gives the parallel one**, with a bound that ignores the depth. -/
theorem QuantumStronglyUnforgeable.par [Fintype Seed] {limit : ℕ} {bound : ℕ → ℝ≥0∞}
    (h : QuantumStronglyUnforgeable sch e limit bound) :
    QuantumStronglyUnforgeablePar sch e limit fun q _ ↦ bound q :=
  fun q _ A hw _ hs ↦
    h q (serialize A) (fun pk ↦ isChargeBound_toSeq_perm (hw pk))
      fun pk ↦ isChargeBound_toSeq_sign (hs pk)

/-! ## Fidelity: a round is the product unitary -/

/-- A subinstrument with one outcome forgets nothing when its outcome is forgotten. -/
theorem map_const_unit {X Y : Type} [Fintype X] [Fintype Y] (p : SubInstrument X Y Unit) :
    p.map (fun _ ↦ ()) = p :=
  (map_eq_bind_pure _ p).trans (bind_pure p)

/-- The bijection of a round of the oracle of `φ`: slot `i` adds `φ` or `φ⁻¹`, as `dir i` says,
into its response register. -/
def parPermEquiv (φ : Equiv.Perm S) {w : ℕ} (dir : Fin w → PermutationPort) :
    (Fin w → S × S) ≃ (Fin w → S × S) :=
  Equiv.piCongrRight fun i ↦ oracleEquiv ⇑(portPerm φ (dir i))

/-- The step of the oracle of `φ` at the port `p` relabels along the oracle bijection of
`portPerm φ p`. -/
theorem step_permutationRuntime (φ : Equiv.Perm S) (p : PermutationPort) :
    (permutationRuntime φ).step p =
      (relabel ((oracleEquiv ⇑(portPerm φ p)).prodCongr (Equiv.refl Unit))).map fun _ ↦ () := by
  rw [map_const_unit]
  cases p <;> exact frame_relabel _ _

/-- **A round against the oracle of `φ`**: its calls relabel the exposed register along the
product oracle bijection `parPermEquiv φ dir`, `|x_i, y_i⟩ ↦ |x_i, y_i + φ_{dir i} x_i⟩` in every
slot, then along `post`. -/
theorem run₂_seqCalls_permutationRuntime (φ : Equiv.Perm S) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec S) dir × E) (post : roundOut (qrpmSpec S) dir × E ≃ B) :
    (permutationRuntime φ).run₂ .instruments (seqCalls dir E ℓ post) =
      (relabel (((ℓ.trans ((parPermEquiv φ dir).prodCongr (Equiv.refl E))).trans
        post).prodCongr (Equiv.refl Unit))).map fun _ _ ↦ () :=
  (permutationRuntime φ).run₂_seqCalls_eq_relabel dir
    (fun i ↦ oracleEquiv ⇑(portPerm φ (dir i))) (fun _ ↦ ())
    (fun i ↦ step_permutationRuntime φ (dir i)) E ℓ post

/-- The challenger passes a permutation call through. -/
theorem challenged_queryBind_perm (sk : SK) (p : PermutationPort) (E : QReg) {A B : QReg}
    {α : Type} (ℓ : A ≃ (advSpec Req Resp S).In (.perm p) × E)
    (k : Unit → QComp (advSpec Req Resp S) (QReg.of ((advSpec Req Resp S).Out (.perm p) × E)) B
      α) :
    challenged sch e sk (QuantumComp₂.queryBind (.perm p) E ℓ k) =
      QuantumComp₂.queryBind (spec := qrpmSpec S) p E ℓ fun r ↦ challenged sch e sk (k r) :=
  rfl

/-- The challenger commutes with relabelling the return value. -/
theorem challenged_map (sk : SK) {A B : QReg} {α β : Type} (g : α → β)
    (x : QComp (advSpec Req Resp S) A B α) :
    challenged sch e sk (x.map g) = (challenged sch e sk x).map g := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure]
  show IFreeM.substitute (challenge sch e sk) (IFreeM.bind x _) =
    IFreeM.bind (IFreeM.substitute (challenge sch e sk) x) _
  refine (IFreeM.substitute_bind _ _ _).trans
    (congrArg (IFreeM.bind _) (funext fun _ ↦ funext fun p ↦ ?_))
  obtain ⟨h, _⟩ := p
  cases h
  rfl

/-- **The challenger keeps a round of permutation calls**: the same calls of `qrpmSpec S`. -/
theorem challenged_seqCalls (sk : SK) : ∀ {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg)
    {A B : QReg} (ℓ : A ≃ roundIn (advSpec Req Resp S) (fun i ↦ .perm (dir i)) × E)
    (post : roundOut (advSpec Req Resp S) (fun i ↦ .perm (dir i)) × E ≃ B),
    challenged sch e sk (seqCalls (fun i ↦ AdvPort.perm (dir i)) E ℓ post) =
      seqCalls (spec := qrpmSpec S) dir E ℓ post
  | 0, _, _, _, _, _, _ => rfl
  | _ + 1, dir, E, _, _, ℓ, post => by
    rw [seqCalls_succ, seqCalls_succ]
    refine (challenged_queryBind_perm sch e sk _ _ _ _).trans
      (congrArg (QuantumComp₂.queryBind _ _ _) (funext fun r ↦ ?_))
    rw [challenged_map]
    exact congrArg (QuantumComp₂.map _) (challenged_seqCalls sk (fun i ↦ dir i.succ) _ _ _)

/-- **Fidelity of a round in the game.** Against the oracle of `φ`, a round of width `w` of the
serialized adversary, as the challenger runs it, is the product unitary
`|x_i, y_i⟩ ↦ |x_i, y_i + φ_{dir i} x_i⟩` in every slot of the exposed register. -/
theorem run₂_challenged_permRound (φ : Equiv.Perm S) (sk : SK) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpecPar Req Resp S).In (.permPar w dir) × E) :
    (permutationRuntime φ).run₂ .instruments (challenged sch e sk (permRound dir E ℓ)) =
      (relabel ((ℓ.trans ((parPermEquiv φ dir).prodCongr (Equiv.refl E))).prodCongr
        (Equiv.refl Unit))).map fun _ _ ↦ () := by
  rw [permRound, challenged_seqCalls, run₂_seqCalls_permutationRuntime]
  rfl

end Quantum.SufCma

end
