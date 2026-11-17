module

public import Quantum.Qrom.Xmss.DepthPar

@[expose] public section

/-!
# Programs that run alike, with the same weights off one port

Two programs over a signature `spec` are `RunTWEq R p`-related when they run alike against the
runtime `R` and have the same summed weight for every weight vanishing at the port `p`. This is
the relation between the game of a serialized parallel adversary and a game with the same calls
reordered inside each round (the regrouped calls of leanSPHINCS), where every reordered block
makes only calls of `p`.

* `RunTWEq.queryBind`, `RunTWEq.primBind`, `runTWEq_bind_congr`: congruence.
* `FreeAt R p x`: a block whose calls are all calls of `p` and whose results are unique: the
  weights after it are those of its continuation from its single branch.
* `runTWEq_bind_freeAt`: two such blocks that run alike, then related continuations.
* `runTWEq_bind_substitute`: substitutions related command by command give related programs.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.QuantumRuntime

open Quantum.Par

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) (p : spec.Port)

/-- **Two programs run alike against `R`**, with the same summed weight for every weight
vanishing at `p`. -/
def RunTWEq {X : QReg → Type} {A : QReg} (x y : QuantumComp LocalSig.instruments.{0} spec X A) :
    Prop :=
  R.run .instruments x = R.run .instruments y ∧
    ∀ (W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞), (∀ σ, W p σ = 0) →
      ∀ ρ, R.totalWeight .instruments W x ρ = R.totalWeight .instruments W y ρ

variable {R p}

theorem RunTWEq.refl {X : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} spec X A) : RunTWEq R p x x :=
  ⟨rfl, fun _ _ _ ↦ rfl⟩

theorem RunTWEq.queryBind {X : QReg → Type} {A : QReg} (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E)
    {k₁ k₂ : spec.Result i →
      QuantumComp LocalSig.instruments.{0} spec X (QReg.of (spec.Out i × E))}
    (h : ∀ r, RunTWEq R p (k₁ r) (k₂ r)) :
    RunTWEq R p (QuantumComp.queryBind i E ℓ k₁) (QuantumComp.queryBind i E ℓ k₂) :=
  ⟨by rw [run_queryBind, run_queryBind]; exact congrArg _ (funext fun r ↦ (h r).1),
    fun W hW ρ ↦ by
      rw [totalWeight_queryBind, totalWeight_queryBind]
      exact congrArg _ (tsum_congr fun r ↦ (h r).2 W hW _)⟩

theorem RunTWEq.primBind {X : QReg → Type} {A : QReg} (o : LocalSig.instruments.{0}.Op A)
    {k₁ k₂ : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} spec X (LocalSig.instruments.{0}.next o b)}
    (h : ∀ b, RunTWEq R p (k₁ b) (k₂ b)) :
    RunTWEq R p (QuantumComp.primBind o k₁) (QuantumComp.primBind o k₂) :=
  ⟨by rw [run_primBind, run_primBind]; exact congrArg _ (funext fun b ↦ (h b).1),
    fun W hW ρ ↦ by
      rw [totalWeight_primBind, totalWeight_primBind]
      exact tsum_congr fun b ↦ (h b).2 W hW _⟩

/-- **Congruence of the continuation.** -/
theorem runTWEq_bind_congr {X Y : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} spec X A)
    {g₁ g₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u}
    (h : ∀ u a, RunTWEq R p (g₁ u a) (g₂ u a)) : RunTWEq R p (x.bind g₁) (x.bind g₂) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => exact h _ y
  | primBind _ o k ih => exact RunTWEq.primBind o ih
  | queryBind _ i E ℓ k ih => exact RunTWEq.queryBind i E ℓ ih

variable (R p)

/-- **A block of calls of `p` with a unique result**: the summed weight of the block followed by
any continuation, for a weight vanishing at `p`, is the weight of the continuation from the
block's single branch. -/
def FreeAt {A B : QReg} {α : Type} [Unique α] (x : QComp spec A B α) : Prop :=
  ∀ (W : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞), (∀ σ, W p σ = 0) →
    ∀ {Y : QReg → Type}
      (g : ∀ u, QuantumComp₂.Leaf B α u → QuantumComp LocalSig.instruments.{0} spec Y u) ρ,
      R.totalWeight .instruments W (IFreeM.bind x g) ρ =
        R.totalWeight .instruments W (g B ⟨rfl, default⟩)
          ((R.run₂ .instruments x).branch default ρ)

variable {R p}

theorem tsum_default {β M : Type*} [Unique β] [AddCommMonoid M] [TopologicalSpace M]
    (f : β → M) : ∑' b, f b = f default :=
  tsum_eq_single default fun b hb ↦ absurd (Subsingleton.elim b default) hb

theorem RunTWEq.of_eq {X : QReg → Type} {A : QReg}
    {x x' y y' : QuantumComp LocalSig.instruments.{0} spec X A} (hx : x = x') (hy : y = y')
    (h : RunTWEq R p x' y') : RunTWEq R p x y :=
  hx ▸ hy ▸ h

theorem freeAt_pure {A : QReg} {α : Type} [Unique α] (a : α) :
    FreeAt R p (QuantumComp₂.pure (L := LocalSig.instruments.{0}) (spec := spec) (A := A) a) := by
  intro W _ Y g ρ
  have hb : (R.run₂ .instruments (QuantumComp₂.pure (L := LocalSig.instruments.{0})
      (spec := spec) (A := A) a)).branch default ρ = ρ := by
    rw [run₂_pure, Subsingleton.elim a default, SubInstrument.branch_pure_self,
      LinearMap.id_apply]
  rw [hb, Subsingleton.elim a default]
  rfl

theorem freeAt_primBind {A B : QReg} {α : Type} [Unique α] (o : LocalSig.instruments.{0}.Op A)
    [Unique (LocalSig.instruments.{0}.Outcome o)]
    {k : (b : LocalSig.instruments.{0}.Outcome o) →
      QComp spec (LocalSig.instruments.{0}.next o b) B α}
    (hk : ∀ b, FreeAt R p (k b)) : FreeAt R p (QuantumComp₂.primBind o k) := by
  intro W hW Y g ρ
  have hb : (R.run₂ .instruments (QuantumComp₂.primBind o k)).branch default ρ =
      (R.run₂ .instruments (k default)).branch default
        (((LocalSig.Interp.instruments o).frame R.D).branch default ρ) := by
    rw [run₂_primBind, DSubInstrument.branch_bind_apply]
    exact tsum_default _
  exact (R.totalWeight_primBind .instruments o (fun b ↦ IFreeM.bind (k b) g) ρ).trans
    ((tsum_default _).trans ((hk default W hW g _).trans (congrArg _ hb.symm)))

theorem freeAt_queryBind {A B : QReg} {α : Type} [Unique α] [Unique (spec.Result p)] (E : QReg)
    (ℓ : A ≃ spec.In p × E)
    {k : spec.Result p → QComp spec (QReg.of (spec.Out p × E)) B α}
    (hk : ∀ r, FreeAt R p (k r)) : FreeAt R p (QuantumComp₂.queryBind p E ℓ k) := by
  intro W hW Y g ρ
  have hb : (R.run₂ .instruments (QuantumComp₂.queryBind p E ℓ k)).branch default ρ =
      (R.run₂ .instruments (k default)).branch default
        ((R.queryStep p E ℓ).branch default ρ) := by
    rw [run₂_queryBind, DSubInstrument.branch_bind_apply]
    exact tsum_default _
  exact (R.totalWeight_queryBind .instruments p E ℓ (fun r ↦ IFreeM.bind (k r) g) ρ).trans
    ((congrArg (· + _) (hW _)).trans ((zero_add _).trans ((tsum_default _).trans
      ((hk default W hW g _).trans (congrArg _ hb.symm)))))

theorem freeAt_bind {A B C : QReg} {α β : Type} [Unique α] [Unique β] {x : QComp spec A B α}
    {k : α → QComp spec B C β} (hx : FreeAt R p x) (hk : ∀ a, FreeAt R p (k a)) :
    FreeAt R p (x.bind k) := by
  intro W hW Y g ρ
  have hb : (R.run₂ .instruments (x.bind k)).branch default ρ =
      (R.run₂ .instruments (k default)).branch default
        ((R.run₂ .instruments x).branch default ρ) := by
    rw [run₂_bind, DSubInstrument.branch_bind_apply]
    exact tsum_default _
  exact (congrArg (fun y ↦ R.totalWeight .instruments W y ρ) (IFreeM.bind_assoc _ _ _)).trans
    ((hx W hW _ ρ).trans ((hk default W hW g _).trans (congrArg _ hb.symm)))

theorem freeAt_map {A B : QReg} {α β : Type} [Unique α] [Unique β] {x : QComp spec A B α}
    (hx : FreeAt R p x) (f : α → β) : FreeAt R p (x.map f) := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact freeAt_bind hx fun a ↦ freeAt_pure (f a)

theorem freeAt_act {A B : QReg} {α : Type} [Unique α] (q : SubInstrument A B α) :
    FreeAt R p (QComp.act (spec := spec) q) :=
  freeAt_primBind (o := ⟨α, fun _ ↦ B, q⟩) fun a ↦ freeAt_pure a

theorem freeAt_primBind_punit {A C B : QReg} {α : Type} [Unique α]
    (q : SubInstrument A C PUnit) {k : PUnit → QComp spec C B α}
    (hk : ∀ b, FreeAt R p (k b)) :
    FreeAt R p (QuantumComp₂.primBind (L := LocalSig.instruments.{0})
      (⟨PUnit, fun _ ↦ C, q⟩ : LocalSig.instruments.{0}.Op A) k) :=
  haveI : Unique (LocalSig.instruments.{0}.Outcome
      (⟨PUnit, fun _ ↦ C, q⟩ : LocalSig.instruments.{0}.Op A)) := inferInstanceAs (Unique PUnit)
  freeAt_primBind _ hk

theorem freeAt_seqCalls [Unique (spec.Result p)] {w : ℕ} (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec (fun _ : Fin w ↦ p) × E)
    (post : roundOut spec (fun _ : Fin w ↦ p) × E ≃ B) :
    FreeAt R p (seqCalls (fun _ : Fin w ↦ p) E ℓ post) := fun _ hW _ g ρ ↦
  (R.totalWeight_bind_seqCalls_of_eq_zero (fun _ ↦ p) (fun _ ↦ hW) E ℓ post g ρ).trans
    (tsum_default _)

/-- **Two blocks of calls of `p` that run alike, then related continuations.** -/
theorem runTWEq_bind_freeAt {A B : QReg} {α : Type} [Unique α] {Y : QReg → Type}
    {x₁ x₂ : QComp spec A B α} (h₁ : FreeAt R p x₁) (h₂ : FreeAt R p x₂)
    (hrun : R.run₂ .instruments x₁ = R.run₂ .instruments x₂)
    {g₁ g₂ : ∀ u, QuantumComp₂.Leaf B α u → QuantumComp LocalSig.instruments.{0} spec Y u}
    (hg : RunTWEq R p (g₁ B ⟨rfl, default⟩) (g₂ B ⟨rfl, default⟩)) :
    RunTWEq R p (IFreeM.bind x₁ g₁) (IFreeM.bind x₂ g₂) := by
  refine ⟨?_, fun W hW ρ ↦ ?_⟩
  · refine (R.run_bind_leaf .instruments x₁ g₁).trans (Eq.trans ?_
      (R.run_bind_leaf .instruments x₂ g₂).symm)
    rw [hrun]
    exact congrArg _ (funext fun a ↦ by rw [Subsingleton.elim a default]; exact hg.1)
  · refine (h₁ W hW g₁ ρ).trans (Eq.trans ?_ (h₂ W hW g₂ ρ).symm)
    rw [hrun]
    exact hg.2 W hW _

/-- **Substitutions related command by command** give related programs, with related
continuations. -/
theorem runTWEq_bind_substitute {spec₀ : QuantumOracleSpec.{0, 0}}
    {σ₁ σ₂ : CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec)}
    (hσ : ∀ A c {Y : QReg → Type}
      (g₁ g₂ : ∀ u, {b // (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀).src A c b = u}
        → QuantumComp LocalSig.instruments.{0} spec Y u),
      (∀ u b, RunTWEq R p (g₁ u b) (g₂ u b)) →
        RunTWEq R p ((σ₁ A c).bind g₁) ((σ₂ A c).bind g₂))
    {X : QReg → Type} {A : QReg}
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec₀) X A)
    {Y : QReg → Type} {k₁ k₂ : ∀ u, X u → QuantumComp LocalSig.instruments.{0} spec Y u}
    (hk : ∀ u a, RunTWEq R p (k₁ u a) (k₂ u a)) :
    RunTWEq R p ((y.substitute σ₁).bind k₁) ((y.substitute σ₂).bind k₂) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact hk _ a
  | liftBind A c next ih =>
    refine RunTWEq.of_eq (IFreeM.bind_assoc _ _ _) (IFreeM.bind_assoc _ _ _)
      (hσ A c _ _ fun u b ↦ ?_)
    obtain ⟨b, rfl⟩ := b
    exact ih b

end Quantum.QuantumRuntime

namespace Quantum.QuantumRuntime

variable {spec : QuantumOracleSpec.{0, 0}} {R : QuantumRuntime spec} {p : spec.Port}

theorem RunTWEq.liftBind {X : QReg → Type} {A : QReg}
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec).A A)
    {n₁ n₂ : (b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec).B A c) →
      QuantumComp LocalSig.instruments.{0} spec X
        ((QuantumComp.toIPFunctor LocalSig.instruments.{0} spec).src A c b)}
    (h : ∀ b, RunTWEq R p (n₁ b) (n₂ b)) :
    RunTWEq R p (IFreeM.liftBind c n₁) (IFreeM.liftBind c n₂) := by
  rcases c with o | ⟨i, E, ℓ⟩
  · exact RunTWEq.primBind o fun b ↦ h (ULift.up b)
  · exact RunTWEq.queryBind i E ℓ fun r ↦ h (ULift.up r)

end Quantum.QuantumRuntime

namespace Quantum.Par

variable {spec : QuantumOracleSpec.{0, 0}} {Q : Type} (port : Q → spec.Port)

/-- Serializing keeps a local operation. -/
theorem substitute_parToSeq_primBind {X : QReg → Type} {A : QReg}
    (o : LocalSig.instruments.{0}.Op A)
    (k : (b : LocalSig.instruments.{0}.Outcome o) →
      QuantumComp LocalSig.instruments.{0} (parSpec spec port) X
        (LocalSig.instruments.{0}.next o b)) :
    IFreeM.substitute (parToSeq port) (QuantumComp.primBind o k) =
      QuantumComp.primBind o fun b ↦ IFreeM.substitute (parToSeq port) (k b) :=
  rfl

/-- **Serializing a round**: its calls in order, then the serialized continuation. -/
theorem substitute_parToSeq_round₂ {w : ℕ} (f : Fin w → Q) (E : QReg) {A B : QReg} {α : Type}
    (ℓ : A ≃ roundIn spec (fun i ↦ port (f i)) × E)
    (k : RoundResult spec (fun i ↦ port (f i)) →
      QComp (parSpec spec port) (QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) B α) :
    IFreeM.substitute (parToSeq port)
      (QuantumComp₂.queryBind (spec := parSpec spec port) (.inr (.round w f)) E ℓ k) =
      QuantumComp₂.bind (seqCalls (fun i ↦ port (f i)) E
        (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) ℓ (Equiv.refl _)) fun rs ↦
          IFreeM.substitute (parToSeq port) (k rs) := by
  refine (IFreeM.bind_assoc _ _ _).trans (congrArg (IFreeM.bind _)
    (funext fun u ↦ funext fun l ↦ ?_))
  obtain ⟨h, a⟩ := l
  subst h
  rfl

end Quantum.Par

end
