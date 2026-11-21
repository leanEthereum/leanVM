module

public import Quantum.Qrom.Sphincs.DepthRegroup
public import Quantum.Qrom.Sphincs.DepthRun

@[expose] public section

/-!
# Runtime 1's sponge programs on runtime 2, and the batched round

A program over the sponge ports, lifted to runtime 1's ports (`liftOrdinary`), read as a
template (`readLift`) and realized at `v` (`realizeT`), keeps its local operations and calls port
`h` of runtime 2 where it called `h` (`liftRG_seqCalls`). The batched round over the sponge ports
(`batRoundSG`) thus becomes `batRoundR` (`liftRG_batRoundSG`). Both rounds make only calls of `h`
with unique results (`freeAt_regRoundR`, `freeAt_batRoundR`). Stated for abstract types, so that
no concrete register is unfolded.
-/

open IPFunctor
open scoped ENNReal

namespace Quantum.Qrom.Sphincs

open Quantum Quantum.Par Quantum.Sponge
open Quantum.Xmss.Assembly (recHwSpec tmplSpec realizeT readLift readLens tmplLens)
open Quantum.Xmss.Hybrid (LazyProg)

/-- A lens transport distributes over sequencing of fixed-register programs. -/
theorem mapLens_bind₂ {spec spec' : QuantumOracleSpec.{0, 0}}
    (l : Lens (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec'))
    {A B C : QReg} {α β : Type} (x : QComp spec A B α) (k : α → QComp spec B C β) :
    IFreeM.mapLens l (x.bind k) =
      QuantumComp₂.bind (IFreeM.mapLens l x) fun a ↦ IFreeM.mapLens l (k a) := by
  have h := IFreeM.substitute_bind l.toSubstitution
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec)
      (QuantumComp₂.Leaf B α) A) (fun _ p ↦ p.casesOn fun h a ↦ h ▸ k a)
  simp only [IFreeM.substitute_toSubstitution] at h
  refine h.trans ?_
  congr 1
  funext u p
  rcases p with ⟨rfl, a⟩
  rfl

variable {Z Y : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] {S : Type}
  {D : S → Type} {M : Type} {good : LazyProg (Y × Y) Z S D → Prop}

variable (good) in
/-- A sponge program of runtime 1 as a realized program of runtime 2 at `v`. -/
noncomputable def liftRG (v : (s : S) → D s) {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (spongeSpec (Y × Y) Z) Ω A) :
    QuantumComp LocalSig.instruments.{0} (recHwSpec (Y × Y) Z S M) Ω A :=
  realizeT v (readLift good (y.liftOrdinary (t := hwReadCmdSpec (Y × Y) Z M)))

variable (v : (s : S) → D s)

theorem liftRG_bind₂ {A B C : QReg} {α β : Type} (x : QComp (spongeSpec (Y × Y) Z) A B α)
    (k : α → QComp (spongeSpec (Y × Y) Z) B C β) :
    liftRG good (M := M) v (x.bind k) =
      QuantumComp₂.bind (liftRG good v x) fun a ↦ liftRG good v (k a) :=
  (congrArg (fun z ↦ realizeT v (readLift good z))
    (mapLens_bind₂ QuantumComp.ordinaryLens x k)).trans
    ((congrArg (realizeT v) (mapLens_bind₂ (readLens good) _ _)).trans
      (mapLens_bind₂ (tmplLens v) _ _))

theorem liftRG_map {A B : QReg} {α β : Type} (x : QComp (spongeSpec (Y × Y) Z) A B α)
    (g : α → β) :
    liftRG good (M := M) v (x.map g) = QuantumComp₂.map g (liftRG good v x) :=
  (congrArg (liftRG good v) (QuantumComp₂.map_eq_bind_pure g x)).trans
    ((liftRG_bind₂ v x _).trans (QuantumComp₂.map_eq_bind_pure g _).symm)

theorem liftRG_act {A B : QReg} {α : Type} (q : SubInstrument A B α) :
    liftRG good (M := M) v (QComp.act (spec := spongeSpec (Y × Y) Z) q) = QComp.act q :=
  rfl

/-- **A round of calls of `h` of runtime 1 is the round of calls of `h` of runtime 2.** -/
theorem liftRG_seqCalls :
    ∀ {w : ℕ} (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (spongeSpec (Y × Y) Z) (fun _ : Fin w ↦ SpongePort.h) × E)
    (post : roundOut (spongeSpec (Y × Y) Z) (fun _ : Fin w ↦ SpongePort.h) × E ≃ B),
    liftRG good (M := M) v (seqCalls (fun _ : Fin w ↦ SpongePort.h) E ℓ post) =
      seqCalls (spec := recHwSpec (Y × Y) Z S M) (fun _ : Fin w ↦ hPortR S M) E ℓ post
  | 0, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, _ =>
    (congrArg (liftRG good v) (seqCalls_succ _ _ _ _)).trans (Eq.trans
      (congrArg (QuantumComp₂.queryBind _ _ _) (funext fun _ ↦
        (liftRG_map v _ _).trans (congrArg (QuantumComp₂.map _) (liftRG_seqCalls _ _ _))))
      (seqCalls_succ (spec := recHwSpec (Y × Y) Z S M) (fun _ ↦ hPortR S M) _ _ _).symm)

variable [Nonempty Y]

variable (S M) (τ : Equiv.Perm (Z × Bool))

/-- **The batched round over the sponge ports**, with the relabelling `post` the identity. -/
noncomputable def batRoundSG (w : ℕ) (E : QReg) {A : QReg} (ℓ : A ≃ hRound Z Y w × E) :
    QComp (spongeSpec (Y × Y) Z) A (QReg.of (hRound Z Y w × E)) (Fin w → Unit) :=
  (QComp.act (embAll S M τ w E ℓ)).bind fun _ ↦
    (seqCalls (spec := spongeSpec (Y × Y) Z) (fun _ : Fin w ↦ SpongePort.h)
      (QReg.of ((Fin w → Bool) × E))
      (B := QReg.of (roundOut (recHwSpec (Y × Y) Z S M) (fun _ : Fin w ↦ hPortR S M) ×
        QReg.of ((Fin w → Bool) × E))) (Equiv.refl _) (Equiv.refl _)).bind fun rs ↦
      (QComp.act (projAll S M τ w E (Equiv.refl _))).map fun _ ↦ rs

theorem liftRG_batRoundSG (w : ℕ) (E : QReg) {A : QReg} (ℓ : A ≃ hRound Z Y w × E) :
    liftRG good v (batRoundSG S M τ w E ℓ) = batRoundR S M τ w E ℓ (Equiv.refl _) := by
  unfold batRoundSG batRoundR
  refine (liftRG_bind₂ v _ _).trans (congrArg (QuantumComp₂.bind _) (funext fun _ ↦ ?_))
  refine (liftRG_bind₂ v _ _).trans ?_
  exact congrArg₂ QuantumComp₂.bind (liftRG_seqCalls v _ _ _) (funext fun _ ↦ liftRG_map v _ _)

/-! ## The rounds' calls are calls of `h` -/

instance instUniqueResultHPortR :
    Unique ((recHwSpec (Y × Y) Z S M).Result (hPortR S M)) :=
  inferInstanceAs (Unique Unit)

variable (R : QuantumRuntime (recHwSpec (Y × Y) Z S M))

omit [Nonempty Y] in
/-- **The interleaved round makes only calls of `h`.** -/
theorem freeAt_regRoundR [AddCommGroup Y] :
    ∀ {w : ℕ} (E : QReg) {A B : QReg} (ℓ : A ≃ hRound Z Y w × E)
    (post : roundOut (qromSpec Z Y) (fun _ : Fin w ↦ ()) × E ≃ B),
    QuantumRuntime.FreeAt R (hPortR S M) (regRoundR S M τ E ℓ post)
  | 0, _, _, _, _, _ => QuantumRuntime.freeAt_act _
  | _ + 1, _, _, _, _, _ =>
    QuantumRuntime.freeAt_primBind_punit _ fun _ ↦ QuantumRuntime.freeAt_queryBind _ _ fun _ ↦
      QuantumRuntime.freeAt_primBind_punit _ fun _ ↦
        QuantumRuntime.freeAt_map (freeAt_regRoundR _ _ _) _

/-- **The batched round makes only calls of `h`.** -/
theorem freeAt_batRoundR (w : ℕ) (E : QReg) {A B : QReg} (ℓ : A ≃ hRound Z Y w × E)
    (post : hRound Z Y w × E ≃ B) :
    QuantumRuntime.FreeAt R (hPortR S M) (batRoundR S M τ w E ℓ post) :=
  QuantumRuntime.freeAt_bind (QuantumRuntime.freeAt_act _) fun _ ↦
    QuantumRuntime.freeAt_bind (QuantumRuntime.freeAt_seqCalls _ _ _) fun _ ↦
      QuantumRuntime.freeAt_map (QuantumRuntime.freeAt_act _) _

end Quantum.Qrom.Sphincs

end
