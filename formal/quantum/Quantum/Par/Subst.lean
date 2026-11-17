module

public import Quantum.Par.Spec
public import VCVio.Quantum.Comp.TotalQueryBound

@[expose] public section

/-!
# Substitutions and the serialization of rounds

Games translate the adversary's commands by command substitutions before running them. A
substitution `σ` from `spec` to `spec'` that *passes the quantum ports through*, answering a call
of `port q` by one call of `port' q` up to relabellings of its registers
(`Quantum.Par.PassesThrough`), commutes with the serialization of rounds: the translated
serialization runs as the serialization of the translated parallel program.

* `frame_eq_relabel_frame`: framing is natural in the spectator.
* `QuantumRuntime.run₂_seqCalls_remainder`, `QuantumRuntime.queryStep_remainder`: the remainder
  of a round or of a call can be relabelled.
* `run₂_substitute_seqCalls`: under `σ`, the calls of a round of `spec` run as the calls of the
  corresponding round of `spec'`.
* `parLift σ`: the substitution of parallel programs that translates single calls by `σ` and
  rounds by the corresponding round; `run_substitute_parLift`: the translated serialization runs
  as the parallel translation against `R'.par port'`.
-/

open IPFunctor Quantum Quantum.SubInstrument

universe u v w w₁ u₁ v₁

namespace Quantum.Par

/-! ## Naturality of framing -/

section frame

variable {S T F F' : Type*} [Fintype S] [Fintype T] [Fintype F] [Fintype F'] [DecidableEq S]
  [DecidableEq T] [DecidableEq F] [DecidableEq F'] {α : Type*}

/-- **Framing is natural in the spectator**: framing by `F` is relabelling the spectator along
`g : F ≃ F'`, framing by `F'`, and relabelling back. -/
theorem frame_eq_relabel_frame (p : SubInstrument S T α) (g : F ≃ F') :
    p.frame F = (relabel ((Equiv.refl S).prodCongr g)).bind fun _ ↦ (p.frame F').bind fun a ↦
      (relabel ((Equiv.refl T).prodCongr g.symm)).bind fun _ ↦ SubInstrument.pure a :=
  DSubInstrument.ext <| funext fun a ↦ LinearMap.ext fun ρ ↦ by
    rw [DSubInstrument.branch_bind_unit, DSubInstrument.branch_bind_bind_unit_ret]
    ext x y
    simp only [LinearMap.comp_apply, relabel_branch_apply, DSubInstrument.branch_frame_apply,
      MatrixMap.amplify_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
      Equiv.symm_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply]

/-- Framing a relabelling with relabelled outcomes, before a continuation. -/
theorem bind_frame_map_relabel {D : Type*} [Fintype D] [DecidableEq D] (e : S ≃ T)
    {β : Type*} (g : Unit → β) {ι : Type*} {C : ι → Type*} [∀ i, Fintype (C i)]
    (Y : β → DSubInstrument (T × D) ι C) :
    DSubInstrument.bind (((relabel e).map g).frame D) Y =
      DSubInstrument.bind (relabel (e.prodCongr (Equiv.refl D))) fun u ↦ Y (g u) := by
  rw [SubInstrument.frame_map, frame_relabel, SubInstrument.map_eq_bind_pure, SubInstrument.bind,
    DSubInstrument.bind_assoc]
  exact congrArg _ (funext fun _ ↦ DSubInstrument.ret_bind _ _)

end frame

/-! ## Substitution and the value of a program -/

/-- A substitution keeps the relabelling of the value. -/
theorem substitute_map {L : LocalSig.{u, v}} {spec spec' : QuantumOracleSpec.{u₁, v₁}}
    (σ : CommandSubstitution (QuantumComp.toIPFunctor L spec) (QuantumComp.toIPFunctor L spec'))
    {A B : QReg} {α β : Type w} (x : QuantumComp₂ L spec A B α) (g : α → β) :
    IFreeM.substitute σ (x.map g) =
      QuantumComp₂.map (L := L) (spec := spec') g (IFreeM.substitute σ x) :=
  (congrArg (IFreeM.substitute σ) (QuantumComp₂.map_eq_bind_pure g x)).trans
    (((IFreeM.substitute_bind σ x _).trans
      (congrArg _ (funext fun _ ↦ funext fun ⟨h, _⟩ ↦ by subst h; rfl))).trans
      (QuantumComp₂.map_eq_bind_pure (L := L) (spec := spec') g _).symm)

end Quantum.Par

namespace Quantum.QuantumRuntime

open Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

/-- The remainder of a call can be relabelled along `g : E ≃ E'`. -/
theorem queryStep_remainder (i : spec.Port) {E E' : QReg} (g : E ≃ E') {A : QReg}
    (ℓ : A ≃ spec.In i × E) :
    R.queryStep i E ℓ =
      (R.queryStep i E' (ℓ.trans ((Equiv.refl _).prodCongr g))).bind fun r ↦
        (relabel (((Equiv.refl _).prodCongr g.symm).prodCongr (Equiv.refl R.D))).bind fun _ ↦
          SubInstrument.pure r := by
  rw [queryStep, queryStep, frame_eq_relabel_frame (R.step i) g]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind, relabel_bind_relabel_bind]
  rfl

/-- The remainder of a round can be relabelled along `g : E ≃ E'`. -/
theorem run₂_seqCalls_remainder {w : ℕ} (f : Fin w → spec.Port) {E E' : QReg} (g : E ≃ E')
    {A B : QReg} (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    R.run₂ .instruments (seqCalls f E ℓ post) =
      R.run₂ .instruments (seqCalls f E' (ℓ.trans ((Equiv.refl _).prodCongr g))
        (((Equiv.refl _).prodCongr g.symm).trans post)) := by
  rw [run₂_seqCalls, run₂_seqCalls, frame_eq_relabel_frame (R.roundStep f) g]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind, relabel_bind_relabel_bind]
  rfl

/-- A relabelling before a round is absorbed into its input. -/
theorem relabel_bind_run₂_seqCalls {w : ℕ} (f : Fin w → spec.Port) (E : QReg) {A' A B : QReg}
    (e : A' ≃ A) (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    ((relabel (e.prodCongr (Equiv.refl R.D))).bind fun _ ↦
      R.run₂ .instruments (seqCalls f E ℓ post)) =
      R.run₂ .instruments (seqCalls f E (e.trans ℓ) post) := by
  rw [run₂_seqCalls, run₂_seqCalls, relabel_bind_relabel_bind]
  rfl

end Quantum.QuantumRuntime

namespace Quantum.QuantumRuntime

open Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

/-- A relabelling before a round, with a continuation, is absorbed into its input. -/
theorem relabel_bind_run₂_seqCalls_bind {w : ℕ} (f : Fin w → spec.Port) (E : QReg)
    {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T] {B C : QReg}
    (e : S ≃ T) (ℓ : T ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B)
    {β : Type*} (k : RoundResult spec f → SubInstrument (B × R.D) (C × R.D) β) :
    ((relabel (e.prodCongr (Equiv.refl R.D))).bind fun _ ↦
      (R.run₂ .instruments (seqCalls f E (A := QReg.of T) ℓ post)).bind k) =
      (R.run₂ .instruments (seqCalls f E (A := QReg.of S) (e.trans ℓ) post)).bind k := by
  rw [← R.relabel_bind_run₂_seqCalls f E (A' := QReg.of S) (A := QReg.of T) e ℓ post,
    SubInstrument.bind_assoc]

end Quantum.QuantumRuntime

namespace Quantum.Par

/-! ## Substitutions that pass the quantum ports through -/

section pass

variable {spec spec' : QuantumOracleSpec.{u₁, v₁}} {Q : Type u₁} (port : Q → spec.Port)
  (port' : Q → spec'.Port) (eIn : ∀ q, spec.In (port q) ≃ spec'.In (port' q))
  (eOut : ∀ q, spec'.Out (port' q) ≃ spec.Out (port q))
  (res : ∀ q, spec'.Result (port' q) → spec.Result (port q))
  (σ : CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} spec)
    (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} spec'))
  (R' : QuantumRuntime spec')

/-- The substitution keeps every local operation. -/
def KeepsPrims : Prop :=
  ∀ A (o : LocalSig.instruments.{v₁}.Op A),
    σ A (.prim o) = QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩

/-- **The substitution passes the quantum ports through**: against `R'`, a call of `port q`
runs as a call of `port' q` with its input relabelled along `eIn q`, its output along `eOut q`,
and its result read through `res q`. -/
def PassesThrough : Prop :=
  ∀ q (A E : QReg) (ℓ : A ≃ spec.In (port q) × E),
    R'.run .instruments (σ A (.query (port q) E ℓ)) =
      DSubInstrument.bind (R'.queryStep (port' q) E (ℓ.trans ((eIn q).prodCongr (Equiv.refl E))))
        fun r ↦ DSubInstrument.bind
          (relabel (((eOut q).prodCongr (Equiv.refl E)).prodCongr (Equiv.refl R'.D))) fun _ ↦
            DSubInstrument.ret (fun p : (Σ u : QReg, {_b : ULift.{v₁} (spec.Result (port q)) //
                QReg.of (spec.Out (port q) × E) = u}) ↦ p.1 × R'.D)
              ⟨QReg.of (spec.Out (port q) × E), ⟨ULift.up (res q r), rfl⟩⟩

variable {port port' eIn eOut res σ R'}

/-- A call of a quantum port, translated by a substitution that passes it through. -/
theorem run_substitute_queryBind_of_passesThrough
    (hσ : PassesThrough port port' eIn eOut res σ R') (q : Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ spec.In (port q) × E) {X : QReg → Type w}
    (k : spec.Result (port q) →
      QuantumComp LocalSig.instruments.{v₁} spec X (QReg.of (spec.Out (port q) × E))) :
    R'.run .instruments (IFreeM.substitute σ (QuantumComp.queryBind (port q) E ℓ k)) =
      DSubInstrument.bind (R'.queryStep (port' q) E (ℓ.trans ((eIn q).prodCongr (Equiv.refl E))))
        fun r ↦ DSubInstrument.bind
          (relabel (((eOut q).prodCongr (Equiv.refl E)).prodCongr (Equiv.refl R'.D))) fun _ ↦
            R'.run .instruments (IFreeM.substitute σ (k (res q r))) := by
  refine (R'.run_bind _ (σ A (.query (port q) E ℓ)) _).trans ?_
  refine (congrFun (congrArg DSubInstrument.bind (hσ q A E ℓ)) _).trans ?_
  exact (DSubInstrument.bind_assoc _ _ _).trans (congrArg _ (funext fun _ ↦
    (DSubInstrument.bind_assoc _ _ _).trans
      (congrArg _ (funext fun _ ↦ DSubInstrument.ret_bind _ _))))

/-- The fixed-register form of `run_substitute_queryBind_of_passesThrough`. -/
theorem run₂_substitute_queryBind_of_passesThrough
    (hσ : PassesThrough port port' eIn eOut res σ R') (q : Q) (E : QReg) {A B : QReg}
    (ℓ : A ≃ spec.In (port q) × E) {α : Type v₁}
    (k : spec.Result (port q) → QComp spec (QReg.of (spec.Out (port q) × E)) B α) :
    R'.run₂ .instruments (IFreeM.substitute σ (QuantumComp₂.queryBind (port q) E ℓ k)) =
      (R'.queryStep (port' q) E (ℓ.trans ((eIn q).prodCongr (Equiv.refl E)))).bind fun r ↦
        (relabel (((eOut q).prodCongr (Equiv.refl E)).prodCongr (Equiv.refl R'.D))).bind fun _ ↦
          R'.run₂ .instruments (IFreeM.substitute σ (k (res q r))) := by
  refine DSubInstrument.ext (funext fun a ↦ LinearMap.ext fun ρ ↦ ?_)
  refine (congrArg (fun P ↦ DSubInstrument.branch P ⟨B, rfl, a⟩ ρ)
    (run_substitute_queryBind_of_passesThrough hσ q E ℓ k)).trans ?_
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  rfl

/-- A substitution that keeps local operations keeps a local subinstrument. -/
theorem substitute_act_of_keepsPrims (hprim : KeepsPrims σ) {A B : QReg} {α : Type v₁}
    (p : SubInstrument A B α) :
    (IFreeM.substitute σ (QComp.act (spec := spec) p) : QComp spec' A B α) = QComp.act p := by
  change IFreeM.bind (σ A (.prim _)) _ = _
  rw [hprim]
  rfl

/-- A substitution keeps the relabelling of the value, in the run. -/
theorem run₂_substitute_map {A B : QReg} {α β : Type v₁} (x : QComp spec A B α) (g : α → β) :
    R'.run₂ .instruments (IFreeM.substitute σ (x.map g)) =
      (R'.run₂ .instruments (IFreeM.substitute σ x)).map g :=
  (congrArg (R'.run₂ .instruments) (substitute_map σ x g)).trans (R'.run₂_map _ g _)

/-- **A round of quantum ports under a substitution that passes them through** runs as the
corresponding round of `spec'`, with its inputs relabelled along `eIn`, its outputs along `eOut`
and its results read through `res`. -/
theorem run₂_substitute_seqCalls (hprim : KeepsPrims σ)
    (hσ : PassesThrough port port' eIn eOut res σ R') {w : ℕ} (f : Fin w → Q) (E : QReg)
    {A B : QReg} (ℓ : A ≃ roundIn spec (fun i ↦ port (f i)) × E)
    (post : roundOut spec (fun i ↦ port (f i)) × E ≃ B) :
    R'.run₂ .instruments (IFreeM.substitute σ (seqCalls (fun i ↦ port (f i)) E ℓ post)) =
      (R'.run₂ .instruments (seqCalls (fun i ↦ port' (f i)) E
        (ℓ.trans ((Equiv.piCongrRight fun i ↦ eIn (f i)).prodCongr (Equiv.refl E)))
        (((Equiv.piCongrRight fun i ↦ eOut (f i)).prodCongr (Equiv.refl E)).trans post))).map
        fun rs i ↦ res (f i) (rs i) := by
  induction w generalizing E A B with
  | zero =>
    rw [seqCalls_zero, seqCalls_zero, substitute_act_of_keepsPrims hprim, R'.run₂_act,
      R'.run₂_act]
    simp only [SubInstrument.map_eq_bind_pure, SubInstrument.frame_bind, frame_relabel,
      SubInstrument.frame_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1
    · exact congrArg relabel (Equiv.ext fun x ↦
        Prod.ext (congrArg post (Prod.ext (funext fun i ↦ Fin.elim0 i) rfl)) rfl)
    · refine funext fun _ ↦ ?_
      congr 1
      exact funext fun i ↦ Fin.elim0 i
  | succ w ih =>
    simp only [seqCalls_succ]
    rw [run₂_substitute_queryBind_of_passesThrough hσ, R'.run₂_queryBind]
    simp only [run₂_substitute_map, ih]
    rw [R'.queryStep_remainder _
        (E' := QReg.of (roundIn spec' (fun i ↦ port' (f i.succ)) × E))
        ((Equiv.piCongrRight fun i : Fin w ↦ eIn (f i.succ)).prodCongr (Equiv.refl E)),
      R'.run₂_seqCalls_remainder _ (E' := QReg.of (spec'.Out (port' (f 0)) × E))
        ((eOut (f 0)).symm.prodCongr (Equiv.refl E))]
    simp only [SubInstrument.map_eq_bind_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind,
      QuantumRuntime.relabel_bind_run₂_seqCalls_bind, R'.run₂_map]
    congr 1
    refine funext fun a ↦ congrArg₂ DSubInstrument.bind ?_
      (funext fun rs ↦ congrArg SubInstrument.pure (funext fun i ↦ ?_))
    · congr 2
      · exact Equiv.ext fun x ↦ Prod.ext (funext fun i ↦ (eIn (f i.succ)).apply_symm_apply _)
          (Prod.ext ((eOut (f 0)).symm_apply_apply _) rfl)
      · exact Equiv.ext fun y ↦
          congrArg post (Prod.ext (funext fun i ↦ by cases i using Fin.cases <;> rfl) rfl)
    · cases i using Fin.cases <;> rfl

/-- A substitution that keeps local operations, run after a local operation. -/
theorem run_substitute_primBind_of_keepsPrims (hprim : KeepsPrims σ) {A : QReg}
    (o : LocalSig.instruments.{v₁}.Op A) {X : QReg → Type w}
    (k : (b : LocalSig.instruments.{v₁}.Outcome o) →
      QuantumComp LocalSig.instruments.{v₁} spec X (LocalSig.instruments.{v₁}.next o b)) :
    R'.run .instruments (IFreeM.substitute σ (QuantumComp.primBind o k)) =
      ((LocalSig.Interp.instruments o).frame R'.D).bind fun b ↦
        R'.run .instruments (IFreeM.substitute σ (k b)) := by
  refine (R'.run_bind _ (σ A (.prim o)) _).trans ?_
  rw [hprim, R'.run_primBind, DSubInstrument.bind_assoc]
  exact congrArg _ (funext fun _ ↦ DSubInstrument.ret_bind _ _)

/-- A round of quantum ports followed by a continuation, under a substitution that passes them
through. -/
theorem run_substitute_seqCalls_bind (hprim : KeepsPrims σ)
    (hσ : PassesThrough port port' eIn eOut res σ R') {w : ℕ} (f : Fin w → Q) (E : QReg)
    {A B : QReg} (ℓ : A ≃ roundIn spec (fun i ↦ port (f i)) × E)
    (post : roundOut spec (fun i ↦ port (f i)) × E ≃ B) {X : QReg → Type w}
    (g : ∀ u, QuantumComp₂.Leaf B (RoundResult spec fun i ↦ port (f i)) u →
      QuantumComp LocalSig.instruments.{v₁} spec X u) :
    R'.run .instruments
        (IFreeM.substitute σ (IFreeM.bind (seqCalls (fun i ↦ port (f i)) E ℓ post) g)) =
      DSubInstrument.bind (R'.run₂ .instruments (seqCalls (fun i ↦ port' (f i)) E
        (ℓ.trans ((Equiv.piCongrRight fun i ↦ eIn (f i)).prodCongr (Equiv.refl E)))
        (((Equiv.piCongrRight fun i ↦ eOut (f i)).prodCongr (Equiv.refl E)).trans post)))
        fun rs ↦ R'.run .instruments
          (IFreeM.substitute σ (g B ⟨rfl, fun i ↦ res (f i) (rs i)⟩)) := by
  refine (congrArg (R'.run .instruments) (IFreeM.substitute_bind σ _ g)).trans ?_
  refine (R'.run_bind_leaf _ _ _).trans ?_
  rw [run₂_substitute_seqCalls hprim hσ, SubInstrument.map_eq_bind_pure, SubInstrument.bind,
    DSubInstrument.bind_assoc]
  exact congrArg _ (funext fun _ ↦ DSubInstrument.ret_bind _ _)

variable (port port' eIn eOut res σ)

/-- **The parallel translation**: local operations and single calls are translated by `σ` (on the
single ports of `parSpec spec' port'`), and a round of `port ∘ f` becomes the round of
`port' ∘ f`, its registers relabelled along `eIn` and `eOut` and its results read through
`res`. -/
noncomputable def parLift :
    CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} (parSpec spec port))
      (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} (parSpec spec' port'))
  | A, .prim o => IFreeM.mapLens QuantumComp.ordinaryLens (σ A (.prim o))
  | A, .query (.inl p) E ℓ => IFreeM.mapLens QuantumComp.ordinaryLens (σ A (.query p E ℓ))
  | _, .query (.inr (.round _ f)) E ℓ =>
      QuantumComp.queryBind (spec := parSpec spec' port') (.inr (.round _ f)) E
        (ℓ.trans ((Equiv.piCongrRight fun i ↦ eIn (f i)).prodCongr (Equiv.refl E))) fun rs ↦
        QuantumComp.primBind (L := LocalSig.instruments.{v₁})
          ⟨PUnit, fun _ ↦ QReg.of (roundOut spec (fun i ↦ port (f i)) × E),
            (relabel ((Equiv.piCongrRight fun i ↦ eOut (f i)).prodCongr (Equiv.refl E))).map
              fun _ ↦ PUnit.unit⟩ fun _ ↦
          QuantumComp.pure ⟨ULift.up fun i ↦ res (f i) (rs i), rfl⟩

end pass

end Quantum.Par

namespace Quantum.QuantumRuntime

open Quantum.Par

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec)

/-- The final relabelling of a round, split off after the round. -/
theorem run₂_seqCalls_post {w : ℕ} (f : Fin w → spec.Port) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn spec f × E) (post : roundOut spec f × E ≃ B) :
    R.run₂ .instruments (seqCalls f E ℓ post) =
      (R.run₂ .instruments (seqCalls f E (B := QReg.of (roundOut spec f × E)) ℓ
        (Equiv.refl _))).bind fun rs ↦
        (relabel (post.prodCongr (Equiv.refl R.D))).bind fun _ ↦ SubInstrument.pure rs := by
  rw [run₂_seqCalls, run₂_seqCalls]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind, relabel_bind_relabel_bind]
  rfl

/-- A program lifted to the single ports of `R.par`, followed by a continuation. -/
theorem run_par_mapLens_bind {Q : Type u₁} (port : Q → spec.Port) {A : QReg}
    {X : QReg → Type w₁} {Y : QReg → Type w}
    (x : QuantumComp LocalSig.instruments.{v₁} spec X A)
    (g : ∀ u, X u → QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) Y u) :
    (R.par port).run .instruments (IFreeM.bind (IFreeM.mapLens QuantumComp.ordinaryLens x) g) =
      (R.run .instruments x).bind fun p ↦ (R.par port).run .instruments (g p.1 p.2) :=
  ((R.par port).run_bind _ (QuantumComp.liftOrdinary x) g).trans
    (congrArg (fun P ↦ DSubInstrument.bind P _) (R.run_liftOrdinary _ _ x))

end Quantum.QuantumRuntime

namespace Quantum.Par

variable {spec spec' : QuantumOracleSpec.{u₁, v₁}} {Q : Type u₁} {port : Q → spec.Port}
  {port' : Q → spec'.Port} {eIn : ∀ q, spec.In (port q) ≃ spec'.In (port' q)}
  {eOut : ∀ q, spec'.Out (port' q) ≃ spec.Out (port q)}
  {res : ∀ q, spec'.Result (port' q) → spec.Result (port q)}
  {σ : CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} spec)
    (QuantumComp.toIPFunctor LocalSig.instruments.{v₁} spec')}
  {R' : QuantumRuntime spec'}

/-- The parallel translation of a round, run against `R'.par port'`. -/
theorem run_par_substitute_parLift_round {w : ℕ} (f : Fin w → Q) (E : QReg) {A : QReg}
    (ℓ : A ≃ roundIn spec (fun i ↦ port (f i)) × E) {X : QReg → Type w₁}
    (k : RoundResult spec (fun i ↦ port (f i)) → QuantumComp LocalSig.instruments.{v₁}
      (parSpec spec port) X (QReg.of (roundOut spec (fun i ↦ port (f i)) × E))) :
    (R'.par port').run .instruments (IFreeM.substitute (parLift port port' eIn eOut res σ)
        (QuantumComp.queryBind (spec := parSpec spec port) (.inr (.round w f)) E ℓ k)) =
      DSubInstrument.bind ((R'.par port').queryStep (.inr (.round w f)) E
        (ℓ.trans ((Equiv.piCongrRight fun i ↦ eIn (f i)).prodCongr (Equiv.refl E)))) fun rs ↦
        DSubInstrument.bind
          (((relabel ((Equiv.piCongrRight fun i ↦ eOut (f i)).prodCongr (Equiv.refl E))).map
            fun _ ↦ PUnit.unit.{v₁ + 1}).frame R'.D) fun _ ↦
          (R'.par port').run .instruments (IFreeM.substitute (parLift port port' eIn eOut res σ)
            (k fun i ↦ res (f i) (rs i))) :=
  rfl

/-- **Substitution commutes with serialization.** For a substitution `σ` that keeps local
operations and passes the quantum ports through, translating the serialization of a parallel
program by `σ` runs, against `R'`, as the parallel translation `parLift` against `R'.par port'`.
-/
theorem run_substitute_parLift (hprim : KeepsPrims σ)
    (hσ : PassesThrough port port' eIn eOut res σ R') {X : QReg → Type w} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v₁} (parSpec spec port) X A) :
    R'.run .instruments (IFreeM.substitute σ (IFreeM.substitute (parToSeq port) x)) =
      (R'.par port').run .instruments
        (IFreeM.substitute (parLift port port' eIn eOut res σ) x) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y => rfl
  | primBind _ o k ih =>
    refine (run_substitute_primBind_of_keepsPrims hprim o
      fun b ↦ IFreeM.substitute (parToSeq port) (k b)).trans ?_
    refine Eq.trans ?_ (R'.run_par_mapLens_bind port' (σ _ (.prim o)) _).symm
    rw [hprim, R'.run_primBind]
    refine Eq.trans ?_ (DSubInstrument.bind_assoc _ _ _).symm
    refine congrArg _ (funext fun b ↦ (ih b).trans ?_)
    simp only [R'.run_pure]
    symm
    exact DSubInstrument.ret_bind _ _
  | queryBind _ i E ℓ k ih =>
    rcases i with p | ⟨w, f⟩
    · refine (R'.run_bind _ (σ _ (.query p E ℓ)) _).trans ?_
      refine Eq.trans ?_ (R'.run_par_mapLens_bind port' (σ _ (.query p E ℓ)) _).symm
      refine congrArg _ (funext fun ⟨_, b, h⟩ ↦ ?_)
      subst h
      exact ih b.down
    · refine (congrArg (fun t ↦ R'.run .instruments (IFreeM.substitute σ t))
        (IFreeM.bind_assoc (seqCalls (fun i ↦ port (f i)) E
          (B := QReg.of (roundOut spec (fun i ↦ port (f i)) × E)) ℓ (Equiv.refl _)) _ _)).trans ?_
      refine (run_substitute_seqCalls_bind hprim hσ f E ℓ _ _).trans ?_
      refine (congrArg (fun P ↦ DSubInstrument.bind P _)
        (R'.run₂_seqCalls_post (fun i ↦ port' (f i)) E _ _)).trans ?_
      refine (DSubInstrument.bind_assoc _ _ _).trans ?_
      refine Eq.trans ?_ (run_par_substitute_parLift_round f E ℓ k).symm
      refine Eq.trans ?_
        (congrArg (fun P ↦ DSubInstrument.bind P _) (R'.queryStep_par_round port' f E _)).symm
      refine congrArg _ (funext fun rs ↦ ?_)
      refine (DSubInstrument.bind_assoc _ _ _).trans ?_
      refine Eq.trans ?_ (bind_frame_map_relabel _ _ _).symm
      refine congrArg _ (funext fun _ ↦ ?_)
      refine (DSubInstrument.ret_bind _ _).trans ?_
      exact ih _

end Quantum.Par
