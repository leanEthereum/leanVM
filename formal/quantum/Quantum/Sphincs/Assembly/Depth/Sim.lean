module

public import Quantum.Xmss.Assembly.Depth.Sim
public import Quantum.Sphincs.Assembly.Stream
public import Quantum.Sphincs.Assembly.CostRefined
public import Quantum.Sponge.Oracle.Hardwired.EventSplit

@[expose] public section

/-!
# leanSPHINCS's canonical game of a parallel adversary, with rounds

The canonical game `gameR pol (serialize Ap) p v` of the serialization of a parallel adversary
`Ap` runs each round of `w` permutation calls as the simulation of its calls in order.
`gameRPar Ap pol p v` is the same game over `parSpec (recHwSpec ..) (portR ..)` where each round is
the lifted lockstep round `lockRoundR`. Since the sponge parts of runtime 2 and runtime 1 with
record ports read their functions in the basis of the compression (leanXMSS's
`isReadRuntime_runtimeR`, `isReadRuntime_runtime1R`), both games have the same run against the
runtime and its parallel runtime (the port of leanXMSS's `Depth.Sim`).

* Commands: `cmdR` (the realized command of the sequential challenger), `advSubstR` (the
  challenged parallel adversary), `cmdR_permPar` (a serialized round is the lifted simulation).
* Games: `prefixRPar`, `gameRPar`; `prefixR_serialize`.
* Runs: `run_prefixRPar_eq`, `run_gameRPar_eq`, `p1R_eq_par`, `p2R_eq_par`,
  `eventWeight_prefixRPar_eq`.
* Weights vanishing on the sponge ports: `totalWeight_prefixRPar_eq`, `totalWeight_gameRPar_eq`,
  `twPR_eq_par`, `readMass_gameRPar_eq`.
* Charges: `isChargeBound_prefixRPar`, `isChargeBound_gameRPar` (generic); the prefix's calls of
  `h` (`prefixRPar_hWidth`, `prefixRPar_hDepth`), of `k` and `k'` (`prefixRPar_capWidth`),
  classical (`prefixRPar_cls`), mixed rounds (`prefixRPar_mixed`); `spongeRounds_gameRPar` (at
  most `10 min d q`).
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Sphincs Common Common.SufCma
open HashSig (Message)
open Quantum.Xmss (X Z keccakStateEquiv)
open Quantum.Xmss.Hybrid (readMass)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR runtime1R realizeT readLift revealThen
  RevealVals realizeT_bind realizeT_bind₂ realizeT_substitute substitute_substitute
  isReadRuntime_runtimeR isReadRuntime_runtime1R bind_eq_self_of portR extWeight extCls chg_map
  chg_readsProgram)

namespace Quantum.Sphincs.Assembly

/-- leanSPHINCS's parallel adversary over the sponge's state. -/
abbrev SAdversaryPar : Type 1 :=
  Quantum.SufCma.AdversaryPar PublicKey Message (Option Signature) Forgery (X × Z)

set_option quotPrecheck false in
-- The signing transcript.
local notation "SLog" => Quantum.SufCma.SignLog Message (Option Signature)

set_option quotPrecheck false in
-- The parallel adversary's commands.
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z))

set_option quotPrecheck false in
-- The signature of the parallel game: runtime 2's ports with record ports, and rounds.
local notation "ParR" => parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)

set_option quotPrecheck false in
-- The permutation calls as the adversary's.
local notation "PermL" => (Quantum.SufCma.permLens (Req := Message)
  (Resp := Option Signature) (S := X × Z) (L := LocalSig.instruments.{0}))

/-! ## The serialized game, command by command -/

section cmd

variable (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)

/-- A program over the sponge ports, as a template of runtime 1 realized at `v`: the lifted
program. -/
theorem realizeT_readLift_liftOrdinary {W : QReg → Type} {A : QReg}
    (z : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W A) :
    realizeT v (readLift (S := HPos) (D := XD) (M := Selections) goodAll
      (z.liftOrdinary (t := hwReadCmdSpec X Z Selections))) =
        IFreeM.mapLens (hwLens X Z (Mem HPos) (recSpec HPos Selections)) z := by
  induction z using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih => exact congrArg (QuantumComp.primBind o) (funext ih)
  | queryBind _ i E ℓ k ih =>
    exact congrArg (QuantumComp.queryBind (spec := recHwSpec X Z HPos Selections)
      (.inl (.inl (.inl i))) E ℓ) (funext ih)

/-- The challenger of runtime 2, realized, on a permutation call or local operation: the lifted
simulation. -/
theorem realizeT_substitute_challengeT_permLens (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (qrpmSpec (X × Z))).A A) :
    realizeT v (IFreeM.substitute (challengeT Selections cwUpd pol p)
      (IPFunctor.Lens.toSubstitution PermL A c)) =
      IFreeM.mapLens (hwLens X Z (Mem HPos) (recSpec HPos Selections))
        (simSubst LocalSig.Interp.instruments p.perm A c) := by
  rcases c with o | ⟨q, E, ℓ⟩
  · have h1 : IFreeM.substitute (challengeT Selections cwUpd pol p)
        (IPFunctor.Lens.toSubstitution PermL A
          (.prim o)) = challengeT Selections cwUpd pol p A (.prim o) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    have h2 : simulate LocalSig.Interp.instruments p.perm
        (Quantum.SufCma.challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv
          (0 : SecretKey) A (.prim o)) =
          simSubst LocalSig.Interp.instruments p.perm A (.prim o) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    exact (congrArg (realizeT v) h1).trans
      ((realizeT_readLift_liftOrdinary _ _).trans (congrArg _ h2))
  · have h1 : IFreeM.substitute (challengeT Selections cwUpd pol p)
        (IPFunctor.Lens.toSubstitution PermL A
          (.query q E ℓ)) = challengeT Selections cwUpd pol p A (.query (.perm q) E ℓ) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    have h2 : simulate LocalSig.Interp.instruments p.perm
        (Quantum.SufCma.challenge RandomPermutationModel.sufCmaScheme keccakStateEquiv
          (0 : SecretKey) A (.query (.perm q) E ℓ)) =
          simSubst LocalSig.Interp.instruments p.perm A (.query q E ℓ) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    exact (congrArg (realizeT v) h1).trans
      ((realizeT_readLift_liftOrdinary _ _).trans (congrArg _ h2))

/-- **The challenger of runtime 2, realized, on a permutation program**: the lifted
simulation. -/
theorem realizeT_challengeT_mapLens_permLens {W : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (qrpmSpec (X × Z)) W A) :
    realizeT v (IFreeM.substitute (challengeT Selections cwUpd pol p)
      (IFreeM.mapLens PermL y)) =
      IFreeM.mapLens (hwLens X Z (Mem HPos) (recSpec HPos Selections))
        (simulate LocalSig.Interp.instruments p.perm y) := by
  have hy := (IFreeM.substitute_toSubstitution PermL
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (qrpmSpec (X × Z))) W A)).symm
  refine (congrArg (fun z ↦ realizeT v (IFreeM.substitute
    (challengeT Selections cwUpd pol p) z)) hy).trans ?_
  refine (congrArg (realizeT v) (substitute_substitute _ _ _)).trans ?_
  refine (realizeT_substitute _ _ _).trans ?_
  refine Eq.trans ?_ (IFreeM.substitute_toSubstitution
    (hwLens X Z (Mem HPos) (recSpec HPos Selections))
    (simulate LocalSig.Interp.instruments p.perm y))
  refine Eq.trans ?_ (substitute_substitute _ _ _).symm
  exact congrArg (fun σ ↦ IFreeM.substitute σ y) (funext fun A ↦ funext fun c ↦
    (realizeT_substitute_challengeT_permLens pol p v A c).trans
      (IFreeM.substitute_toSubstitution _ _).symm)

/-- **The realized command of the serialized adversary**: the challenger of runtime 2 on the
serialization of a parallel command. -/
noncomputable def cmdR (A : QReg) (c : (AdvPP).A A) :
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos Selections))
      (fun t ↦ {b : (AdvPP).B A c // (AdvPP).src A c b = t}) A :=
  realizeT v (IFreeM.substitute (challengeT Selections cwUpd pol p) (Quantum.SufCma.toSeq A c))

/-- **A serialized round, realized**: the lifted simulation of its calls in order. -/
theorem cmdR_permPar {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z)).In
      (.permPar w dir) × E) :
    cmdR pol p v A (.query (.permPar w dir) E ℓ) =
      QuantumComp.bind (IFreeM.mapLens (hwLens X Z (Mem HPos) (recSpec HPos Selections))
        (simulate LocalSig.Interp.instruments p.perm
          (seqCalls (spec := qrpmSpec (X × Z)) dir E
            (B := QReg.of ((Quantum.SufCma.advSpecPar Message (Option Signature)
              (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _))))
        fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩ :=
  (congrArg (realizeT v) (IFreeM.substitute_bind _ _ _)).trans
    ((realizeT_bind _ _ _).trans (congrArg (fun z ↦ QuantumComp.bind z _)
      ((congrArg (fun z ↦ realizeT v (IFreeM.substitute
        (challengeT Selections cwUpd pol p) z))
        (Quantum.SufCma.mapLens_permLens_seqCalls dir E ℓ _).symm).trans
        (realizeT_challengeT_mapLens_permLens pol p v _))))

/-- **The challenged parallel adversary**: a round of permutation calls is the lifted lockstep
round with rounds (`lockRoundR`); a local operation or signing request is the realized command
of the sequential challenger. -/
noncomputable def advSubstR :
    CommandSubstitution AdvPP (QuantumComp.toIPFunctor LocalSig.instruments.{0} ParR)
  | A, .prim o => QuantumComp.liftOrdinary (cmdR pol p v A (.prim o))
  | _, .query (.permPar w dir) E ℓ =>
      QuantumComp.bind (IFreeM.mapLens (hwParLens X Z (Mem HPos) (recSpec HPos Selections))
        (lockRoundR p.perm dir
          (B := QReg.of ((Quantum.SufCma.advSpecPar Message (Option Signature)
            (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _)))
        fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩
  | A, .query (.sign r) E ℓ => QuantumComp.liftOrdinary (cmdR pol p v A (.query (.sign r) E ℓ))

end cmd

/-! ## The games with rounds -/

section game

variable (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)

/-- The public key's reveal, realized at `v`. -/
noncomputable def pkRevealR :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      (RevealVals XD {.val rootPos} × (Finset HPos × Selections)) :=
  realizeT v (revealThen (M := Selections) (B := QReg.of Unit) goodAll {.val rootPos}
    QuantumComp₂.pure)

/-- The challenged serialized adversary with its transcript, realized, command by command. -/
noncomputable def advSeqR {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z)) A B α) :
    QComp (recHwSpec X Z HPos Selections) A B (α × SLog) :=
  IFreeM.substitute (cmdR pol p v)
    (Quantum.SufCma.logSignsPerm (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])

/-- **The challenged parallel adversary with its transcript**, with rounds. -/
noncomputable def advParR {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z)) A B α) :
    QComp ParR A B (α × SLog) :=
  IFreeM.substitute (advSubstR pol p v)
    (Quantum.SufCma.logSignsPerm (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])

/-- **The challenge prefix of a parallel adversary, with rounds**: the public key's reveal, then
the challenged parallel adversary with its transcript. -/
noncomputable def prefixRPar (Ap : SAdversaryPar) (pol : DigestPolicy) (p : Pub)
    (v : (s : HPos) → XD s) :
    QComp ParR (QReg.of Unit) (QReg.of Unit)
      (PublicKey × (Forgery × SLog)) :=
  QuantumComp₂.bind (QuantumComp.liftOrdinary (t := roundSpec (recHwSpec X Z HPos Selections)
    (portR X Z HPos Selections)) (pkRevealR v)) fun r₀ ↦
      (advParR pol p v (Ap (pkOf p r₀.1))).bind fun run ↦ QuantumComp₂.pure (pkOf p r₀.1, run)

/-- **The canonical game of a parallel adversary, with rounds**: the prefix, then the
verification. -/
noncomputable def gameRPar (Ap : SAdversaryPar) (pol : DigestPolicy) (p : Pub)
    (v : (s : HPos) → XD s) : QComp ParR (QReg.of Unit) (QReg.of Unit) Bool :=
  (prefixRPar Ap pol p v).bind fun pre ↦ QuantumComp.liftOrdinary
    (t := roundSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections))
    (realizeT v (verifyT Selections p pre))

variable (Ap : SAdversaryPar)

/-- **The challenge prefix of the serialization**, command by command. -/
theorem prefixR_serialize :
    prefixR pol (Quantum.SufCma.serialize Ap) p v =
      (pkRevealR v).bind fun r₀ ↦
        (advSeqR pol p v (Ap (pkOf p r₀.1))).bind fun run ↦
          QuantumComp₂.pure (pkOf p r₀.1, run) := by
  have h1 : prefixT Selections cwUpd pol p (Quantum.SufCma.serialize Ap) =
      (revealThen (M := Selections) (B := QReg.of Unit) goodAll {.val rootPos}
        QuantumComp₂.pure).bind fun r₀ ↦
        (challengedT Selections cwUpd pol p
          (Quantum.SufCma.withSignLog (Quantum.SufCma.serialize Ap (pkOf p r₀.1)))).bind
          fun run ↦ QuantumComp₂.pure (pkOf p r₀.1, run) :=
    rfl
  refine ((congrArg (realizeT v) h1).trans (realizeT_bind₂ _ _ _)).trans ?_
  refine congrArg (QuantumComp₂.bind _) (funext fun r₀ ↦ ?_)
  refine (realizeT_bind₂ _ _ _).trans (congrArg (fun z ↦ QuantumComp₂.bind z _) ?_)
  refine (congrArg (fun z ↦ realizeT v (IFreeM.substitute
    (challengeT Selections cwUpd pol p) z))
      (Quantum.SufCma.logSigns_substitute_toSeq' _ (Ap (pkOf p r₀.1)) [])).trans ?_
  exact (congrArg (realizeT v) (substitute_substitute _ _ _)).trans
    (realizeT_substitute _ _ _)

end game

/-! ## The runs -/

section run

variable (R : QuantumRuntime (recHwSpec X Z HPos Selections)) {U : Matrix R.D R.D ℂ}
  (hU : U ∈ unitaryGroup R.D ℂ) {rd : R.D → SpongeKeys X Z}
  (hR : IsReadRuntime (hwPart (recSpec HPos Selections) R) U rd)
  (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
include hU hR

/-- **A serialized round, lifted, against a read runtime**: the lifted lockstep round. -/
theorem branch_lift_simulate_eq_lockRoundR {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z)).In
      (.permPar w dir) × E) (rs : RoundResult (qrpmSpec (X × Z)) dir) :
    (R.run₂ .instruments (IFreeM.mapLens (hwLens X Z (Mem HPos) (recSpec HPos Selections))
      (simulate LocalSig.Interp.instruments p.perm
        (seqCalls (spec := qrpmSpec (X × Z)) dir E
          (B := QReg.of ((Quantum.SufCma.advSpecPar Message (Option Signature)
            (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _))))).branch rs =
      ((R.par (portR X Z HPos Selections)).run₂ .instruments
        (IFreeM.mapLens (hwParLens X Z (Mem HPos) (recSpec HPos Selections))
          (lockRoundR p.perm dir
            (B := QReg.of ((Quantum.SufCma.advSpecPar Message (Option Signature)
              (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _)))).branch () := by
  have h1 := run₂_mapLens_hwLens (recSpec HPos Selections) R .instruments
    (simulate LocalSig.Interp.instruments p.perm
        (seqCalls (spec := qrpmSpec (X × Z)) dir E
          (B := QReg.of ((Quantum.SufCma.advSpecPar Message (Option Signature)
            (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _)))
  have h2 := run₂_mapLens_hwParLens (recSpec HPos Selections) R .instruments
    (lockRoundR p.perm dir
      (B := QReg.of ((Quantum.SufCma.advSpecPar Message (Option Signature)
        (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _))
  have h3 := branch_run₂_simulate_seqCalls_eq_lockRoundR (hwPart (recSpec HPos Selections) R) U
    hU rd hR p.perm dir E ℓ
      (B := QReg.of ((Quantum.SufCma.advSpecPar Message (Option Signature)
        (X × Z)).Out (.permPar w dir) × E)) (Equiv.refl _) rs
  exact ((congrArg (fun P ↦ DSubInstrument.branch P rs) h1).trans h3).trans
    (congrArg (fun P ↦ DSubInstrument.branch P ()) h2).symm

/-- **Command by command**, the challenged parallel adversary runs as the serialized one, against
a runtime whose sponge part reads its functions in the basis of a unitary. -/
theorem run_cmdR_eq (A : QReg) (c : (AdvPP).A A) :
    R.run .instruments (cmdR pol p v A c) =
      (R.par (portR X Z HPos Selections)).run .instruments (advSubstR pol p v A c) := by
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact (R.run_liftOrdinary .instruments _ _).symm
  · have : Unique (RoundResult (qrpmSpec (X × Z)) dir) := inferInstanceAs (Unique (Fin w → Unit))
    refine (congrArg (R.run .instruments) (cmdR_permPar pol p v dir E ℓ)).trans ?_
    exact run_bind_leaf_eq_par (portR X Z HPos Selections) R
      (Y := fun t ↦ {b : (AdvPP).B A (.query (.permPar w dir) E ℓ) //
        (AdvPP).src A (.query (.permPar w dir) E ℓ) b = t})
      (fun u h ↦ ⟨ULift.up (), h⟩) _ _
      (branch_lift_simulate_eq_lockRoundR R hU hR p dir E ℓ default)
  · exact (R.run_liftOrdinary .instruments _ _).symm

/-- The challenged parallel adversary runs as the serialized one. -/
theorem run_advParR_eq {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z)) A B α) :
    R.run .instruments (advSeqR pol p v x) =
      (R.par (portR X Z HPos Selections)).run .instruments (advParR pol p v x) :=
  run_substitute_eq_par (portR X Z HPos Selections) R (cmdR pol p v) (advSubstR pol p v)
    (run_cmdR_eq R hU hR pol p v) _

variable (Ap : SAdversaryPar)

/-- **The challenge prefix with rounds runs as the prefix of the serialization.** -/
theorem run_prefixRPar_eq :
    R.run .instruments (prefixR pol (Quantum.SufCma.serialize Ap) p v) =
      (R.par (portR X Z HPos Selections)).run .instruments (prefixRPar Ap pol p v) := by
  rw [prefixR_serialize]
  exact run_bind₂_liftOrdinary_par (portR X Z HPos Selections) R (pkRevealR v) fun r₀ ↦
    run_bind₂_eq_par (portR X Z HPos Selections) R (run_advParR_eq R hU hR pol p v _) fun run ↦
      (R.run_pure _ _).trans ((R.par (portR X Z HPos Selections)).run_pure _ _).symm

/-- **The game with rounds runs as the game of the serialization.** -/
theorem run_gameRPar_eq :
    R.run .instruments (gameR pol (Quantum.SufCma.serialize Ap) p v) =
      (R.par (portR X Z HPos Selections)).run .instruments (gameRPar Ap pol p v) := by
  rw [gameR_eq]
  exact run_bind₂_eq_par (portR X Z HPos Selections) R (run_prefixRPar_eq R hU hR pol p v Ap)
    fun _ ↦ (R.run_liftOrdinary .instruments _ _).symm

end run

section runs

variable (Ap : SAdversaryPar) (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)

/-- `run_gameRPar_eq` against runtime 2 with record ports. -/
theorem run_gameRPar_eq_runtimeR (m₀ : Mem HPos) :
    (runtimeR m₀).run .instruments (gameR pol (Quantum.SufCma.serialize Ap) p v) =
      ((runtimeR m₀).par (portR X Z HPos Selections)).run .instruments (gameRPar Ap pol p v) :=
  run_gameRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m₀) pol p v Ap

/-- `run_gameRPar_eq` against runtime 1 with record ports. -/
theorem run_gameRPar_eq_runtime1R (Lt : Hw X Z) (m₀ : Mem HPos) :
    (runtime1R X Z Lt m₀).run .instruments (gameR pol (Quantum.SufCma.serialize Ap) p v) =
      ((runtime1R X Z Lt m₀).par (portR X Z HPos Selections)).run .instruments
        (gameRPar Ap pol p v) :=
  run_gameRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtime1R Lt m₀) pol p v Ap

/-- `run_prefixRPar_eq` against runtime 2 with record ports. -/
theorem run_prefixRPar_eq_runtimeR (m₀ : Mem HPos) :
    (runtimeR m₀).run .instruments (prefixR pol (Quantum.SufCma.serialize Ap) p v) =
      ((runtimeR m₀).par (portR X Z HPos Selections)).run .instruments (prefixRPar Ap pol p v) :=
  run_prefixRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m₀) pol p v Ap

/-- The game's winning distribution against runtime 2, with rounds. -/
theorem p2R_eq_par :
    p2R pol (Quantum.SufCma.serialize Ap) p v =
      ((runtimeR m0R).par (portR X Z HPos Selections)).evalDistMap .instruments
        (gameRPar Ap pol p v) (SubState.basis ()) winObs {true} := by
  unfold p2R
  rw [evalDistMap_par_eq (portR X Z HPos Selections) _ (run_gameRPar_eq_runtimeR Ap pol p v m0R)]

/-- The game's winning distribution against runtime 1, with rounds. -/
theorem p1R_eq_par (Lt : HonestTable → Hw X Z) (L : HonestTable) :
    p1R (Quantum.SufCma.serialize Ap) Lt L =
      ((runtime1R X Z (Lt L) m0R).par (portR X Z HPos Selections)).evalDistMap .instruments
        (gameRPar Ap msgPol (pubOf L) (valueAt L)) (SubState.basis ()) winObs {true} := by
  unfold p1R
  rw [evalDistMap_par_eq (portR X Z HPos Selections) _
    (run_gameRPar_eq_runtime1R Ap msgPol (pubOf L) (valueAt L) (Lt L) m0R)]

/-- The prefix's event weight against runtime 2, with rounds. -/
theorem eventWeight_prefixRPar_eq (P : Matrix (HwReg X Z (Mem HPos)) (HwReg X Z (Mem HPos)) ℂ)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
      (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ) :
    (runtimeR m0R).eventWeight .instruments P (prefixR pol (Quantum.SufCma.serialize Ap) p v) ρ =
      ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight .instruments P
        (prefixRPar Ap pol p v) ρ :=
  eventWeight_par_eq (portR X Z HPos Selections) _
    (run_prefixRPar_eq_runtimeR Ap pol p v m0R) P ρ

end runs

/-! ## Weights vanishing on the sponge ports -/

section weight

variable (R : QuantumRuntime (recHwSpec X Z HPos Selections)) {U : Matrix R.D R.D ℂ}
  (hU : U ∈ unitaryGroup R.D ℂ) {rd : R.D → SpongeKeys X Z}
  (hR : IsReadRuntime (hwPart (recSpec HPos Selections) R) U rd)
  (W : ∀ i, Matrix ((recHwSpec X Z HPos Selections).In i × R.D)
    ((recHwSpec X Z HPos Selections).In i × R.D) ℂ → ℝ≥0∞)
  (hW : ∀ p σ, W (portR X Z HPos Selections p) σ = 0)
  (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
include hU hR hW

/-- **Command by command**, the challenged parallel adversary has the weights of the serialized
one, for continuations of the same weights. -/
theorem totalWeight_cmdR_bind_eq (A : QReg) (c : (AdvPP).A A) {Y : QReg → Type}
    (k₁ : ∀ u, {b : (AdvPP).B A c // (AdvPP).src A c b = u} →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Y u)
    (k₂ : ∀ u, {b : (AdvPP).B A c // (AdvPP).src A c b = u} →
      QuantumComp LocalSig.instruments.{0} ParR Y u)
    (hk : ∀ u b ρ, R.totalWeight .instruments W (k₁ u b) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (k₂ u b) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W ((cmdR pol p v A c).bind k₁) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) ((advSubstR pol p v A c).bind k₂) ρ := by
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact totalWeight_bind_liftOrdinary_par (portR X Z HPos Selections) R W _ k₁ k₂ hk ρ
  · have : Unique (RoundResult (qrpmSpec (X × Z)) dir) := inferInstanceAs (Unique (Fin w → Unit))
    refine (congrArg (fun z ↦ R.totalWeight .instruments W (QuantumComp.bind z k₁) ρ)
      (cmdR_permPar pol p v dir E ℓ)).trans ?_
    exact totalWeight_bind_leaf_eq_par (portR X Z HPos Selections) R W
      (N₁ := HwPorts X Z (Mem HPos) (recSpec HPos Selections))
      (N₂ := HwParPorts X Z (Mem HPos) (recSpec HPos Selections))
      (eq_zero_of_hwPorts (recSpec HPos Selections) hW)
      (parWeight_eq_zero_of (recSpec HPos Selections) hW)
      (Y := fun t ↦ {b : (AdvPP).B A (.query (.permPar w dir) E ℓ) //
        (AdvPP).src A (.query (.permPar w dir) E ℓ) b = t})
      (fun u h ↦ ⟨ULift.up (), h⟩) _ _
      (isThin_mapLens_hwLens _ (isThin_simulate _ _
        (isThin_seqCalls (spec := qrpmSpec (X × Z)) (N := fun _ ↦ True) dir
          (fun _ ↦ ⟨trivial, ⟨()⟩, inferInstanceAs (Subsingleton Unit)⟩) _ _ _)))
      (isThin_mapLens_hwParLens _ (isThin_lockRoundR _ _ _ _))
      (branch_lift_simulate_eq_lockRoundR R hU hR p dir E ℓ default) k₁ k₂ hk ρ
  · exact totalWeight_bind_liftOrdinary_par (portR X Z HPos Selections) R W _ k₁ k₂ hk ρ

/-- The challenged parallel adversary has the weights of the serialized one, for continuations of
the same weights. -/
theorem totalWeight_advParR_bind_eq {A B C : QReg} {α β : Type}
    (x : QComp (Quantum.SufCma.advSpecPar Message (Option Signature) (X × Z)) A B α)
    (k₁ : α × SLog →
      QComp (recHwSpec X Z HPos Selections) B C β)
    (k₂ : α × SLog → QComp ParR B C β)
    (hk : ∀ a ρ, R.totalWeight .instruments W (k₁ a) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (k₂ a) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W ((advSeqR pol p v x).bind k₁) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) ((advParR pol p v x).bind k₂) ρ :=
  totalWeight_substitute_bind_eq_par (portR X Z HPos Selections) R (cmdR pol p v)
    (advSubstR pol p v) W
    (fun A c _ k₁ k₂ hk ρ ↦ totalWeight_cmdR_bind_eq R hU hR W hW pol p v A c k₁ k₂ hk ρ) _ _ _
    (fun u q ρ' ↦ by
      rcases q with ⟨rfl, a⟩
      exact hk a ρ') ρ

variable (Ap : SAdversaryPar)

/-- **The prefix with rounds has the weights of the prefix of the serialization**, for
continuations of the same weights. -/
theorem totalWeight_prefixRPar_bind_eq {β : Type}
    (k₁ : PublicKey × (Forgery × SLog) →
      QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) β)
    (k₂ : PublicKey × (Forgery × SLog) →
      QComp ParR (QReg.of Unit) (QReg.of Unit) β)
    (hk : ∀ a ρ, R.totalWeight .instruments W (k₁ a) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (k₂ a) ρ)
    (ρ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ) :
    R.totalWeight .instruments W ((prefixR pol (Quantum.SufCma.serialize Ap) p v).bind k₁) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) ((prefixRPar Ap pol p v).bind k₂) ρ := by
  rw [prefixR_serialize]
  refine (congrArg (fun z ↦ R.totalWeight .instruments W z ρ)
    (QuantumComp₂.bind_assoc _ _ _)).trans (Eq.trans ?_ (congrArg (fun z ↦
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) z ρ) (QuantumComp₂.bind_assoc _ _ _)).symm)
  refine totalWeight_bind₂_liftOrdinary_par (portR X Z HPos Selections) R W (pkRevealR v)
    (fun r₀ ρ' ↦ ?_) ρ
  refine (congrArg (fun z ↦ R.totalWeight .instruments W z ρ')
    (QuantumComp₂.bind_assoc _ _ _)).trans (Eq.trans ?_ (congrArg (fun z ↦
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) z ρ') (QuantumComp₂.bind_assoc _ _ _)).symm)
  exact totalWeight_advParR_bind_eq R hU hR W hW pol p v _ _ _ (fun a ρ'' ↦ hk _ ρ'') ρ'

/-- **The prefix with rounds has the weights of the prefix of the serialization.** -/
theorem totalWeight_prefixRPar_eq (ρ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ) :
    R.totalWeight .instruments W (prefixR pol (Quantum.SufCma.serialize Ap) p v) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (prefixRPar Ap pol p v) ρ := by
  have h := totalWeight_prefixRPar_bind_eq R hU hR W hW pol p v Ap QuantumComp₂.pure
    QuantumComp₂.pure (fun a ρ' ↦ (R.totalWeight_pure _ _ ρ').trans
      ((R.par (portR X Z HPos Selections)).totalWeight_pure _ _ ρ').symm) ρ
  rwa [QuantumComp₂.bind_pure, QuantumComp₂.bind_pure] at h

/-- **The game with rounds has the weights of the game of the serialization.** -/
theorem totalWeight_gameRPar_eq (ρ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ) :
    R.totalWeight .instruments W (gameR pol (Quantum.SufCma.serialize Ap) p v) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (gameRPar Ap pol p v) ρ := by
  rw [gameR_eq]
  exact totalWeight_prefixRPar_bind_eq R hU hR W hW pol p v Ap _ _
    (fun a ρ' ↦ (totalWeight_liftOrdinary_par (portR X Z HPos Selections) R W _ ρ').symm) ρ

end weight

section weights

variable (Ap : SAdversaryPar) (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)

/-- **The prefix's classical costs, with rounds** (CostRefined's `twPR`). -/
theorem twPR_eq_par :
    twPR pol (Quantum.SufCma.serialize Ap) p v =
      ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref p v) (dPof p v))))
        (prefixRPar Ap pol p v) initR :=
  totalWeight_prefixRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m0R) _
    (fun _ _ ↦ rfl) pol p v Ap initR

/-- **The game's hidden mass at the classical ports, with rounds.** -/
theorem readMass_gameRPar_eq (Hh : Set Z) (Hk Hk' : Set X) :
    (runtimeR m0R).totalWeight .instruments (readMass Hh Hk Hk')
        (gameR pol (Quantum.SufCma.serialize Ap) p v) initR =
      ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) (readMass Hh Hk Hk')) (gameRPar Ap pol p v)
        initR :=
  totalWeight_gameRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m0R) _
    (fun _ _ ↦ rfl) pol p v Ap initR

end weights

/-! ## Charges -/

/-- The charge of a parallel adversary's command: `f w` for a round of width `w`, `S` for a
signing request. -/
def lockAdvCharge (f : ℕ → ℕ) (S : ℕ) : Quantum.SufCma.AdvPortPar Message → ℕ
  | .permPar w _ => f w
  | .sign _ => S

section charges

variable (κ : (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)).Port → ℕ)
  {a b c d : ℕ}

/-- A program over runtime 2's ports with record ports, as a program with rounds: charges below
`rCharge` on the single calls. -/
theorem isChargeBound_liftOrdinary_rCharge
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections a b c d i) {Y : QReg → Type} {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Y A} {m : ℕ}
    (h : IFreeM.IsChargeBound x (portCharge (rCharge Selections a b c d)) m) :
    IFreeM.IsChargeBound (QuantumComp.liftOrdinary
      (t := roundSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)) x)
      (callCharge κ) m :=
  IFreeM.IsChargeBound.mapLens (c := callCharge κ) QuantumComp.ordinaryLens
    (isChargeBound_of_charge_le (fun _ cmd ↦ by
      rcases cmd with o | ⟨i, E, ℓ⟩
      · exact le_rfl
      · exact hinl i) h)

variable {S : ℕ} (hS : signCalls b c d ≤ S) (pol : DigestPolicy) (p : Pub)
  (v : (s : HPos) → XD s)

include hS in
/-- The realized command of a local operation or signing request: the charges of the sequential
challenger. -/
theorem isChargeBound_cmdR (A : QReg) (c₀ : (AdvPP).A A)
    (hc₀ : ∀ w dir E ℓ, c₀ ≠ .query (.permPar w dir) E ℓ) :
    IFreeM.IsChargeBound (cmdR pol p v A c₀) (portCharge (rCharge Selections a b c d))
      (Quantum.SufCma.cmdChargePar (lockAdvCharge (fun _ ↦ 0) S) A c₀) := by
  refine isChargeBound_realizeT a b c d v (IFreeM.IsChargeBound.substitute _
    (chg_challengeT a b c d cwUpd pol p (S := S) fun B msg ↦
      (chg_signT a b c d cwUpd pol p B msg).mono hS) ?_)
  rcases c₀ with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact ⟨by simp [advCharge, Quantum.SufCma.cmdCharge], fun _ ↦ trivial⟩
  · exact absurd rfl (hc₀ w dir E ℓ)
  · exact ⟨by simp [advCharge, Quantum.SufCma.cmdCharge, Quantum.SufCma.permCharge,
      Quantum.SufCma.signCharge, Quantum.SufCma.cmdChargePar, lockAdvCharge], fun _ ↦ trivial⟩

variable (f : ℕ → ℕ)
  (hround : ∀ {w : ℕ} (dir : Fin w → PermutationPort),
    lockCharge (fun i ↦ κ (hwParPort X Z (Mem HPos) (recSpec HPos Selections) i)) dir ≤ f w)
  (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections a b c d i)

include hS hround hinl in
/-- **The charges of the challenged parallel adversary's commands**: `f w` for a round of width
`w` (the lifted lockstep round), the sequential challenger's for the others. -/
theorem isChargeBound_advSubstR (A : QReg) (c₀ : (AdvPP).A A) :
    IFreeM.IsChargeBound (advSubstR pol p v A c₀) (callCharge κ)
      (Quantum.SufCma.cmdChargePar (lockAdvCharge f S) A c₀) := by
  rcases c₀ with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact isChargeBound_liftOrdinary_rCharge κ hinl
      (isChargeBound_cmdR hS pol p v A (.prim o) fun _ _ _ _ h ↦ by cases h)
  · exact IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (n₂ := 0)
      (isChargeBound_mapLens_hwParLens _ κ ((isChargeBound_lockRoundR _ _ dir ℓ _).mono
        (hround dir))) fun _ _ ↦ trivial) (Nat.add_zero _).le
  · exact isChargeBound_liftOrdinary_rCharge κ hinl
      (isChargeBound_cmdR hS pol p v A (.query (.sign r) E ℓ) fun _ _ _ _ h ↦ by cases h)

variable (Ap : SAdversaryPar) {n : ℕ}
  (hA : ∀ pk, IFreeM.IsChargeBound (Ap pk) (Quantum.SufCma.cmdChargePar (lockAdvCharge f S)) n)

include hS hround hinl hA in
/-- **The charges of the prefix with rounds**: the root's reveal, and the parallel adversary's
commands at their charges. -/
theorem isChargeBound_prefixRPar :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v) (callCharge κ) (d + n) := by
  have hrev' : IFreeM.IsChargeBound (revealThen (M := Selections) (B := QReg.of Unit) goodAll
      {.val rootPos} QuantumComp₂.pure) (portCharge (tCharge Selections a b c d)) (d + 0) :=
    chg_revealThen a b c d {.val rootPos} QuantumComp₂.pure (n := 0) fun _ ↦
      IFreeM.isChargeBound_pure _ 0
  have hrev : IFreeM.IsChargeBound (pkRevealR v) (portCharge (rCharge Selections a b c d)) d :=
    IFreeM.IsChargeBound.mono (isChargeBound_realizeT a b c d v hrev') (Nat.add_zero d).le
  unfold prefixRPar
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := n + 0)
    (isChargeBound_liftOrdinary_rCharge κ hinl hrev) fun r₀ ↦ ?_) (by omega)
  exact FreeM₂.isChargeBound_bind (n₂ := 0)
    (IFreeM.IsChargeBound.substitute (advSubstR pol p v)
      (isChargeBound_advSubstR κ hS pol p v f hround hinl)
      (Quantum.SufCma.isChargeBound_logSignsPerm _ _ [] (hA _))) fun _ ↦
    IFreeM.isChargeBound_pure _ 0

include hS hround hinl hA in
/-- **The charges of the game with rounds**: the prefix's and the verification's reads. -/
theorem isChargeBound_gameRPar :
    IFreeM.IsChargeBound (gameRPar Ap pol p v) (callCharge κ) (d + n + 3 * b * verifyBlocks) := by
  have hv : ∀ pre : PublicKey × (Forgery × SLog),
      IFreeM.IsChargeBound (verifyT Selections p pre) (portCharge (tCharge Selections a b c d))
        (3 * b * verifyBlocks) := fun pre ↦ by
    unfold verifyT
    exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (isChargeBound_readLift a b c d (chg_map _ Prod.fst
        (chg_readsProgram (M := Selections) a b p.perm (QReg.of Unit)
          (verify_hashBlocks pre.1 pre.2.1)))) fun _ ↦ trivial) (Nat.add_zero _).le
  exact FreeM₂.isChargeBound_bind (isChargeBound_prefixRPar κ hS pol p v f hround hinl Ap hA)
    fun pre ↦ isChargeBound_liftOrdinary_rCharge κ hinl
      (isChargeBound_realizeT a b c d v (hv pre))

end charges

/-! ## The charges from the parallel adversary's budgets -/

/-- The prefix's classical calls fit the game's. -/
theorem cls_budget_le (x y : ℕ) : 1 + x ≤ 1 + ((6 * 0 * 0 + x) + y) := by
  omega

section budgets

variable (Ap : SAdversaryPar) {q d : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.widthCharge) q)
  (hd : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)

include hq in
/-- Width budgets of the parallel adversary. -/
theorem isChargeBound_lockAdv_width (C : ℕ) (pk : PublicKey) :
    IFreeM.IsChargeBound (Ap pk)
      (Quantum.SufCma.cmdChargePar (lockAdvCharge (fun w ↦ C * w) 0)) (C * q) :=
  isChargeBound_of_charge_le (fun _ cmd ↦ by
    rcases cmd with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩ <;>
      simp [Quantum.SufCma.cmdChargePar, lockAdvCharge, Quantum.SufCma.widthCharge])
    ((hq pk).mul C)

include hq hd in
/-- Depth budgets of the parallel adversary: rounds of positive width, at most `min d q`. -/
theorem isChargeBound_lockAdv_depth (C : ℕ) (pk : PublicKey) :
    IFreeM.IsChargeBound (Ap pk)
      (Quantum.SufCma.cmdChargePar (lockAdvCharge (fun w ↦ C * min 1 w) 0)) (C * min d q) :=
  isChargeBound_of_charge_le (fun _ cmd ↦ by
    rcases cmd with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩ <;>
      simp [Quantum.SufCma.cmdChargePar, lockAdvCharge])
    ((isChargeBound_min_of_le (c := Quantum.SufCma.cmdChargePar (lockAdvCharge (fun w ↦ min 1 w) 0))
      (fun _ cmd ↦ by
        rcases cmd with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩ <;>
          simp [Quantum.SufCma.cmdChargePar, lockAdvCharge, Quantum.SufCma.widthCharge,
            Quantum.SufCma.roundCharge])
      (hd pk) (hq pk)).mul C)

include hs in
/-- Signing budgets of the parallel adversary. -/
theorem isChargeBound_lockAdv_sign (S : ℕ) (pk : PublicKey) :
    IFreeM.IsChargeBound (Ap pk)
      (Quantum.SufCma.cmdChargePar (lockAdvCharge (fun _ ↦ 0) S)) (S * signatureLimit) :=
  isChargeBound_of_charge_le (fun _ cmd ↦ by
    rcases cmd with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩ <;>
      simp [Quantum.SufCma.cmdChargePar, lockAdvCharge, Quantum.SufCma.signChargePar])
    ((hs pk).mul S)

variable (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)
  (κ : (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)).Port → ℕ)

include hq in
/-- **Width charges of the prefix with rounds**: a port charge `c p` per call in a round, and no
classical charge, give `2 (c h + c k + c k') q`. -/
theorem isChargeBound_prefixRPar_width {K : ℕ} {c : SpongePort → ℕ}
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections K 0 0 0 i)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) ≤ m * c p) :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v) (callCharge κ)
      ((2 * c .h + 2 * c .k + 2 * c .k') * q) :=
  (isChargeBound_prefixRPar κ (a := K) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [signCalls, forsCalls, layerCalls]) pol p v _
    (fun dir ↦ lockCharge_le_width _ hκ dir) hinl Ap
    (isChargeBound_lockAdv_width Ap hq _)).mono (Nat.zero_add _).le

include hq hd in
/-- **Depth charges of the prefix with rounds**: a port charge `c p` per round of positive width,
and no classical charge, give `(2 c h + 4 c k + 4 c k') min d q`. -/
theorem isChargeBound_prefixRPar_depth {K : ℕ} {c : SpongePort → ℕ}
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections K 0 0 0 i)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) ≤ min 1 m * c p) :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v) (callCharge κ)
      ((2 * c .h + 4 * c .k + 4 * c .k') * min d q) :=
  (isChargeBound_prefixRPar κ (a := K) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [signCalls, forsCalls, layerCalls]) pol p v _
    (fun dir ↦ lockCharge_le_depth _ hκ dir) hinl Ap
    (isChargeBound_lockAdv_depth Ap hq hd _)).mono (Nat.zero_add _).le

include hs in
/-- **Classical charges of the prefix with rounds**: at most `clsCap`. -/
theorem isChargeBound_prefixRPar_cls
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections 0 1 1 1 i)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) = 0) :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v) (callCharge κ) clsCap :=
  (isChargeBound_prefixRPar κ (a := 0) (b := 1) (c := 1) (d := 1)
    (S := signCalls 1 1 1) le_rfl pol p v (fun _ ↦ 0)
    (fun dir ↦ by simp [lockCharge, subCharge, hwParPort, hκ]) hinl Ap
    (isChargeBound_lockAdv_sign Ap hs _)).mono (cls_budget_le _ (3 * 1 * verifyBlocks))

/-- **Charges vanishing on the prefix with rounds**: a charge vanishing on single calls and on
rounds of one port. -/
theorem isChargeBound_prefixRPar_zero (hinl : ∀ i, κ (.inl i) = 0)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) = 0) :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v) (callCharge κ) 0 :=
  isChargeBound_prefixRPar κ (a := 0) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [signCalls, forsCalls, layerCalls]) pol p v (fun _ ↦ 0)
    (fun dir ↦ by simp [lockCharge, subCharge, hwParPort, hκ])
    (fun i ↦ (hinl i).le.trans (Nat.zero_le _)) Ap (fun pk ↦ isChargeBound_of_charge_le
      (fun _ cmd ↦ by
        rcases cmd with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩ <;>
          simp [Quantum.SufCma.cmdChargePar, lockAdvCharge, portCharge])
      (isChargeBound_zero_portCharge (Ap pk)))

include hq hd in
/-- **The rounds of the game with rounds** (`spongeRounds`: single sponge calls and rounds of
positive width): at most `10 min d q`. -/
theorem spongeRounds_gameRPar :
    IFreeM.IsChargeBound (gameRPar Ap pol p v) (portCharge (spongeRounds
      (portR X Z HPos Selections) (extCls X Z (Mem HPos) (recSpec HPos Selections))))
      (10 * min d q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_gameRPar _ (a := 1) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [signCalls, forsCalls, layerCalls]) pol p v
    (fun w ↦ (2 * 1 + 4 * 1 + 4 * 1) * min 1 w)
    (fun dir ↦ lockCharge_le_depth _ (c := fun _ ↦ 1) (fun m p ↦ ?_) dir) (fun i ↦ ?_) Ap
    (isChargeBound_lockAdv_depth Ap hq hd _)).mono (by simp)
  · cases m <;> simp [spongeRounds, roundCharge, widthCharge, hwParPort, extCls, hwCls]
  · rcases i with ((i | c) | c) | T <;>
      simp [spongeRounds, roundCharge, widthCharge, extCls, hwCls, rCharge]

end budgets

/-! ## The prefix's charges for the event bound -/

section par

variable (Ap : SAdversaryPar) {q d : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.widthCharge) q)
  (hd : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.roundCharge) d)
  (hs : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) signatureLimit)
  (pol : DigestPolicy) (p : Pub) (v : (s : HPos) → XD s)

include hq in
/-- The prefix's calls of `h`: at most `2q`. -/
theorem prefixRPar_hWidth :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v)
      (portCharge (portWidth (portR X Z HPos Selections) .h)) (2 * q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_prefixRPar_width Ap hq pol p v _ (K := 1)
    (c := fun p ↦ if p = .h then 1 else 0) (fun i ↦ ?_) fun m p ↦ ?_).mono (by simp)
  · rcases i with ((p | c) | c) | j
    · change (if p = SpongePort.h then 1 else 0) ≤ 1
      split_ifs <;> simp
    all_goals exact Nat.zero_le _
  · rw [portWidth_round_const]
    cases p <;> simp

include hq hd in
/-- The prefix's rounds of `h`: at most `2 min d q`. -/
theorem prefixRPar_hDepth :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v)
      (portCharge (portDepth (portR X Z HPos Selections) .h)) (2 * min d q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_prefixRPar_depth Ap hq hd pol p v _ (K := 1)
    (c := fun p ↦ if p = .h then 1 else 0) (fun i ↦ ?_) fun m p ↦ ?_).mono (by simp)
  · rcases i with ((p | c) | c) | j
    · change (if (if p = SpongePort.h then 1 else 0) = 0 then 0 else 1) ≤ 1
      split_ifs <;> simp
    all_goals exact Nat.zero_le _
  · unfold portDepth
    rw [portWidth_round_const]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · cases p <;> simp
    · cases p <;> simp [Nat.min_eq_left hm, hm.ne']

include hq in
/-- The prefix's calls of `k` and `k'`: at most `4q`. -/
theorem prefixRPar_capWidth :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v)
      (portCharge (capWidth (portR X Z HPos Selections))) (4 * q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_prefixRPar_width Ap hq pol p v _ (K := 2)
    (c := fun p ↦ if p = .h then 0 else 1) (fun i ↦ ?_) fun m p ↦ ?_).mono (by simp)
  · rcases i with ((p | c) | c) | j
    · change (if p = SpongePort.k then 1 else 0) + (if p = SpongePort.k' then 1 else 0) ≤ 2
      split_ifs <;> simp
    all_goals exact Nat.zero_le _
  · rw [capWidth, portWidth_round_const, portWidth_round_const]
    cases p <;> simp

include hs in
/-- The prefix's classical calls: at most `clsCap`. -/
theorem prefixRPar_cls :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v) (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z (Mem HPos) (recSpec HPos Selections)))) clsCap := by
  rw [portCharge_eq_callCharge]
  refine isChargeBound_prefixRPar_cls Ap hs pol p v _ (fun i ↦ ?_) fun m p ↦
    clsCount_round (port := portR X Z HPos Selections) (cls := hwExtCls X Z (Mem HPos)
      (recSpec HPos Selections)) (fun _ ↦ rfl) m fun _ ↦ p
  rcases i with ((p | c) | c) | j <;> simp [clsCount, Par.widthCharge, hwExtCls, hwCls, rCharge]

/-- The prefix has no rounds mixing ports. -/
theorem prefixRPar_mixed :
    IFreeM.IsChargeBound (prefixRPar Ap pol p v)
      (portCharge (mixedRounds (portR X Z HPos Selections))) 0 := by
  rw [portCharge_eq_callCharge]
  exact isChargeBound_prefixRPar_zero Ap pol p v _ (fun _ ↦ rfl) fun m p ↦ by
    change (if (∀ _ : Fin m, p = .h) ∨ (∀ _ : Fin m, p = .k) ∨ (∀ _ : Fin m, p = .k')
      then 0 else 1) = 0
    cases p <;> simp

end par

end Quantum.Sphincs.Assembly

end
