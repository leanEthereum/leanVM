module

public import Quantum.Par.LockLift
public import Quantum.Par.LockstepRounds
public import Quantum.Xmss.Assembly.Security
public import Quantum.Xmss.Assembly.Depth.Ports
public import Quantum.SufCma.GamePar
public import Quantum.Sponge.Oracle.Hardwired.EventPar

@[expose] public section

/-!
# The canonical game of a parallel adversary, with rounds

The canonical game `gameR (serialize Ap) L` of the serialization of a parallel adversary `Ap` runs
each round of `w` permutation calls as the simulation of its calls in order. `gameRPar Ap L` is the
same game over `parSpec (recHwSpec ..) (portR ..)` where each round is the lifted lockstep round
`lockRoundR` (two rounds of `h`, eight of `k` or `k'`). Since the sponge parts of runtime 2 and
runtime 1 with record ports read their functions in the basis of the compression
(`isReadRuntime_runtimeR`, `isReadRuntime_runtime1R`), both games have the same run against the
runtime and its parallel runtime.

* Commands: `cmdR` (the realized command of the sequential challenger), `advSubstR` (the
  challenged parallel adversary), `cmdR_permPar` (a serialized round is the lifted simulation).
* Games: `prefixRPar`, `gameRPar`; `prefixR_serialize`.
* Runs: `run_prefixRPar_eq`, `run_gameRPar_eq` (and against `runtimeR`, `runtime1R`),
  `p1R_eq_par`, `p2R_eq_par`, `eventWeight_prefixRPar_eq`.
* Weights vanishing on the sponge ports: `totalWeight_prefixRPar_eq`, `totalWeight_gameRPar_eq`,
  `twPR_eq_par`, `readMass_gameRPar_eq`.
* Charges: `isChargeBound_prefixRPar`, `isChargeBound_gameRPar` (generic), the width, depth,
  classical and vanishing charges of the prefix, and `spongeRounds_gameRPar` (at most
  `10 min d q`). The verification is classical: its reads are among the classical charges.
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker

universe u v

/-! ## Signing transcripts of parallel adversaries and permutation calls -/

namespace Quantum.SufCma

open Quantum Quantum.Par

variable {Req Resp : Type} {S : Type} [Fintype S] [DecidableEq S]

/-- The transcript after a command of a parallel adversary answered `b`: a signing request
appends itself and its answer. -/
def logAfterPerm {L : LocalSig.{u, v}} {A : QReg} :
    (c : QuantumComp.Cmd L (advSpecPar Req Resp S) A) → c.Resp → SignLog Req Resp →
      SignLog Req Resp
  | .query (.sign r) _ _, b, log => log ++ [⟨r, b.down⟩]
  | _, _, log => log

/-- `logSigns` for parallel adversaries: the same commands, the transcript threaded along each
path and handed to the leaf map `leaf` at the end. -/
def logSignsPerm {L : LocalSig.{u, v}} {X : QReg → Type} {Y : QReg → Type}
    (leaf : ∀ u, X u → SignLog Req Resp → Y u) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (advSpecPar Req Resp S)) X A →
      SignLog Req Resp → IFreeM (QuantumComp.toIPFunctor L (advSpecPar Req Resp S)) Y A
  | _, .pure x, log => .pure (leaf _ x log)
  | _, .liftBind c next, log =>
      .liftBind c fun b ↦ logSignsPerm leaf (next b) (logAfterPerm c b log)

/-- Keeping the transcript of a parallel adversary keeps every charge bound. -/
theorem isChargeBound_logSignsPerm {L : LocalSig.{u, v}} {X Y : QReg → Type}
    (leaf : ∀ u, X u → SignLog Req Resp → Y u)
    {c : (A : QReg) → QuantumComp.Cmd L (advSpecPar Req Resp S) A → ℕ} {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L (advSpecPar Req Resp S)) X A) (log : SignLog Req Resp)
    {n : ℕ} (hx : IFreeM.IsChargeBound x c n) :
    IFreeM.IsChargeBound (logSignsPerm leaf x log) c n := by
  induction x using IFreeM.inductionOn generalizing log n with
  | pure _ _ => trivial
  | liftBind _ c' next ih => exact ⟨hx.1, fun r ↦ ih r _ (hx.2 r)⟩

/-- The transcript passes through a round's permutation calls. -/
theorem logSigns_bind_seqCalls_perm {X Y : QReg → Type} (leaf : ∀ u, X u → SignLog Req Resp → Y u) :
    ∀ {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (advSpec Req Resp S) (fun i ↦ .perm (dir i)) × E)
    (post : roundOut (advSpec Req Resp S) (fun i ↦ .perm (dir i)) × E ≃ B)
    (g : ∀ u, QuantumComp₂.Leaf B (Fin w → Unit) u →
      QuantumComp LocalSig.instruments.{0} (advSpec Req Resp S) X u) (log : SignLog Req Resp),
    logSigns leaf (IFreeM.bind (seqCalls (fun i ↦ AdvPort.perm (dir i)) E ℓ post) g) log =
      IFreeM.bind (seqCalls (fun i ↦ AdvPort.perm (dir i)) E ℓ post) fun u l ↦
        logSigns leaf (g u l) log
  | 0, _, _, _, _, _, _, _, _ => rfl
  | w + 1, dir, E, _, B, ℓ, post, g, log =>
    congrArg (IFreeM.liftBind _) (funext fun b ↦ by
      dsimp only [QuantumComp.onDown]
      exact (congrArg (logSigns leaf · log) (IFreeM.bind_imap _ _ _)).trans
        ((logSigns_bind_seqCalls_perm leaf (w := w) (fun i ↦ dir i.succ) _ _ _ _ log).trans
          (IFreeM.bind_imap (fun s (p : QuantumComp₂.Leaf B (Fin w → Unit) s) ↦
            (⟨p.1, Fin.cons b.down p.2⟩ : QuantumComp₂.Leaf B (Fin (w + 1) → Unit) s))
            (fun u l ↦ logSigns leaf (g u l) log) _).symm))

/-- **Transcripts commute with serialization.** -/
theorem logSigns_substitute_toSeq' {X Y : QReg → Type} (leaf : ∀ u, X u → SignLog Req Resp → Y u)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpecPar Req Resp S)) X A)
    (log : SignLog Req Resp) :
    logSigns leaf (IFreeM.substitute toSeq x) log =
      IFreeM.substitute toSeq (logSignsPerm leaf x log) := by
  induction x using IFreeM.inductionOn generalizing log with
  | pure _ _ => rfl
  | liftBind _ c next ih =>
    rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b log)
    · refine (congrArg (logSigns leaf · log) (IFreeM.bind_assoc _ _ _)).trans
        ((logSigns_bind_seqCalls_perm leaf dir E ℓ _ _ log).trans
          ((congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_)).trans
            (IFreeM.bind_assoc _ _ _).symm))
      obtain ⟨h, a⟩ := l
      subst h
      exact ih _ log
    · exact congrArg (IFreeM.liftBind _) (funext fun b ↦ ih b _)

/-- The permutation calls as the adversary's permutation ports. -/
def permLens {L : LocalSig.{u, v}} :
    IPFunctor.Lens (QuantumComp.toIPFunctor L (qrpmSpec S))
      (QuantumComp.toIPFunctor L (advSpec Req Resp S)) where
  toFunA _
    | .prim o => .prim o
    | .query p E ℓ => .query (.perm p) E ℓ
  toFunB _ c := by cases c <;> exact id
  src_eq _ c _ := by cases c <;> rfl

/-- A round's permutation calls are the adversary's. -/
theorem mapLens_permLens_seqCalls : ∀ {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg)
    {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec S) dir × E) (post : roundOut (qrpmSpec S) dir × E ≃ B),
    IFreeM.mapLens (permLens (Req := Req) (Resp := Resp) (L := LocalSig.instruments.{0}))
        (seqCalls dir E ℓ post) =
      seqCalls (spec := advSpec Req Resp S) (fun i ↦ AdvPort.perm (dir i)) E ℓ post
  | 0, _, _, _, _, _, _ => rfl
  | _ + 1, dir, E, _, _, ℓ, post => by
    rw [seqCalls_succ, seqCalls_succ]
    exact congrArg (QuantumComp₂.queryBind (spec := advSpec Req Resp S) _ _ _) (funext fun r ↦
      (mapLens_map₂ _ _ _).trans (congrArg (QuantumComp₂.map _)
        (mapLens_permLens_seqCalls (fun i ↦ dir i.succ) _ _ _)))

end Quantum.SufCma

/-! ## The hardwired runtimes read their functions -/

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid Quantum.Par
  HashSig LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

section read

variable {X₁ Z₁ M₁ : Type} [Fintype X₁] [DecidableEq X₁] [AddCommGroup X₁] [Fintype Z₁]
  [DecidableEq Z₁] [AddCommGroup Z₁] [Fintype M₁] [DecidableEq M₁]

/-- The functions the sponge ports of runtime 1 read: the view `hwView W L` over the
databases. -/
def hw1Keys (L : Hw X₁ Z₁) : HwReg X₁ Z₁ M₁ → SpongeKeys X₁ Z₁ :=
  readKeys (fun s z ↦ ((hwView s.2.1 L).1 z).getD (s.1.1.lookup z))
    (fun s x ↦ ((hwView s.2.1 L).2.1 x).getD (s.1.2.1.lookup x))
    (fun s x ↦ ((hwView s.2.1 L).2.2 x).getD (s.1.2.2.lookup x))

/-- **The sponge ports of runtime 1 read their functions** in the basis of the compression. -/
theorem isReadRuntime_spongeHardwired1 (L : Hw X₁ Z₁) (m₀ : M₁) :
    IsReadRuntime ((spongeHardwired1 X₁ Z₁ L m₀).toRuntime : QuantumRuntime (spongeSpec X₁ Z₁))
      (compressReg X₁ Z₁ M₁) (hw1Keys L) := by
  intro p
  rw [(spongeHardwired1 X₁ Z₁ L m₀).toRuntime_step_branch p (), conjTranspose_compressReg]
  cases p <;> rfl

variable {S M' : Type} [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] [Nonempty X₁]
  [Nonempty Z₁]

/-- The sponge part of runtime 2 with record ports reads its functions. -/
theorem isReadRuntime_runtimeR (m₀ : Finset S × M') :
    IsReadRuntime (hwPart (recSpec S M') (runtimeR (X := X₁) (Z := Z₁) m₀))
      (compressReg X₁ Z₁ (Finset S × M')) (hwKeys X₁ Z₁ (Finset S × M')) :=
  isReadRuntime_spongeHardwired (hwEmpty X₁ Z₁) m₀

/-- The sponge part of runtime 1 with record ports reads its functions. -/
theorem isReadRuntime_runtime1R (L : Hw X₁ Z₁) (m₀ : Finset S × M') :
    IsReadRuntime (hwPart (recSpec S M') (runtime1R X₁ Z₁ L m₀))
      (compressReg X₁ Z₁ (Finset S × M')) (hw1Keys L) :=
  isReadRuntime_spongeHardwired1 L m₀

end read

/-! ## The serialized game, command by command -/

set_option quotPrecheck false in
-- The parallel adversary's commands.
local notation "AdvPP" => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z))

set_option quotPrecheck false in
-- The signature of the parallel game: runtime 2's ports with record ports, and rounds.
local notation "ParR" => parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)

set_option quotPrecheck false in
-- The permutation calls as the adversary's.
local notation "PermL" => (Quantum.SufCma.permLens (Req := SigningRequest)
  (Resp := Option Signature) (S := X × Z) (L := LocalSig.instruments.{0}))

section cmd

/-- A program over the sponge ports, as a template of runtime 1 realized at `v`: the lifted
program. -/
theorem realizeT_readLift_liftOrdinary (v : HPos → Digest) {W : QReg → Type} {A : QReg}
    (z : QuantumComp LocalSig.instruments.{0} (spongeSpec X Z) W A) :
    realizeT v (readLift (S := HPos) (D := XD) (M := Selections) goodAll
      (z.liftOrdinary (t := hwReadCmdSpec X Z Selections))) =
        IFreeM.mapLens (hwLens X Z Mem (recSpec HPos Selections)) z := by
  induction z using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih => exact congrArg (QuantumComp.primBind o) (funext ih)
  | queryBind _ i E ℓ k ih =>
    exact congrArg (QuantumComp.queryBind (spec := recHwSpec X Z HPos Selections)
      (.inl (.inl (.inl i))) E ℓ) (funext ih)

/-- A continuation returning every leaf unchanged. -/
theorem bind_eq_self_of {P : IPFunctor.Endo QReg} {Y : QReg → Type} {A : QReg}
    {x : IFreeM P Y A} {g : ∀ t, Y t → IFreeM P Y t} (hg : ∀ t y, g t y = IFreeM.pure y) :
    x.bind g = x :=
  (congrArg (IFreeM.bind x) (funext fun t ↦ funext (hg t))).trans (IFreeM.bind_pure_right x)

/-- The challenger of runtime 2, realized, on a permutation call or local operation: the lifted
simulation. -/
theorem realizeT_substitute_challengeT_permLens (L : HonestTable) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (qrpmSpec (X × Z))).A A) :
    realizeT (valueAt L) (IFreeM.substitute (challengeT Selections cwUpd (pubOf L))
      (IPFunctor.Lens.toSubstitution PermL A c)) =
      IFreeM.mapLens (hwLens X Z Mem (recSpec HPos Selections))
        (simSubst LocalSig.Interp.instruments (pubOf L).perm A c) := by
  rcases c with o | ⟨p, E, ℓ⟩
  · have h1 : IFreeM.substitute (challengeT Selections cwUpd (pubOf L))
        (IPFunctor.Lens.toSubstitution PermL A
          (.prim o)) = challengeT Selections cwUpd (pubOf L) A (.prim o) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    have h2 : simulate LocalSig.Interp.instruments (pubOf L).perm
        (Quantum.SufCma.challenge sufCmaScheme keccakStateEquiv (noKey (pubOf L)) A (.prim o)) =
          simSubst LocalSig.Interp.instruments (pubOf L).perm A (.prim o) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    exact (congrArg (realizeT (valueAt L)) h1).trans
      ((realizeT_readLift_liftOrdinary _ _).trans (congrArg _ h2))
  · have h1 : IFreeM.substitute (challengeT Selections cwUpd (pubOf L))
        (IPFunctor.Lens.toSubstitution PermL A
          (.query p E ℓ)) = challengeT Selections cwUpd (pubOf L) A (.query (.perm p) E ℓ) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    have h2 : simulate LocalSig.Interp.instruments (pubOf L).perm
        (Quantum.SufCma.challenge sufCmaScheme keccakStateEquiv (noKey (pubOf L)) A
          (.query (.perm p) E ℓ)) =
          simSubst LocalSig.Interp.instruments (pubOf L).perm A (.query p E ℓ) :=
      bind_eq_self_of fun t y ↦ by
        obtain ⟨b, rfl⟩ := y
        rfl
    exact (congrArg (realizeT (valueAt L)) h1).trans
      ((realizeT_readLift_liftOrdinary _ _).trans (congrArg _ h2))

/-- **The challenger of runtime 2, realized, on a permutation program**: the lifted
simulation. -/
theorem realizeT_challengeT_mapLens_permLens (L : HonestTable) {W : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments.{0} (qrpmSpec (X × Z)) W A) :
    realizeT (valueAt L) (IFreeM.substitute (challengeT Selections cwUpd (pubOf L))
      (IFreeM.mapLens PermL y)) =
      IFreeM.mapLens (hwLens X Z Mem (recSpec HPos Selections))
        (simulate LocalSig.Interp.instruments (pubOf L).perm y) := by
  have hy := (IFreeM.substitute_toSubstitution PermL
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (qrpmSpec (X × Z))) W A)).symm
  refine (congrArg (fun z ↦ realizeT (valueAt L) (IFreeM.substitute
    (challengeT Selections cwUpd (pubOf L)) z)) hy).trans ?_
  refine (congrArg (realizeT (valueAt L)) (substitute_substitute _ _ _)).trans ?_
  refine (realizeT_substitute _ _ _).trans ?_
  refine Eq.trans ?_ (IFreeM.substitute_toSubstitution (hwLens X Z Mem (recSpec HPos Selections))
    (simulate LocalSig.Interp.instruments (pubOf L).perm y))
  refine Eq.trans ?_ (substitute_substitute _ _ _).symm
  exact congrArg (fun σ ↦ IFreeM.substitute σ y) (funext fun A ↦ funext fun c ↦
    (realizeT_substitute_challengeT_permLens L A c).trans
      (IFreeM.substitute_toSubstitution _ _).symm)

/-- **The realized command of the serialized adversary** at the table `L`: the challenger of
runtime 2 on the serialization of a parallel command. -/
noncomputable def cmdR (L : HonestTable) (A : QReg) (c : (AdvPP).A A) :
    IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (recHwSpec X Z HPos Selections))
      (fun t ↦ {b : (AdvPP).B A c // (AdvPP).src A c b = t}) A :=
  realizeT (valueAt L) (IFreeM.substitute (challengeT Selections cwUpd (pubOf L))
    (Quantum.SufCma.toSeq A c))

/-- **A serialized round, realized**: the lifted simulation of its calls in order. -/
theorem cmdR_permPar (L : HonestTable) {w : ℕ} (dir : Fin w → PermutationPort) (E : QReg)
    {A : QReg}
    (ℓ : A ≃ (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z)).In
      (.permPar w dir) × E) :
    cmdR L A (.query (.permPar w dir) E ℓ) =
      QuantumComp.bind (IFreeM.mapLens (hwLens X Z Mem (recSpec HPos Selections))
        (simulate LocalSig.Interp.instruments (pubOf L).perm
          (seqCalls (spec := qrpmSpec (X × Z)) dir E
            (B := QReg.of ((Quantum.SufCma.advSpecPar SigningRequest (Option Signature)
              (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _))))
        fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩ :=
  (congrArg (realizeT (valueAt L)) (IFreeM.substitute_bind _ _ _)).trans
    ((realizeT_bind _ _ _).trans (congrArg (fun z ↦ QuantumComp.bind z _)
      ((congrArg (fun z ↦ realizeT (valueAt L) (IFreeM.substitute
        (challengeT Selections cwUpd (pubOf L)) z))
        (Quantum.SufCma.mapLens_permLens_seqCalls dir E ℓ _).symm).trans
        (realizeT_challengeT_mapLens_permLens L _))))

/-- **The challenged parallel adversary** at the table `L`: a round of permutation calls is the
lifted lockstep round with rounds (`lockRoundR`); a local operation or signing request is the
realized command of the sequential challenger. -/
noncomputable def advSubstR (L : HonestTable) :
    CommandSubstitution AdvPP (QuantumComp.toIPFunctor LocalSig.instruments.{0} ParR)
  | A, .prim o => QuantumComp.liftOrdinary (cmdR L A (.prim o))
  | _, .query (.permPar w dir) E ℓ =>
      QuantumComp.bind (IFreeM.mapLens (hwParLens X Z Mem (recSpec HPos Selections))
        (lockRoundR (pubOf L).perm dir
          (B := QReg.of ((Quantum.SufCma.advSpecPar SigningRequest (Option Signature)
            (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _)))
        fun _ l ↦ QuantumComp.pure ⟨ULift.up (), l.1.symm⟩
  | A, .query (.sign r) E ℓ => QuantumComp.liftOrdinary (cmdR L A (.query (.sign r) E ℓ))

end cmd

/-! ## The games with rounds -/

section game

/-- The public key's reveal, realized at `L`. -/
noncomputable def pkRevealR (L : HonestTable) :
    QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit)
      (RevealVals XD {.inl rootPos} × (Finset HPos × Selections)) :=
  realizeT (valueAt L) (revealThen (M := Selections) (B := QReg.of Unit) goodAll {.inl rootPos}
    QuantumComp₂.pure)

/-- The public key from the revealed root. -/
def pkR (L : HonestTable) (r₀ : RevealVals XD {.inl rootPos} × (Finset HPos × Selections)) :
    PublicKey :=
  ⟨extendVals r₀.1 rootPos, (pubOf L).param⟩

/-- The challenged serialized adversary with its transcript, realized at `L`, command by
command. -/
noncomputable def advSeqR (L : HonestTable) {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z)) A B α) :
    QComp (recHwSpec X Z HPos Selections) A B (α × SignLog) :=
  IFreeM.substitute (cmdR L) (Quantum.SufCma.logSignsPerm (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])

/-- **The challenged parallel adversary with its transcript** at `L`, with rounds. -/
noncomputable def advParR (L : HonestTable) {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z)) A B α) :
    QComp ParR A B (α × SignLog) :=
  IFreeM.substitute (advSubstR L)
    (Quantum.SufCma.logSignsPerm (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x [])

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z))

/-- **The challenge prefix of a parallel adversary, with rounds**: the public key's reveal, then
the challenged parallel adversary with its transcript. -/
noncomputable def prefixRPar (L : HonestTable) :
    QComp ParR (QReg.of Unit) (QReg.of Unit) (PublicKey × (Forgery × SignLog)) :=
  QuantumComp₂.bind (QuantumComp.liftOrdinary (t := roundSpec (recHwSpec X Z HPos Selections)
    (portR X Z HPos Selections)) (pkRevealR L)) fun r₀ ↦
      (advParR L (Ap (pkR L r₀))).bind fun run ↦ QuantumComp₂.pure (pkR L r₀, run)

/-- **The canonical game of a parallel adversary, with rounds**: the prefix, then the
verification. -/
noncomputable def gameRPar (L : HonestTable) : QComp ParR (QReg.of Unit) (QReg.of Unit) Bool :=
  (prefixRPar Ap L).bind fun pre ↦ QuantumComp.liftOrdinary
    (t := roundSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections))
    (realizeT (valueAt L) (verifyT Selections (pubOf L) pre))

/-- **The challenge prefix of the serialization**, command by command. -/
theorem prefixR_serialize (L : HonestTable) :
    prefixR (Quantum.SufCma.serialize Ap) L =
      (pkRevealR L).bind fun r₀ ↦
        (advSeqR L (Ap (pkR L r₀))).bind fun run ↦ QuantumComp₂.pure (pkR L r₀, run) := by
  have h1 : prefixT Selections cwUpd (pubOf L) (Quantum.SufCma.serialize Ap) =
      (revealThen (M := Selections) (B := QReg.of Unit) goodAll {.inl rootPos}
        QuantumComp₂.pure).bind fun r₀ ↦
        (challengedT Selections cwUpd (pubOf L)
          (Quantum.SufCma.withSignLog (Quantum.SufCma.serialize Ap (pkR L r₀)))).bind fun run ↦
            QuantumComp₂.pure (pkR L r₀, run) :=
    rfl
  refine ((congrArg (realizeT (valueAt L)) h1).trans (realizeT_bind₂ _ _ _)).trans ?_
  refine congrArg (QuantumComp₂.bind _) (funext fun r₀ ↦ ?_)
  refine (realizeT_bind₂ _ _ _).trans (congrArg (fun z ↦ QuantumComp₂.bind z _) ?_)
  refine (congrArg (fun z ↦ realizeT (valueAt L) (IFreeM.substitute
    (challengeT Selections cwUpd (pubOf L)) z))
      (Quantum.SufCma.logSigns_substitute_toSeq' _ (Ap (pkR L r₀)) [])).trans ?_
  exact (congrArg (realizeT (valueAt L)) (substitute_substitute _ _ _)).trans
    (realizeT_substitute _ _ _)

end game

/-! ## The runs -/

section run

variable (R : QuantumRuntime (recHwSpec X Z HPos Selections)) {U : Matrix R.D R.D ℂ}
  (hU : U ∈ unitaryGroup R.D ℂ) {rd : R.D → SpongeKeys X Z}
  (hR : IsReadRuntime (hwPart (recSpec HPos Selections) R) U rd)
include hU hR

/-- **A serialized round, lifted, against a read runtime**: the lifted lockstep round. -/
theorem branch_lift_simulate_eq_lockRoundR (L : HonestTable) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A : QReg}
    (ℓ : A ≃ (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z)).In
      (.permPar w dir) × E) (rs : RoundResult (qrpmSpec (X × Z)) dir) :
    (R.run₂ .instruments (IFreeM.mapLens (hwLens X Z Mem (recSpec HPos Selections))
      (simulate LocalSig.Interp.instruments (pubOf L).perm
        (seqCalls (spec := qrpmSpec (X × Z)) dir E
          (B := QReg.of ((Quantum.SufCma.advSpecPar SigningRequest (Option Signature)
            (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _))))).branch rs =
      ((R.par (portR X Z HPos Selections)).run₂ .instruments
        (IFreeM.mapLens (hwParLens X Z Mem (recSpec HPos Selections))
          (lockRoundR (pubOf L).perm dir
            (B := QReg.of ((Quantum.SufCma.advSpecPar SigningRequest (Option Signature)
              (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _)))).branch () := by
  have h1 := run₂_mapLens_hwLens (recSpec HPos Selections) R .instruments
    (simulate LocalSig.Interp.instruments (pubOf L).perm
        (seqCalls (spec := qrpmSpec (X × Z)) dir E
          (B := QReg.of ((Quantum.SufCma.advSpecPar SigningRequest (Option Signature)
            (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _)))
  have h2 := run₂_mapLens_hwParLens (recSpec HPos Selections) R .instruments
    (lockRoundR (pubOf L).perm dir
      (B := QReg.of ((Quantum.SufCma.advSpecPar SigningRequest (Option Signature)
        (X × Z)).Out (.permPar w dir) × E)) ℓ (Equiv.refl _))
  have h3 := branch_run₂_simulate_seqCalls_eq_lockRoundR (hwPart (recSpec HPos Selections) R) U
    hU rd hR (pubOf L).perm dir E ℓ
      (B := QReg.of ((Quantum.SufCma.advSpecPar SigningRequest (Option Signature)
        (X × Z)).Out (.permPar w dir) × E)) (Equiv.refl _) rs
  exact ((congrArg (fun P ↦ DSubInstrument.branch P rs) h1).trans h3).trans
    (congrArg (fun P ↦ DSubInstrument.branch P ()) h2).symm

/-- **Command by command**, the challenged parallel adversary runs as the serialized one, against
a runtime whose sponge part reads its functions in the basis of a unitary. -/
theorem run_cmdR_eq (L : HonestTable) (A : QReg) (c : (AdvPP).A A) :
    R.run .instruments (cmdR L A c) =
      (R.par (portR X Z HPos Selections)).run .instruments (advSubstR L A c) := by
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact (R.run_liftOrdinary .instruments _ _).symm
  · have : Unique (RoundResult (qrpmSpec (X × Z)) dir) := inferInstanceAs (Unique (Fin w → Unit))
    refine (congrArg (R.run .instruments) (cmdR_permPar L dir E ℓ)).trans ?_
    exact run_bind_leaf_eq_par (portR X Z HPos Selections) R
      (Y := fun t ↦ {b : (AdvPP).B A (.query (.permPar w dir) E ℓ) //
        (AdvPP).src A (.query (.permPar w dir) E ℓ) b = t})
      (fun u h ↦ ⟨ULift.up (), h⟩) _ _
      (branch_lift_simulate_eq_lockRoundR R hU hR L dir E ℓ default)
  · exact (R.run_liftOrdinary .instruments _ _).symm

/-- The challenged parallel adversary runs as the serialized one. -/
theorem run_advParR_eq (L : HonestTable) {A B : QReg} {α : Type}
    (x : QComp (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z)) A B α) :
    R.run .instruments (advSeqR L x) =
      (R.par (portR X Z HPos Selections)).run .instruments (advParR L x) :=
  run_substitute_eq_par (portR X Z HPos Selections) R (cmdR L) (advSubstR L)
    (run_cmdR_eq R hU hR L) _

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z))

/-- **The challenge prefix with rounds runs as the prefix of the serialization.** -/
theorem run_prefixRPar_eq (L : HonestTable) :
    R.run .instruments (prefixR (Quantum.SufCma.serialize Ap) L) =
      (R.par (portR X Z HPos Selections)).run .instruments (prefixRPar Ap L) := by
  rw [prefixR_serialize]
  exact run_bind₂_liftOrdinary_par (portR X Z HPos Selections) R (pkRevealR L) fun r₀ ↦
    run_bind₂_eq_par (portR X Z HPos Selections) R (run_advParR_eq R hU hR L _) fun run ↦
      (R.run_pure _ _).trans ((R.par (portR X Z HPos Selections)).run_pure _ _).symm

/-- **The game with rounds runs as the game of the serialization.** -/
theorem run_gameRPar_eq (L : HonestTable) :
    R.run .instruments (gameR (Quantum.SufCma.serialize Ap) L) =
      (R.par (portR X Z HPos Selections)).run .instruments (gameRPar Ap L) := by
  rw [gameR_eq]
  exact run_bind₂_eq_par (portR X Z HPos Selections) R (run_prefixRPar_eq R hU hR Ap L)
    fun _ ↦ (R.run_liftOrdinary .instruments _ _).symm

end run

section runs

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z)) (L : HonestTable)

/-- `run_gameRPar_eq` against runtime 2 with record ports. -/
theorem run_gameRPar_eq_runtimeR (m₀ : Mem) :
    (runtimeR m₀).run .instruments (gameR (Quantum.SufCma.serialize Ap) L) =
      ((runtimeR m₀).par (portR X Z HPos Selections)).run .instruments (gameRPar Ap L) :=
  run_gameRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m₀) Ap L

/-- `run_gameRPar_eq` against runtime 1 with record ports. -/
theorem run_gameRPar_eq_runtime1R (Lt : Hw X Z) (m₀ : Mem) :
    (runtime1R X Z Lt m₀).run .instruments (gameR (Quantum.SufCma.serialize Ap) L) =
      ((runtime1R X Z Lt m₀).par (portR X Z HPos Selections)).run .instruments
        (gameRPar Ap L) :=
  run_gameRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtime1R Lt m₀) Ap L

/-- `run_prefixRPar_eq` against runtime 2 with record ports. -/
theorem run_prefixRPar_eq_runtimeR (m₀ : Mem) :
    (runtimeR m₀).run .instruments (prefixR (Quantum.SufCma.serialize Ap) L) =
      ((runtimeR m₀).par (portR X Z HPos Selections)).run .instruments (prefixRPar Ap L) :=
  run_prefixRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m₀) Ap L

/-- `run_prefixRPar_eq` against runtime 1 with record ports. -/
theorem run_prefixRPar_eq_runtime1R (Lt : Hw X Z) (m₀ : Mem) :
    (runtime1R X Z Lt m₀).run .instruments (prefixR (Quantum.SufCma.serialize Ap) L) =
      ((runtime1R X Z Lt m₀).par (portR X Z HPos Selections)).run .instruments
        (prefixRPar Ap L) :=
  run_prefixRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtime1R Lt m₀) Ap L

/-- The game's winning distribution against runtime 2, with rounds. -/
theorem p2R_eq_par :
    p2R (gameR (Quantum.SufCma.serialize Ap)) L =
      ((runtimeR m0R).par (portR X Z HPos Selections)).evalDistMap .instruments (gameRPar Ap L)
        (SubState.basis ()) winObs {true} := by
  unfold p2R
  rw [evalDistMap_par_eq (portR X Z HPos Selections) _ (run_gameRPar_eq_runtimeR Ap L m0R)]

/-- The game's winning distribution against runtime 1, with rounds. -/
theorem p1R_eq_par (Lt : HonestTable → Hw X Z) :
    p1R (Quantum.SufCma.serialize Ap) Lt L =
      ((runtime1R X Z (Lt L) m0R).par (portR X Z HPos Selections)).evalDistMap .instruments
        (gameRPar Ap L) (SubState.basis ()) winObs {true} := by
  unfold p1R
  rw [evalDistMap_par_eq (portR X Z HPos Selections) _
    (run_gameRPar_eq_runtime1R Ap L (Lt L) m0R)]

/-- The prefix's event weight against runtime 2, with rounds. -/
theorem eventWeight_prefixRPar_eq (P : Matrix (HwReg X Z Mem) (HwReg X Z Mem) ℂ)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z Mem)) (QReg.of Unit × QReg.of (HwReg X Z Mem))
      ℂ) :
    (runtimeR m0R).eventWeight .instruments P (prefixR (Quantum.SufCma.serialize Ap) L) ρ =
      ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight .instruments P
        (prefixRPar Ap L) ρ :=
  eventWeight_par_eq (portR X Z HPos Selections) _ (run_prefixRPar_eq_runtimeR Ap L m0R) P ρ

end runs

/-! ## Weights vanishing on the sponge ports -/

section weight

variable (R : QuantumRuntime (recHwSpec X Z HPos Selections)) {U : Matrix R.D R.D ℂ}
  (hU : U ∈ unitaryGroup R.D ℂ) {rd : R.D → SpongeKeys X Z}
  (hR : IsReadRuntime (hwPart (recSpec HPos Selections) R) U rd)
  (W : ∀ i, Matrix ((recHwSpec X Z HPos Selections).In i × R.D)
    ((recHwSpec X Z HPos Selections).In i × R.D) ℂ → ℝ≥0∞)
  (hW : ∀ p σ, W (portR X Z HPos Selections p) σ = 0)
include hU hR hW

/-- **Command by command**, the challenged parallel adversary has the weights of the serialized
one on its single calls, for continuations of the same weights. -/
theorem totalWeight_cmdR_bind_eq (L : HonestTable) (A : QReg) (c : (AdvPP).A A)
    {Y : QReg → Type}
    (k₁ : ∀ u, {b : (AdvPP).B A c // (AdvPP).src A c b = u} →
      QuantumComp LocalSig.instruments.{0} (recHwSpec X Z HPos Selections) Y u)
    (k₂ : ∀ u, {b : (AdvPP).B A c // (AdvPP).src A c b = u} →
      QuantumComp LocalSig.instruments.{0} ParR Y u)
    (hk : ∀ u b ρ, R.totalWeight .instruments W (k₁ u b) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (k₂ u b) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W ((cmdR L A c).bind k₁) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) ((advSubstR L A c).bind k₂) ρ := by
  rcases c with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact totalWeight_bind_liftOrdinary_par (portR X Z HPos Selections) R W _ k₁ k₂ hk ρ
  · have : Unique (RoundResult (qrpmSpec (X × Z)) dir) := inferInstanceAs (Unique (Fin w → Unit))
    refine (congrArg (fun z ↦ R.totalWeight .instruments W (QuantumComp.bind z k₁) ρ)
      (cmdR_permPar L dir E ℓ)).trans ?_
    exact totalWeight_bind_leaf_eq_par (portR X Z HPos Selections) R W
      (N₁ := HwPorts X Z Mem (recSpec HPos Selections))
      (N₂ := HwParPorts X Z Mem (recSpec HPos Selections))
      (eq_zero_of_hwPorts (recSpec HPos Selections) hW)
      (parWeight_eq_zero_of (recSpec HPos Selections) hW)
      (Y := fun t ↦ {b : (AdvPP).B A (.query (.permPar w dir) E ℓ) //
        (AdvPP).src A (.query (.permPar w dir) E ℓ) b = t})
      (fun u h ↦ ⟨ULift.up (), h⟩) _ _
      (isThin_mapLens_hwLens _ (isThin_simulate _ _
        (isThin_seqCalls (spec := qrpmSpec (X × Z)) (N := fun _ ↦ True) dir
          (fun _ ↦ ⟨trivial, ⟨()⟩, inferInstanceAs (Subsingleton Unit)⟩) _ _ _)))
      (isThin_mapLens_hwParLens _ (isThin_lockRoundR _ _ _ _))
      (branch_lift_simulate_eq_lockRoundR R hU hR L dir E ℓ default) k₁ k₂ hk ρ
  · exact totalWeight_bind_liftOrdinary_par (portR X Z HPos Selections) R W _ k₁ k₂ hk ρ

/-- The challenged parallel adversary has the weights of the serialized one, for continuations of
the same weights. -/
theorem totalWeight_advParR_bind_eq (L : HonestTable) {A B C : QReg} {α β : Type}
    (x : QComp (Quantum.SufCma.advSpecPar SigningRequest (Option Signature) (X × Z)) A B α)
    (k₁ : α × SignLog → QComp (recHwSpec X Z HPos Selections) B C β)
    (k₂ : α × SignLog → QComp ParR B C β)
    (hk : ∀ a ρ, R.totalWeight .instruments W (k₁ a) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (k₂ a) ρ)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight .instruments W ((advSeqR L x).bind k₁) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) ((advParR L x).bind k₂) ρ :=
  totalWeight_substitute_bind_eq_par (portR X Z HPos Selections) R (cmdR L) (advSubstR L) W
    (fun A c _ k₁ k₂ hk ρ ↦ totalWeight_cmdR_bind_eq R hU hR W hW L A c k₁ k₂ hk ρ) _ _ _
    (fun u p ρ' ↦ by
      rcases p with ⟨rfl, a⟩
      exact hk a ρ') ρ

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z))

/-- **The prefix with rounds has the weights of the prefix of the serialization**, for
continuations of the same weights. -/
theorem totalWeight_prefixRPar_bind_eq (L : HonestTable) {β : Type}
    (k₁ : PublicKey × (Forgery × SignLog) →
      QComp (recHwSpec X Z HPos Selections) (QReg.of Unit) (QReg.of Unit) β)
    (k₂ : PublicKey × (Forgery × SignLog) → QComp ParR (QReg.of Unit) (QReg.of Unit) β)
    (hk : ∀ a ρ, R.totalWeight .instruments W (k₁ a) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (k₂ a) ρ)
    (ρ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ) :
    R.totalWeight .instruments W ((prefixR (Quantum.SufCma.serialize Ap) L).bind k₁) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) ((prefixRPar Ap L).bind k₂) ρ := by
  rw [prefixR_serialize]
  refine (congrArg (fun z ↦ R.totalWeight .instruments W z ρ)
    (QuantumComp₂.bind_assoc _ _ _)).trans (Eq.trans ?_ (congrArg (fun z ↦
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) z ρ) (QuantumComp₂.bind_assoc _ _ _)).symm)
  refine totalWeight_bind₂_liftOrdinary_par (portR X Z HPos Selections) R W (pkRevealR L)
    (fun r₀ ρ' ↦ ?_) ρ
  refine (congrArg (fun z ↦ R.totalWeight .instruments W z ρ')
    (QuantumComp₂.bind_assoc _ _ _)).trans (Eq.trans ?_ (congrArg (fun z ↦
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) z ρ') (QuantumComp₂.bind_assoc _ _ _)).symm)
  exact totalWeight_advParR_bind_eq R hU hR W hW L _ _ _ (fun a ρ'' ↦ hk _ ρ'') ρ'

/-- **The prefix with rounds has the weights of the prefix of the serialization.** -/
theorem totalWeight_prefixRPar_eq (L : HonestTable)
    (ρ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ) :
    R.totalWeight .instruments W (prefixR (Quantum.SufCma.serialize Ap) L) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (prefixRPar Ap L) ρ := by
  have h := totalWeight_prefixRPar_bind_eq R hU hR W hW Ap L QuantumComp₂.pure
    QuantumComp₂.pure (fun a ρ' ↦ (R.totalWeight_pure _ _ ρ').trans
      ((R.par (portR X Z HPos Selections)).totalWeight_pure _ _ ρ').symm) ρ
  rwa [QuantumComp₂.bind_pure, QuantumComp₂.bind_pure] at h

/-- **The game with rounds has the weights of the game of the serialization.** -/
theorem totalWeight_gameRPar_eq (L : HonestTable)
    (ρ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ) :
    R.totalWeight .instruments W (gameR (Quantum.SufCma.serialize Ap) L) ρ =
      (R.par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) W) (gameRPar Ap L) ρ := by
  rw [gameR_eq]
  exact totalWeight_prefixRPar_bind_eq R hU hR W hW Ap L _ _
    (fun a ρ' ↦ (totalWeight_liftOrdinary_par (portR X Z HPos Selections) R W _ ρ').symm) ρ

end weight

section weights

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z)) (L : HonestTable)

/-- **The prefix's classical costs, with rounds** (CostRefined's `twPR`). -/
theorem twPR_eq_par :
    twPR (Quantum.SufCma.serialize Ap) L =
      ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref L) (dPof L))))
        (prefixRPar Ap L) initR :=
  totalWeight_prefixRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m0R) _
    (fun _ _ ↦ rfl) Ap L initR

/-- **The game's hidden mass at the classical ports, with rounds.** -/
theorem readMass_gameRPar_eq (Hh : Set Z) (Hk Hk' : Set X) :
    (runtimeR m0R).totalWeight .instruments (readMass Hh Hk Hk')
        (gameR (Quantum.SufCma.serialize Ap) L) initR =
      ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight .instruments
        (parWeight (portR X Z HPos Selections) (readMass Hh Hk Hk')) (gameRPar Ap L) initR :=
  totalWeight_gameRPar_eq _ compressReg_mem_unitaryGroup (isReadRuntime_runtimeR m0R) _
    (fun _ _ ↦ rfl) Ap L initR

end weights

/-! ## Charges -/

/-- The charge of a parallel adversary's command: `f w` for a round of width `w`, `S` for a
signing request. -/
def lockAdvCharge (f : ℕ → ℕ) (S : ℕ) : Quantum.SufCma.AdvPortPar SigningRequest → ℕ
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

variable {S : ℕ} (hS : 2 * layerCalls b c d ≤ S) (L : HonestTable)

include hS in
/-- The realized command of a local operation or signing request: the charges of the sequential
challenger. -/
theorem isChargeBound_cmdR (A : QReg) (c₀ : (AdvPP).A A)
    (hc₀ : ∀ w dir E ℓ, c₀ ≠ .query (.permPar w dir) E ℓ) :
    IFreeM.IsChargeBound (cmdR L A c₀) (portCharge (rCharge Selections a b c d))
      (Quantum.SufCma.cmdChargePar (lockAdvCharge (fun _ ↦ 0) S) A c₀) := by
  refine isChargeBound_realizeT a b c d (valueAt L) (IFreeM.IsChargeBound.substitute _
    (chg_challengeT a b c d cwUpd (pubOf L) (S := S) fun B r ↦
      (chg_signT a b c d cwUpd (pubOf L) B r).mono hS) ?_)
  rcases c₀ with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact ⟨by simp [advCharge, Quantum.SufCma.cmdCharge], fun _ ↦ trivial⟩
  · exact absurd rfl (hc₀ w dir E ℓ)
  · exact ⟨by simp [advCharge, Quantum.SufCma.cmdCharge, Quantum.SufCma.permCharge,
      Quantum.SufCma.signCharge, Quantum.SufCma.cmdChargePar, lockAdvCharge], fun _ ↦ trivial⟩

variable (f : ℕ → ℕ)
  (hround : ∀ {w : ℕ} (dir : Fin w → PermutationPort),
    lockCharge (fun i ↦ κ (hwParPort X Z Mem (recSpec HPos Selections) i)) dir ≤ f w)
  (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections a b c d i)

include hS hround hinl in
/-- **The charges of the challenged parallel adversary's commands**: `f w` for a round of width
`w` (the lifted lockstep round), the sequential challenger's for the others. -/
theorem isChargeBound_advSubstR (A : QReg) (c₀ : (AdvPP).A A) :
    IFreeM.IsChargeBound (advSubstR L A c₀) (callCharge κ)
      (Quantum.SufCma.cmdChargePar (lockAdvCharge f S) A c₀) := by
  rcases c₀ with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩
  · exact isChargeBound_liftOrdinary_rCharge κ hinl
      (isChargeBound_cmdR hS L A (.prim o) fun _ _ _ _ h ↦ by cases h)
  · exact IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (n₂ := 0)
      (isChargeBound_mapLens_hwParLens _ κ ((isChargeBound_lockRoundR _ _ dir ℓ _).mono
        (hround dir))) fun _ _ ↦ trivial) (Nat.add_zero _).le
  · exact isChargeBound_liftOrdinary_rCharge κ hinl
      (isChargeBound_cmdR hS L A (.query (.sign r) E ℓ) fun _ _ _ _ h ↦ by cases h)

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z)) {n : ℕ}
  (hA : ∀ pk, IFreeM.IsChargeBound (Ap pk) (Quantum.SufCma.cmdChargePar (lockAdvCharge f S)) n)

include hS hround hinl hA in
/-- **The charges of the prefix with rounds**: the root's reveal, and the parallel adversary's
commands at their charges. -/
theorem isChargeBound_prefixRPar :
    IFreeM.IsChargeBound (prefixRPar Ap L) (callCharge κ) (d + n) := by
  have hrev' : IFreeM.IsChargeBound (revealThen (M := Selections) (B := QReg.of Unit) goodAll
      {.inl rootPos} QuantumComp₂.pure) (portCharge (tCharge Selections a b c d)) (d + 0) :=
    chg_revealThen a b c d {.inl rootPos} QuantumComp₂.pure (n := 0) fun _ ↦
      IFreeM.isChargeBound_pure _ 0
  have hrev : IFreeM.IsChargeBound (pkRevealR L) (portCharge (rCharge Selections a b c d)) d :=
    IFreeM.IsChargeBound.mono (isChargeBound_realizeT a b c d (valueAt L) hrev')
      (Nat.add_zero d).le
  unfold prefixRPar
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := n + 0)
    (isChargeBound_liftOrdinary_rCharge κ hinl hrev) fun r₀ ↦ ?_) (by omega)
  exact FreeM₂.isChargeBound_bind (n₂ := 0)
    (IFreeM.IsChargeBound.substitute (advSubstR L)
      (isChargeBound_advSubstR κ hS L f hround hinl)
      (Quantum.SufCma.isChargeBound_logSignsPerm _ _ [] (hA _))) fun _ ↦
    IFreeM.isChargeBound_pure _ 0

include hS hround hinl hA in
/-- **The charges of the game with rounds**: the prefix's and the verification's reads. -/
theorem isChargeBound_gameRPar :
    IFreeM.IsChargeBound (gameRPar Ap L) (callCharge κ) (d + n + 3 * b * verifyBlocks) := by
  have hv : ∀ pre : PublicKey × (Forgery × SignLog), IFreeM.IsChargeBound
      (verifyT Selections (pubOf L) pre) (portCharge (tCharge Selections a b c d))
      (3 * b * verifyBlocks) := fun pre ↦ by
    unfold verifyT
    exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (isChargeBound_readLift a b c d (chg_map _ Prod.fst
        (chg_readsProgram (M := Selections) a b (pubOf L).perm (QReg.of Unit)
          (verify_cost' pre.1 pre.2.1)))) fun _ ↦ trivial) (Nat.add_zero _).le
  exact FreeM₂.isChargeBound_bind (isChargeBound_prefixRPar κ hS L f hround hinl Ap hA) fun pre ↦
    isChargeBound_liftOrdinary_rCharge κ hinl (isChargeBound_realizeT a b c d (valueAt L) (hv pre))

end charges

/-! ## The charges from the parallel adversary's budgets -/

theorem cls_budget_le (x y : ℕ) : 1 + x ≤ 1 + ((6 * 0 * 0 + x) + y) := by omega

theorem cls_budget_le' (x y : ℕ) : 1 + x + 3 * 1 * y ≤ 1 + ((6 * 0 * 0 + x) + 3 * 1 * y) := by
  omega

section budgets

variable (Ap : Quantum.SufCma.AdversaryPar PublicKey SigningRequest (Option Signature) Forgery
  (X × Z)) (L : HonestTable) {q dp : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.widthCharge) q)
  (hd : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.roundCharge) dp)
  (hs : ∀ pk, IFreeM.IsChargeBound (Ap pk)
    (Quantum.SufCma.cmdChargePar Quantum.SufCma.signChargePar) lifetime)

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
      (Quantum.SufCma.cmdChargePar (lockAdvCharge (fun w ↦ C * min 1 w) 0)) (C * min dp q) :=
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
      (Quantum.SufCma.cmdChargePar (lockAdvCharge (fun _ ↦ 0) S)) (S * lifetime) :=
  isChargeBound_of_charge_le (fun _ cmd ↦ by
    rcases cmd with o | ⟨⟨w, dir⟩ | r, E, ℓ⟩ <;>
      simp [Quantum.SufCma.cmdChargePar, lockAdvCharge, Quantum.SufCma.signChargePar])
    ((hs pk).mul S)

variable (κ : (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)).Port → ℕ)

include hq in
/-- **Width charges of the prefix with rounds**: a port charge `c p` per call in a round, and no
classical charge, give `2 (c h + c k + c k') q`. -/
theorem isChargeBound_prefixRPar_width {K : ℕ} {c : SpongePort → ℕ}
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections K 0 0 0 i)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) ≤ m * c p) :
    IFreeM.IsChargeBound (prefixRPar Ap L) (callCharge κ)
      ((2 * c .h + 2 * c .k + 2 * c .k') * q) :=
  (isChargeBound_prefixRPar κ (a := K) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [layerCalls]) L _ (fun dir ↦ lockCharge_le_width _ hκ dir) hinl Ap
    (isChargeBound_lockAdv_width Ap hq _)).mono (Nat.zero_add _).le

include hq hd in
/-- **Depth charges of the prefix with rounds**: a port charge `c p` per round of positive width,
and no classical charge, give `(2 c h + 4 c k + 4 c k') min d q`. -/
theorem isChargeBound_prefixRPar_depth {K : ℕ} {c : SpongePort → ℕ}
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections K 0 0 0 i)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) ≤ min 1 m * c p) :
    IFreeM.IsChargeBound (prefixRPar Ap L) (callCharge κ)
      ((2 * c .h + 4 * c .k + 4 * c .k') * min dp q) :=
  (isChargeBound_prefixRPar κ (a := K) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [layerCalls]) L _ (fun dir ↦ lockCharge_le_depth _ hκ dir) hinl Ap
    (isChargeBound_lockAdv_depth Ap hq hd _)).mono (Nat.zero_add _).le

include hs in
/-- **Classical charges of the prefix with rounds**: at most `clsCap`. -/
theorem isChargeBound_prefixRPar_cls
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections 0 1 1 1 i)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) = 0) :
    IFreeM.IsChargeBound (prefixRPar Ap L) (callCharge κ) clsCap :=
  (isChargeBound_prefixRPar κ (a := 0) (b := 1) (c := 1) (d := 1)
    (S := 2 * layerCalls 1 1 1) le_rfl L (fun _ ↦ 0)
    (fun dir ↦ by simp [lockCharge, subCharge, hwParPort, hκ]) hinl Ap
    (isChargeBound_lockAdv_sign Ap hs _)).mono
    ((cls_budget_le _ (3 * 1 * verifyBlocks)).trans (gameCalls_cls_le 0))

include hs in
/-- **Classical charges of the game with rounds**: at most `clsCap`. -/
theorem isChargeBound_gameRPar_cls
    (hinl : ∀ i, κ (.inl i) ≤ rCharge Selections 0 1 1 1 i)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) = 0) :
    IFreeM.IsChargeBound (gameRPar Ap L) (callCharge κ) clsCap :=
  (isChargeBound_gameRPar κ (a := 0) (b := 1) (c := 1) (d := 1)
    (S := 2 * layerCalls 1 1 1) le_rfl L (fun _ ↦ 0)
    (fun dir ↦ by simp [lockCharge, subCharge, hwParPort, hκ]) hinl Ap
    (isChargeBound_lockAdv_sign Ap hs _)).mono
    ((cls_budget_le' _ _).trans (gameCalls_cls_le 0))

/-- **Charges vanishing on the prefix with rounds**: a charge vanishing on single calls and on
rounds of one port. -/
theorem isChargeBound_prefixRPar_zero (hinl : ∀ i, κ (.inl i) = 0)
    (hκ : ∀ m p, κ (.inr (.round m fun _ ↦ p)) = 0) :
    IFreeM.IsChargeBound (prefixRPar Ap L) (callCharge κ) 0 :=
  isChargeBound_prefixRPar κ (a := 0) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [layerCalls]) L (fun _ ↦ 0)
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
    IFreeM.IsChargeBound (gameRPar Ap L) (portCharge (spongeRounds (portR X Z HPos Selections)
      (extCls X Z Mem (recSpec HPos Selections)))) (10 * min dp q) := by
  rw [portCharge_eq_callCharge]
  refine (isChargeBound_gameRPar _ (a := 1) (b := 0) (c := 0) (d := 0) (S := 0)
    (by simp [layerCalls]) L (fun w ↦ (2 * 1 + 4 * 1 + 4 * 1) * min 1 w)
    (fun dir ↦ lockCharge_le_depth _ (c := fun _ ↦ 1) (fun m p ↦ ?_) dir) (fun i ↦ ?_) Ap
    (isChargeBound_lockAdv_depth Ap hq hd _)).mono (by simp)
  · cases m <;> simp [spongeRounds, roundCharge, widthCharge, hwParPort, extCls, hwCls]
  · rcases i with ((i | c) | c) | T <;>
      simp [spongeRounds, roundCharge, widthCharge, extCls, hwCls, rCharge]

end budgets

end Quantum.Xmss.Assembly

end
