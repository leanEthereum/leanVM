module

public import Quantum.Qrom.Sphincs.Multi.Template

@[expose] public section

/-!
# leanSPHINCS's multi-user game with honest read ports and a selection memo, in the QROM

The `n`-user analog of `Quantum.Qrom.Sphincs.GameReads`, with the selection memo on the
adversary's side (`memoFromS`, `Quantum.Qrom.Sphincs.Multi.Memo`): each signing request of user
`i` carries user `i`'s memo, and the answer carries the request's index and its three layers'
selections. The game's oracle is `regroup hmsgRoute F` for `F : HashDomain → PairOut`; its
honest hashing becomes reads of `F` (`readsProgram`), the adversary's calls are regrouped and
lifted to port `h`. A read signer may answer a memoized key's selection without searching: a key
signs one fixed value (`msgPos_eq`), so its selection against a fixed function is a function of
the key (`keySel`).

* `keySel v H K`, `memoAnsOf v H M`: a key's selection, the memo answer of the honest signer.
* `SignerSN M n`, `challengeWithSN M sgn`, `gameReadsWithSN M sgn pks valid A`: read signers,
  the multi-user game after key generation with a read signer against `memoFromS` from the empty
  memo, the forgery verified as reads, masked by `pdOK`.
* `SelMemoSOK`, `SignsSN`: a memo agreeing with the function; a signer returning the users'
  signatures and memo answers from such a memo.

## Main statements

* `intertwines_muChallenged_memoFromS`: against a function consistent with every user's table,
  the challenged adversary and its memo transform with a read signer satisfying `SignsSN`
  intertwine, from every memo agreeing with the function.
* `evalDistMap_muGame_eq_readsSN`: with distinct `PK.seed`s, the multi-user game has the law of
  `gameReadsWithSN` against the classical reads.
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key keyOf msgPos)
open Quantum.Sponge (Hw hwReadSpec hwReadCmdSpec spongeFnReadRuntime overwrite ReadsTo hwAt
  hwCol hwAt_basis conjTranspose_hwCol_mul_self intertwines_run_pure intertwines_run₂_pure
  intertwines_run₂_bind intertwines_run₂_act_bind intertwines_run_of_run₂ intertwines_run₂_of_run
  intertwines_run_bind run₂_bind_of_classicalOn_pure evalDistMap_eq_of_intertwines)
open Quantum.Qrom.Xmss (not_isHash_inl classicalOn_toQuantumAt_romImpl
  classicalOn_toQuantumAt_romImpl_pure)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec muChallenge muChallenged muGame generateAll
  withMuSignLog MuSignLog)

namespace Quantum.Qrom.Sphincs.Multi

attribute [local irreducible] sphincsRom

variable {n : ℕ}

-- The adversary's commands, as indexed polynomial functors.
set_option quotPrecheck false in
local notation "MuPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n Message (Option Signature))

set_option quotPrecheck false in
local notation "MemoPS" n => QuantumComp.toIPFunctor LocalSig.instruments.{0} (memoSpecS n)

/-! ## Selections and memo answers -/

/-- The selection of key `K` of table `v` against `H` (`QTable.select` on the value `K` signs). -/
def keySel (v : QTable) (H : HashDomain → HashOutput) (K : Key) : SelS :=
  v.select H K.1 K.2.1 K.2.2 (v.valuePos (msgPos K))

theorem keySel_keyOf (v : QTable) (H : HashDomain → HashOutput) (l : Layer) (idx : Index) :
    keySel v H (keyOf l idx) = v.layerSelect H idx l :=
  (v.layerSelect_eq H idx l).symm

/-- The memo answer of the honest signer of `v` on `M`. -/
def memoAnsOf (v : QTable) (H : HashDomain → HashOutput) (M : Message) : MemoAns :=
  (v.index M, fun l ↦ v.layerSelect H (v.index M) l)

/-! ## Read signers -/

/-- A read signer: user, message, user's memo, register. -/
abbrev SignerSN (M : Type) [Fintype M] [DecidableEq M] (n : ℕ) : Type 1 :=
  Fin n → Message → KeyMemo → (B : QReg) →
    QComp (hwReadSpec PairOut HashDomain M) B B (Option Signature × MemoAns)

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The multi-user challenger with honest reads, from a read signer**: local operations and hash
calls as `muChallenge`, regrouped and lifted to port `h`; a signing request answered by `sgn`. -/
noncomputable def challengeWithSN (sgn : SignerSN M n) :
    IPFunctor.CommandSubstitution (MemoPS n)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (hwReadSpec PairOut HashDomain M))
  | A, .prim o =>
      (liftH (regroupCalls hmsgRoute
        (muChallenge sphincsRom (noKeysS (n := n)) A (.prim o)))).liftOrdinary
  | A, .query .hash E ℓ =>
      (liftH (regroupCalls hmsgRoute
        (muChallenge sphincsRom (noKeysS (n := n)) A (.query .hash E ℓ)))).liftOrdinary
  | _, .query (.sign i q) E ℓ =>
      QuantumComp.bind (signAtSN i q E ℓ (sgn i q.1 q.2)) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- **The multi-user game with honest reads after key generation**: the adversary's memo transform
against `challengeWithSN M sgn` from the empty memo, with all users' transcript, the verification
through read ports under the forged user's key, and the winning condition masked by `pdOK`. -/
noncomputable def gameReadsWithSN (sgn : SignerSN M n) (pks : Fin n → PublicKey)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    QComp (hwReadSpec PairOut HashDomain M) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (IFreeM.substitute (challengeWithSN M sgn)
    (memoFromS (fun _ _ ↦ none) (withMuSignLog (A pks)))) fun run ↦
    ((readsProgram M _ (sphincsRom.verify (pks run.1.1) run.1.2)).map Prod.fst).bind fun b ↦
      QuantumComp₂.pure (pdOK pks && sphincsRom.winningCondition (run.2.user run.1.1) run.1.2 &&
        run.2.allValid valid && b)

variable {M}

/-! ## The commands at a signing request -/

/-- The challenged program at a signing request, for any scheme: the signer's answer program,
then the challenged continuation. -/
theorem muChallenged_liftBind_signS {Seed PK SK Req Resp F : Type}
    (sch : SchemeOver RomOracles Seed PK SK Req Resp F) (sks : Fin n → SK) {B : QReg} {α : Type}
    {A : QReg} (i : Fin n) (r : Req) (E : QReg)
    (ℓ : A ≃ (muAdvSpec n Req Resp).In (.sign i r) × E)
    (next : (b : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (muAdvSpec n Req Resp)).B A
        (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ)) →
      IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (muAdvSpec n Req Resp))
        (QuantumComp₂.Leaf B α)
        ((QuantumComp.toIPFunctor LocalSig.instruments.{0} (muAdvSpec n Req Resp)).src A
          (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) b)) :
    muChallenged sch sks
        (IFreeM.liftBind (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) next) =
      QuantumComp₂.bind (SufCma.signTree sch (sks i) r E ℓ) fun resp ↦
        muChallenged sch sks (next (ULift.up resp)) := by
  refine (IFreeM.bind_assoc _ _ _).trans
    (congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_))
  obtain ⟨rfl, a⟩ := l
  rfl

/-- The substituted memo transform at a signing request: the signer's answer program, then the
transform of the continuation with the answer memoized. -/
theorem substitute_memoFromS_liftBind_sign (sgn : SignerSN M n) {C : QReg} {α : Type} {A : QReg}
    (T : SelMemoS n) (i : Fin n) (r : Message) (E : QReg)
    (ℓ : A ≃ (muAdvSpec n Message (Option Signature)).In (.sign i r) × E)
    (next : (b : (MuPS n).B A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ)) →
      IFreeM (MuPS n) (QuantumComp₂.Leaf C α)
        ((MuPS n).src A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) b)) :
    (memoFromS T (IFreeM.liftBind (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) next)).substitute
        (challengeWithSN M sgn) =
      QuantumComp₂.bind (signAtSN i (r, T i) E ℓ (sgn i r (T i)))
        fun a ↦ (memoFromS (T.put i a.2) (next (ULift.up a.1))).substitute
          (challengeWithSN M sgn) := by
  refine (IFreeM.bind_assoc _ _ _).trans
    (congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_))
  obtain ⟨rfl, a⟩ := l
  rfl

/-! ## Intertwining with the game -/

section intertwine

attribute [local irreducible] QTable.select QTable.signature

variable {t : (HashDomain → PairOut) × (PairOut → HashDomain) × (PairOut → HashDomain)}
  {W : Hw PairOut HashDomain} {m : M}

/-- **A deterministic step on each side, then intertwining continuations**: an honest
computation returning `a₀` with certainty against the regrouped function and a read program
returning `b₀` with certainty on the block, continued by programs intertwining at `a₀`, `b₀`. -/
theorem intertwines_bind_classicalOn_readsToS {B C : QReg} {α β γ : Type}
    {x₁ : QComp romSpec B B α} {a₀ : α}
    (h₁ : ClassicalOn (additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)) x₁ (pure a₀)
      LinearMap.id)
    {x₂ : QComp (hwReadSpec PairOut HashDomain M) B B β} {b₀ : β} (h₂ : ReadsTo t W m x₂ b₀)
    {k₁ : α → QComp romSpec B C γ} {k₂ : β → QComp (hwReadSpec PairOut HashDomain M) B C γ}
    (hk : DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments (k₁ a₀))
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments (k₂ b₀))) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (x₁.bind k₁))
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments (x₂.bind k₂)) := by
  rw [run₂_bind_of_classicalOn_pure h₁]
  intro c
  have key : ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments
      (x₂.bind k₂)).branch c ∘ₗ (hwAt W m).amplifyLeft B =
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments (k₂ b₀)).branch c ∘ₗ
        (hwAt W m).amplifyLeft B := by
    refine LinearMap.ext fun ρ ↦ ?_
    have h₀ : ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments x₂).branch b₀
        ((hwAt W m).amplifyLeft B ρ) = (hwAt W m).amplifyLeft B ρ :=
      LinearMap.congr_fun h₂.1 ρ
    have h₃ : ∀ b ≠ b₀, ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments
        x₂).branch b ((hwAt W m).amplifyLeft B ρ) = 0 := fun b hb ↦
      LinearMap.congr_fun (h₂.2 b hb) ρ
    change ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments (x₂.bind k₂)).branch
        c ((hwAt W m).amplifyLeft B ρ) =
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments (k₂ b₀)).branch c
        ((hwAt W m).amplifyLeft B ρ)
    rw [QuantumRuntime.run₂_bind]
    erw [DSubInstrument.branch_bind_apply]
    rw [tsum_eq_single b₀ fun b hb ↦ by erw [h₃ b hb, map_zero]]
    erw [h₀]
  exact key.trans (hk c)

/-- **A local operation, a deterministic step on each side, then intertwining continuations.** -/
theorem intertwines_act_bind_bindS {A B C : QReg} {α β γ : Type} (p : SubInstrument A B Unit)
    {x₁ : QComp romSpec B B α} {a₀ : α}
    (h₁ : ClassicalOn (additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)) x₁ (pure a₀)
      LinearMap.id)
    {x₂ : QComp (hwReadSpec PairOut HashDomain M) B B β} {b₀ : β} (h₂ : ReadsTo t W m x₂ b₀)
    {k₁ : α → QComp romSpec B C γ} {k₂ : β → QComp (hwReadSpec PairOut HashDomain M) B C γ}
    (hk : DSubInstrument.Intertwines ((hwAt W m).amplifyLeft B) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments (k₁ a₀))
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments (k₂ b₀))) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (((QComp.act p).bind fun _ ↦ x₁).bind k₁))
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments
        (((QComp.act p).bind fun _ ↦ x₂).bind k₂)) := by
  rw [QuantumComp₂.bind_assoc, QuantumComp₂.bind_assoc]
  exact intertwines_run₂_act_bind
    (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m) p
    fun _ ↦ intertwines_bind_classicalOn_readsToS h₁ h₂ hk

variable (t W m)

/-- **The memo agrees with `H`**: every memoized selection of user `i` is the key's selection of
`w`'s user `i` against `H`. -/
def SelMemoSOK (w : QTableN n) (H : HashDomain → HashOutput) (T : SelMemoS n) : Prop :=
  ∀ i K o, T i K = some o → o = keySel (w.user i) H K

theorem selMemoSOK_empty (w : QTableN n) (H : HashDomain → HashOutput) :
    SelMemoSOK w H fun _ _ ↦ none :=
  fun _ _ _ h ↦ by simp at h

/-- Memoizing the honest memo answer keeps the memo agreeing with `H`. -/
theorem SelMemoSOK.put {w : QTableN n} {H : HashDomain → HashOutput} {T : SelMemoS n}
    (hT : SelMemoSOK w H T) (i : Fin n) (r : Message) :
    SelMemoSOK w H (T.put i (memoAnsOf (w.user i) H r)) := by
  intro j K o h
  by_cases hji : j = i ∧ K = keyOf K.1 (memoAnsOf (w.user i) H r).1
  · obtain ⟨rfl, hK⟩ := hji
    rw [hK, SelMemoS.put_self] at h
    rw [hK, keySel_keyOf]
    exact (Option.some.inj h).symm
  · rw [SelMemoS.put_of_ne _ hji] at h
    exact hT j K o h

/-- **A read signer returning the users' signatures and memo answers**: from a memo of user `i`
agreeing with the regrouped function, the signer of user `i` returns `w`'s signature and memo
answer with certainty on the block. -/
def SignsSN (w : QTableN n) (sgn : SignerSN M n) : Prop :=
  ∀ i r h B, (∀ K o, h K = some o →
      o = keySel (w.user i) (regroup hmsgRoute (overwrite W t).1) K) →
    ReadsTo t W m (sgn i r h B)
      ((w.user i).signature (regroup hmsgRoute (overwrite W t).1) r,
        memoAnsOf (w.user i) (regroup hmsgRoute (overwrite W t).1) r)

/-- **The challenged adversary and its memo transform intertwine**: against the regrouped
`(overwrite W t).1`, consistent with every user's table, the adversary against the challenger with
the master seeds and its memo transform against `challengeWithSN M sgn` with a signer satisfying
`SignsSN`, from every memo that agrees with the function. -/
theorem intertwines_muChallenged_memoFromS {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hv : ∀ i, Consistent (S0 i) (w.user i) (overwrite W t).1) {sgn : SignerSN M n}
    (hsgn : SignsSN t W m w sgn) {C : QReg} {α : Type} {A : QReg}
    (x : IFreeM (MuPS n) (QuantumComp₂.Leaf C α) A) (T : SelMemoS n)
    (hT : SelMemoSOK w (regroup hmsgRoute (overwrite W t).1) T) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft A) (fun _ ↦ (hwAt W m).amplifyLeft C)
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (muChallenged sphincsRom S0 x))
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments
        ((memoFromS T x).substitute (challengeWithSN M sgn))) := by
  induction x using IFreeM.inductionOn generalizing T with
  | pure _ y =>
    exact intertwines_run₂_of_run
      (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
      (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m)
      (intertwines_run_pure y)
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · refine intertwines_run₂_of_run
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m)
        (intertwines_run_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
          (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m)
          (intertwines_liftH t W m (muChallenge sphincsRom S0 A (.prim o))) fun p ↦ ?_)
      obtain ⟨u, b, hb⟩ := p
      subst hb
      exact intertwines_run_of_run₂ (ih b T hT)
    · refine intertwines_run₂_of_run
        (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
        (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m)
        (intertwines_run_bind (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
          (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m)
          (intertwines_liftH t W m (muChallenge sphincsRom S0 A (.query .hash E ℓ))) fun p ↦ ?_)
      obtain ⟨u, b, hb⟩ := p
      subst hb
      exact intertwines_run_of_run₂ (ih b T hT)
    · rw [muChallenged_liftBind_signS, substitute_memoFromS_liftBind_sign, SufCma.signTree,
        signAtSN]
      have hc := (classicalOn_toQuantumAt_romImpl_pure
        (B := QReg.of ((SufCma.advSpec Message (Option Signature)).Out (.sign r) × E))
        (not_romRead_inl _) _ (signReads_sign (agrees_regroup (hv i)) r)).congr
        (congrArg pure (eval_sign (agrees_regroup (hv i)) r)) rfl
      refine intertwines_act_bind_bindS (A := A)
        (B := QReg.of ((SufCma.advSpec Message (Option Signature)).Out (.sign r) × E))
        (C := C) (b₀ := ((w.user i).signature (regroup hmsgRoute (overwrite W t).1) r,
          memoAnsOf (w.user i) (regroup hmsgRoute (overwrite W t).1) r))
        (SubInstrument.relabel ℓ) hc ?_ ?_
      · exact hsgn i r (T i) _ fun K o ho ↦ hT i K o ho
      · exact ih _ _ (hT.put i r)

/-- **The game and its reads intertwine**: against the regrouped `(overwrite W t).1`, consistent
with every user's table, with distinct `PK.seed`s, the multi-user game runs as `gameReadsWithSN`
from the users' public keys with a signer satisfying `SignsSN`. -/
theorem intertwines_muGame_readsSN {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hv : ∀ i, Consistent (S0 i) (w.user i) (overwrite W t).1) (hP : PDistinct w)
    {sgn : SignerSN M n} (hsgn : SignsSN t W m w sgn)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    DSubInstrument.Intertwines ((hwAt W m).amplifyLeft (QReg.of Unit))
      (fun _ ↦ (hwAt W m).amplifyLeft (QReg.of Unit))
      ((additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).run₂ .instruments
        (muGame sphincsRom valid S0 A))
      ((spongeFnReadRuntime PairOut HashDomain t W m).run₂ .instruments
        (gameReadsWithSN M sgn (fun i ↦ (w.user i).publicKey) valid A)) := by
  have hpd : pdOK (fun i ↦ (w.user i).publicKey) = true :=
    pdOK_eq_true fun i j h ↦ hP (by
      simpa only [QTable.publicKey_publicSeed] using h)
  rw [muGame, run₂_bind_of_classicalOn_pure
    ((classicalOn_toQuantumAt_romImpl (regroup hmsgRoute (overwrite W t).1) _ _).congr
      (simulateQ_generateAll (fun _ ↦ rfl) n S0 w fun i ↦ agrees_regroup (hv i)) rfl)]
  dsimp only
  refine intertwines_run₂_bind
    (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m)
    (intertwines_muChallenged_memoFromS t W m hv hsgn _ _ (selMemoSOK_empty w _)) fun run ↦ ?_
  refine intertwines_run₂_bind
    (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (V := hwAt W m)
    (intertwines_readsProgram not_isHash_inl _ (isHash_verify _ _)) fun b ↦ ?_
  rw [hpd, Bool.true_and]
  exact intertwines_run₂_pure _

/-- **The game is its reads at a fixed function** consistent with every user's table, with
distinct `PK.seed`s. -/
theorem evalDistMap_muGame_eq_readsSN {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hv : ∀ i, Consistent (S0 i) (w.user i) (overwrite W t).1) (hP : PDistinct w)
    {sgn : SignerSN M n} (hsgn : SignsSN t W m w sgn)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (ρ : SubState (QReg.of Unit)) {γ : Type*} [MeasurableSpace γ]
    (f : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → γ) :
    (additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1)).evalDistMap .instruments
        (muGame sphincsRom valid S0 A) ρ f =
      (spongeFnReadRuntime PairOut HashDomain t W m).evalDistMap .instruments
        (gameReadsWithSN M sgn (fun i ↦ (w.user i).publicKey) valid A) ρ f :=
  evalDistMap_eq_of_intertwines
    (R₁ := additiveOracleRuntime (regroup hmsgRoute (overwrite W t).1))
    (R₂ := spongeFnReadRuntime PairOut HashDomain t W m) (K := hwCol W m)
    (conjTranspose_hwCol_mul_self W m) (hwAt_basis W m)
    (intertwines_run_of_run₂ (intertwines_muGame_readsSN t W m hv hP hsgn valid A)) ρ f

end intertwine

end Quantum.Qrom.Sphincs.Multi

end
