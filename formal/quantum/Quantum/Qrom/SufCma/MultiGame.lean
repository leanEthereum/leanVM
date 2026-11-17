module

public import Quantum.Qrom.SufCma.Game

@[expose] public section

/-!
# The multi-user SUF-CMA game in the QROM

`n` users draw their seeds independently from the scheme's seed law and generate their keys in
index order. The adversary sees all public keys, calls the random function `H` on superpositions
(the port `.hash`) and asks classical signing requests of any user (the port `.sign i r` asks user
`i` to sign `r`); it returns a user and a claimed forgery for that user. The challenger and the
signer are the single-user ones (`romImpl`, `signTree`); the per-user transcript (`MuSignLog.user`)
decides the winning condition of the forged user.

The game also takes a transcript validity `valid` (leanXMSS: no leaf index requested twice) and a
run in which some user's transcript is invalid loses: the honest signers never misuse their keys,
as in the single-user game, where an invalid transcript fails the winning condition. For a
validity implied by the winning condition (or `fun _ ↦ true`) and `n = 1` this is the single-user
game (`Quantum.Qrom.SufCma.Multi.muQuantumStronglyUnforgeable_one_iff`).

* `muGame sch valid S0 A`: key generation of all users from the seeds `S0`, the adversary against
  the challenger with the transcript of all users, then the verification of the forgery under the
  forged user's public key.
* `muWinProb sch valid n A`: the winning probability, averaged over i.i.d. seeds and `H`.
* `MuQuantumStronglyUnforgeable sch valid n perUser total bound`: every adversary making at most
  `q` calls of `H`, at most `perUser` requests to each user and at most `total` requests overall
  on every path wins with probability at most `bound q`.

## Main statements

* `lossless_muGame`: the game of a lossless adversary is lossless.
* `isTotalQueryBound_muChallenged`, `isTotalQueryBound_muGame`: the challenged adversary makes at
  most `q + sc * total` calls of `H`; the game adds key generation and verification.
* `muWinProb_eq_uniform`: for a uniform seed law, the winning probability is `c ^ n` times the sum
  over the seed vectors.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

universe u v w w₁

namespace Quantum.Qrom.SufCma.Multi

open Common HashSig
open Quantum.Qrom.SufCma (romImpl signTree SignLog lossless_romImpl lossless_signTree
  isTotalQueryBound_toQuantumAt_romImpl)

/-! ## The adversary -/

/-- The adversary's ports: the random function, and one classical signing port per user and
request. -/
inductive MuPort (n : ℕ) (Req : Type) where
  /-- A call of `H`. -/
  | hash
  /-- The signing request `r` to user `i`. -/
  | sign (i : Fin n) (r : Req)

variable (n : ℕ) (PK Req Resp F : Type)

/-- The adversary's signature: the hash port acts on `HashDomain × HashOutput` and reports
nothing; a signing port acts on no register and reports the signer's answer. -/
@[reducible]
def muAdvSpec : QuantumOracleSpec.{0, 0} where
  Port := MuPort n Req
  In
    | .hash => QReg.of (HashDomain × HashOutput)
    | .sign _ _ => QReg.of Unit
  Out
    | .hash => QReg.of (HashDomain × HashOutput)
    | .sign _ _ => QReg.of Unit
  Result
    | .hash => Unit
    | .sign _ _ => Resp

/-- A multi-user adversary: from all public keys, a program over `muAdvSpec` that returns a user
and a claimed forgery for that user. -/
abbrev MuAdversary :=
  (Fin n → PK) → QComp (muAdvSpec n Req Resp) (QReg.of Unit) (QReg.of Unit) (Fin n × F)

variable {n PK Req Resp F}

/-- A hash call costs one, a signing request nothing. -/
def hashCharge : MuPort n Req → ℕ
  | .hash => 1
  | .sign _ _ => 0

/-- A signing request costs one, a hash call nothing. -/
def signCharge : MuPort n Req → ℕ
  | .hash => 0
  | .sign _ _ => 1

/-- A signing request to user `i` costs one, every other call nothing. -/
def signChargeAt (i : Fin n) : MuPort n Req → ℕ
  | .hash => 0
  | .sign j _ => if j = i then 1 else 0

/-- A charge on ports as a charge on commands: a call of port `p` costs `c p`, a local operation
nothing. -/
def cmdCharge {L : LocalSig.{u, v}} (c : MuPort n Req → ℕ) (A : QReg) :
    QuantumComp.Cmd L (muAdvSpec n Req Resp) A → ℕ
  | .prim _ => 0
  | .query p _ _ => c p

/-! ## The signing transcript -/

variable (n Req Resp) in
/-- The transcript of all users: each request with its user and its answer, in order. -/
abbrev MuSignLog := QueryLog ((Fin n × Req) →ₒ Resp)

/-- **User `i`'s transcript**: the requests to user `i` with their answers, in order. -/
def MuSignLog.user (log : MuSignLog n Req Resp) (i : Fin n) : SignLog Req Resp :=
  log.filterMap fun e ↦ if e.1.1 = i then some ⟨e.1.2, e.2⟩ else none

@[simp]
theorem MuSignLog.user_nil (i : Fin n) : MuSignLog.user ([] : MuSignLog n Req Resp) i = [] :=
  rfl

theorem MuSignLog.user_append_singleton (log : MuSignLog n Req Resp) (j : Fin n) (r : Req)
    (b : Resp) (i : Fin n) :
    MuSignLog.user (log ++ [⟨(j, r), b⟩]) i =
      MuSignLog.user log i ++ if j = i then [⟨r, b⟩] else [] := by
  unfold MuSignLog.user
  rw [List.filterMap_append]
  by_cases h : j = i <;> simp [h]

/-- The transcript after a command answered `b`: a signing request appends its user, itself and
its answer. -/
def muLogAfter {L : LocalSig.{u, v}} {A : QReg} :
    (c : QuantumComp.Cmd L (muAdvSpec n Req Resp) A) → c.Resp → MuSignLog n Req Resp →
      MuSignLog n Req Resp
  | .query (.sign i r) _ _, b, log => log ++ [⟨(i, r), b.down⟩]
  | _, _, log => log

/-- Run a program and keep the transcript of all users, starting from `log`. -/
def muLogSigns {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    (leaf : ∀ u, X u → MuSignLog n Req Resp → Y u) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (muAdvSpec n Req Resp)) X A →
      MuSignLog n Req Resp → IFreeM (QuantumComp.toIPFunctor L (muAdvSpec n Req Resp)) Y A
  | _, .pure x, log => .pure (leaf _ x log)
  | _, .liftBind c next, log => .liftBind c fun b ↦ muLogSigns leaf (next b) (muLogAfter c b log)

/-- **The program with the transcript of all users**: the same commands; the leaf also returns
the signing requests with their users and answers, in order. -/
def withMuSignLog {L : LocalSig.{u, v}} {A B : QReg} {α : Type w}
    (x : QuantumComp₂ L (muAdvSpec n Req Resp) A B α) :
    QuantumComp₂ L (muAdvSpec n Req Resp) A B (α × MuSignLog n Req Resp) :=
  muLogSigns (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x []

/-- Keeping the transcript keeps every roll bound: the commands are the same. -/
theorem isRollBound_muLogSigns {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    {β : Type*} {canRoll : (A : QReg) → QuantumComp.Cmd L (muAdvSpec n Req Resp) A → β → Prop}
    {cost : (A : QReg) → QuantumComp.Cmd L (muAdvSpec n Req Resp) A → β → β}
    (leaf : ∀ u, X u → MuSignLog n Req Resp → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L (muAdvSpec n Req Resp)) X A)
    (log : MuSignLog n Req Resp) {b : β} (hx : IFreeM.IsRollBound x b canRoll cost) :
    IFreeM.IsRollBound (muLogSigns leaf x log) b canRoll cost := by
  induction x using IFreeM.inductionOn generalizing log b with
  | pure _ _ => trivial
  | liftBind _ c next ih => exact ⟨hx.1, fun r ↦ ih r _ (hx.2 r)⟩

/-- Keeping the transcript keeps losslessness. -/
theorem lossless_withMuSignLog {A B : QReg} {α : Type} {x : QComp (muAdvSpec n Req Resp) A B α}
    (hx : x.Lossless .instruments) : (withMuSignLog x).Lossless .instruments :=
  isRollBound_muLogSigns _ x [] hx

/-- Keeping the transcript keeps every charge bound. -/
theorem isChargeBound_withMuSignLog {A B : QReg} {α : Type}
    {x : QComp (muAdvSpec n Req Resp) A B α} {c : MuPort n Req → ℕ} {m : ℕ}
    (hx : IFreeM.IsChargeBound x (cmdCharge c) m) :
    IFreeM.IsChargeBound (withMuSignLog x) (cmdCharge c) m :=
  isRollBound_muLogSigns _ x [] hx

/-! ## Key generation -/

variable {ι : Type} {O : OracleSpec.{0, 0} ι} {Seed SK : Type}

/-- **Key generation of users `0, …, n - 1`** from their seeds, in index order. -/
def generateAll (sch : SchemeOver O Seed PK SK Req Resp F) :
    (n : ℕ) → (Fin n → Seed) → OracleComp O (Fin n → PK × SK)
  | 0, _ => pure Fin.elim0
  | n + 1, S0 => do
      let k ← sch.generateKeys (S0 0)
      let ks ← generateAll sch n (S0 ∘ Fin.succ)
      pure (Fin.cons k ks : Fin (n + 1) → PK × SK)

/-- A classical algorithm run by `romImpl`, sequenced: the program of `oa >>= f` is the program
of `oa` followed by the programs of `f`. -/
theorem toQuantumAt_romImpl_bind (B : QReg) {α β : Type} (oa : OracleComp RomOracles α)
    (f : α → OracleComp RomOracles β) :
    (oa >>= f).toQuantumAt (romImpl B) =
      (oa.toQuantumAt (romImpl B)).bind fun a ↦ (f a).toQuantumAt (romImpl B) := by
  rw [OracleComp.toQuantumAt, simulateQ_bind]
  rfl

/-! ## The challenger -/

variable (sch : SchemeOver RomOracles Seed PK SK Req Resp F)
  (valid : SignLog Req Resp → Bool)

/-- Every user's transcript is valid. -/
def MuSignLog.allValid (log : MuSignLog n Req Resp) : Bool :=
  decide (∀ j, valid (log.user j) = true)

/-- **The challenger**: a local operation stays, a hash call becomes the same call of `romSpec`,
and a signing request to user `i` is answered by user `i`'s signer (`signTree`). -/
noncomputable def muChallenge (sks : Fin n → SK) :
    CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} (muAdvSpec n Req Resp))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} romSpec)
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query .hash E ℓ =>
      QuantumComp.queryBind (spec := romSpec) () E ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.sign i r) E ℓ =>
      QuantumComp.bind (signTree sch (sks i) r E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program with the challenger substituted, on `romSpec`. -/
noncomputable def muChallenged (sks : Fin n → SK) {A B : QReg} {α : Type}
    (x : QComp (muAdvSpec n Req Resp) A B α) : QComp romSpec A B α :=
  IFreeM.substitute (muChallenge sch sks) x

/-- **The multi-user SUF-CMA game** at the seeds `S0`: key generation of all users, the adversary
against the challenger with the transcript of all users, the verification of its forgery under the
forged user's public key, the scheme's winning condition on that user's transcript, and the
validity of every user's transcript. -/
noncomputable def muGame (S0 : Fin n → Seed) (A : MuAdversary n PK Req Resp F) :
    QComp romSpec (QReg.of Unit) (QReg.of Unit) Bool :=
  ((generateAll sch n S0).toQuantumAt (romImpl _)).bind fun keys ↦
    (muChallenged sch (fun i ↦ (keys i).2) (withMuSignLog (A fun i ↦ (keys i).1))).bind
      fun run ↦
        ((sch.verify (keys run.1.1).1 run.1.2).toQuantumAt (romImpl _)).bind fun verified ↦
          QuantumComp₂.pure (sch.winningCondition (run.2.user run.1.1) run.1.2 &&
            run.2.allValid valid && verified)

/-- **The winning probability**: the game's probability of returning `true` in the QROM, averaged
over independent seeds of the users from the scheme's seed law. -/
noncomputable def muWinProb [Fintype Seed] (n : ℕ) (A : MuAdversary n PK Req Resp F) : ℝ≥0∞ :=
  ∑ S0 : Fin n → Seed, (∏ i, Pr{let s ← sch.sampleSeed}[s = S0 i]) *
    qromEvalDistMap .instruments (muGame sch valid S0 A) (SubState.basis ()) (fun _ p ↦ p.2.2)
      {true}

/-- **Multi-user SUF-CMA of `sch` against quantum adversaries in the QROM**: every adversary that
sees the public keys of `n` users and makes at most `q` calls of `H`, at most `perUser` signing
requests to each user and at most `total` signing requests overall on every path wins, against any
user of its choice and with every user's transcript valid, with probability at most `bound q`. -/
def MuQuantumStronglyUnforgeable [Fintype Seed] (n perUser total : ℕ) (bound : ℕ → ℝ≥0∞) :
    Prop :=
  ∀ q (A : MuAdversary n PK Req Resp F),
    (∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q) →
    (∀ pks i, IFreeM.IsChargeBound (A pks) (cmdCharge (signChargeAt i)) perUser) →
    (∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total) →
    muWinProb sch valid n A ≤ bound q

/-- **A uniform seed law**: the winning probability is `c ^ n` times the sum over the seed vectors
of the game's winning probability. -/
theorem muWinProb_eq_uniform [Fintype Seed] {c : ℝ≥0∞}
    (hseed : ∀ S0, Pr{let s ← sch.sampleSeed}[s = S0] = c) (A : MuAdversary n PK Req Resp F) :
    muWinProb sch valid n A = c ^ n * ∑ S0 : Fin n → Seed,
      qromEvalDistMap .instruments (muGame sch valid S0 A) (SubState.basis ()) (fun _ p ↦ p.2.2)
        {true} := by
  rw [muWinProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S0 _ ↦ ?_
  simp only [hseed, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Losslessness -/

/-- The challenger keeps losslessness. -/
theorem lossless_substitute_muChallenge (sks : Fin n → SK) {X : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (muAdvSpec n Req Resp) X A)
    (hx : x.Lossless .instruments) :
    QuantumComp.Lossless (spec := romSpec) LocalSig.Interp.instruments
      (IFreeM.substitute (muChallenge sch sks) x) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rw [IFreeM.substitute_liftBind]
    refine QuantumComp.Lossless.bind ?_ fun u ⟨b, h⟩ ↦ ?_
    · rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
      · exact (QuantumComp.lossless_primBind_iff _ _).mpr ⟨hx.1, fun _ ↦ trivial⟩
      · exact (QuantumComp.lossless_queryBind_iff _ _ _ _).mpr fun _ ↦ trivial
      · exact QuantumComp.Lossless.bind (lossless_signTree sch (sks i) r E ℓ) fun _ _ ↦ trivial
    · subst h
      exact ih b (hx.2 b)

/-- **The game of a lossless adversary is lossless.** -/
theorem lossless_muGame (S0 : Fin n → Seed) {A : MuAdversary n PK Req Resp F}
    (hA : ∀ pks, (A pks).Lossless .instruments) :
    (muGame sch valid S0 A).Lossless .instruments :=
  QuantumComp₂.lossless_bind (lossless_toQuantumAt (lossless_romImpl _) _) fun _ ↦
    QuantumComp₂.lossless_bind
      (lossless_substitute_muChallenge sch _ _ (lossless_withMuSignLog (hA _)))
      fun _ ↦ QuantumComp₂.lossless_bind (lossless_toQuantumAt (lossless_romImpl _) _)
        fun _ ↦ QuantumComp₂.lossless_pure _

/-! ## Call budgets -/

/-- **The challenged adversary's calls.** An adversary making at most `q` hash calls and at most
`total` signing requests on every path, against signers making at most `sc` hash calls per
signature, makes at most `q + sc * total` calls of `H` on every path. -/
theorem isTotalQueryBound_muChallenged (sks : Fin n → SK) {q total sc : ℕ}
    (hsign : ∀ i r, QueryCostAtMost (sch.sign (sks i) r) hashCallCost sc)
    {A B : QReg} {α : Type} {x : QComp (muAdvSpec n Req Resp) A B α}
    (hhash : IFreeM.IsChargeBound x (cmdCharge hashCharge) q)
    (hsignq : IFreeM.IsChargeBound x (cmdCharge signCharge) total) :
    (muChallenged sch sks x).IsTotalQueryBound (q + sc * total) := by
  refine IFreeM.IsChargeBound.substitute (muChallenge sch sks) (fun A c ↦ ?_)
    (hhash.add (hsignq.mul sc))
  rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
  · exact (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial
  · exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
      ⟨by simp [cmdCharge, hashCharge, signCharge], fun _ ↦ trivial⟩
  · have ht : (signTree sch (sks i) r E ℓ).IsTotalQueryBound (0 + sc) :=
      FreeM₂.isChargeBound_bind (Quantum.SufCma.isTotalQueryBound_act _ 0) fun _ ↦
        isTotalQueryBound_toQuantumAt_romImpl _ (hsign i r)
    refine IFreeM.IsChargeBound.mono (n₁ := 0 + sc + 0) ?_
      (by simp [cmdCharge, hashCharge, signCharge])
    exact IFreeM.isChargeBound_bind ht fun _ _ ↦ IFreeM.isChargeBound_pure _ _

/-- **The game's calls**: key generation's `kc`, the challenged adversary's `q + sc * total`, and
verification's `vc`. -/
theorem isTotalQueryBound_muGame (S0 : Fin n → Seed) {A : MuAdversary n PK Req Resp F}
    {q total kc sc vc : ℕ}
    (hkeygen : QueryCostAtMost (generateAll sch n S0) hashCallCost kc)
    (hsign : ∀ sk r, QueryCostAtMost (sch.sign sk r) hashCallCost sc)
    (hverify : ∀ pk f, QueryCostAtMost (sch.verify pk f) hashCallCost vc)
    (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
    (hsignq : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total) :
    (muGame sch valid S0 A).IsTotalQueryBound (kc + (q + sc * total) + vc) := by
  refine QuantumComp.IsTotalQueryBound.mono (n := kc + ((q + sc * total) + (vc + 0))) ?_
    (by omega)
  unfold muGame
  refine FreeM₂.isChargeBound_bind (isTotalQueryBound_toQuantumAt_romImpl _ hkeygen)
    fun keys ↦ ?_
  refine FreeM₂.isChargeBound_bind (isTotalQueryBound_muChallenged sch _ (fun i ↦ hsign _)
    (isChargeBound_withMuSignLog (hhash _)) (isChargeBound_withMuSignLog (hsignq _)))
    fun run ↦ ?_
  exact FreeM₂.isChargeBound_bind
    (isTotalQueryBound_toQuantumAt_romImpl _ (hverify _ run.1.2))
    fun _ ↦ IFreeM.isChargeBound_pure _ _

end Quantum.Qrom.SufCma.Multi

end
