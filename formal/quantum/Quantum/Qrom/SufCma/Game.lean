module

public import Quantum.Qrom.Model
public import Quantum.SufCma.Game

@[expose] public section

/-!
# The SUF-CMA game of a signature scheme against quantum adversaries, in the QROM

The adversary calls the uniform random function `H : HashDomain → HashOutput` on superpositions
(the port `.hash`, on the register `HashDomain × HashOutput`) and asks classical signing requests
(one port `.sign r` per request `r : Req`). The challenger runs a scheme over the model's classical
oracles (`SchemeOver RomOracles`: key generation, signing, verification and winning condition) as
classical algorithms whose hash calls are classical basis calls of the QROM port (`romImpl`), and
logs the signing transcript (`withSignLog`). Structure and names follow the QRPM game
`Quantum.SufCma.Game`.

* `game sch S0 A`: key generation from the seed `S0`, the adversary with every signing request
  answered by the signer (`challenge`), then the verification of the forgery.
* `winProb sch A`: the winning probability, averaged over the scheme's seed law and `H`.
* `QuantumStronglyUnforgeable sch limit bound`: every adversary making at most `q` calls of `H`
  and at most `limit` signing requests on every path wins with probability at most `bound q`.

## Main statements

* `lossless_game`: the game of a lossless adversary is lossless.
* `isTotalQueryBound_challenged`, `isTotalQueryBound_game`: the challenged adversary makes at
  most `q + sc · n` calls of `H` when the adversary makes `q` hash calls and `n` signing requests
  and each signature costs at most `sc` hash calls; the game adds key generation and verification.
* `winProb_eq_uniform`: for a uniform seed, the winning probability is the uniform average over
  the seeds.

For an adversary whose hash calls are classical, this game has the winning probability of
`forgeryGameOver RomOracles` under `runWithRandomOracle`
(`Quantum.Qrom.SufCma.winProb_classicalAdversary`).
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

universe u v w w₁

namespace Quantum.Qrom.SufCma

open Common HashSig

/-! ## The adversary -/

/-- The adversary's ports: the random function, and one classical signing port per request. -/
inductive AdvPort (Req : Type) where
  /-- A call of `H`. -/
  | hash
  /-- The signing request `r`. -/
  | sign (r : Req)

variable (PK Req Resp F : Type)

/-- The adversary's signature: the hash port acts on the register `HashDomain × HashOutput`
(query input, then response) and reports nothing; a signing port acts on no register and reports
the signer's answer. -/
@[reducible]
def advSpec : QuantumOracleSpec.{0, 0} where
  Port := AdvPort Req
  In
    | .hash => QReg.of (HashDomain × HashOutput)
    | .sign _ => QReg.of Unit
  Out
    | .hash => QReg.of (HashDomain × HashOutput)
    | .sign _ => QReg.of Unit
  Result
    | .hash => Unit
    | .sign _ => Resp

/-- A quantum SUF-CMA adversary: from the public key, a program over `advSpec` that keeps its
own registers across calls and returns a claimed forgery. -/
abbrev Adversary := PK → QComp (advSpec Req Resp) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F}

/-- A hash call costs one, a signing request nothing. -/
def hashCharge : AdvPort Req → ℕ
  | .hash => 1
  | .sign _ => 0

/-- A signing request costs one, a hash call nothing. -/
def signCharge : AdvPort Req → ℕ
  | .hash => 0
  | .sign _ => 1

/-- A charge on ports as a charge on commands, for `IPFunctor.IFreeM.IsChargeBound`: a call of
port `i` costs `c i`, a local operation nothing. -/
def cmdCharge {L : LocalSig.{u, v}} (c : AdvPort Req → ℕ) (A : QReg) :
    QuantumComp.Cmd L (advSpec Req Resp) A → ℕ
  | .prim _ => 0
  | .query i _ _ => c i

/-! ## The signing transcript -/

variable (Req Resp) in
/-- The signing transcript: each request with its answer, in order. -/
abbrev SignLog := QueryLog (Req →ₒ Resp)

/-- The transcript after a command answered `b`: a signing request appends itself and its
answer. -/
def logAfter {L : LocalSig.{u, v}} {A : QReg} :
    (c : QuantumComp.Cmd L (advSpec Req Resp) A) → c.Resp → SignLog Req Resp →
      SignLog Req Resp
  | .query (.sign r) _ _, b, log => log ++ [⟨r, b.down⟩]
  | _, _, log => log

/-- Run a program and keep its signing transcript, starting from `log`: the same commands, the
transcript threaded along each path and handed to the leaf map `leaf` at the end. -/
def logSigns {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    (leaf : ∀ u, X u → SignLog Req Resp → Y u) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (advSpec Req Resp)) X A →
      SignLog Req Resp → IFreeM (QuantumComp.toIPFunctor L (advSpec Req Resp)) Y A
  | _, .pure x, log => .pure (leaf _ x log)
  | _, .liftBind c next, log => .liftBind c fun b ↦ logSigns leaf (next b) (logAfter c b log)

/-- **The program with its signing transcript**: the same commands; the leaf also returns the
signing requests and their answers, in order. -/
def withSignLog {L : LocalSig.{u, v}} {A B : QReg} {α : Type w}
    (x : QuantumComp₂ L (advSpec Req Resp) A B α) :
    QuantumComp₂ L (advSpec Req Resp) A B (α × SignLog Req Resp) :=
  logSigns (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x []

/-- Keeping the transcript keeps every roll bound: the commands are the same. -/
theorem isRollBound_logSigns {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    {β : Type*} {canRoll : (A : QReg) → QuantumComp.Cmd L (advSpec Req Resp) A → β → Prop}
    {cost : (A : QReg) → QuantumComp.Cmd L (advSpec Req Resp) A → β → β}
    (leaf : ∀ u, X u → SignLog Req Resp → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L (advSpec Req Resp)) X A) (log : SignLog Req Resp)
    {b : β} (hx : IFreeM.IsRollBound x b canRoll cost) :
    IFreeM.IsRollBound (logSigns leaf x log) b canRoll cost := by
  induction x using IFreeM.inductionOn generalizing log b with
  | pure _ _ => trivial
  | liftBind _ c next ih => exact ⟨hx.1, fun r ↦ ih r _ (hx.2 r)⟩

/-- Keeping the signing transcript keeps losslessness. -/
theorem lossless_withSignLog {A B : QReg} {α : Type} {x : QComp (advSpec Req Resp) A B α}
    (hx : x.Lossless .instruments) : (withSignLog x).Lossless .instruments :=
  isRollBound_logSigns _ x [] hx

/-- Keeping the signing transcript keeps every charge bound. -/
theorem isChargeBound_withSignLog {A B : QReg} {α : Type} {x : QComp (advSpec Req Resp) A B α}
    {c : AdvPort Req → ℕ} {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge c) n) :
    IFreeM.IsChargeBound (withSignLog x) (cmdCharge c) n :=
  isRollBound_logSigns _ x [] hx

/-! ## The challenger -/

/-- **The model's classical oracles, by classical calls of the QROM port** beside the held
register `B`: coins by uniform coins, `H x` by a basis call of the port at `(x, 0)`, reading the
response. -/
noncomputable def romImpl (B : QReg) : QueryImpl RomOracles (QComp romSpec B B)
  | .inl n => QComp.coinImpl romSpec B n
  | .inr x => QComp.callBasis (spec := romSpec) () B ((x, 0) : HashDomain × HashOutput)
      fun o _ ↦ (o : HashDomain × HashOutput).2

variable {Seed SK : Type} (sch : SchemeOver RomOracles Seed PK SK Req Resp F)

/-- The answer to the signing request `r` with the adversary's register `A ≃ Unit × E` held:
relabel the register, then run the scheme's signer with `romImpl`. -/
noncomputable def signTree (sk : SK) (r : Req) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec Req Resp).In (.sign r) × E) :
    QComp romSpec A (QReg.of ((advSpec Req Resp).Out (.sign r) × E)) Resp :=
  (QComp.act (B := QReg.of ((advSpec Req Resp).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ (sch.sign sk r).toQuantumAt (romImpl _)

/-- **The challenger**: a local operation stays, a hash call becomes the same call of `romSpec`,
and a signing request is answered by the signer (`signTree`). -/
noncomputable def challenge (sk : SK) :
    CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec Req Resp))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} romSpec)
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query .hash E ℓ =>
      QuantumComp.queryBind (spec := romSpec) () E ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signTree sch sk r E ℓ) fun _ l ↦
        QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program with the challenger substituted, on `romSpec`. -/
noncomputable def challenged (sk : SK) {A B : QReg} {α : Type}
    (x : QComp (advSpec Req Resp) A B α) : QComp romSpec A B α :=
  IFreeM.substitute (challenge sch sk) x

/-- **The quantum SUF-CMA game** at the seed `S0`, as `forgeryGameOver RomOracles` for `sch`: key
generation, the adversary against the challenger with its signing transcript, the verification of
its forgery, and the scheme's winning condition. -/
noncomputable def game (S0 : Seed) (A : Adversary PK Req Resp F) :
    QComp romSpec (QReg.of Unit) (QReg.of Unit) Bool :=
  ((sch.generateKeys S0).toQuantumAt (romImpl _)).bind fun keys ↦
    (challenged sch keys.2 (withSignLog (A keys.1))).bind fun run ↦
      ((sch.verify keys.1 run.1).toQuantumAt (romImpl _)).bind fun verified ↦
        QuantumComp₂.pure (sch.winningCondition run.2 run.1 && verified)

/-- **The winning probability**: the game's probability of returning `true` in the QROM,
averaged over the scheme's seed law. -/
noncomputable def winProb [Fintype Seed] (A : Adversary PK Req Resp F) : ℝ≥0∞ :=
  ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] *
    qromEvalDistMap .instruments (game sch S0 A) (SubState.basis ()) (fun _ p ↦ p.2.2) {true}

/-- **SUF-CMA of `sch` against quantum adversaries in the QROM**: every adversary that makes at
most `q` calls of `H` and at most `limit` signing requests on every path wins with probability at
most `bound q`. The signer's, key generation's and verification's calls are not charged. -/
def QuantumStronglyUnforgeable [Fintype Seed] (limit : ℕ) (bound : ℕ → ℝ≥0∞) : Prop :=
  ∀ q (A : Adversary PK Req Resp F),
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) limit) → winProb sch A ≤ bound q

/-- **A uniform seed**: the winning probability is the uniform average over the seeds of the
game's winning probability. -/
theorem winProb_eq_uniform [Fintype Seed] {c : ℝ≥0∞}
    (hseed : ∀ S0, Pr{let s ← sch.sampleSeed}[s = S0] = c) (A : Adversary PK Req Resp F) :
    winProb sch A = c * ∑ S0 : Seed,
      qromEvalDistMap .instruments (game sch S0 A) (SubState.basis ()) (fun _ p ↦ p.2.2)
        {true} := by
  rw [winProb, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S0 _ ↦ by rw [hseed]

/-! ## Losslessness -/

/-- The model's oracles are answered by lossless programs. -/
theorem lossless_romImpl (B : QReg) (t : RomOracles.Domain) :
    (romImpl B t).Lossless .instruments := by
  rcases t with n | x
  exacts [QComp.lossless_coinImpl n, QComp.lossless_callBasis _ _ _ _]

/-- The signer's answer is lossless. -/
theorem lossless_signTree (sk : SK) (r : Req) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec Req Resp).In (.sign r) × E) :
    (signTree sch sk r E ℓ).Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_relabel _)) fun _ ↦
    lossless_toQuantumAt (lossless_romImpl _) _

/-- The challenger keeps losslessness. -/
theorem lossless_substitute_challenge (sk : SK) {X : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (advSpec Req Resp) X A)
    (hx : x.Lossless .instruments) :
    QuantumComp.Lossless (spec := romSpec) LocalSig.Interp.instruments
      (IFreeM.substitute (challenge sch sk) x) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rw [IFreeM.substitute_liftBind]
    refine QuantumComp.Lossless.bind ?_ fun u ⟨b, h⟩ ↦ ?_
    · rcases c with o | ⟨_ | r, E, ℓ⟩
      · exact (QuantumComp.lossless_primBind_iff _ _).mpr ⟨hx.1, fun _ ↦ trivial⟩
      · exact (QuantumComp.lossless_queryBind_iff _ _ _ _).mpr fun _ ↦ trivial
      · exact QuantumComp.Lossless.bind (lossless_signTree sch sk r E ℓ) fun _ _ ↦ trivial
    · subst h
      exact ih b (hx.2 b)

/-- **The game of a lossless adversary is lossless.** -/
theorem lossless_game (S0 : Seed) {A : Adversary PK Req Resp F}
    (hA : ∀ pk, (A pk).Lossless .instruments) : (game sch S0 A).Lossless .instruments :=
  QuantumComp₂.lossless_bind (lossless_toQuantumAt (lossless_romImpl _) _) fun keys ↦
    QuantumComp₂.lossless_bind
      (lossless_substitute_challenge sch keys.2 _ (lossless_withSignLog (hA keys.1)))
      fun _ ↦ QuantumComp₂.lossless_bind (lossless_toQuantumAt (lossless_romImpl _) _)
        fun _ ↦ QuantumComp₂.lossless_pure _

/-! ## Call budgets -/

/-- Answering one of the model's queries makes as many calls as it costs: none for a coin, one
for `H`. -/
theorem isTotalQueryBound_romImpl (B : QReg) (t : RomOracles.Domain) :
    (romImpl B t).IsTotalQueryBound (hashCallCost t) := by
  rcases t with n | x
  · exact Quantum.SufCma.isTotalQueryBound_act _ _
  · exact Quantum.SufCma.isTotalQueryBound_callBasis _ _ _ _

/-- **A classical algorithm making at most `n` hash calls** (`QueryCostAtMost`, coins free) runs
to a program making at most `n` calls of `romSpec`. -/
theorem isTotalQueryBound_toQuantumAt_romImpl (B : QReg) {α : Type}
    {oa : OracleComp RomOracles α} {n : ℕ} (h : QueryCostAtMost oa hashCallCost n) :
    (oa.toQuantumAt (romImpl B)).IsTotalQueryBound n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    have hb := FreeM₂.isChargeBound_bind (isTotalQueryBound_romImpl B t) fun y ↦ ih y (h.2 y)
    rwa [Nat.add_sub_cancel' h.1] at hb

/-- **The challenged adversary's calls.** An adversary making at most `q` hash calls and at most
`n` signing requests on every path, against a signer making at most `sc` hash calls per
signature, makes at most `q + sc * n` calls of `H` on every path. -/
theorem isTotalQueryBound_challenged (sk : SK) {q n sc : ℕ}
    (hsign : ∀ r, QueryCostAtMost (sch.sign sk r) hashCallCost sc)
    {A B : QReg} {α : Type} {x : QComp (advSpec Req Resp) A B α}
    (hhash : IFreeM.IsChargeBound x (cmdCharge hashCharge) q)
    (hsignq : IFreeM.IsChargeBound x (cmdCharge signCharge) n) :
    (challenged sch sk x).IsTotalQueryBound (q + sc * n) := by
  refine IFreeM.IsChargeBound.substitute (challenge sch sk) (fun A c ↦ ?_)
    (hhash.add (hsignq.mul sc))
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial
  · exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
      ⟨by simp [cmdCharge, hashCharge, signCharge], fun _ ↦ trivial⟩
  · have ht : (signTree sch sk r E ℓ).IsTotalQueryBound (0 + sc) :=
      FreeM₂.isChargeBound_bind (Quantum.SufCma.isTotalQueryBound_act _ 0) fun _ ↦
        isTotalQueryBound_toQuantumAt_romImpl _ (hsign r)
    refine IFreeM.IsChargeBound.mono (n₁ := 0 + sc + 0) ?_
      (by simp [cmdCharge, hashCharge, signCharge])
    exact IFreeM.isChargeBound_bind ht fun _ _ ↦ IFreeM.isChargeBound_pure _ _

/-- **The game's calls**: key generation's `kc`, the challenged adversary's `q + sc * n`, and
verification's `vc`. -/
theorem isTotalQueryBound_game (S0 : Seed) {A : Adversary PK Req Resp F} {q n kc sc vc : ℕ}
    (hkeygen : QueryCostAtMost (sch.generateKeys S0) hashCallCost kc)
    (hsign : ∀ sk r, QueryCostAtMost (sch.sign sk r) hashCallCost sc)
    (hverify : ∀ pk f, QueryCostAtMost (sch.verify pk f) hashCallCost vc)
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
    (hsignq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) n) :
    (game sch S0 A).IsTotalQueryBound (kc + (q + sc * n) + vc) := by
  refine QuantumComp.IsTotalQueryBound.mono (n := kc + ((q + sc * n) + (vc + 0))) ?_ (by omega)
  unfold game
  refine FreeM₂.isChargeBound_bind (isTotalQueryBound_toQuantumAt_romImpl _ hkeygen)
    fun keys ↦ ?_
  refine FreeM₂.isChargeBound_bind (isTotalQueryBound_challenged sch keys.2 (hsign keys.2)
    (isChargeBound_withSignLog (hhash keys.1)) (isChargeBound_withSignLog (hsignq keys.1)))
    fun run ↦ ?_
  exact FreeM₂.isChargeBound_bind
    (isTotalQueryBound_toQuantumAt_romImpl _ (hverify keys.1 run.1))
    fun _ ↦ IFreeM.isChargeBound_pure _ _

end Quantum.Qrom.SufCma

end
