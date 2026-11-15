module

public import Statement.LeanXmss
public import Statement.SufCma
public import Quantum.Model
public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.Quantum.Comp.TotalQueryBound
public import PolyFun.IPFunctor.Free.Bound.Substitution

@[expose] public section

/-!
# The SUF-CMA game of leanXMSS against quantum adversaries, in the QRPM

The adversary calls a uniform permutation `φ` of the Keccak state in both directions on
superpositions (the ports `.perm p`) and asks classical signing requests (one port `.sign r` per
request `r`, so the request is classical by construction). The challenger runs the statement's
leanXMSS (`LeanXmss.RandomPermutationModel.sufCmaScheme`: key generation, signing, verification
and winning condition, unchanged) as classical algorithms whose permutation calls are classical
basis calls of the QRPM ports (`permImpl`), and logs the signing transcript (`withSignLog`).

The QRPM state type `S` is a parameter with an equivalence `e : KeccakState ≃ S`: the statement's
`π` is `e.symm ∘ φ ∘ e`. The oracle unitary adds `φ x` into the response register
(`Quantum.permutationRuntime`), so `S` carries an additive group; the intended instance is the
sponge's `X × Z` with `X`, `Z` vectors over `ZMod 2`, where addition is XOR and every element is
its own inverse.

* `game e S0 A`: key generation from the seed `S0`, the adversary with every signing request
  answered by the signer (`challenge`), then the verification of the forgery.
* `winProb e A`: the winning probability, averaged over the uniform seed and `φ`.
* `QuantumStronglyUnforgeable e bound`: every adversary making at most `q` permutation calls and
  at most `lifetime` signing requests on every path wins with probability at most `bound q`.

## Main statements

* `lossless_game`: the game of a lossless adversary is lossless.
* `isTotalQueryBound_challenged`, `isTotalQueryBound_game`: the challenged adversary makes at
  most `q + sc · n` calls of `φ`, `φ⁻¹` when the adversary makes `q` permutation calls and `n`
  signing requests and each signature costs at most `sc` calls; the game adds key generation and
  verification.

For an adversary whose permutation calls are classical, this game has the winning probability of
the statement's `forgeryGame` under `runWithRandomPermutation`
(`Quantum.Xmss.winProb_classicalAdversary`).
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

universe u v w w₁

namespace Quantum.Xmss

open LeanXmss HashSig Common Common.SufCma LeanXmss.RandomPermutationModel
open LeanVM.Semantics (KeccakState)

/-! ## The adversary -/

/-- The adversary's ports: the permutation in either direction, and one classical signing port
per request. -/
inductive AdvPort where
  /-- A call of `φ` or `φ⁻¹`. -/
  | perm (p : PermutationPort)
  /-- The signing request `r`. -/
  | sign (r : SigningRequest)

variable (S : Type) [Fintype S] [DecidableEq S]

/-- The adversary's signature: a permutation port acts on the register `S × S` (query input,
then response) and reports nothing; a signing port acts on no register and reports the
signature. -/
@[reducible]
def advSpec : QuantumOracleSpec.{0, 0} where
  Port := AdvPort
  In
    | .perm _ => QReg.of (S × S)
    | .sign _ => QReg.of Unit
  Out
    | .perm _ => QReg.of (S × S)
    | .sign _ => QReg.of Unit
  Result
    | .perm _ => Unit
    | .sign _ => Option Signature

/-- A quantum SUF-CMA adversary: from the public key, a program over `advSpec` that keeps its
own registers across calls and returns a claimed forgery. -/
abbrev Adversary := PublicKey → QComp (advSpec S) (QReg.of Unit) (QReg.of Unit) Forgery

/-- A permutation call costs one, a signing request nothing. -/
def permCharge : AdvPort → ℕ
  | .perm _ => 1
  | .sign _ => 0

/-- A signing request costs one, a permutation call nothing. -/
def signCharge : AdvPort → ℕ
  | .perm _ => 0
  | .sign _ => 1

variable {S}

/-- A charge on ports as a charge on commands, for `IPFunctor.IFreeM.IsChargeBound`: a call of
port `i` costs `c i`, a local operation nothing. -/
def cmdCharge {L : LocalSig.{u, v}} (c : AdvPort → ℕ) (A : QReg) :
    QuantumComp.Cmd L (advSpec S) A → ℕ
  | .prim _ => 0
  | .query i _ _ => c i

/-! ## The signing transcript -/

/-- The signing transcript: each request with its answer, in order. -/
abbrev SignLog := QueryLog SigningOracleSpec

/-- The transcript after a command answered `b`: a signing request appends itself and its
answer. -/
def logAfter {L : LocalSig.{u, v}} {A : QReg} :
    (c : QuantumComp.Cmd L (advSpec S) A) → c.Resp → SignLog → SignLog
  | .query (.sign r) _ _, b, log => log ++ [⟨r, b.down⟩]
  | _, _, log => log

/-- Run a program and keep its signing transcript, starting from `log`: the same commands, the
transcript threaded along each path and handed to the leaf map `leaf` at the end. -/
def logSigns {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    (leaf : ∀ u, X u → SignLog → Y u) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (advSpec S)) X A → SignLog →
      IFreeM (QuantumComp.toIPFunctor L (advSpec S)) Y A
  | _, .pure x, log => .pure (leaf _ x log)
  | _, .liftBind c next, log => .liftBind c fun b ↦ logSigns leaf (next b) (logAfter c b log)

/-- **The program with its signing transcript**: the same commands; the leaf also returns the
signing requests and their answers, in order. -/
def withSignLog {L : LocalSig.{u, v}} {A B : QReg} {α : Type w}
    (x : QuantumComp₂ L (advSpec S) A B α) : QuantumComp₂ L (advSpec S) A B (α × SignLog) :=
  logSigns (fun _ l log ↦ ⟨l.1, (l.2, log)⟩) x []

/-- Keeping the transcript keeps every roll bound: the commands are the same. -/
theorem isRollBound_logSigns {L : LocalSig.{u, v}} {X : QReg → Type w} {Y : QReg → Type w₁}
    {β : Type*} {canRoll : (A : QReg) → QuantumComp.Cmd L (advSpec S) A → β → Prop}
    {cost : (A : QReg) → QuantumComp.Cmd L (advSpec S) A → β → β}
    (leaf : ∀ u, X u → SignLog → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L (advSpec S)) X A) (log : SignLog) {b : β}
    (hx : IFreeM.IsRollBound x b canRoll cost) :
    IFreeM.IsRollBound (logSigns leaf x log) b canRoll cost := by
  induction x using IFreeM.inductionOn generalizing log b with
  | pure _ _ => trivial
  | liftBind _ c next ih => exact ⟨hx.1, fun r ↦ ih r _ (hx.2 r)⟩

/-- Keeping the signing transcript keeps losslessness. -/
theorem lossless_withSignLog {A B : QReg} {α : Type} {x : QComp (advSpec S) A B α}
    (hx : x.Lossless .instruments) : (withSignLog x).Lossless .instruments :=
  isRollBound_logSigns _ x [] hx

/-- Keeping the signing transcript keeps every charge bound. -/
theorem isChargeBound_withSignLog {A B : QReg} {α : Type} {x : QComp (advSpec S) A B α}
    {c : AdvPort → ℕ} {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge c) n) :
    IFreeM.IsChargeBound (withSignLog x) (cmdCharge c) n :=
  isRollBound_logSigns _ x [] hx

/-! ## The challenger -/

variable [AddCommGroup S] (e : KeccakState ≃ S)

/-- **The statement's oracles, by classical calls of the QRPM ports** beside the held register
`B`: coins by uniform coins, `π s` by a basis call of `φ` at `e s` read back through `e`, and
`π⁻¹` likewise with `φ⁻¹`. -/
noncomputable def permImpl (B : QReg) :
    QueryImpl RandomPermutationOracles (QComp (qrpmSpec S) B B)
  | .inl n => QComp.coinImpl (qrpmSpec S) B n
  | .inr (.forward s) => QComp.callBasis (spec := qrpmSpec S) PermutationPort.forward B
      ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2
  | .inr (.inverse s) => QComp.callBasis (spec := qrpmSpec S) PermutationPort.inverse B
      ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2

/-- The answer to the signing request `r` with the adversary's register `A ≃ Unit × E` held:
relabel the register, then run the statement's signer with `permImpl`. -/
noncomputable def signTree (sk : SecretKey) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec S).In (.sign r) × E) :
    QComp (qrpmSpec S) A (QReg.of ((advSpec S).Out (.sign r) × E)) (Option Signature) :=
  (QComp.act (B := QReg.of ((advSpec S).Out (.sign r) × E)) (SubInstrument.relabel ℓ)).bind
    fun _ ↦ (sufCmaScheme.sign sk r).toQuantumAt (permImpl e _)

/-- **The challenger**: a local operation stays, a permutation call becomes the same call of
`qrpmSpec S`, and a signing request is answered by the signer (`signTree`). -/
noncomputable def challenge (sk : SecretKey) :
    CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec S))
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (qrpmSpec S))
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query (.perm p) E ℓ =>
      QuantumComp.queryBind (spec := qrpmSpec S) p E ℓ fun r ↦ QuantumComp.pure ⟨ULift.up r, rfl⟩
  | _, .query (.sign r) E ℓ =>
      QuantumComp.bind (signTree e sk r E ℓ) fun _ l ↦ QuantumComp.pure ⟨ULift.up l.2, l.1.symm⟩

/-- The adversary's program with the challenger substituted, on `qrpmSpec S`. -/
noncomputable def challenged (sk : SecretKey) {A B : QReg} {α : Type}
    (x : QComp (advSpec S) A B α) : QComp (qrpmSpec S) A B α :=
  IFreeM.substitute (challenge e sk) x

/-- **The quantum SUF-CMA game** at the seed `S0`, as `Common.SufCma.forgeryGame` for
`sufCmaScheme`: key generation, the adversary against the challenger with its signing transcript,
the verification of its forgery, and the scheme's winning condition. -/
noncomputable def game (S0 : MasterSeed) (A : Adversary S) :
    QComp (qrpmSpec S) (QReg.of Unit) (QReg.of Unit) Bool :=
  ((sufCmaScheme.generateKeys S0).toQuantumAt (permImpl e _)).bind fun keys ↦
    (challenged e keys.2 (withSignLog (A keys.1))).bind fun run ↦
      ((sufCmaScheme.verify keys.1 run.1).toQuantumAt (permImpl e _)).bind fun verified ↦
        QuantumComp₂.pure (sufCmaScheme.winningCondition run.2 run.1 && verified)

/-- **The winning probability**: the game's probability of returning `true` in the QRPM,
averaged over the uniform seed. -/
noncomputable def winProb (A : Adversary S) : ℝ≥0∞ :=
  (2 ^ 256 : ℝ≥0∞)⁻¹ * ∑ S0 : MasterSeed,
    qrpmEvalDistMap .instruments (game e S0 A) (SubState.basis ()) (fun _ p ↦ p.2.2) {true}

/-- **SUF-CMA of leanXMSS against quantum adversaries in the QRPM**: every adversary that makes
at most `q` calls of `φ` and `φ⁻¹` and at most `lifetime = 2^32` signing requests on every path
wins with probability at most `bound q`. The signer's, key generation's and verification's calls
are not charged. -/
def QuantumStronglyUnforgeable (bound : ℕ → ℝ≥0∞) : Prop :=
  ∀ q (A : Adversary S), (∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime) → winProb e A ≤ bound q

/-! ## Losslessness -/

/-- The statement's oracles are answered by lossless programs. -/
theorem lossless_permImpl (B : QReg) (t : RandomPermutationOracles.Domain) :
    (permImpl e B t).Lossless .instruments := by
  rcases t with n | (s | s)
  exacts [QComp.lossless_coinImpl n, QComp.lossless_callBasis _ _ _ _,
    QComp.lossless_callBasis _ _ _ _]

/-- The signer's answer is lossless. -/
theorem lossless_signTree (sk : SecretKey) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (advSpec S).In (.sign r) × E) : (signTree e sk r E ℓ).Lossless .instruments :=
  QuantumComp₂.lossless_bind (QComp.lossless_act (SubInstrument.lossless_relabel _)) fun _ ↦
    lossless_toQuantumAt (lossless_permImpl e _) _

/-- The challenger keeps losslessness. -/
theorem lossless_substitute_challenge (sk : SecretKey) {X : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (advSpec S) X A)
    (hx : x.Lossless .instruments) :
    QuantumComp.Lossless (spec := qrpmSpec S) LocalSig.Interp.instruments
      (IFreeM.substitute (challenge e sk) x) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rw [IFreeM.substitute_liftBind]
    refine QuantumComp.Lossless.bind ?_ fun u ⟨b, h⟩ ↦ ?_
    · rcases c with o | ⟨p | r, E, ℓ⟩
      · exact (QuantumComp.lossless_primBind_iff _ _).mpr ⟨hx.1, fun _ ↦ trivial⟩
      · exact (QuantumComp.lossless_queryBind_iff _ _ _ _).mpr fun _ ↦ trivial
      · exact QuantumComp.Lossless.bind (lossless_signTree e sk r E ℓ) fun _ _ ↦ trivial
    · subst h
      exact ih b (hx.2 b)

/-- **The game of a lossless adversary is lossless.** -/
theorem lossless_game (S0 : MasterSeed) {A : Adversary S}
    (hA : ∀ pk, (A pk).Lossless .instruments) : (game e S0 A).Lossless .instruments :=
  QuantumComp₂.lossless_bind (lossless_toQuantumAt (lossless_permImpl e _) _) fun keys ↦
    QuantumComp₂.lossless_bind
      (lossless_substitute_challenge e keys.2 _ (lossless_withSignLog (hA keys.1)))
      fun _ ↦ QuantumComp₂.lossless_bind (lossless_toQuantumAt (lossless_permImpl e _) _)
        fun _ ↦ QuantumComp₂.lossless_pure _

/-! ## Call budgets -/

section Budget

variable {spec : QuantumOracleSpec.{0, 0}}

/-- A local subinstrument makes no call. -/
theorem isTotalQueryBound_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (n : ℕ) :
    (QComp.act (spec := spec) p).IsTotalQueryBound n :=
  (QuantumComp.isTotalQueryBound_primBind_iff _ _ n).mpr fun _ ↦ trivial

/-- A call makes one call. -/
theorem isTotalQueryBound_query₂ {A : QReg} (i : spec.Port) (E : QReg)
    (ℓ : A ≃ spec.In i × E) :
    (QuantumComp₂.query (L := LocalSig.instruments.{0}) i E ℓ).IsTotalQueryBound 1 :=
  (IFreeM.isChargeBound_liftBind_iff _ _ 1).mpr ⟨Nat.le_refl 1, fun _ ↦ trivial⟩

/-- A basis call makes one call. -/
theorem isTotalQueryBound_callBasis {β : Type} (p : spec.Port) (B : QReg) (a : spec.In p)
    (read : spec.Out p → spec.Result p → β) :
    (QComp.callBasis p B a read).IsTotalQueryBound 1 := by
  unfold QComp.callBasis
  exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 1) (isTotalQueryBound_act _ 0) fun _ ↦
    FreeM₂.isChargeBound_bind (n₁ := 1) (n₂ := 0) (isTotalQueryBound_query₂ _ _ _)
      fun _ ↦ isTotalQueryBound_act _ 0

end Budget

/-- Answering one of the statement's queries makes as many calls as it costs: none for a coin,
one for `π` or `π⁻¹`. -/
theorem isTotalQueryBound_permImpl (B : QReg) (t : RandomPermutationOracles.Domain) :
    (permImpl e B t).IsTotalQueryBound (permutationCallCost t) := by
  rcases t with n | (s | s)
  · exact isTotalQueryBound_act _ _
  · exact isTotalQueryBound_callBasis _ _ _ _
  · exact isTotalQueryBound_callBasis _ _ _ _

/-- **A classical algorithm making at most `n` permutation calls** (`QueryCostAtMost`, coins free)
runs to a program making at most `n` calls of `qrpmSpec S`. -/
theorem isTotalQueryBound_toQuantumAt_permImpl (B : QReg) {α : Type}
    {oa : OracleComp RandomPermutationOracles α} {n : ℕ}
    (h : QueryCostAtMost oa permutationCallCost n) :
    (oa.toQuantumAt (permImpl e B)).IsTotalQueryBound n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [QueryCostAtMost, isQueryBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    have hb := FreeM₂.isChargeBound_bind (isTotalQueryBound_permImpl e B t) fun y ↦ ih y (h.2 y)
    rwa [Nat.add_sub_cancel' h.1] at hb

/-- Two charge bounds add. -/
theorem _root_.IPFunctor.IFreeM.IsChargeBound.add {I : Type*} {P : IPFunctor.Endo I}
    {X : I → Type*} {c₁ c₂ : (s : I) → P.A s → ℕ} {s : I} {x : IFreeM P X s} {n₁ n₂ : ℕ}
    (h₁ : x.IsChargeBound c₁ n₁) (h₂ : x.IsChargeBound c₂ n₂) :
    x.IsChargeBound (fun s a ↦ c₁ s a + c₂ s a) (n₁ + n₂) := by
  induction x using IFreeM.inductionOn generalizing n₁ n₂ with
  | pure _ _ => trivial
  | liftBind s a next ih =>
    rw [IFreeM.isChargeBound_liftBind_iff] at h₁ h₂ ⊢
    refine ⟨Nat.add_le_add h₁.1 h₂.1, fun b ↦ ?_⟩
    have hb := ih b (h₁.2 b) (h₂.2 b)
    have h1 := h₁.1
    have h2 := h₂.1
    rwa [show n₁ - c₁ s a + (n₂ - c₂ s a) = n₁ + n₂ - (c₁ s a + c₂ s a) by omega] at hb

/-- **The challenged adversary's calls.** An adversary making at most `q` permutation calls and
at most `n` signing requests on every path, against a signer making at most `sc` permutation
calls per signature, makes at most `q + sc * n` calls of `φ` and `φ⁻¹` on every path. -/
theorem isTotalQueryBound_challenged (sk : SecretKey) {q n sc : ℕ}
    (hsign : ∀ r, QueryCostAtMost (sufCmaScheme.sign sk r) permutationCallCost sc)
    {A B : QReg} {α : Type} {x : QComp (advSpec S) A B α}
    (hperm : IFreeM.IsChargeBound x (cmdCharge permCharge) q)
    (hsignq : IFreeM.IsChargeBound x (cmdCharge signCharge) n) :
    (challenged e sk x).IsTotalQueryBound (q + sc * n) := by
  refine IFreeM.IsChargeBound.substitute (challenge e sk) (fun A c ↦ ?_)
    (hperm.add (hsignq.mul sc))
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial
  · exact (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
      ⟨by simp [cmdCharge, permCharge, signCharge], fun _ ↦ trivial⟩
  · have ht : (signTree e sk r E ℓ).IsTotalQueryBound (0 + sc) :=
      FreeM₂.isChargeBound_bind (isTotalQueryBound_act _ 0) fun _ ↦
        isTotalQueryBound_toQuantumAt_permImpl e _ (hsign r)
    refine IFreeM.IsChargeBound.mono (n₁ := 0 + sc + 0) ?_
      (by simp [cmdCharge, permCharge, signCharge])
    exact IFreeM.isChargeBound_bind ht fun _ _ ↦ IFreeM.isChargeBound_pure _ _

/-- **The game's calls**: key generation's `kc`, the challenged adversary's `q + sc * n`, and
verification's `vc`. -/
theorem isTotalQueryBound_game (S0 : MasterSeed) {A : Adversary S} {q n kc sc vc : ℕ}
    (hkeygen : QueryCostAtMost (sufCmaScheme.generateKeys S0) permutationCallCost kc)
    (hsign : ∀ sk r, QueryCostAtMost (sufCmaScheme.sign sk r) permutationCallCost sc)
    (hverify : ∀ pk f, QueryCostAtMost (sufCmaScheme.verify pk f) permutationCallCost vc)
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsignq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) n) :
    (game e S0 A).IsTotalQueryBound (kc + (q + sc * n) + vc) := by
  refine QuantumComp.IsTotalQueryBound.mono (n := kc + ((q + sc * n) + (vc + 0))) ?_ (by omega)
  unfold game
  refine FreeM₂.isChargeBound_bind (isTotalQueryBound_toQuantumAt_permImpl e _ hkeygen)
    fun keys ↦ ?_
  refine FreeM₂.isChargeBound_bind (isTotalQueryBound_challenged e keys.2 (hsign keys.2)
    (isChargeBound_withSignLog (hperm keys.1)) (isChargeBound_withSignLog (hsignq keys.1)))
    fun run ↦ ?_
  exact FreeM₂.isChargeBound_bind
    (isTotalQueryBound_toQuantumAt_permImpl e _ (hverify keys.1 run.1))
    fun _ ↦ IFreeM.isChargeBound_pure _ _

end Quantum.Xmss

end
