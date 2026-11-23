module

public import Quantum.StdModel.Sphincs.Prf

@[expose] public section

/-!
# leanSPHINCS at a fixed table: the ITSR hop

The ideal hybrid read through the ITSR decision (`ideal W tab A (itsrDec h)`) is the success of a
straight-line reduction `itsrRed W A` (B3) against the ITSR challenger of the message hash
(`Props.itsr W itsrMap`), at every table of a world with fair coins.

* `itsrRed W A`: samples `PK.seed = P` and the secret digests `s`, computes the public key by the
  routed key generation (`routeHash`, which reads no randomizer); answers a signing request `M`
  with the randomizer of `M` if `M` was signed before, else with the randomizer of an ITSR query on
  `(PK.seed, PK.root, M)`, and signs with the routed signer; outputs the forgery's randomizer and
  message.
* At a fixed table, the reduction's kernel (`hKernel`) is, through a state projection, the lazily
  sampled kernel of the signer `itsrSigner` reading the randomizer function through a query
  (`itsr_hK`, `itsrInv_step`); its eagerly sampled kernel at `r` is the signer of the table
  `digTable h P s r` (`probAt_eager_itsr`), and lazy sampling averages over `r`
  (`probAt_lazy_itsr`). The ITSR transcript has one entry per signed message, so the challenger's
  decision is the ITSR event of the ideal game (`itsrJudge_eq`, `itsrDec_eq`).
* `ideal_itsr_eq`: `ideal W tab A (itsrDec h) = (Props.itsr W itsrMap).succAt tab (itsrRed W A)`.
* `isChargeBound_itsrRed_hash`: `A`'s hash calls plus the honest work of key generation and of
  each signature; `isChargeBound_itsrRed_call`: at most one ITSR query per signing request.
-/

open OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Qrom.Sphincs (QTable)

namespace Quantum.StdModel.Sphincs

/-! ## Generic facts -/

section Generic

variable {W : OracleWorld} {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

/-- A world program as a program of a reduction with the ports `R'`. -/
noncomputable def liftW (R' : OracleSpec.{0, 0} Q') {α : Type} (oa : OracleComp W.Oracles α) :
    OracleComp (W.Oracles + R') α :=
  simulateQ (fun t ↦ liftM ((W.Oracles + R').query (.inl t)) :
    QueryImpl W.Oracles (OracleComp (W.Oracles + R'))) oa

/-- A world program in a reduction runs at the table without touching the transcript. -/
theorem run_simulateQ_logImpl_liftW (tab : W.Tab)
    (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q')) {α : Type}
    (oa : OracleComp W.Oracles α) (log : QueryLog R') :
    (simulateQ (logImpl tab ans) (liftW R' oa)).run log =
      (fun a ↦ (a, log)) <$> simulateQ (W.eager tab) oa := by
  unfold liftW
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih => simp [logImpl, StateT.run_bind, StateT.run_lift, ih]

/-- A query of the challenger's port is answered and logged. -/
theorem run_logImpl_inr (tab : W.Tab) (ans : (q' : Q') → OracleComp W.Oracles (R'.Range q'))
    (q' : Q') (log : QueryLog R') :
    (logImpl tab ans (.inr q')).run log =
      (fun a ↦ (a, log ++ [⟨q', a⟩])) <$> simulateQ (W.eager tab) (ans q') :=
  rfl

/-- A cell is in the union of a list of sets when one of them has it. -/
theorem mem_foldr_union_iff {β : Type} [DecidableEq β] {y : β} :
    ∀ {l : List (Finset β)}, y ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ S ∈ l, y ∈ S
  | [] => by simp
  | S :: l => by
    rw [List.foldr_cons, Finset.mem_union, mem_foldr_union_iff]
    simp

/-- Two relabellings of a value relabel by their composition. -/
theorem qmap_map {spec : QuantumOracleSpec.{0, 0}} {A B : QReg} {α β γ : Type} (f : α → β)
    (g : β → γ) (x : QComp spec A B α) : (x.map f).map g = x.map fun a ↦ g (f a) := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure,
    QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]

end Generic

section Average

variable (W : OracleWorld) (tab : W.Tab)

/-- **A uniform average of runs**: if `|Θ|` times the branch of `x` at `true` is the sum of the
branches of the `xs θ`, the probability of `x` is the uniform average of theirs. -/
theorem probAt_eq_unifAvg_of_branch {Θ : Type} [Fintype Θ] [Nonempty Θ]
    (x : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool)
    (xs : Θ → QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool)
    (h : ∀ ρ, (Fintype.card Θ : ℂ) • ((W.runtime tab).run .instruments x).branch
        (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true) ρ =
      ∑ θ, ((W.runtime tab).run .instruments (xs θ)).branch
        (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true) ρ) :
    W.probAt tab x = unifAvg Θ fun θ ↦ W.probAt tab (xs θ) := by
  set Rt := W.runtime tab
  set ρS := (SubState.basis ()).prod Rt.init
  have ht (y : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
      W.probAt tab y = ENNReal.ofReal (((Rt.run .instruments y).branch
        (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true) ρS.matrix).trace.re) :=
    probAt_eq_ofReal_trace W tab y
  have hnn (y : QComp W.spec (QReg.of Unit) (QReg.of Unit) Bool) :
      0 ≤ ((Rt.run .instruments y).branch
        (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true) ρS.matrix).trace.re :=
    DSubInstrument.trace_re_branch_apply_nonneg _ _ ρS.posSemidef
  have h1 : (Fintype.card Θ : ℝ) * ((Rt.run .instruments x).branch
      (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true) ρS.matrix).trace.re =
        ∑ θ, ((Rt.run .instruments (xs θ)).branch
          (QuantumComp₂.leafEquiv (QReg.of Unit) Bool true) ρS.matrix).trace.re := by
    have e := congrArg (fun M ↦ (Matrix.trace M).re) (h ρS.matrix)
    simp only [Matrix.trace_smul, Matrix.trace_sum, Complex.re_sum, smul_eq_mul, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at e
    exact e
  rw [ht x, unifAvg]
  simp only [ht]
  rw [← ENNReal.ofReal_sum_of_nonneg fun θ _ ↦ hnn (xs θ), ← h1,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

end Average

/-! ## The reduction -/

/-- A query of the ITSR port: `(PK.seed, PK.root, M)`. -/
abbrev ItsrMsg : Type := PublicParameter × Digest × Message

/-- A cell of the message hash: the FORS instance, a tree, a leaf. -/
abbrev ItsrCell : Type := Index × ForsTreeIndex × ForsLeafIndex

/-- The ITSR port of the reduction. -/
abbrev ItsrSpec : OracleSpec ItsrMsg := ItsrMsg →ₒ Randomizer × Finset ItsrCell

/-- The reduction's setup: `PK.seed`, the secret digests, the public key. -/
abbrev ItsrSetup : Type := PublicParameter × (KeygenDomain → Digest) × PublicKey

/-- The reduction's state: its setup, the signed messages with their randomizers, and the
randomizers of the signed messages. -/
abbrev ItsrState : Type :=
  ItsrSetup × List (Message × Randomizer) × (Message →ₒ Randomizer).QueryCache

/-- Uniform secret digests. -/
@[instance_reducible]
noncomputable def secretsSampleable : SampleableType (KeygenDomain → Digest) :=
  SampleableType.ofFintype _

attribute [local instance] secretsSampleable

/-- The signature of `M` with the randomizer `R` at the table of `P` and `s`. -/
noncomputable def itsrSig (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) (R : Randomizer) (M : Message) : Option Signature :=
  (digTable h P s fun _ ↦ R).signature (cellHash h) M

/-- The public key at the table of `P` and `s` (it reads no randomizer). -/
noncomputable def itsrPk (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) : PublicKey :=
  (digTable h P s fun _ ↦ 0).publicKey

/-- The ITSR transcript entry of a signed message and its randomizer. -/
def itsrEntry (h : HashInput → HashOutput) (pk : PublicKey) (e : Message × Randomizer) :
    (t : ItsrSpec.Domain) × ItsrSpec.Range t :=
  ⟨(pk.publicSeed, pk.root, e.1), (e.2, digestCells (digestOf h pk e.2 e.1))⟩

theorem itsrSig_eq (h : HashInput → HashOutput) (P : PublicParameter) (s : KeygenDomain → Digest)
    (r : Message → Randomizer) (M : Message) :
    itsrSig h P s (r M) M = (digTable h P s r).signature (cellHash h) M :=
  signature_digTable_congr h P s (fun _ ↦ r M) (cellHash h) rfl

variable (W : OracleWorld)

/-- The world's Keccak-256 as a classical call of the reduction. -/
noncomputable def itsrHash (l : HashInput) : OracleComp (W.Oracles + ItsrSpec) HashOutput :=
  liftW ItsrSpec (W.hash l)

/-- **The setup of the reduction**: uniform `PK.seed` and secret digests, the public key by the
routed key generation. -/
noncomputable def itsrPre : OracleComp (W.Oracles + ItsrSpec) ItsrSetup := do
  let P ← liftW ItsrSpec (Props.sample W PublicParameter)
  let s ← liftW ItsrSpec (Props.sample W (KeygenDomain → Digest))
  let keys ← Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
    (routeHash P (fun d ↦ pure (s d)) (fun _ ↦ pure 0) (itsrHash W)) 0
  pure (P, s, keys.1)

/-- The randomizer of `M`: the cached one, else the randomizer of an ITSR query, cached. -/
noncomputable def itsrRnd (pk : PublicKey) (c : (Message →ₒ Randomizer).QueryCache)
    (M : Message) :
    OracleComp (W.Oracles + ItsrSpec) (Randomizer × (Message →ₒ Randomizer).QueryCache) :=
  match c M with
  | some R => pure (R, c)
  | none => (fun (a : Randomizer × Finset ItsrCell) ↦ (a.1, c.cacheQuery M a.1)) <$>
      liftM ((W.Oracles + ItsrSpec).query (.inr (pk.publicSeed, pk.root, M)))

/-- **The reduction's signer**: the randomizer of `M` (`itsrRnd`), then the routed signer. -/
noncomputable def itsrHandler : HHandler W SignSpec ItsrSpec ItsrState := fun st M ↦ do
  let x ← itsrRnd W st.1.2.2 st.2.2 M
  let σ ← Qrom.Sphincs.LeanSphincsOver.sign
    (routeHash st.1.1 (fun d ↦ pure (st.1.2.1 d)) (fun _ ↦ pure x.1) (itsrHash W)) 0 M
  pure (σ, (st.1, st.2.1 ++ [(M, x.1)], x.2))

/-- The reduction's output: the forgery's randomizer and message under the public key. -/
def itsrPost (a : ItsrSetup) (forg : Forgery) (_ : ItsrState) :
    OracleComp (W.Oracles + ItsrSpec) (Randomizer × ItsrMsg) :=
  pure (forg.signature.randomizer, (a.2.2.publicSeed, a.2.2.root, forg.message))

/-- **The ITSR reduction (B3)**: the adversary run once against the reduction's signer. -/
noncomputable def itsrRed (A : SAdv W) :
    Props.Adversary W ItsrSpec Unit (Randomizer × ItsrMsg) := fun _ ↦
  slRed W (itsrPre W) (fun a ↦ A a.2.2) (fun a ↦ (a, [], ∅)) (itsrHandler W) (itsrPost W)

/-! ## Decisions and the lazily sampled signer -/

/-- The ITSR challenger's decision on the reduction's run. -/
noncomputable def itsrJudge (h : HashInput → HashOutput) (pk : PublicKey)
    (r : (Forgery × ItsrState) × QueryLog ItsrSpec) : Bool :=
  Props.holds ((r.1.1.signature.randomizer, (pk.publicSeed, pk.root, r.1.1.message)) ∉
      r.2.map (fun e ↦ (e.2.1, e.1)) ∧
    digestCells (digestOf h pk r.1.1.signature.randomizer r.1.1.message) ⊆
      Props.coveredCells r.2)

/-- The ITSR event read from the signed messages with their randomizers. -/
noncomputable def itsrRndDec (h : HashInput → HashOutput) (pk : PublicKey)
    (r : Forgery × List (Message × Randomizer)) : Bool :=
  Props.holds ((r.1.signature.randomizer, r.1.message) ∉ r.2.map (fun e ↦ (e.2, e.1)) ∧
    digestCells (digestOf h pk r.1.signature.randomizer r.1.message) ⊆
      (r.2.map fun e ↦ digestCells (digestOf h pk e.2 e.1)).foldr (· ∪ ·) ∅)

/-- **The signer reading the randomizer function**: the randomizer of `M` by a query, the
signature of the table with that randomizer, the pair logged. -/
noncomputable def itsrSigner (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) (rl : List (Message × Randomizer)) (M : Message) :
    OracleComp (unifSpec + (Message →ₒ Randomizer))
      (Option Signature × List (Message × Randomizer)) := do
  let R : Randomizer ← liftM ((unifSpec + (Message →ₒ Randomizer)).query (.inr M))
  pure (itsrSig h P s R M, rl ++ [(M, R)])

/-- The invariant of the reduction's run: its setup, its transcript the entries of its signed
messages, its cache their randomizers. -/
def ItsrInv (h : HashInput → HashOutput) (a0 : ItsrSetup) (st : ItsrState × QueryLog ItsrSpec) :
    Prop :=
  st.1.1 = a0 ∧ (∀ x, x ∈ st.2 ↔ x ∈ st.1.2.1.map (itsrEntry h a0.2.2)) ∧
    (∀ e ∈ st.1.2.1, st.1.2.2 e.1 = some e.2) ∧
      ∀ M R, st.1.2.2 M = some R → (M, R) ∈ st.1.2.1

/-! ## The reduction at a fixed table -/

section Table

variable (tab : W.Tab)

theorem simulateQ_logImpl_itsrHash (ans : (q : ItsrMsg) → OracleComp W.Oracles (ItsrSpec.Range q))
    (l : HashInput) :
    simulateQ (logImpl tab ans) (itsrHash W l) =
      (pure (W.hashOf tab l) : StateT (QueryLog ItsrSpec) ProbComp HashOutput) := by
  refine StateT.ext fun log ↦ ?_
  rw [itsrHash, run_simulateQ_logImpl_liftW, W.simulateQ_hash, map_pure, StateT.run_pure]

/-- The routed signer at a fixed table returns the signature of the table. -/
theorem simulateQ_logImpl_sign (ans : (q : ItsrMsg) → OracleComp W.Oracles (ItsrSpec.Range q))
    (P : PublicParameter) (s : KeygenDomain → Digest) (R : Randomizer) (M : Message) :
    simulateQ (logImpl tab ans) (Qrom.Sphincs.LeanSphincsOver.sign
      (routeHash P (fun d ↦ pure (s d)) (fun _ ↦ pure R) (itsrHash W)) 0 M) =
      (pure (itsrSig (W.hashOf tab) P s R M) :
        StateT (QueryLog ItsrSpec) ProbComp (Option Signature)) := by
  rw [Over.simulateQ_sign]
  simp only [simulateQ_routeHash, simulateQ_pure, simulateQ_logImpl_itsrHash]
  exact sign_routeHash (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) M

/-- The routed key generation at a fixed table returns the public key of the table. -/
theorem simulateQ_logImpl_keygen
    (ans : (q : ItsrMsg) → OracleComp W.Oracles (ItsrSpec.Range q)) (P : PublicParameter)
    (s : KeygenDomain → Digest) :
    simulateQ (logImpl tab ans) (Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
      (routeHash P (fun d ↦ pure (s d)) (fun _ ↦ pure 0) (itsrHash W)) 0) =
      (pure (itsrPk (W.hashOf tab) P s, 0) :
        StateT (QueryLog ItsrSpec) ProbComp (PublicKey × SecretKey)) := by
  rw [Over.simulateQ_keygenFromSeed]
  simp only [simulateQ_routeHash, simulateQ_pure, simulateQ_logImpl_itsrHash]
  exact keygenFromSeed_routeHash (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- **The setup at a fixed table**: uniform `PK.seed` and secrets, the table's public key. -/
theorem run_simulateQ_itsrPre (hW : W.CoinsFair)
    (ans : (q : ItsrMsg) → OracleComp W.Oracles (ItsrSpec.Range q)) :
    (simulateQ (logImpl tab ans) (itsrPre W)).run [] =
      (do
        let P ← $ᵗ PublicParameter
        let s ← $ᵗ (KeygenDomain → Digest)
        pure ((P, s, itsrPk (W.hashOf tab) P s), ([] : QueryLog ItsrSpec))) := by
  simp only [itsrPre, simulateQ_bind, StateT.run_bind, run_simulateQ_logImpl_liftW,
    W.simulateQ_sample hW tab, bind_map_left, simulateQ_logImpl_keygen, StateT.run_pure, pure_bind,
    simulateQ_pure]

/-- The ITSR challenger's answer at a fixed table: a uniform randomizer and its cells. -/
theorem simulateQ_itsr_answer (hW : W.CoinsFair) (pk : PublicKey) (M : Message) :
    simulateQ (W.eager tab) ((Props.itsr W itsrMap).answer () (pk.publicSeed, pk.root, M)) =
      (fun R ↦ (R, digestCells (digestOf (W.hashOf tab) pk R M))) <$> ($ᵗ Randomizer) := by
  simp only [Props.itsr, simulateQ_bind, W.simulateQ_sample hW tab, simulateQ_itsr_select,
    pure_bind, simulateQ_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- The ITSR challenger's decision at a fixed table. -/
theorem simulateQ_itsr_judge (pk : PublicKey) (L : QueryLog ItsrSpec) (R : Randomizer)
    (M : Message) :
    simulateQ (W.eager tab) ((Props.itsr W itsrMap).judge () L (R, (pk.publicSeed, pk.root, M))) =
      pure (Props.holds ((R, (pk.publicSeed, pk.root, M)) ∉ L.map (fun e ↦ (e.2.1, e.1)) ∧
        digestCells (digestOf (W.hashOf tab) pk R M) ⊆ Props.coveredCells L)) := by
  simp only [Props.itsr, simulateQ_bind, simulateQ_itsr_select, pure_bind, simulateQ_pure]

theorem run_simulateQ_itsrRnd_some
    (ans : (q : ItsrMsg) → OracleComp W.Oracles (ItsrSpec.Range q)) (pk : PublicKey)
    (c : (Message →ₒ Randomizer).QueryCache) (M : Message) (R : Randomizer)
    (L : QueryLog ItsrSpec) (hc : c M = some R) :
    (simulateQ (logImpl tab ans) (itsrRnd W pk c M)).run L = pure ((R, c), L) := by
  unfold itsrRnd
  rw [hc]
  dsimp only
  rw [simulateQ_pure, StateT.run_pure]

theorem run_simulateQ_itsrRnd_none (hW : W.CoinsFair) (pk : PublicKey)
    (c : (Message →ₒ Randomizer).QueryCache) (M : Message) (L : QueryLog ItsrSpec)
    (hc : c M = none) :
    (simulateQ (logImpl tab ((Props.itsr W itsrMap).answer ())) (itsrRnd W pk c M)).run L =
      (fun R ↦ ((R, c.cacheQuery M R), L ++ [itsrEntry (W.hashOf tab) pk (M, R)])) <$>
        ($ᵗ Randomizer) := by
  unfold itsrRnd
  rw [hc]
  dsimp only
  rw [simulateQ_map, StateT.run_map, simulateQ_spec_query, run_logImpl_inr,
    simulateQ_itsr_answer W tab hW pk M, Functor.map_map, Functor.map_map]
  rfl

/-- **The reduction's kernel on a signed message**: the cached randomizer. -/
theorem hKernel_itsr_some (ans : (q : ItsrMsg) → OracleComp W.Oracles (ItsrSpec.Range q))
    (P : PublicParameter) (s : KeygenDomain → Digest) (pk : PublicKey)
    (rl : List (Message × Randomizer)) (c : (Message →ₒ Randomizer).QueryCache)
    (L : QueryLog ItsrSpec) (M : Message) (R : Randomizer) (hc : c M = some R) :
    hKernel tab ans (itsrHandler W) (((P, s, pk), rl, c), L) M =
      pure (itsrSig (W.hashOf tab) P s R M, (((P, s, pk), rl ++ [(M, R)], c), L)) := by
  simp only [hKernel, itsrHandler, simulateQ_bind, StateT.run_bind,
    run_simulateQ_itsrRnd_some W tab ans pk c M R L hc, pure_bind, simulateQ_logImpl_sign,
    StateT.run_pure, simulateQ_pure, map_pure]

/-- **The reduction's kernel on a new message**: a fresh uniform randomizer, its entry logged. -/
theorem hKernel_itsr_none (hW : W.CoinsFair) (P : PublicParameter) (s : KeygenDomain → Digest)
    (pk : PublicKey) (rl : List (Message × Randomizer)) (c : (Message →ₒ Randomizer).QueryCache)
    (L : QueryLog ItsrSpec) (M : Message) (hc : c M = none) :
    hKernel tab ((Props.itsr W itsrMap).answer ()) (itsrHandler W) (((P, s, pk), rl, c), L) M =
      (fun R ↦ (itsrSig (W.hashOf tab) P s R M, (((P, s, pk), rl ++ [(M, R)], c.cacheQuery M R),
        L ++ [itsrEntry (W.hashOf tab) pk (M, R)]))) <$> ($ᵗ Randomizer) := by
  simp only [hKernel, itsrHandler, simulateQ_bind, StateT.run_bind,
    run_simulateQ_itsrRnd_none W tab hW pk c M L hc, bind_map_left, simulateQ_logImpl_sign,
    StateT.run_pure, pure_bind, simulateQ_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

end Table

section Lazy

variable (h : HashInput → HashOutput) (P : PublicParameter) (s : KeygenDomain → Digest)

theorem lazyKernel_itsr_some (rl : List (Message × Randomizer))
    (c : (Message →ₒ Randomizer).QueryCache) (M : Message) (R : Randomizer) (hc : c M = some R) :
    lazyKernel (R := SignSpec) (itsrSigner h P s) (rl, c) M =
      pure (itsrSig h P s R M, (rl ++ [(M, R)], c)) := by
  unfold lazyKernel itsrSigner
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  erw [randomOracle.run_eq]
  rw [hc]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure, map_pure]

theorem lazyKernel_itsr_none (rl : List (Message × Randomizer))
    (c : (Message →ₒ Randomizer).QueryCache) (M : Message) (hc : c M = none) :
    lazyKernel (R := SignSpec) (itsrSigner h P s) (rl, c) M =
      (fun R ↦ (itsrSig h P s R M, (rl ++ [(M, R)], c.cacheQuery M R))) <$> ($ᵗ Randomizer) := by
  unfold lazyKernel itsrSigner
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  erw [randomOracle.run_eq]
  rw [hc]
  simp only [bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

theorem eagerKernel_itsr (H : Message → Randomizer) (rl : List (Message × Randomizer))
    (M : Message) :
    eagerKernel (R := SignSpec) (itsrSigner h P s) H rl M =
      pure (itsrSig h P s (H M) M, rl ++ [(M, H M)]) := by
  simp only [eagerKernel, itsrSigner, simulateQ_bind, simulateQ_spec_query, Qrom.eagerFunOracles,
    pure_bind, simulateQ_pure]

/-- **The challenger's decision is the event read from the signed pairs** when the transcript
has the entries of the signed messages. -/
theorem itsrJudge_eq (pk : PublicKey) (forg : Forgery) (st : ItsrState) (L : QueryLog ItsrSpec)
    (hL : ∀ x, x ∈ L ↔ x ∈ st.2.1.map (itsrEntry h pk)) :
    itsrJudge h pk ((forg, st), L) = itsrRndDec h pk (forg, st.2.1) := by
  have hcov : Props.coveredCells L =
      (st.2.1.map fun e ↦ digestCells (digestOf h pk e.2 e.1)).foldr (· ∪ ·) ∅ := by
    ext y
    rw [Props.coveredCells, mem_foldr_union_iff, mem_foldr_union_iff]
    constructor
    · rintro ⟨_, hS, hy⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hS
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ((hL x).mp hx)
      exact ⟨_, List.mem_map_of_mem he, hy⟩
    · rintro ⟨_, hS, hy⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hS
      exact ⟨_, List.mem_map_of_mem ((hL (itsrEntry h pk e)).mpr (List.mem_map_of_mem he)), hy⟩
  have hmem : (forg.signature.randomizer, (pk.publicSeed, pk.root, forg.message)) ∈
      L.map (fun e ↦ (e.2.1, e.1)) ↔
        (forg.signature.randomizer, forg.message) ∈ st.2.1.map (fun e ↦ (e.2, e.1)) := by
    constructor
    · intro hx
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ((hL x).mp hx)
      have h1 := Prod.mk.inj hxe
      have h2 := Prod.mk.inj (Prod.mk.inj h1.2).2
      exact List.mem_map.mpr ⟨e, he, Prod.ext h1.1 h2.2⟩
    · intro hx
      obtain ⟨e, he, hee⟩ := List.mem_map.mp hx
      have h1 := Prod.mk.inj hee
      refine List.mem_map.mpr ⟨itsrEntry h pk e, (hL _).mpr (List.mem_map_of_mem he),
        Prod.ext h1.1 ?_⟩
      exact congrArg (fun m ↦ (pk.publicSeed, pk.root, m)) h1.2
  unfold itsrJudge itsrRndDec
  dsimp only
  rw [hcov]
  exact congrArg Props.holds (propext (and_congr (not_congr hmem) Iff.rfl))

/-- **The event read from the signed pairs is the ITSR decision** of the table of the randomizer
function when the pairs carry its randomizers. -/
theorem itsrDec_eq (H : Message → Randomizer) (forg : Forgery)
    (rl : List (Message × Randomizer)) (hrl : ∀ e ∈ rl, e.2 = H e.1) :
    itsrDec h (digTable h P s H) (forg, rl.map fun e ↦ ⟨e.1, itsrSig h P s e.2 e.1⟩) =
      itsrRndDec h (itsrPk h P s) (forg, rl) := by
  have hpk : (digTable h P s H).publicKey = itsrPk h P s :=
    publicKey_digTable_congr h P s H (fun _ ↦ 0)
  have hmsgs : logMsgs (rl.map fun e ↦
      (⟨e.1, itsrSig h P s e.2 e.1⟩ : (t : Message) × Option Signature)) = rl.map Prod.fst := by
    simp only [logMsgs, logPairs, List.map_map]
    rfl
  have e1 : (logMsgs (rl.map fun e ↦
      (⟨e.1, itsrSig h P s e.2 e.1⟩ : (t : Message) × Option Signature))).map
        (fun M' ↦ ((digTable h P s H).randomizer M', M')) = rl.map (fun e ↦ (e.2, e.1)) := by
    rw [hmsgs, List.map_map]
    exact List.map_congr_left fun e he ↦ by
      simp [Function.comp, randomizer_digTable, hrl e he]
  have e2 : (logMsgs (rl.map fun e ↦
      (⟨e.1, itsrSig h P s e.2 e.1⟩ : (t : Message) × Option Signature))).map
        (fun M' ↦ digestCells (digestOf h (digTable h P s H).publicKey
          ((digTable h P s H).randomizer M') M')) =
        rl.map (fun e ↦ digestCells (digestOf h (itsrPk h P s) e.2 e.1)) := by
    rw [hmsgs, List.map_map, hpk]
    exact List.map_congr_left fun e he ↦ by
      simp [Function.comp, randomizer_digTable, hrl e he]
  unfold itsrDec EvItsr
  dsimp only
  rw [e1, e2, hpk]
  rfl

end Lazy

section Run

variable (tab : W.Tab) (A : SAdv W)

/-- **The reduction's kernel is the lazily sampled signer** through the state projection. -/
theorem itsr_hK (hW : W.CoinsFair) (P : PublicParameter) (s : KeygenDomain → Digest)
    (pk : PublicKey) (st : ItsrState × QueryLog ItsrSpec)
    (hst : ItsrInv (W.hashOf tab) (P, s, pk) st) (M : Message) :
    Prod.map id (fun st : ItsrState × QueryLog ItsrSpec ↦ (st.1.2.1, st.1.2.2)) <$>
        hKernel tab ((Props.itsr W itsrMap).answer ()) (itsrHandler W) st M =
      lazyKernel (R := SignSpec) (itsrSigner (W.hashOf tab) P s) (st.1.2.1, st.1.2.2) M := by
  obtain ⟨⟨a, rl, c⟩, L⟩ := st
  obtain ⟨ha, -, -, -⟩ := hst
  dsimp only at ha ⊢
  subst ha
  cases hc : c M with
  | some R =>
    rw [hKernel_itsr_some W tab _ P s pk rl c L M R hc,
      lazyKernel_itsr_some (W.hashOf tab) P s rl c M R hc]
    simp only [map_pure, Prod.map_apply, id_eq]
  | none =>
    rw [hKernel_itsr_none W tab hW P s pk rl c L M hc,
      lazyKernel_itsr_none (W.hashOf tab) P s rl c M hc, Functor.map_map]
    simp only [Prod.map_apply, id_eq]

/-- **The invariant is kept** by the reduction's kernel. -/
theorem itsrInv_step (hW : W.CoinsFair) (a0 : ItsrSetup) (st : ItsrState × QueryLog ItsrSpec)
    (hst : ItsrInv (W.hashOf tab) a0 st) (M : Message) :
    ∀ p ∈ support (hKernel tab ((Props.itsr W itsrMap).answer ()) (itsrHandler W) st M),
      ItsrInv (W.hashOf tab) a0 p.2 := by
  obtain ⟨⟨a, rl, c⟩, L⟩ := st
  obtain ⟨ha, hL, hc1, hc2⟩ := hst
  dsimp only at ha hL hc1 hc2
  obtain ⟨P, s, pk⟩ := a0
  subst ha
  intro p hp
  cases hc : c M with
  | some R =>
    rw [hKernel_itsr_some W tab _ P s pk rl c L M R hc, support_pure,
      Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨rfl, fun x ↦ ?_, fun e he ↦ ?_, fun M' R' h' ↦ ?_⟩
    · dsimp only
      rw [hL x, List.map_append, List.mem_append]
      refine ⟨Or.inl, ?_⟩
      rintro (hx | hx)
      · exact hx
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
        subst hx
        exact List.mem_map_of_mem (hc2 M R hc)
    · rcases List.mem_append.mp he with he | he
      · exact hc1 e he
      · rw [List.mem_singleton.mp he]
        exact hc
    · exact List.mem_append_left _ (hc2 M' R' h')
  | none =>
    rw [hKernel_itsr_none W tab hW P s pk rl c L M hc, support_map] at hp
    obtain ⟨R, -, rfl⟩ := hp
    refine ⟨rfl, fun x ↦ ?_, fun e he ↦ ?_, fun M' R' h' ↦ ?_⟩
    · dsimp only
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, hL x]
    · rcases List.mem_append.mp he with he | he
      · have hne : e.1 ≠ M := fun h ↦ by
          rw [← h, hc1 e he] at hc
          exact Option.some_ne_none _ hc
        exact (QueryCache.cacheQuery_of_ne c R hne).trans (hc1 e he)
      · rw [List.mem_singleton.mp he]
        exact QueryCache.cacheQuery_self c M R
    · by_cases hM : M' = M
      · subst hM
        rw [QueryCache.cacheQuery_self] at h'
        obtain rfl := Option.some.inj h'
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · rw [QueryCache.cacheQuery_of_ne c R hM] at h'
        exact List.mem_append_left _ (hc2 M' R' h')

/-- **The reduction's run is the lazily sampled signer's run.** -/
theorem probAt_itsrRed_lazy (hW : W.CoinsFair) (P : PublicParameter) (s : KeygenDomain → Digest) :
    W.probAt tab ((kRunL W (hKernel tab ((Props.itsr W itsrMap).answer ()) (itsrHandler W))
      (A (itsrPk (W.hashOf tab) P s)) ((P, s, itsrPk (W.hashOf tab) P s), [], ∅) []).map
        (itsrJudge (W.hashOf tab) (itsrPk (W.hashOf tab) P s))) =
    W.probAt tab ((kRunQ W (lazyKernel (R := SignSpec) (itsrSigner (W.hashOf tab) P s))
      (A (itsrPk (W.hashOf tab) P s)) ([], ∅)).map
        fun r ↦ itsrRndDec (W.hashOf tab) (itsrPk (W.hashOf tab) P s) (r.1, r.2.1)) := by
  rw [kRunL_eq_map, qmap_map]
  refine probAt_eq_of_run₂ W tab (run₂_map_kRunQ_sim (W.runtime tab)
    (lazyKernel (R := SignSpec) (itsrSigner (W.hashOf tab) P s))
    (hKernel tab ((Props.itsr W itsrMap).answer ()) (itsrHandler W))
    (ItsrInv (W.hashOf tab) (P, s, itsrPk (W.hashOf tab) P s))
    (fun st ↦ (st.1.2.1, st.1.2.2)) (fun st hst M ↦ itsr_hK W tab hW P s _ st hst M)
    (fun st hst M ↦ itsrInv_step W tab hW _ st hst M) _ _ ?_ _ _ ?_)
  · refine ⟨rfl, fun x ↦ ?_, fun e he ↦ ?_, fun M R hMR ↦ ?_⟩
    · simp
    · simp at he
    · simp [QueryCache.empty_apply] at hMR
  · intro a st hst
    exact itsrJudge_eq (W.hashOf tab) _ a st.1 st.2 hst.2.1

/-- **Lazy sampling**: the lazily sampled signer's run is the average over the randomizer
functions of the eagerly sampled signer's runs. -/
theorem probAt_lazy_itsr (x : QComp (advSpec W.spec SignSpec) (QReg.of Unit) (QReg.of Unit) Forgery)
    (h : HashInput → HashOutput) (P : PublicParameter) (s : KeygenDomain → Digest)
    (pk : PublicKey) :
    W.probAt tab ((kRunQ W (lazyKernel (R := SignSpec) (itsrSigner h P s)) x ([], ∅)).map
        fun r ↦ itsrRndDec h pk (r.1, r.2.1)) =
      unifAvg (Message → Randomizer) fun H ↦
        W.probAt tab ((kRunQ W (eagerKernel (R := SignSpec) (itsrSigner h P s) H) x []).map
          (itsrRndDec h pk)) := by
  refine probAt_eq_unifAvg_of_branch W tab _ _ fun ρ ↦ ?_
  have eL : (kRunQ W (lazyKernel (R := SignSpec) (itsrSigner h P s)) x ([], ∅)).map
      (fun r ↦ itsrRndDec h pk (r.1, r.2.1)) =
        kRun W (lazyKernel (R := SignSpec) (itsrSigner h P s))
          (Y := QuantumComp₂.Leaf (QReg.of Unit) Bool)
          (fun _ y sc ↦ ⟨y.1, itsrRndDec h pk (y.2, sc.1)⟩) x ([], ∅) :=
    imap_kRun W _ (X := QuantumComp₂.Leaf (QReg.of Unit) Forgery) (fun _ l s ↦ ⟨l.1, (l.2, s)⟩)
      _ x _
  have eE (H : Message → Randomizer) :
      (kRunQ W (eagerKernel (R := SignSpec) (itsrSigner h P s) H) x []).map (itsrRndDec h pk) =
        kRun W (eagerKernel (R := SignSpec) (itsrSigner h P s) H)
          (Y := QuantumComp₂.Leaf (QReg.of Unit) Bool)
          (fun _ y rl ↦ ⟨y.1, itsrRndDec h pk (y.2, rl)⟩) x [] :=
    imap_kRun W _ (X := QuantumComp₂.Leaf (QReg.of Unit) Forgery) (fun _ l s ↦ ⟨l.1, (l.2, s)⟩)
      _ x _
  rw [eL]
  refine (card_smul_branch_kRun_lazy W (W.runtime tab) (itsrSigner h P s)
    (X := QuantumComp₂.Leaf (QReg.of Unit) Forgery) (Y := QuantumComp₂.Leaf (QReg.of Unit) Bool)
    (fun _ y sc ↦ ⟨y.1, itsrRndDec h pk (y.2, sc.1)⟩)
    (fun _ _ y rl ↦ ⟨y.1, itsrRndDec h pk (y.2, rl)⟩) (fun _ _ _ _ _ ↦ rfl) x [] ∅ _ ρ).trans ?_
  refine Finset.sum_congr rfl fun H _ ↦ ?_
  rw [tableExtending_empty, eE H]

/-- **The eagerly sampled signer is the signer of the table** of the randomizer function. -/
theorem probAt_eager_itsr (P : PublicParameter) (s : KeygenDomain → Digest)
    (H : Message → Randomizer) :
    W.probAt tab ((kRunQ W (eagerKernel (R := SignSpec) (itsrSigner (W.hashOf tab) P s) H)
      (A (itsrPk (W.hashOf tab) P s)) []).map
        (itsrRndDec (W.hashOf tab) (itsrPk (W.hashOf tab) P s))) =
      gameAt W tab A (digTable (W.hashOf tab) P s H)
        (itsrDec (W.hashOf tab) (digTable (W.hashOf tab) P s H)) := by
  unfold gameAt
  set h := W.hashOf tab
  rw [publicKey_digTable_congr h P s H (fun _ ↦ 0)]
  refine probAt_eq_of_run₂ W tab (run₂_map_kRunQ_sim (W.runtime tab)
    (detKernel h (digTable h P s H)) (eagerKernel (R := SignSpec) (itsrSigner h P s) H)
    (fun rl ↦ ∀ e ∈ rl, e.2 = H e.1) (fun rl ↦ rl.map fun e ↦ ⟨e.1, itsrSig h P s e.2 e.1⟩)
    ?_ ?_ (A (itsrPk h P s)) [] (by simp) (itsrDec h (digTable h P s H))
    (itsrRndDec h (itsrPk h P s)) ?_)
  · intro rl _ M
    rw [eagerKernel_itsr, map_pure]
    simp only [Prod.map_apply, id_eq, List.map_append, List.map_cons, List.map_nil, detKernel]
    rw [itsrSig_eq h P s H M]
  · intro rl hrl M p hp
    rw [eagerKernel_itsr, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hrl e he
    · rw [List.mem_singleton.mp he]
  · intro a rl hrl
    exact (itsrDec_eq h P s H a rl hrl).symm

/-- **The reduction's run at `PK.seed = P` and secrets `s`** is the average over the randomizer
functions of the game at their tables, read through the ITSR decision. -/
theorem probAt_itsrRed_run (hW : W.CoinsFair) (P : PublicParameter)
    (s : KeygenDomain → Digest) :
    W.probAt tab ((kRunL W (hKernel tab ((Props.itsr W itsrMap).answer ()) (itsrHandler W))
      (A (itsrPk (W.hashOf tab) P s)) ((P, s, itsrPk (W.hashOf tab) P s), [], ∅) []).map
        (itsrJudge (W.hashOf tab) (itsrPk (W.hashOf tab) P s))) =
      unifAvg (Message → Randomizer) fun r ↦ gameAt W tab A (digTable (W.hashOf tab) P s r)
        (itsrDec (W.hashOf tab) (digTable (W.hashOf tab) P s r)) :=
  (probAt_itsrRed_lazy W tab A hW P s).trans ((probAt_lazy_itsr W tab _ _ P s _).trans
    (unifAvg_congr fun H ↦ probAt_eager_itsr W tab A P s H))

/-- **The ITSR game of the reduction at a fixed table**: the average over `PK.seed` and the
secrets of the reduction's run. -/
theorem succAt_itsrRed (hW : W.CoinsFair) :
    (Props.itsr W itsrMap).succAt tab (itsrRed W A) =
      unifAvg PublicParameter fun P ↦ unifAvg (KeygenDomain → Digest) fun s ↦
        W.probAt tab ((kRunL W (hKernel tab ((Props.itsr W itsrMap).answer ()) (itsrHandler W))
          (A (itsrPk (W.hashOf tab) P s)) ((P, s, itsrPk (W.hashOf tab) P s), [], ∅) []).map
            (itsrJudge (W.hashOf tab) (itsrPk (W.hashOf tab) P s))) := by
  unfold Props.Experiment.succAt
  have hset : ClassicalOn (W.runtime tab) ((simulateQ (W.eager tab)
      (Props.itsr W itsrMap).setup).toQuantumAt (QComp.coinImpl W.spec (QReg.of Unit)))
      (pure ()) LinearMap.id :=
    (classicalOn_coinImpl_toQuantumAt _ _).congr (simulateQ_pure _ _) rfl
  refine (probAt_eq_of_run₂ W tab ((run₂_game_slRed tab (Props.itsr W itsrMap)
    (fun _ ↦ itsrPre W) (fun _ a ↦ A a.2.2) (fun _ a ↦ (a, [], ∅)) (fun _ ↦ itsrHandler W)
    (fun _ ↦ itsrPost W)).trans (run₂_bind_of_classicalOn_pure _ hset _))).trans ?_
  rw [slNormal, QuantumComp₂.bind_assoc]
  refine (probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt _ _) _).trans ?_
  rw [run_simulateQ_itsrPre W tab hW]
  simp only [tsum_prEvent_bind_mul, tsum_prEvent_pure_mul, tsum_prEvent_uniformSample]
  refine unifAvg_congr fun P ↦ unifAvg_congr fun s ↦ probAt_eq_of_run₂ W tab ?_
  rw [QuantumComp₂.bind_assoc, QuantumComp₂.map_eq_bind_pure]
  refine run₂_bind_congr rfl fun r ↦ ?_
  obtain ⟨⟨forg, st⟩, L⟩ := r
  simp only [itsrPost, simulateQ_pure, StateT.run_pure]
  refine (run₂_bind_of_classicalOn_pure _ (classicalOn_coinImpl_toQuantumAt _ _) _).trans ?_
  dsimp only
  rw [simulateQ_itsr_judge]
  exact run₂_eq_of_classicalOn (classicalOn_coinImpl_toQuantumAt _ _) (classicalOn_pure _)

/-- **The ITSR hop of Theorem 2**: at every table of a world with fair coins, the ideal game read
through the ITSR decision is the ITSR success of the reduction `itsrRed W A`. -/
theorem ideal_itsr_eq (hW : W.CoinsFair) :
    ideal W tab A (itsrDec (W.hashOf tab)) = (Props.itsr W itsrMap).succAt tab (itsrRed W A) := by
  rw [succAt_itsrRed W tab A hW]
  exact unifAvg_congr fun P ↦ unifAvg_congr fun s ↦ (probAt_itsrRed_run W tab A hW P s).symm

/-- **The ITSR hop of Theorem 2**, as a bound. -/
theorem ideal_itsr_le (hW : W.CoinsFair) :
    ideal W tab A (itsrDec (W.hashOf tab)) ≤ Props.itsrSucc W itsrMap tab (itsrRed W A) :=
  (ideal_itsr_eq W tab A hW).le

end Run

/-! ## Charges -/

section Charges

open IPFunctor

/-- **The reduction's hash calls**: `A`'s hash calls, the key generation's honest work `c₀` and
the signer's honest work `k` per signing request of `A`. -/
theorem isChargeBound_itsrRed_hash (A : SAdv W) {c₀ k n m : ℕ}
    (hpre : Common.QueryCostAtMost (itsrPre W) (hcallCost W (R' := ItsrSpec)) c₀)
    (hσ : ∀ st M, Common.QueryCostAtMost (itsrHandler W st M) (hcallCost W (R' := ItsrSpec)) k)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (itsrRed W A ()) (cmdCharge hashCharge) (c₀ + ((n + k * m) + 0)) :=
  isChargeBound_slRed_hash W (itsrPre W) (fun a ↦ A a.2.2) (fun a ↦ (a, [], ∅)) (itsrHandler W)
    (itsrPost W) hpre hσ (fun _ _ _ ↦ trivial) (fun a ↦ hn a.2.2) (fun a ↦ hm a.2.2)

variable {Q' : Type} {R' : OracleSpec.{0, 0} Q'}

omit W in
theorem queryCostAtMost_bind {ι α β : Type} {O : OracleSpec.{0, 0} ι} (cost : ι → ℕ)
    {oa : OracleComp O α} {ob : α → OracleComp O β} {n₁ n₂ : ℕ}
    (h₁ : Common.QueryCostAtMost oa cost n₁) (h₂ : ∀ x, Common.QueryCostAtMost (ob x) cost n₂) :
    Common.QueryCostAtMost (oa >>= ob) cost (n₁ + n₂) :=
  OracleComp.isQueryBound_bind (· + ·)
    (fun t b₁' b₂' b (_ : cost t ≤ b) ↦
      ⟨(by omega : cost t ≤ b₁' + b), (by omega : cost t ≤ b + b₂')⟩)
    (fun t b₁' b₂' b (_ : cost t ≤ b) ↦ ⟨(by omega : b₁' + (b - cost t) = b₁' + b - cost t),
      (by omega : b + b₂' - cost t = b - cost t + b₂')⟩) h₁ h₂

/-- A world program makes no call of the reduction's ports. -/
theorem queryCostAtMost_liftW {α : Type} (oa : OracleComp W.Oracles α) (b : ℕ) :
    Common.QueryCostAtMost (liftW R' oa) (portCost W (R' := R')) b := by
  unfold liftW
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure]
    trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (OracleComp.isQueryBound_query_bind_iff _ _ _ _ _).mpr ⟨Nat.zero_le _, ih⟩

/-- **A reduction's charge under any port charge `c`**: at most `n` when `A` is within `n`
counting a hash call by `c` and a classical call `k`, every handler being within `k`. -/
theorem isChargeBound_runH {Q St : Type} {R : OracleSpec.{0, 0} Q} {X Y : QReg → Type}
    (σ : HHandler W R R' St) (leaf : ∀ u, X u → St → Y u) (c : Port W.spec.Port Q' → ℕ) {k : ℕ}
    (hσ : ∀ s q B, IFreeM.IsChargeBound ((σ s q).toQuantumAt (hcallImpl W R' B)) (cmdCharge c) k)
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) {n : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge (srcCharge c k)) n) :
    IFreeM.IsChargeBound (runH W σ leaf x s) (cmdCharge c) n := by
  induction x using IFreeM.inductionOn generalizing s n with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    replace hx := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hx
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨hx.1, fun b ↦ ih b s (hx.2 b)⟩
    · have ht : IFreeM.IsChargeBound (answerTreeH W σ s q E ℓ) (cmdCharge c) (0 + k) :=
        FreeM₂.isChargeBound_bind (isChargeBound_act c _ 0) fun _ ↦ hσ s q _
      have hk : k ≤ n := hx.1
      refine (IFreeM.isChargeBound_bind (n₂ := n - k) ht fun u l ↦ ?_).mono (by omega)
      obtain ⟨rfl, v⟩ := l
      exact ih ⟨v.1⟩ v.2 (hx.2 ⟨v.1⟩)

/-- An adversary within `m` classical calls is within `k * m` when a classical call counts `k`
and a hash call nothing. -/
theorem isChargeBound_srcCharge_call {Q : Type} {R : OracleSpec.{0, 0} Q} {X : QReg → Type}
    {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    {m : ℕ} (k : ℕ) (hm : IFreeM.IsChargeBound x (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound x (cmdCharge (srcCharge (callCharge (Q := Q')) k)) (k * m) := by
  induction x using IFreeM.inductionOn generalizing m with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    replace hm := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hm
    refine (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ?_
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact ⟨Nat.zero_le _, fun b ↦ ih b (hm.2 b)⟩
    · exact ⟨Nat.zero_le _, fun b ↦ ih b (hm.2 b)⟩
    · have h1 : 1 ≤ m := hm.1
      refine ⟨Nat.le_mul_of_pos_right k h1, fun b ↦ (ih b (hm.2 b)).mono ?_⟩
      change k * (m - 1) ≤ k * m - k
      rw [Nat.mul_sub_one]

theorem itsrHash_eq : itsrHash W = fun l ↦ liftW ItsrSpec (W.hash l) :=
  rfl

/-- The setup makes no ITSR query. -/
theorem queryCostAtMost_itsrPre :
    Common.QueryCostAtMost (itsrPre W) (portCost W (R' := ItsrSpec)) 0 := by
  have e : itsrPre W = liftW ItsrSpec (do
      let P ← Props.sample W PublicParameter
      let s ← Props.sample W (KeygenDomain → Digest)
      let keys ← Qrom.Sphincs.LeanSphincsOver.keygenFromSeed
        (routeHash P (fun d ↦ pure (s d)) (fun _ ↦ pure 0) W.hash) 0
      pure (P, s, keys.1)) := by
    simp only [itsrPre, itsrHash_eq, liftW, simulateQ_bind, simulateQ_pure,
      Over.simulateQ_keygenFromSeed, simulateQ_routeHash]
  rw [e]
  exact queryCostAtMost_liftW W _ 0

/-- The signer makes at most one ITSR query, none on a message signed before. -/
theorem queryCostAtMost_itsrHandler (st : ItsrState) (M : Message) :
    Common.QueryCostAtMost (itsrHandler W st M) (portCost W (R' := ItsrSpec)) 1 := by
  have hsign (R : Randomizer) : Qrom.Sphincs.LeanSphincsOver.sign
      (routeHash st.1.1 (fun d ↦ pure (st.1.2.1 d)) (fun _ ↦ pure R) (itsrHash W)) 0 M =
      liftW ItsrSpec (Qrom.Sphincs.LeanSphincsOver.sign
        (routeHash st.1.1 (fun d ↦ pure (st.1.2.1 d)) (fun _ ↦ pure R) W.hash) 0 M) := by
    simp only [itsrHash_eq, liftW, Over.simulateQ_sign, simulateQ_routeHash, simulateQ_pure]
  simp only [itsrHandler]
  refine queryCostAtMost_bind (portCost W (R' := ItsrSpec)) (n₁ := 1) (n₂ := 0) ?_ fun x ↦ ?_
  · unfold itsrRnd
    cases st.2.2 M with
    | some R => trivial
    | none =>
      exact (OracleComp.isQueryBound_map_iff _ _ _ _ _).mpr
        ((OracleComp.isQueryBound_query_iff _ _ _ _).mpr le_rfl)
  · rw [hsign]
    exact queryCostAtMost_bind (portCost W (R' := ItsrSpec)) (n₁ := 0) (n₂ := 0)
      (queryCostAtMost_liftW W _ 0) fun _ ↦ trivial

/-- **The reduction's ITSR queries**: at most one per signing request of `A`. -/
theorem isChargeBound_itsrRed_call (A : SAdv W) {m : ℕ}
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (itsrRed W A ()) (cmdCharge callCharge) (0 + (1 * m + 0)) :=
  FreeM₂.isChargeBound_bind
    (isChargeBound_toQuantumAt_hcallImpl_call W _ (queryCostAtMost_itsrPre W)) fun a ↦
    FreeM₂.isChargeBound_bind (x := runHQ W (itsrHandler W) (A a.2.2) (a, [], ∅))
      (isChargeBound_runH W (itsrHandler W) _ callCharge
        (fun st M B ↦ isChargeBound_toQuantumAt_hcallImpl_call W B
          (queryCostAtMost_itsrHandler W st M))
        (A a.2.2) _ (isChargeBound_srcCharge_call W (A a.2.2) 1 (hm a.2.2)))
      fun (r : Forgery × ItsrState) ↦
        isChargeBound_toQuantumAt_hcallImpl_call W _ (oa := itsrPost W a r.1 r.2) trivial

end Charges

end Quantum.StdModel.Sphincs

end
