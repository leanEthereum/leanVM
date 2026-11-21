module

public import Quantum.StdModel.Sphincs.Hybrid

@[expose] public section

/-!
# leanSPHINCS at a fixed table: the two PRF hops

At a fixed table `tab` of a world `W` (`h := W.hashOf tab`), the SUF-CMA game of
`sphincsOver W.hash` is replaced by the ideal game (`ideal`) in two hops, each a straight-line
reduction (`slRed`) that runs `A` once against a routed signer (`routeHash`): the secrets and
randomizers come from given computations, every other input from the world's Keccak-256.

* `hyb1 W tab A`: the hybrid between the hops, with uniform `PK.seed`, uniform secret digests and
  the randomizers `rndK h K P` of a uniform `SK.prf = K`.
* `B1 W A` (KIM-PRF, D1): `PK.seed`, `SK.prf` and the secrets from the challenger's `SK.seed`-keyed
  calls; `kimPrfAdv_B1`: its advantage is the SUF-CMA winning probability minus `hyb1`.
* `B2 W A` (PRF_msg, D2): `PK.seed` and the secrets sampled by `B2`, the randomizers from the
  challenger; `prfMsgAdv_B2`: its advantage is `hyb1` minus the ideal winning probability.
* Both are routed reductions (`routedRed`); `succAt_routedRed` evaluates any routed reduction
  against a PRF challenger at `tab` as an average of `gameAt` over the routed tables
  (`succAt_slRed` for any straight-line reduction).
* `isChargeBound_B1`, `isChargeBound_B2` (from `isChargeBound_routedRed`,
  `isChargeBound_routedRed_call`): each makes `A`'s hash calls plus its honest work, and one
  classical call per challenger query of its code (`portCost`, `isChargeBound_slRed_call`).
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (keyDerivationInput)
open Quantum.Sphincs (prfMessageInput)
open Quantum.Qrom.Sphincs (QTable sphincsOver)

namespace Quantum.StdModel.Sphincs

open Props (Experiment)

/-! ## The intermediate hybrid -/

/-- **The randomizers of `SK.prf = K`** under `PK.seed = P`, evaluated with `h`. -/
def rndK (h : HashInput → HashOutput) (K : HashOutput) (P : PublicParameter) :
    Message → Digest :=
  fun M ↦ truncateHash (h (prfMessageInput K P M))

/-- **The hybrid after the KIM-PRF hop**: uniform `PK.seed`, uniform secret digests and the
randomizers of a uniform `SK.prf`. -/
noncomputable def hyb1 (W : OracleWorld) (tab : W.Tab) (A : SAdv W) : ℝ≥0∞ :=
  unifAvg PublicParameter fun P ↦ unifAvg (KeygenDomain → Digest) fun s ↦
    unifAvg HashOutput fun K ↦
      gameAt W tab A (digTable (W.hashOf tab) P s (rndK (W.hashOf tab) K P))
        (winDec (W.hashOf tab) (digTable (W.hashOf tab) P s (rndK (W.hashOf tab) K P)))

/-! ## Generic facts -/

/-- Weighting through a map of the sampler. -/
theorem tsum_prEvent_map_mul {β γ : Type} (mx : ProbComp β) (g : β → γ) (f : γ → ℝ≥0∞) :
    ∑' b, Pr{let z ← mx}[z = b] * f (g b) = ∑' c, Pr{let z ← g <$> mx}[z = c] * f c := by
  rw [map_eq_bind_pure_comp, tsum_prEvent_bind_mul]
  exact tsum_congr fun b ↦ congrArg _ (tsum_prEvent_pure_mul (g b) f).symm

/-- Relabelling twice relabels by the composite. -/
theorem map_map_qcomp {spec : QuantumOracleSpec.{0, 0}} {A B : QReg} {α β γ : Type}
    (x : QComp spec A B α) (f : α → β) (g : β → γ) : (x.map f).map g = x.map (g ∘ f) := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.map_eq_bind_pure,
    QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
  simp only [QuantumComp₂.pure_bind]
  rfl

/-- The uniform seed law as a uniform average. -/
theorem sum_sampleMasterSeed (Φ : MasterSeed → ℝ≥0∞) :
    ∑ S0 : MasterSeed, Pr{let s ← sampleMasterSeed}[s = S0] * Φ S0 = unifAvg MasterSeed Φ :=
  @sum_prEvent_uniformSample MasterSeed (SampleableType.ofFintype MasterSeed) _ Φ

/-- Under fair coins, the challenger's uniform sample weighs as the uniform average. -/
theorem tsum_sample_mul (W : OracleWorld) (tab : W.Tab) (hW : W.CoinsFair) {α : Type}
    [SampleableType α] [Fintype α] (f : α → ℝ≥0∞) :
    ∑' a, Pr{let z ← simulateQ (W.eager tab) (Props.sample W α)}[z = a] * f a =
      unifAvg α f := by
  rw [W.simulateQ_sample hW tab, tsum_prEvent_uniformSample]

/-- The real PRF challenger's key law as the uniform average. -/
theorem tsum_prfReal_setup (W : OracleWorld) (tab : W.Tab) (hW : W.CoinsFair)
    {Key Dom Rng : Type} [SampleableType Key] [Fintype Key]
    (F : Key → Dom → OracleComp W.Oracles Rng) (f : Key → ℝ≥0∞) :
    ∑' s, Pr{let z ← simulateQ (W.eager tab) (Props.prfReal W F).setup}[z = s] * f s =
      unifAvg Key f :=
  tsum_sample_mul W tab hW f

/-- The ideal PRF challenger's function law as the uniform average. -/
theorem tsum_prfIdeal_setup (W : OracleWorld) (tab : W.Tab) (hW : W.CoinsFair)
    {Dom U Rng : Type} [Fintype Dom] [SampleableType U] [Fintype (Dom → U)]
    (post : Dom → U → Rng) (f : (Dom → U) → ℝ≥0∞) :
    ∑' s, Pr{let z ← simulateQ (W.eager tab) (Props.prfIdeal W post).setup}[z = s] * f s =
      unifAvg (Dom → U) f :=
  tsum_sample_mul W tab hW f

/-! ## A straight-line reduction against a PRF challenger -/

section SlRed

variable (W : OracleWorld) (tab : W.Tab) {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
  {R' : OracleSpec.{0, 0} Q'}

/-- **A straight-line reduction against a challenger that outputs the adversary's bit**: when the
handler's answers at the table simulate the kernels `K₁` through `π` (on the states satisfying
`Inv`) and the output is the decision `d`, the success probability is the average over the
challenger's setup and the reduction's setup of the canonical run against `K₁`. -/
theorem succAt_slRed (E : Experiment W R' Unit Bool) (hj : ∀ s log b, E.judge s log b = pure b)
    {S0 St St₁ F : Type} (pre : OracleComp (W.Oracles + R') S0)
    (adv : S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F) (st0 : S0 → St)
    (σ : HHandler W R R' St) (post : S0 → F → St → OracleComp (W.Oracles + R') Bool)
    (K₁ : E.State → S0 → Kernel R St₁) (Inv : E.State → S0 → St → Prop) (π : St → St₁)
    (d : S0 → F × St₁ → Bool) (h0 : ∀ s a, Inv s a (st0 a))
    (hK : ∀ s a st, Inv s a st → ∀ q,
      Prod.map id π <$> simulateQ (plainImpl tab (E.answer s)) (σ st q) = K₁ s a (π st) q)
    (hInv : ∀ s a st, Inv s a st → ∀ q,
      ∀ p ∈ support (simulateQ (plainImpl tab (E.answer s)) (σ st q)), Inv s a p.2)
    (hpost : ∀ s a f st,
      simulateQ (plainImpl tab (E.answer s)) (post a f st) = pure (d a (f, π st))) :
    E.succAt tab (fun _ ↦ slRed W pre adv st0 σ post) =
      ∑' s, Pr{let z ← simulateQ (W.eager tab) E.setup}[z = s] *
        ∑' a, Pr{let z ← simulateQ (plainImpl tab (E.answer s)) pre}[z = a] *
          W.probAt tab ((kRunQ W (K₁ s a) (adv a) (π (st0 a))).map (d a)) := by
  refine (probAt_eq_of_run₂ W tab (run₂_game_slRed tab E (fun _ ↦ pre) (fun _ ↦ adv)
    (fun _ ↦ st0) (fun _ ↦ σ) (fun _ ↦ post))).trans
    ((probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt (W.runtime tab) _)
      _).trans (tsum_congr fun s ↦ congrArg _ ?_))
  set ans := E.answer s
  rw [slNormal, QuantumComp₂.bind_assoc]
  refine (probAt_bind_classicalOn W tab (classicalOn_coinImpl_toQuantumAt (W.runtime tab) _)
    _).trans ?_
  rw [← fst_run_logImpl tab ans pre [], ← tsum_prEvent_map_mul]
  refine tsum_congr fun p ↦ congrArg _ (probAt_eq_of_run₂ W tab ?_)
  rw [QuantumComp₂.bind_assoc]
  have htail : ∀ r : (F × St) × QueryLog R', (W.runtime tab).run₂ .instruments
      (QuantumComp₂.bind (((simulateQ (logImpl tab ans) (post p.1 r.1.1 r.1.2)).run
        r.2).toQuantumAt (QComp.coinImpl W.spec (QReg.of Unit))) fun r' ↦
        (simulateQ (W.eager tab) (E.judge s r'.2 r'.1)).toQuantumAt
          (QComp.coinImpl W.spec (QReg.of Unit))) =
      (W.runtime tab).run₂ .instruments (QuantumComp₂.pure (d p.1 (r.1.1, π r.1.2))) := by
    intro r
    refine run₂_eq_of_classicalOn (((classicalOn_coinImpl_toQuantumAt _ _).bind_id fun r' ↦
      classicalOn_coinImpl_toQuantumAt _ _).congr ?_ rfl) (classicalOn_pure _)
    simp only [hj, simulateQ_pure]
    rw [bind_pure_comp, fst_run_logImpl, hpost]
  refine (run₂_bind_congr rfl htail).trans ?_
  rw [← QuantumComp₂.map_eq_bind_pure, kRunL_eq_map, map_map_qcomp]
  have hK' : ∀ st : St × QueryLog R', Inv s p.1 st.1 → ∀ q,
      Prod.map id (fun st : St × QueryLog R' ↦ π st.1) <$> hKernel tab ans σ st q =
        K₁ s p.1 (π st.1) q := by
    rintro ⟨c, log⟩ hst q
    refine Eq.trans ?_ (hK s p.1 c hst q)
    rw [← fst_run_logImpl tab ans (σ c q) log]
    simp only [hKernel, Functor.map_map]
    rfl
  have hInv' : ∀ st : St × QueryLog R', Inv s p.1 st.1 → ∀ q,
      ∀ x ∈ support (hKernel tab ans σ st q), Inv s p.1 x.2.1 := by
    rintro ⟨c, log⟩ hst q x hx
    simp only [hKernel, support_map, Set.mem_image] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    refine hInv s p.1 c hst q r.1 ?_
    rw [← fst_run_logImpl tab ans (σ c q) log, support_map]
    exact ⟨r, hr, rfl⟩
  exact run₂_map_kRunQ_sim (W.runtime tab) (K₁ s p.1) (hKernel tab ans σ)
    (fun st ↦ Inv s p.1 st.1) (fun st ↦ π st.1) hK' hInv' (adv p.1) (st0 p.1, p.2) (h0 s p.1)
    (d p.1) _ fun _ _ _ ↦ rfl

end SlRed

/-! ## Classical calls of a straight-line reduction -/

section Calls

variable (W : OracleWorld) {Q : Type} {R : OracleSpec.{0, 0} Q} {Q' : Type}
  {R' : OracleSpec.{0, 0} Q'} {St : Type}

/-- The challenger calls of a reduction's classical query: one per query of the challenger's
port, none for the world's oracles. -/
def portCost : (W.Oracles + R').Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- A lifted world program makes no challenger call. -/
theorem isChargeBound_liftHash_call {X : QReg → Type} {A : QReg}
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} W.spec) X A) :
    IFreeM.IsChargeBound (liftHash W R' y) (cmdCharge callCharge) 0 := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rcases c with o | ⟨p, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
        ⟨le_rfl, fun b ↦ (ih b).mono (Nat.zero_le _)⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr
        ⟨le_rfl, fun b ↦ (ih b).mono (Nat.zero_le _)⟩

/-- A reduction's classical query makes one challenger call per query of the challenger's
port. -/
theorem isChargeBound_hcallImpl_call (B : QReg) (t : (W.Oracles + R').Domain) :
    IFreeM.IsChargeBound (hcallImpl W R' B t) (cmdCharge callCharge) (portCost W t) := by
  rcases t with t | q'
  · exact isChargeBound_liftHash_call W (W.impl B t)
  · change IFreeM.IsChargeBound (callQ W R' q' B) _ 1
    unfold callQ
    refine IFreeM.IsChargeBound.mono (n₁ := 1 + 0) (FreeM₂.isChargeBound_bind (n₁ := 1)
      (n₂ := 0) (isChargeBound_query₂ (S := W.spec) (RS := R') callCharge (.call q') B
        (callSplit W R' q' B)) fun _ ↦ ?_) le_rfl
    exact (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (isChargeBound_act _ _ 0) fun _ ↦
      IFreeM.isChargeBound_pure _ 0).mono le_rfl

/-- A reduction's classical algorithm with at most `n` queries of the challenger's port makes at
most `n` challenger calls. -/
theorem isChargeBound_toQuantumAt_hcallImpl_call (B : QReg) {α : Type}
    {oa : OracleComp (W.Oracles + R') α} {n : ℕ}
    (h : Common.QueryCostAtMost oa (portCost W (R' := R')) n) :
    IFreeM.IsChargeBound (oa.toQuantumAt (hcallImpl W R' B)) (cmdCharge callCharge) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.QueryCostAtMost, isQueryBound_query_bind_iff] at h
    rw [toQuantumAt_query_bind]
    have hb := FreeM₂.isChargeBound_bind (isChargeBound_hcallImpl_call W B t) fun y ↦ ih y (h.2 y)
    rwa [Nat.add_sub_cancel' h.1] at hb

/-- **A reduction's challenger calls**: at most `k` per classical call of `A` when every handler
makes at most `k` challenger queries. -/
theorem isChargeBound_runH_call {X Y : QReg → Type} (σ : HHandler W R R' St)
    (leaf : ∀ u, X u → St → Y u) {k : ℕ}
    (hσ : ∀ s q, Common.QueryCostAtMost (σ s q) (portCost W (R' := R')) k) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec W.spec R)) X A)
    (s : St) {m : ℕ} (hx : IFreeM.IsChargeBound x (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (runH W σ leaf x s) (cmdCharge callCharge) (k * m) := by
  induction x using IFreeM.inductionOn generalizing s m with
  | pure _ _ => trivial
  | liftBind A cmd next ih =>
    replace hx := (IFreeM.isChargeBound_liftBind_iff _ _ _).mp hx
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨Nat.zero_le _, fun b ↦
        (ih b s (hx.2 b)).mono (by change k * (m - 0) ≤ k * m - 0; simp)⟩
    · exact (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨Nat.zero_le _, fun b ↦
        (ih b s (hx.2 b)).mono (by change k * (m - 0) ≤ k * m - 0; simp)⟩
    · have ht : IFreeM.IsChargeBound (answerTreeH W σ s q E ℓ) (cmdCharge callCharge) (0 + k) :=
        FreeM₂.isChargeBound_bind (isChargeBound_act callCharge _ 0) fun _ ↦
          isChargeBound_toQuantumAt_hcallImpl_call W _ (hσ s q)
      have hm : 1 ≤ m := hx.1
      refine (IFreeM.isChargeBound_bind (n₂ := k * (m - 1)) ht fun u l ↦ ?_).mono ?_
      · obtain ⟨rfl, v⟩ := l
        exact ih ⟨v.1⟩ v.2 (hx.2 ⟨v.1⟩)
      · rw [Nat.mul_sub_one]
        have : k ≤ k * m := Nat.le_mul_of_pos_right k hm
        omega

/-- **A straight-line reduction's challenger calls**: those of its setup (`q₀`), `k` per
classical call of `A`, and those of its output (`q₁`), one per query of the challenger's port. -/
theorem isChargeBound_slRed_call {S0 F Out : Type} (pre : OracleComp (W.Oracles + R') S0)
    (adv : S0 → QComp (advSpec W.spec R) (QReg.of Unit) (QReg.of Unit) F) (st0 : S0 → St)
    (σ : HHandler W R R' St) (post : S0 → F → St → OracleComp (W.Oracles + R') Out)
    {q₀ q₁ k m : ℕ} (hpre : Common.QueryCostAtMost pre (portCost W (R' := R')) q₀)
    (hσ : ∀ s q, Common.QueryCostAtMost (σ s q) (portCost W (R' := R')) k)
    (hpost : ∀ a f s, Common.QueryCostAtMost (post a f s) (portCost W (R' := R')) q₁)
    (hm : ∀ a, IFreeM.IsChargeBound (adv a) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (slRed W pre adv st0 σ post) (cmdCharge callCharge)
      (q₀ + (k * m + q₁)) :=
  FreeM₂.isChargeBound_bind (isChargeBound_toQuantumAt_hcallImpl_call W _ hpre) fun a ↦
    FreeM₂.isChargeBound_bind (x := runHQ W σ (adv a) (st0 a))
      (isChargeBound_runH_call W σ _ hσ (adv a) (st0 a) (hm a)) fun (r : F × St) ↦
      isChargeBound_toQuantumAt_hcallImpl_call W _ (hpost a r.1 r.2)

end Calls

/-! ## Routed reductions -/

section Routed

variable (W : OracleWorld) {Q' : Type} (R' : OracleSpec.{0, 0} Q') {C : Type}

/-- A computation over the left summand as a computation over the sum. -/
def liftLeft {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁} {spec₂ : OracleSpec.{0, 0} ι₂}
    {α : Type} (oa : OracleComp spec₁ α) : OracleComp (spec₁ + spec₂) α :=
  liftComp oa (spec₁ + spec₂)

theorem simulateQ_liftLeft {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁}
    {spec₂ : OracleSpec.{0, 0} ι₂} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (spec₁ + spec₂) m) (impl₁ : QueryImpl spec₁ m)
    (h : ∀ t, impl (.inl t) = impl₁ t) {α : Type} (oa : OracleComp spec₁ α) :
    simulateQ impl (liftLeft (spec₂ := spec₂) oa) = simulateQ impl₁ oa :=
  QueryImpl.simulateQ_liftComp_left_eq_of_apply impl impl₁ h oa

/-- Keccak-256 in a reduction's classical code. -/
noncomputable def hashL (l : HashInput) : OracleComp (W.Oracles + R') HashOutput :=
  liftLeft (W.hash l)

/-- A classical query of the challenger's port `x`. -/
def portQ (x : Q') : OracleComp (W.Oracles + R') (R'.Range x) :=
  liftM ((W.Oracles + R').query (.inr x))

variable (par : C → PublicParameter) (sec : C → KeygenDomain → OracleComp (W.Oracles + R') Digest)
  (rnd : C → Message → OracleComp (W.Oracles + R') Digest)

/-- **The routed hash of the context `c`**: `PK.seed = par c`, the secrets from `sec c`, the
randomizers from `rnd c`, every other input from Keccak-256. -/
noncomputable def routed (c : C) : HashInput → OracleComp (W.Oracles + R') HashOutput :=
  routeHash (par c) (sec c) (rnd c) (hashL W R')

/-- **The routed setup**: a context, then the public key of the routed key generation. -/
noncomputable def rPre (ctx : OracleComp (W.Oracles + R') C) :
    OracleComp (W.Oracles + R') (C × PublicKey) := do
  let c ← ctx
  let keys ← Quantum.Qrom.Sphincs.LeanSphincsOver.keygenFromSeed (routed W R' par sec rnd c) 0
  return (c, keys.1)

/-- **The routed signer** of the context in the state, logging each answer. -/
noncomputable def rSign : HHandler W SignSpec R' (C × SignLog) := fun st M ↦ do
  let sig ← Quantum.Qrom.Sphincs.LeanSphincsOver.sign (routed W R' par sec rnd st.1) 0 M
  return (sig, (st.1, st.2 ++ [⟨M, sig⟩]))

/-- **The routed output**: the winning condition against the transcript and verification under
the public key with Keccak-256. -/
noncomputable def rPost (a : C × PublicKey) (forg : Forgery) (st : C × SignLog) :
    OracleComp (W.Oracles + R') Bool := do
  let ok ← Quantum.Qrom.Sphincs.LeanSphincsOver.verify (hashL W R') a.2 forg.message
    forg.signature
  return (RandomPermutationModel.sufCmaScheme.winningCondition st.2 forg && ok)

/-- **A routed reduction**: `A` once against the routed signer of the context sampled by `ctx`,
its forgery checked by `rPost`. -/
noncomputable def routedRed (A : SAdv W) (ctx : OracleComp (W.Oracles + R') C) :
    Props.Adversary W R' Unit Bool :=
  fun _ ↦ slRed W (rPre W R' par sec rnd ctx) (fun a ↦ A a.2) (fun a ↦ (a.1, []))
    (rSign W R' par sec rnd) (rPost W R')

/-- **A routed reduction's hash calls**: `A`'s hash calls, plus the honest work of the setup
(`c₀`), of each signing request (`k`) and of the output (`c₁`). -/
theorem isChargeBound_routedRed (A : SAdv W) (ctx : OracleComp (W.Oracles + R') C)
    {c₀ c₁ k n m : ℕ}
    (hpre : Common.QueryCostAtMost (rPre W R' par sec rnd ctx) (hcallCost W (R' := R')) c₀)
    (hσ : ∀ st M,
      Common.QueryCostAtMost (rSign W R' par sec rnd st M) (hcallCost W (R' := R')) k)
    (hpost : ∀ (a : C × PublicKey) f st,
      Common.QueryCostAtMost (rPost W R' a f st) (hcallCost W (R' := R')) c₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (routedRed W R' par sec rnd A ctx u) (cmdCharge hashCharge)
      (c₀ + ((n + k * m) + c₁)) :=
  isChargeBound_slRed_hash W _ _ _ _ _ hpre hσ hpost (fun a ↦ hn a.2) fun a ↦ hm a.2

/-- **A routed reduction's challenger calls**: one per challenger query of its classical code,
`q₀` in the setup, at most `k` per signing request, `q₁` in the output. -/
theorem isChargeBound_routedRed_call (A : SAdv W) (ctx : OracleComp (W.Oracles + R') C)
    {q₀ q₁ k m : ℕ}
    (hpre : Common.QueryCostAtMost (rPre W R' par sec rnd ctx) (portCost W (R' := R')) q₀)
    (hσ : ∀ st M,
      Common.QueryCostAtMost (rSign W R' par sec rnd st M) (portCost W (R' := R')) k)
    (hpost : ∀ (a : C × PublicKey) f st,
      Common.QueryCostAtMost (rPost W R' a f st) (portCost W (R' := R')) q₁)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (routedRed W R' par sec rnd A ctx u) (cmdCharge callCharge)
      (q₀ + (k * m + q₁)) :=
  isChargeBound_slRed_call W _ _ _ _ _ hpre hσ hpost fun a ↦ hm a.2

end Routed

/-! ## Routed reductions at a fixed table -/

section RoutedSim

variable (W : OracleWorld) (tab : W.Tab) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
  (ans : (x : Q') → OracleComp W.Oracles (R'.Range x))

theorem simulateQ_hashL (l : HashInput) :
    simulateQ (plainImpl tab ans) (hashL W R' l) = pure (W.hashOf tab l) :=
  (simulateQ_liftLeft (plainImpl tab ans) (W.eager tab) (fun _ ↦ rfl) (W.hash l)).trans
    (W.simulateQ_hash tab l)

theorem simulateQ_portQ (x : Q') :
    simulateQ (plainImpl tab ans) (portQ W R' x) = simulateQ (W.eager tab) (ans x) := by
  rw [portQ, simulateQ_spec_query]
  rfl

/-- Under fair coins, a sample lifted to a reduction's oracles is uniform. -/
theorem simulateQ_liftSample (hW : W.CoinsFair) (α : Type) [SampleableType α] :
    simulateQ (plainImpl tab ans) (liftLeft (spec₂ := R') (Props.sample W α)) = $ᵗ α :=
  (simulateQ_liftLeft (plainImpl tab ans) (W.eager tab) (fun _ ↦ rfl) (Props.sample W α)).trans
    (W.simulateQ_sample hW tab α)

variable {C : Type} {par : C → PublicParameter}
  {sec : C → KeygenDomain → OracleComp (W.Oracles + R') Digest}
  {rnd : C → Message → OracleComp (W.Oracles + R') Digest} (c : C)

theorem simulateQ_routed :
    (fun l ↦ simulateQ (plainImpl tab ans) (routed W R' par sec rnd c l)) =
      routeHash (par c) (fun d ↦ simulateQ (plainImpl tab ans) (sec c d))
        (fun M ↦ simulateQ (plainImpl tab ans) (rnd c M))
        (fun l ↦ simulateQ (plainImpl tab ans) (hashL W R' l)) :=
  funext fun l ↦ simulateQ_routeHash _ _ _ _ _ l

variable {S : KeygenDomain → Digest} {Rn : Message → Digest}
  (hs : ∀ d, simulateQ (plainImpl tab ans) (sec c d) = pure (S d))
  (hr : ∀ M, simulateQ (plainImpl tab ans) (rnd c M) = pure (Rn M))
include hs hr

theorem simulateQ_routed_keygen :
    simulateQ (plainImpl tab ans)
        (Quantum.Qrom.Sphincs.LeanSphincsOver.keygenFromSeed (routed W R' par sec rnd c) 0) =
      pure ((digTable (W.hashOf tab) (par c) S Rn).publicKey, 0) := by
  rw [Over.simulateQ_keygenFromSeed, simulateQ_routed]
  exact keygenFromSeed_routeHash hs hr (simulateQ_hashL W tab ans)

theorem simulateQ_routed_sign (M : Message) :
    simulateQ (plainImpl tab ans)
        (Quantum.Qrom.Sphincs.LeanSphincsOver.sign (routed W R' par sec rnd c) 0 M) =
      pure ((digTable (W.hashOf tab) (par c) S Rn).signature (cellHash (W.hashOf tab)) M) := by
  rw [Over.simulateQ_sign, simulateQ_routed]
  exact sign_routeHash hs hr (simulateQ_hashL W tab ans) M

theorem simulateQ_rSign (log : SignLog) (M : Message) :
    simulateQ (plainImpl tab ans) (rSign W R' par sec rnd (c, log) M) =
      pure ((digTable (W.hashOf tab) (par c) S Rn).signature (cellHash (W.hashOf tab)) M,
        (c, log ++ [⟨M,
          (digTable (W.hashOf tab) (par c) S Rn).signature (cellHash (W.hashOf tab)) M⟩])) := by
  simp only [rSign, simulateQ_bind, simulateQ_routed_sign W tab ans c hs hr M, pure_bind,
    simulateQ_pure]

/-- The routed signer at the table answers as the signer of the routed table. -/
theorem rSign_sim (st : C × SignLog) (hst : st.1 = c) (M : Message) :
    Prod.map id Prod.snd <$> simulateQ (plainImpl tab ans) (rSign W R' par sec rnd st M) =
      detKernel (W.hashOf tab) (digTable (W.hashOf tab) (par c) S Rn) st.2 M := by
  obtain ⟨c', log⟩ := st
  obtain rfl : c' = c := hst
  rw [simulateQ_rSign W tab ans _ hs hr log M, map_pure]
  simp only [detKernel, Prod.map_apply, id_eq]

/-- The routed signer keeps its context. -/
theorem rSign_inv (st : C × SignLog) (hst : st.1 = c) (M : Message) :
    ∀ p ∈ support (simulateQ (plainImpl tab ans) (rSign W R' par sec rnd st M)), p.2.1 = c := by
  obtain ⟨c', log⟩ := st
  obtain rfl : c' = c := hst
  intro p hp
  rw [simulateQ_rSign W tab ans _ hs hr log M, support_pure, Set.mem_singleton_iff] at hp
  rw [hp]

omit hs hr in
theorem simulateQ_rPost (a : C × PublicKey) (forg : Forgery) (st : C × SignLog) :
    simulateQ (plainImpl tab ans) (rPost W R' a forg st) =
      pure (RandomPermutationModel.sufCmaScheme.winningCondition st.2 forg &&
        verifyId (W.hashOf tab) a.2 forg) := by
  simp only [rPost, simulateQ_bind, Over.simulateQ_verify,
    verify_eq_pure_of_hash (simulateQ_hashL W tab ans), pure_bind, simulateQ_pure]
  rfl

end RoutedSim

/-- The routed setup's law, weighting the canonical runs against the routed tables. -/
theorem tsum_rPre (W : OracleWorld) (tab : W.Tab) {Q' : Type} {R' : OracleSpec.{0, 0} Q'}
    (ans : (x : Q') → OracleComp W.Oracles (R'.Range x)) {C : Type} (par : C → PublicParameter)
    (sec : C → KeygenDomain → OracleComp (W.Oracles + R') Digest)
    (rnd : C → Message → OracleComp (W.Oracles + R') Digest) (ctx : OracleComp (W.Oracles + R') C)
    (A : SAdv W) (S : C → KeygenDomain → Digest) (Rn : C → Message → Digest)
    (hs : ∀ c d, simulateQ (plainImpl tab ans) (sec c d) = pure (S c d))
    (hr : ∀ c M, simulateQ (plainImpl tab ans) (rnd c M) = pure (Rn c M)) :
    ∑' a, Pr{let z ← simulateQ (plainImpl tab ans) (rPre W R' par sec rnd ctx)}[z = a] *
        W.probAt tab ((kRunQ W (detKernel (W.hashOf tab)
          (digTable (W.hashOf tab) (par a.1) (S a.1) (Rn a.1))) (A a.2) []).map fun r ↦
            RandomPermutationModel.sufCmaScheme.winningCondition r.2 r.1 &&
              verifyId (W.hashOf tab) a.2 r.1) =
      ∑' c, Pr{let z ← simulateQ (plainImpl tab ans) ctx}[z = c] *
        gameAt W tab A (digTable (W.hashOf tab) (par c) (S c) (Rn c))
          (winDec (W.hashOf tab) (digTable (W.hashOf tab) (par c) (S c) (Rn c))) := by
  rw [rPre, simulateQ_bind, tsum_prEvent_bind_mul]
  refine tsum_congr fun c ↦ congrArg _ ?_
  simp only [simulateQ_bind, simulateQ_routed_keygen W tab ans c (hs c) (hr c), pure_bind,
    simulateQ_pure]
  exact tsum_prEvent_pure_mul _ _

section RoutedGame

variable (W : OracleWorld) (tab : W.Tab) {Q' : Type} (R' : OracleSpec.{0, 0} Q') {C : Type}
  (par : C → PublicParameter) (sec : C → KeygenDomain → OracleComp (W.Oracles + R') Digest)
  (rnd : C → Message → OracleComp (W.Oracles + R') Digest)

/-- **A routed reduction against a PRF-style challenger at a fixed table**: when, for the
challenger's state `s` and the context `c`, the secrets and randomizers are answered by `S s c`
and `Rn s c`, the success probability is the average of the game at the routed table. -/
theorem succAt_routedRed (E : Experiment W R' Unit Bool)
    (hj : ∀ s log b, E.judge s log b = pure b) (A : SAdv W) (ctx : OracleComp (W.Oracles + R') C)
    (S : E.State → C → KeygenDomain → Digest) (Rn : E.State → C → Message → Digest)
    (hs : ∀ s c d, simulateQ (plainImpl tab (E.answer s)) (sec c d) = pure (S s c d))
    (hr : ∀ s c M, simulateQ (plainImpl tab (E.answer s)) (rnd c M) = pure (Rn s c M)) :
    E.succAt tab (routedRed W R' par sec rnd A ctx) =
      ∑' s, Pr{let z ← simulateQ (W.eager tab) E.setup}[z = s] *
        ∑' c, Pr{let z ← simulateQ (plainImpl tab (E.answer s)) ctx}[z = c] *
          gameAt W tab A (digTable (W.hashOf tab) (par c) (S s c) (Rn s c))
            (winDec (W.hashOf tab) (digTable (W.hashOf tab) (par c) (S s c) (Rn s c))) := by
  refine (succAt_slRed W tab E hj (rPre W R' par sec rnd ctx) (fun a ↦ A a.2)
    (fun a ↦ (a.1, [])) (rSign W R' par sec rnd) (rPost W R')
    (fun s a ↦ detKernel (W.hashOf tab) (digTable (W.hashOf tab) (par a.1) (S s a.1) (Rn s a.1)))
    (fun _ a st ↦ st.1 = a.1) Prod.snd
    (fun a r ↦ RandomPermutationModel.sufCmaScheme.winningCondition r.2 r.1 &&
      verifyId (W.hashOf tab) a.2 r.1) (fun _ _ ↦ rfl)
    (fun s a st hst M ↦ rSign_sim W tab (E.answer s) a.1 (hs s a.1) (hr s a.1) st hst M)
    (fun s a st hst M ↦ rSign_inv W tab (E.answer s) a.1 (hs s a.1) (hr s a.1) st hst M)
    (fun s a f st ↦ simulateQ_rPost W tab (E.answer s) a f st)).trans
    (tsum_congr fun s ↦ congrArg _ ?_)
  exact tsum_rPre W tab (E.answer s) par sec rnd ctx A (S s) (Rn s) (hs s) (hr s)

end RoutedGame

/-! ## Two tables with the same digests -/

section Congr

variable (W : OracleWorld) (tab : W.Tab)

/-- The game depends on the table only through its public key and its signatures. -/
theorem gameAt_congr (A : SAdv W) {v v' : QTable} (hpk : v.publicKey = v'.publicKey)
    (hsig : ∀ M, v.signature (cellHash (W.hashOf tab)) M =
      v'.signature (cellHash (W.hashOf tab)) M) :
    gameAt W tab A v (winDec (W.hashOf tab) v) =
      gameAt W tab A v' (winDec (W.hashOf tab) v') := by
  have hK : detKernel (W.hashOf tab) v = detKernel (W.hashOf tab) v' := by
    funext log M
    simp only [detKernel, hsig]
  have hd : winDec (W.hashOf tab) v = winDec (W.hashOf tab) v' := by
    funext r
    simp only [winDec, hpk]
  unfold gameAt
  rw [hK, hd, hpk]

variable (h : HashInput → HashOutput) (S0 : MasterSeed)

/-- The table of the digests of the seed `S0` under `h`. -/
noncomputable def seedDig : QTable :=
  digTable h (truncateHash (h (keyDerivationInput S0 0)))
    (fun d ↦ truncateHash (h (addressedHashInput (truncateHash (h (keyDerivationInput S0 0)))
      (keygenDomainFields d) (littleEndianBytes 32 S0))))
    (rndK h (h (keyDerivationInput S0 1)) (truncateHash (h (keyDerivationInput S0 0))))

/-- The seed's table has the public key of the table of its digests. -/
theorem seedTable_publicKey : (seedTable h S0).publicKey = (seedDig h S0).publicKey :=
  publicKey_eq_of_dig (dig_mkTable_congr h (truncateHash_embedDigest _).symm
    fun _ ↦ (truncateHash_embedDigest _).symm)

/-- The seed's table has the signatures of the table of its digests. -/
theorem seedTable_signature (H : Qrom.HashDomain → HashOutput) (M : Message) :
    (seedTable h S0).signature H M = (seedDig h S0).signature H M := by
  have hb := (truncateHash_embedDigest (truncateHash (h (keyDerivationInput S0 0)))).symm
  refine signature_eq_of_dig (dig_mkTable_congr h hb fun _ ↦ (truncateHash_embedDigest _).symm) H
    ?_ (digest_mkTable_congr h hb (fun _ ↦ (truncateHash_embedDigest _).symm) M
      (truncateHash_embedDigest _).symm)
  rw [randomizer_mkTable, randomizer_mkTable]
  exact (truncateHash_embedDigest _).symm

end Congr

/-! ## B1: the KIM-PRF reduction -/

/-- The KIM-PRF port. -/
abbrev KimSpec : OracleSpec KimDom :=
  KimDom →ₒ HashOutput

section B1

variable (W : OracleWorld)

/-- **B1's context**: `PK.seed` and `SK.prf` from the challenger. -/
def b1Ctx : OracleComp (W.Oracles + KimSpec) (PublicParameter × HashOutput) := do
  let o ← portQ W KimSpec .publicSeed
  let K ← portQ W KimSpec .prfKey
  return (truncateHash o, K)

/-- **B1's secrets**: the challenger's `PRF` answers under `PK.seed`. -/
def b1Sec (c : PublicParameter × HashOutput) (d : KeygenDomain) :
    OracleComp (W.Oracles + KimSpec) Digest :=
  truncateHash <$> portQ W KimSpec (.prf c.1 d)

/-- **B1's randomizers**: `PRF_msg` under `SK.prf`, by Keccak-256. -/
noncomputable def b1Rnd (c : PublicParameter × HashOutput) (M : Message) :
    OracleComp (W.Oracles + KimSpec) Digest :=
  truncateHash <$> hashL W KimSpec (prfMessageInput c.2 c.1 M)

/-- **B1, the KIM-PRF reduction**: the routed reduction with `PK.seed`, `SK.prf` and the secrets
from the challenger. -/
noncomputable def B1 (A : SAdv W) : Props.Adversary W KimSpec Unit Bool :=
  routedRed W KimSpec Prod.fst (b1Sec W) (b1Rnd W) A (b1Ctx W)

/-- **B1's charges**: `A`'s hash calls plus B1's honest work (`c₀` in the setup, `k` per signing
request, `c₁` in the output), and one classical call per KIM-PRF query of B1's code (`q₀`, `kq`
per signing request, `q₁`). -/
theorem isChargeBound_B1 (A : SAdv W) {c₀ c₁ k q₀ q₁ kq n m : ℕ}
    (hpre : Common.QueryCostAtMost (rPre W KimSpec Prod.fst (b1Sec W) (b1Rnd W) (b1Ctx W))
      (hcallCost W (R' := KimSpec)) c₀)
    (hσ : ∀ st M, Common.QueryCostAtMost (rSign W KimSpec Prod.fst (b1Sec W) (b1Rnd W) st M)
      (hcallCost W (R' := KimSpec)) k)
    (hpost : ∀ (a : (PublicParameter × HashOutput) × PublicKey) f st,
      Common.QueryCostAtMost (rPost W KimSpec a f st) (hcallCost W (R' := KimSpec)) c₁)
    (qpre : Common.QueryCostAtMost (rPre W KimSpec Prod.fst (b1Sec W) (b1Rnd W) (b1Ctx W))
      (portCost W (R' := KimSpec)) q₀)
    (qσ : ∀ st M, Common.QueryCostAtMost (rSign W KimSpec Prod.fst (b1Sec W) (b1Rnd W) st M)
      (portCost W (R' := KimSpec)) kq)
    (qpost : ∀ (a : (PublicParameter × HashOutput) × PublicKey) f st,
      Common.QueryCostAtMost (rPost W KimSpec a f st) (portCost W (R' := KimSpec)) q₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (B1 W A u) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) ∧
      IFreeM.IsChargeBound (B1 W A u) (cmdCharge callCharge) (q₀ + (kq * m + q₁)) :=
  ⟨isChargeBound_routedRed W KimSpec _ _ _ A _ hpre hσ hpost hn hm u,
    isChargeBound_routedRed_call W KimSpec _ _ _ A _ qpre qσ qpost hm u⟩

variable (tab : W.Tab)

/-- **B1 against a challenger answering `kimTrunc x (g s x)`**. -/
theorem succAt_B1 (E : Experiment W KimSpec Unit Bool) (hj : ∀ s log b, E.judge s log b = pure b)
    (g : E.State → KimDom → HashOutput)
    (hans : ∀ s x, simulateQ (W.eager tab) (E.answer s x) = pure (kimTrunc x (g s x)))
    (A : SAdv W) :
    E.succAt tab (B1 W A) =
      ∑' s, Pr{let z ← simulateQ (W.eager tab) E.setup}[z = s] *
        gameAt W tab A (digTable (W.hashOf tab) (truncateHash (g s .publicSeed))
          (fun d ↦ truncateHash (g s (.prf (truncateHash (g s .publicSeed)) d)))
          (rndK (W.hashOf tab) (g s .prfKey) (truncateHash (g s .publicSeed))))
          (winDec (W.hashOf tab) (digTable (W.hashOf tab) (truncateHash (g s .publicSeed))
            (fun d ↦ truncateHash (g s (.prf (truncateHash (g s .publicSeed)) d)))
            (rndK (W.hashOf tab) (g s .prfKey) (truncateHash (g s .publicSeed))))) := by
  refine (succAt_routedRed W tab KimSpec Prod.fst (b1Sec W) (b1Rnd W) E hj A (b1Ctx W)
    (fun s c d ↦ truncateHash (g s (.prf c.1 d))) (fun _ c ↦ rndK (W.hashOf tab) c.2 c.1)
    (fun s c d ↦ ?_) (fun s c M ↦ ?_)).trans (tsum_congr fun s ↦ congrArg _ ?_)
  · rw [b1Sec, simulateQ_map, simulateQ_portQ, hans, map_pure, truncateHash_kimTrunc]
  · rw [b1Rnd, simulateQ_map, simulateQ_hashL, map_pure]
    rfl
  · have hc : simulateQ (plainImpl tab (E.answer s)) (b1Ctx W) =
        pure ((truncateHash (g s .publicSeed), g s .prfKey) : PublicParameter × HashOutput) := by
      simp only [b1Ctx, simulateQ_bind, simulateQ_portQ, hans, pure_bind, simulateQ_pure,
        truncateHash_kimTrunc]
      rfl
    rw [hc, tsum_prEvent_pure_mul]

/-- **B1 against the ideal KIM-PRF** wins with the hybrid's probability. -/
theorem prfIdeal_B1 (hW : W.CoinsFair) (A : SAdv W) :
    (Props.prfIdeal W kimTrunc).succAt tab (B1 W A) = hyb1 W tab A := by
  refine (succAt_B1 W tab (Props.prfIdeal W kimTrunc) (fun _ _ _ ↦ rfl) (fun f x ↦ f x)
    (fun _ _ ↦ simulateQ_pure _ _) A).trans
    ((tsum_prfIdeal_setup W tab hW _ _).trans ?_)
  exact kim_law_prfKey fun P s K ↦
    gameAt W tab A (digTable (W.hashOf tab) P s (rndK (W.hashOf tab) K P))
      (winDec (W.hashOf tab) (digTable (W.hashOf tab) P s (rndK (W.hashOf tab) K P)))

/-- **B1 against the real KIM-PRF** wins with the SUF-CMA winning probability. -/
theorem prfReal_B1 (hW : W.CoinsFair) (A : SAdv W) :
    (Props.prfReal W (Key := MasterSeed)
        (Props.kimFn W kimFmt (littleEndianBytes 32) kimTrunc)).succAt tab (B1 W A) =
      winProbAt W (sphincsOver W.hash) tab A := by
  have hans : ∀ (S0 : MasterSeed) x, simulateQ (W.eager tab)
      ((Props.prfReal W (Key := MasterSeed)
        (Props.kimFn W kimFmt (littleEndianBytes 32) kimTrunc)).answer S0 x) =
        pure (kimTrunc x (W.hashOf tab ((kimFmt x).1 ++ littleEndianBytes 32 S0 ++
          (kimFmt x).2))) := fun S0 x ↦ by
    change simulateQ (W.eager tab) (kimTrunc x <$> W.hash _) = _
    rw [simulateQ_map, W.simulateQ_hash, map_pure]
  refine (succAt_B1 W tab _ (fun _ _ _ ↦ rfl) _ hans A).trans
    ((tsum_prfReal_setup W tab hW _ _).trans ?_)
  rw [winProbAt_eq, sum_sampleMasterSeed]
  refine unifAvg_congr fun S0 ↦ ?_
  simp only [kimInput_publicSeed, kimInput_prfKey]
  exact gameAt_congr W tab A (seedTable_publicKey (W.hashOf tab) S0).symm
    fun M ↦ (seedTable_signature (W.hashOf tab) S0 _ M).symm

/-- **The KIM-PRF hop** (Theorem 2, first hop): B1's KIM-PRF advantage at `tab` is the SUF-CMA
winning probability minus the hybrid's. -/
theorem kimPrfAdv_B1 (hW : W.CoinsFair) (A : SAdv W) :
    Props.kimPrfAdv W (Key := MasterSeed) kimFmt (littleEndianBytes 32) kimTrunc tab (B1 W A) =
      (winProbAt W (sphincsOver W.hash) tab A).toReal - (hyb1 W tab A).toReal := by
  rw [Props.kimPrfAdv, Props.prfAdv, prfReal_B1 W tab hW A, prfIdeal_B1 W tab hW A]

end B1

/-! ## B2: the PRF_msg reduction -/

/-- The PRF_msg port. -/
abbrev MsgSpec : OracleSpec MsgDom :=
  MsgDom →ₒ Digest

section B2

variable (W : OracleWorld)

/-- **B2's context**: `PK.seed` and the secret digests, sampled by B2. -/
noncomputable def b2Ctx :
    OracleComp (W.Oracles + MsgSpec) (PublicParameter × (KeygenDomain → Digest)) := do
  let P ← liftLeft (spec₂ := MsgSpec) (Props.sample W PublicParameter)
  let s ← liftLeft (spec₂ := MsgSpec) (Props.sample W (KeygenDomain → Digest))
  return (P, s)

/-- **B2's secrets**: its own digests. -/
def b2Sec (c : PublicParameter × (KeygenDomain → Digest)) (d : KeygenDomain) :
    OracleComp (W.Oracles + MsgSpec) Digest :=
  pure (c.2 d)

/-- **B2's randomizers**: the challenger's answers at `(PK.seed, M)`. -/
def b2Rnd (c : PublicParameter × (KeygenDomain → Digest)) (M : Message) :
    OracleComp (W.Oracles + MsgSpec) Digest :=
  portQ W MsgSpec (c.1, M)

/-- **B2, the PRF_msg reduction**: the routed reduction with its own `PK.seed` and secrets and
the randomizers from the challenger. -/
noncomputable def B2 (A : SAdv W) : Props.Adversary W MsgSpec Unit Bool :=
  routedRed W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) A (b2Ctx W)

/-- **B2's charges**: `A`'s hash calls plus B2's honest work (`c₀` in the setup, `k` per signing
request, `c₁` in the output), and one classical call per PRF_msg query of B2's code (`q₀`, `kq`
per signing request, `q₁`). -/
theorem isChargeBound_B2 (A : SAdv W) {c₀ c₁ k q₀ q₁ kq n m : ℕ}
    (hpre : Common.QueryCostAtMost (rPre W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) (b2Ctx W))
      (hcallCost W (R' := MsgSpec)) c₀)
    (hσ : ∀ st M, Common.QueryCostAtMost (rSign W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) st M)
      (hcallCost W (R' := MsgSpec)) k)
    (hpost : ∀ (a : (PublicParameter × (KeygenDomain → Digest)) × PublicKey) f st,
      Common.QueryCostAtMost (rPost W MsgSpec a f st) (hcallCost W (R' := MsgSpec)) c₁)
    (qpre : Common.QueryCostAtMost (rPre W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) (b2Ctx W))
      (portCost W (R' := MsgSpec)) q₀)
    (qσ : ∀ st M, Common.QueryCostAtMost (rSign W MsgSpec Prod.fst (b2Sec W) (b2Rnd W) st M)
      (portCost W (R' := MsgSpec)) kq)
    (qpost : ∀ (a : (PublicParameter × (KeygenDomain → Digest)) × PublicKey) f st,
      Common.QueryCostAtMost (rPost W MsgSpec a f st) (portCost W (R' := MsgSpec)) q₁)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (B2 W A u) (cmdCharge hashCharge) (c₀ + ((n + k * m) + c₁)) ∧
      IFreeM.IsChargeBound (B2 W A u) (cmdCharge callCharge) (q₀ + (kq * m + q₁)) :=
  ⟨isChargeBound_routedRed W MsgSpec _ _ _ A _ hpre hσ hpost hn hm u,
    isChargeBound_routedRed_call W MsgSpec _ _ _ A _ qpre qσ qpost hm u⟩

variable (tab : W.Tab)

/-- **B2 against a challenger answering `ρ s x`**. -/
theorem succAt_B2 (hW : W.CoinsFair) (E : Experiment W MsgSpec Unit Bool)
    (hj : ∀ s log b, E.judge s log b = pure b) (ρ : E.State → MsgDom → Digest)
    (hans : ∀ s x, simulateQ (W.eager tab) (E.answer s x) = pure (ρ s x)) (A : SAdv W) :
    E.succAt tab (B2 W A) =
      ∑' s, Pr{let z ← simulateQ (W.eager tab) E.setup}[z = s] *
        unifAvg PublicParameter fun P ↦ unifAvg (KeygenDomain → Digest) fun sd ↦
          gameAt W tab A (digTable (W.hashOf tab) P sd fun M ↦ ρ s (P, M))
            (winDec (W.hashOf tab) (digTable (W.hashOf tab) P sd fun M ↦ ρ s (P, M))) := by
  refine (succAt_routedRed W tab MsgSpec Prod.fst (b2Sec W) (b2Rnd W) E hj A (b2Ctx W)
    (fun _ c ↦ c.2) (fun s c M ↦ ρ s (c.1, M)) (fun _ _ _ ↦ simulateQ_pure _ _)
    (fun s c M ↦ (simulateQ_portQ W tab (E.answer s) (c.1, M)).trans (hans s _))).trans
    (tsum_congr fun s ↦ congrArg _ ?_)
  have hc : simulateQ (plainImpl tab (E.answer s)) (b2Ctx W) =
      $ᵗ PublicParameter >>= fun P ↦ $ᵗ (KeygenDomain → Digest) >>= fun sd ↦ pure (P, sd) := by
    simp only [b2Ctx, simulateQ_bind, simulateQ_liftSample W tab _ hW, simulateQ_pure]
  rw [hc, tsum_prEvent_bind_mul, tsum_prEvent_uniformSample]
  refine unifAvg_congr fun P ↦ ?_
  rw [tsum_prEvent_bind_mul, tsum_prEvent_uniformSample]
  refine unifAvg_congr fun sd ↦ ?_
  rw [tsum_prEvent_pure_mul]

/-- **B2 against the real PRF_msg** wins with the hybrid's probability. -/
theorem prfReal_B2 (hW : W.CoinsFair) (A : SAdv W) :
    (Props.prfReal W (Key := HashOutput)
        (Props.prefixFn W msgBytes (littleEndianBytes 32) truncateHash)).succAt tab (B2 W A) =
      hyb1 W tab A := by
  have hans : ∀ (K : HashOutput) (x : MsgDom), simulateQ (W.eager tab)
      ((Props.prfReal W (Key := HashOutput)
        (Props.prefixFn W msgBytes (littleEndianBytes 32) truncateHash)).answer K x) =
        pure (rndK (W.hashOf tab) K x.1 x.2) := fun K x ↦ by
    change simulateQ (W.eager tab)
      (truncateHash <$> W.hash ([] ++ littleEndianBytes 32 K ++ msgBytes x)) = _
    rw [simulateQ_map, W.simulateQ_hash, map_pure, prfMsgInput_eq]
    rfl
  refine (succAt_B2 W tab hW _ (fun _ _ _ ↦ rfl) _ hans A).trans
    ((tsum_prfReal_setup W tab hW _ _).trans ?_)
  refine (unifAvg_comm _).trans (unifAvg_congr fun P ↦ (unifAvg_comm _).trans ?_)
  rfl

/-- **B2 against the ideal PRF_msg** wins with the ideal probability. -/
theorem prfIdeal_B2 (hW : W.CoinsFair) (A : SAdv W) :
    (Props.prfIdeal W (U := HashOutput) (fun _ : MsgDom ↦ truncateHash)).succAt tab (B2 W A) =
      ideal W tab A (winDec (W.hashOf tab)) := by
  have h1 := succAt_B2 W tab hW
    (Props.prfIdeal W (U := HashOutput) (fun _ : MsgDom ↦ truncateHash))
    (fun _ _ _ ↦ rfl) (fun g x ↦ truncateHash (g x)) (fun _ _ ↦ simulateQ_pure _ _) A
  refine h1.trans ?_
  refine (tsum_prfIdeal_setup W tab hW _ _).trans ?_
  refine (unifAvg_comm _).trans (unifAvg_congr fun P ↦ (unifAvg_comm _).trans ?_)
  refine unifAvg_congr fun sd ↦ ?_
  exact msg_law P fun r ↦ gameAt W tab A (digTable (W.hashOf tab) P sd r)
    (winDec (W.hashOf tab) (digTable (W.hashOf tab) P sd r))

/-- **The PRF_msg hop** (Theorem 2, second hop): B2's PRF_msg advantage at `tab` is the hybrid's
winning probability minus the ideal one. -/
theorem prfMsgAdv_B2 (hW : W.CoinsFair) (A : SAdv W) :
    Props.prfMsgAdv W (Key := HashOutput) msgBytes (littleEndianBytes 32) truncateHash tab
        (B2 W A) =
      (hyb1 W tab A).toReal - (ideal W tab A (winDec (W.hashOf tab))).toReal := by
  rw [Props.prfMsgAdv, Props.prfAdv, prfReal_B2 W tab hW A, prfIdeal_B2 W tab hW A]

end B2

end Quantum.StdModel.Sphincs

end
