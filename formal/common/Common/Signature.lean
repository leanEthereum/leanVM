module

public import Common.Keccak
public import Common.Lemmas
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.WriterCost
public import Common.Lanes
public import Common.Rerun
public import Common.WithHash

@[expose] public section

/-!
# Signature games in the random-permutation model

The SUF-CMA game of a hash-based signature scheme whose hash `H : List UInt8 → BitVec 256` is
Keccak-256 read through a bijection with its 32 bytes (`e : DigestBytes ≃ BitVec 256`; the statement's,
in leanXMSS and leanSPHINCS, is `digestBytesEquivBitVec`, the bytes read little endian).

* **The ROM game** (`romGame`, `romExperiment`): a seed sampled, keys generated from it, the
  adversary run with the hash and a signing oracle that logs its requests, the forgery verified,
  all hashing through one random oracle; the experiment counts every hash call, cache hits
  included. These are the games of `lean_xmss` and `lean_sphincs`, written for any scheme.
* **The RPM game** (`rpmGameH`, `rpmExperimentH`, `Common.HashOracle`): the same game where `H` is
  Keccak-256, the sponge over the random permutation `π` read through `e`, and the adversary also
  queries `π` and `π⁻¹` and Keccak-256 itself. The statement's game, whose adversary queries `π`
  and `π⁻¹` alone, is this one with each hash call expanded into its permutation calls
  (`Common.PiOnly`).

`rpm_le_romB` (on the bytes of the states): for an RPM adversary `A`, the ROM adversary `romAdv A`
(`A` with its permutation queries answered by the indifferentiability simulator) wins the ROM game
with probability at least `A`'s RPM probability minus `Q² / 2^509`, where `Q` bounds the permutation
calls of the RPM game (`permCallsH`: a hash of `n` bytes costs `⌊n / 136⌋ + 1`, a call of `π` or
`π⁻¹` one), and its experiment makes at most `q` hash calls whenever the RPM game makes at most `q`
calls of `H`, `π` and `π⁻¹` in all (`oracleCalls`). Both budgets bound every path of the game,
whatever the answers (`QueryCostAtMost`). `Common.AdvBudget` builds the end bound on it, at the
adversary's own count (`stronglyUnforgeable_of_romBoundAdv`).

The signing oracle runs inside the adversary's phase: the transfer (`keccak256_transfer`) takes as
its adversary the RPM adversary together with the signer, whose secret key comes from the honest
key generation before it, so the ROM adversary is the RPM adversary with the simulator, and the
signing oracle stays the game's.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common.SufCma

/-! ## Digests as bit vectors -/

/-- Bits `8 i … 8 i + 7` of a digest's bit vector are its byte `i`. -/
theorem digestBitVec_symm_getElem (b : BitVec 256) (i : Fin 32) :
    (digestBytesEquivBitVec.symm b)[i] = UInt8.ofBitVec (b.extractLsb' (8 * i) 8) := by
  apply UInt8.toNat_inj.mp
  simp only [digestBytesEquivBitVec, Equiv.symm_trans_apply, uInt8EquivFin, arrayVectorEquivFin]
  simp
  change ((finFunctionFinEquiv (m := 256) (n := 32)).symm b.toFin i : ℕ) = _
  rw [finFunctionFinEquiv_symm_apply_val, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

/-- Bits `8 i … 8 i + 7` of a digest's bit vector are its byte `i`. -/
theorem digestBitVec_extract (d : DigestBytes) (i : Fin 32) :
    (digestBytesEquivBitVec d).extractLsb' (8 * i) 8 = d[i].toBitVec := by
  have h := digestBitVec_symm_getElem (digestBytesEquivBitVec d) i
  rw [Equiv.symm_apply_apply] at h
  rw [h]

/-! ## Two simulations commute -/

section Commute

variable {ι ι₁ ι₂ ι₃ ι₄ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁}
  {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {σ L α : Type}
  [EmptyCollection L] [Append L] [LawfulAppend L]

/-- **A state layer and a writer layer commute.** Simulating with a stateful `f₁` then a writer
`g₁` (then `h₁`) is simulating with a writer `f₂` then a stateful `g₂`, when it is so query by
query. -/
theorem simulateQ_state_writer_comm
    (f₁ : QueryImpl spec (StateT σ (OracleComp spec₁)))
    (g₁ : QueryImpl spec₁ (WriterT L (OracleComp spec₂)))
    (h₁ : QueryImpl spec₂ (OracleComp spec₃))
    (f₂ : QueryImpl spec (WriterT L (OracleComp spec₄)))
    (g₂ : QueryImpl spec₄ (StateT σ (OracleComp spec₃)))
    (hstep : ∀ t s, simulateQ h₁ ((simulateQ g₁ ((f₁ t).run s)).run) =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$> (simulateQ g₂ ((f₂ t).run)).run s)
    (oa : OracleComp spec α) (s : σ) :
    simulateQ h₁ ((simulateQ g₁ ((simulateQ f₁ oa).run s)).run) =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$> (simulateQ g₂ ((simulateQ f₂ oa).run)).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, WriterT.run_bind', map_bind]
    rw [hstep, bind_map_left]
    refine bind_congr fun z ↦ ?_
    rw [simulateQ_map, ih, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
    rfl

end Commute

/-! ## The games -/

/-- The random oracle of the transfer: byte strings to Keccak-256 digests. -/
abbrev KRom := unifSpec + roSpec (List UInt8) DigestBytes

/-- Coins and the hash. -/
abbrev World := unifSpec + SchemeHashSpec

variable {Seed PK SK Req Resp F : Type}

/-- The signing oracle: answer a request with the signer, and log it. -/
def signingOracle (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp World)) :=
  QueryImpl.withLogging fun r ↦ liftM (S.sign sk r : OracleComp (SchemeHashSpec) Resp)

/-- **The ROM game**: sample the seed, generate the keys, run the adversary with the hash and a
logging signing oracle, verify its forgery. -/
noncomputable def romGame (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) : OracleComp World Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← liftM (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ (QueryImpl.ofLift World
      (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp World)) + signingOracle S sk)
      (main pk)).run
  let verified ← liftM (S.verify pk forgery)
  return S.win log forgery && verified

/-- The random oracle with every hash call counted, cache hits included. -/
noncomputable def countedImpl :=
  (unifFwdImpl (SchemeHashSpec) +
    (randomOracle : QueryImpl (SchemeHashSpec) (StateT (QueryCache (SchemeHashSpec)) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- **The ROM experiment**: the ROM game in the random oracle model, with its hash calls. -/
noncomputable def romExperiment (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) : ProbComp (Bool × Nat) :=
  (simulateQ countedImpl (romGame S main)).run.run' ∅

variable (e : DigestBytes ≃ BitVec 256)

/-! ## The RPM game on byte states

The RPM game with the hash oracle (`rpmGameH`) on lanes, written on byte states (`KSpecB`): the game the
proofs below transfer; `rpmGame_relabel` relates the two. -/

/-- The hash as Keccak-256 read through `e`, on byte states. -/
def hashKB : QueryImpl (SchemeHashSpec) (OracleComp KSpecB) :=
  fun m ↦ e <$> (liftM (KSpecB.query (.inr (.inl m))) : OracleComp KSpecB DigestBytes)

/-- The signing oracle on byte states. -/
def signingOracleKB (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp) (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) :=
  QueryImpl.withLogging fun r ↦ simulateQ (hashKB e) (S.sign sk r)

/-- The RPM game on byte states. -/
noncomputable def rpmGameB (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F) : OracleComp KSpecB Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← simulateQ (hashKB e) (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ (QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) +
      signingOracleKB e S sk) (main pk)).run
  let verified ← simulateQ (hashKB e) (S.verify pk forgery)
  return S.win log forgery && verified

/-- The RPM experiment on byte states. -/
noncomputable def rpmExperimentB (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F) : ProbComp Bool :=
  runKB (rpmGameB e S main)

/-- Calls of `H`, `π` and `π⁻¹`, one each, on byte states. -/
def oracleCallsB : KSpecB.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The permutation calls are the cost of the transfer. -/
theorem permCallsB_eq : permCallsB = queryCost (Dg := DigestBytes) (St := KState) keccakPadding := by
  funext t
  rcases t with n | m | q
  · rfl
  · exact (keccakPad_length m).symm
  · rfl

/-! ## The ROM adversary -/

/-- The hash as the transfer's random oracle read through `e`. -/
def hashR : QueryImpl (SchemeHashSpec) (OracleComp KRom) :=
  fun m ↦ e <$> (liftM (KRom.query (.inr m)) : OracleComp KRom DigestBytes)

/-- The scheme's oracles in the transfer's random-oracle model: coins, and `H` read through
`e`. -/
def toK : QueryImpl World (OracleComp KRom)
  | .inl n => liftM (KRom.query (.inl n))
  | .inr m => hashR e m

/-- The transfer's oracles from the scheme's: coins, and `H` read back through `e⁻¹`. -/
def ofK : QueryImpl KRom (OracleComp World)
  | .inl n => liftM (World.query (.inl n))
  | .inr m => e.symm <$> (liftM (World.query (.inr m)) : OracleComp World (BitVec 256))

/-- The transfer's oracles from the scheme's, with signing requests: coins, and `H` read back
through `e⁻¹`. -/
def ofKS : QueryImpl KRom (OracleComp (World + (Req →ₒ Resp)))
  | .inl n => liftM ((World + (Req →ₒ Resp)).query (.inl (.inl n)))
  | .inr m => e.symm <$>
      (liftM ((World + (Req →ₒ Resp)).query (.inl (.inr m))) : OracleComp (World + (Req →ₒ Resp)) (BitVec 256))

/-- The RPM adversary's oracles from the scheme's ROM oracles: its coins, Keccak-256, `π` and
`π⁻¹` as in the ideal world of indifferentiability (`H` read back through `e⁻¹`, the permutation
answered by the simulator), its signing requests forwarded. -/
noncomputable def simAdv :
    QueryImpl (KSpecB + (Req →ₒ Resp))
      (StateT (SimState DigestBytes KRest KCap) (OracleComp (World + (Req →ₒ Resp))))
  | .inl t => StateT.mk fun σ ↦ simulateQ (ofKS e) ((idealImpl keccakPadding t).run σ)
  | .inr r => liftM ((World + (Req →ₒ Resp)).query (.inr r))

/-- **The ROM adversary of an RPM adversary**: its permutation queries answered by the
simulator, from its initial state. -/
noncomputable def romAdv (main : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F) (pk : PK) :
    OracleComp (World + (Req →ₒ Resp)) F :=
  (simulateQ (simAdv e) (main pk)).run' (SimState.init KState.zero)

theorem simulateQ_toK_ofK {β : Type} (X : OracleComp KRom β) :
    simulateQ (toK e) (simulateQ (ofK e) X) = X := by
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_id' X]
  congr 1
  funext t
  rcases t with n | m
  · simp [ofK, toK]
  · simp [ofK, toK, hashR]

/-- The hash of the RPM game is that of the transfer's ROM, lifted. -/
theorem simulateQ_hashKB {β : Type} (X : OracleComp (SchemeHashSpec) β) :
    simulateQ (hashKB e) X = liftH (E := KRest) (C := KCap) (simulateQ (hashR e) X) := by
  rw [liftH, ← QueryImpl.simulateQ_compose]
  congr 1

/-- A query lifted into a writer writes nothing. -/
theorem run_liftM_query_writer {ι : Type} {spec : OracleSpec ι} {L : Type} [EmptyCollection L]
    [Append L] (t : spec.Domain) :
    (liftM (spec.query t) : WriterT L (OracleComp spec) _).run =
      (·, ∅) <$> (liftM (spec.query t) : OracleComp spec _) := rfl

/-- A simulation whose every step writes nothing writes nothing. -/
theorem run_simulateQ_writer_of_run {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {L β : Type} [EmptyCollection L] [Append L] [LawfulAppend L]
    (impl : QueryImpl spec (WriterT L (OracleComp spec'))) (j : QueryImpl spec (OracleComp spec'))
    (h : ∀ t, (impl t).run = (·, ∅) <$> j t) (X : OracleComp spec β) :
    (simulateQ impl X).run = (·, ∅) <$> simulateQ j X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind', h, ih, bind_map_left, map_bind,
      Functor.map_map]
    simp

/-- A computation of the scheme's oracles run as a writer that logs nothing. -/
theorem run_simulateQ_ofLift_writer {ι : Type} {spec : OracleSpec ι} {L β : Type}
    [EmptyCollection L] [Append L] [LawfulAppend L] (X : OracleComp spec β) :
    (simulateQ (QueryImpl.ofLift spec (WriterT L (OracleComp spec))) X).run = (·, ∅) <$> X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind', QueryImpl.ofLift_apply]
    have : (liftM (spec.query t) : WriterT L (OracleComp spec) _).run =
        (·, ∅) <$> (liftM (spec.query t) : OracleComp spec _) := rfl
    simp [this, ih, map_bind]

/-- **The ROM adversary against the game's signing oracle is the simulated RPM adversary with
the signer**: the ROM game's middle phase, its hash read as the transfer's random oracle, is the
ideal world of the RPM game's middle phase. -/
theorem toK_middle (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) {α : Type}
    (oa : OracleComp (KSpecB + (Req →ₒ Resp)) α) (σ : SimState DigestBytes KRest KCap) :
    simulateQ (toK e) ((simulateQ (QueryImpl.ofLift World
      (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp World)) + signingOracle S sk)
        ((simulateQ (simAdv e) oa).run σ)).run) =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$> (simulateQ (idealImpl keccakPadding)
        ((simulateQ (QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) +
          signingOracleKB e S sk) oa).run)).run σ := by
  refine simulateQ_state_writer_comm _ _ _ _ _ (fun t s ↦ ?_) oa σ
  rcases t with t | r
  · have h1 : (simAdv (Req := Req) (Resp := Resp) e (.inl t)).run s =
        simulateQ (ofKS e) ((idealImpl keccakPadding t).run s) := rfl
    have h3 : ∀ u, (((QueryImpl.ofLift World
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp World)) + signingOracle S sk) ∘ₛ
          ofKS e) u).run = (·, ∅) <$> ofK e u := by
      intro u
      rcases u with n | m
      · rfl
      · simp [ofKS, ofK, run_liftM_query_writer, Functor.map_map]
    have h2 : ((QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) +
        signingOracleKB e S sk) (.inl t)).run =
          (·, ∅) <$> (liftM (KSpecB.query t) : OracleComp KSpecB _) := rfl
    rw [h1, ← QueryImpl.simulateQ_compose, run_simulateQ_writer_of_run _ _ h3, simulateQ_map,
      simulateQ_toK_ofK, h2, simulateQ_map, StateT.run_map, Functor.map_map,
      simulateQ_spec_query]
    rfl
  · have h1 : (simAdv (Req := Req) (Resp := Resp) e (.inr r)).run s =
        (fun u ↦ (u, s)) <$>
          (liftM ((World + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ Resp) := by
      simp [simAdv]
    have h2 : ((QueryImpl.ofLift World
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp World)) + signingOracle S sk)
          (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
            (liftM (S.sign sk r : OracleComp (SchemeHashSpec) Resp) : OracleComp World Resp) := by
      simp [signingOracle]
    have h3 : ((QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) +
        signingOracleKB e S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
          simulateQ (hashKB e) (S.sign sk r) := by
      simp [signingOracleKB]
    have h4 : simulateQ (toK e)
        (liftM (S.sign sk r : OracleComp (SchemeHashSpec) Resp) : OracleComp World Resp) =
          simulateQ (hashR e) (S.sign sk r) :=
      QueryImpl.simulateQ_liftComp_right_eq_of_apply (toK e) (hashR e) (fun _ ↦ rfl) _
    rw [h1, simulateQ_map, simulateQ_spec_query, WriterT.run_map', h2, h3, simulateQ_map,
      simulateQ_map, simulateQ_map, h4, simulateQ_hashKB, StateT.run_map, run_idealImpl_liftH,
      Functor.map_map, Functor.map_map, Functor.map_map]
    rfl

/-! ## The games in the shape of the transfer -/

/-- The honest part before the adversary: the seed and the keys, hashing in the transfer's
ROM. -/
noncomputable def preR (S : SchemeWithHash Seed PK SK Req Resp F) : OracleComp KRom (PK × SK) := do
  let seed ← liftM S.sample
  simulateQ (hashR e) (S.keygen seed)

/-- The adversary of the transfer: the RPM adversary with the signing oracle. -/
noncomputable def advK (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F) (x : PK × SK) :
    OracleComp KSpecB (F × QueryLog (Req →ₒ Resp)) :=
  (simulateQ (QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) +
    signingOracleKB e S x.2) (main x.1)).run

/-- The honest part after the adversary: verify the forgery, hashing in the transfer's ROM. -/
noncomputable def postR (S : SchemeWithHash Seed PK SK Req Resp F) (x : PK × SK)
    (a : F × QueryLog (Req →ₒ Resp)) : OracleComp KRom Bool := do
  let verified ← simulateQ (hashR e) (S.verify x.1 a.1)
  return S.win a.2 a.1 && verified

/-- A coin computation, lifted. -/
theorem liftH_liftM {β : Type} (p : ProbComp β) :
    liftH (E := KRest) (C := KCap) (liftM p : OracleComp KRom β) = (liftM p : OracleComp KSpecB β) := by
  change simulateQ hEmbed (OracleComp.liftComp p _) = OracleComp.liftComp p _
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply hEmbed (fun n ↦ hEmbed (.inl n))
    (fun _ ↦ rfl), OracleComp.liftComp_def]
  rfl

/-- **The RPM game has the transfer's shape.** -/
theorem rpmGameB_eq (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F) :
    rpmGameB e S main = Common.rpmGame (preR e S) (advK e S main) (postR e S) := by
  have h1 := liftH_liftM S.sample
  have h2 := simulateQ_hashKB e (β := Bool)
  have h3 := simulateQ_hashKB e (β := PK × SK)
  simp only [liftH] at h1 h2 h3
  simp only [rpmGameB, Common.rpmGame, preR, postR, advK, liftH, simulateQ_bind, bind_assoc,
    h1, ← h2, ← h3, simulateQ_pure]

/-- Coins, read in the transfer's ROM. -/
theorem simulateQ_toK_liftM_probComp {β : Type} (p : ProbComp β) :
    simulateQ (toK e) (liftM p : OracleComp World β) = (liftM p : OracleComp KRom β) := by
  change simulateQ (toK e) (OracleComp.liftComp p _) = OracleComp.liftComp p _
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (toK e) (fun n ↦ toK e (.inl n))
    (fun _ ↦ rfl), OracleComp.liftComp_def]
  rfl

/-- The scheme's hashing, read in the transfer's ROM. -/
theorem simulateQ_toK_liftM_hash {β : Type} (X : OracleComp (SchemeHashSpec) β) :
    simulateQ (toK e) (liftM X : OracleComp World β) = simulateQ (hashR e) X :=
  QueryImpl.simulateQ_liftComp_right_eq_of_apply (toK e) (hashR e) (fun _ ↦ rfl) X

/-- **The ROM game against the ROM adversary is the ideal world of the RPM game**: read in the
transfer's ROM, it is the transfer's ROM game against `advS` of the RPM adversary with the
signer. -/
theorem simulateQ_toK_romGame (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F) :
    simulateQ (toK e) (romGame S (romAdv e main)) =
      preR e S >>= fun x ↦ advS keccakPadding KState.zero (advK e S main x) >>= fun a ↦
        postR e S x a := by
  simp only [romGame, preR, postR, advK, advS, romAdv, simulateQ_bind, bind_assoc,
    simulateQ_toK_liftM_probComp, simulateQ_toK_liftM_hash, simulateQ_pure, StateT.run'_eq,
    simulateQ_map, WriterT.run_map']
  refine bind_congr fun seed ↦ bind_congr fun x ↦ ?_
  rw [toK_middle, Functor.map_map]
  rfl

/-! ## A random oracle read through a bijection is a random oracle -/

/-- A cache of the transfer's random oracle, read through `e`. -/
def cacheMap (c : (roSpec (List UInt8) DigestBytes).QueryCache) : SchemeHashSpec.QueryCache :=
  QueryCache.ofFn fun m ↦ (c m).map e

theorem cacheMap_cacheQuery (c : (roSpec (List UInt8) DigestBytes).QueryCache) (m : List UInt8)
    (u : DigestBytes) : cacheMap e (c.cacheQuery m u) = (cacheMap e c).cacheQuery m (e u) := by
  refine QueryCache.ext fun m' ↦ ?_
  by_cases h : m' = m
  · subst h; simp [cacheMap]
  · have := QueryCache.cacheQuery_of_ne c u h
    simp only [cacheMap, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ h, this]
    rfl

/-- **The random oracle read through `e` is the random oracle on `BitVec 256`**: running a game of the
scheme's oracles in the transfer's ROM, its hash read through `e`, gives the game's ROM
distribution. -/
theorem romRun_toK {β : Type} (Y : OracleComp World β) :
    romRun (simulateQ (toK e) Y) =ᵈ (simulateQ SchemeHashSpec.romImpl Y).run' ∅ := by
  have h0 : cacheMap e (∅ : (roSpec (List UInt8) DigestBytes).QueryCache) = ∅ := by
    exact QueryCache.ext fun _ ↦ rfl
  rw [romRun, ← QueryImpl.simulateQ_compose, ← h0]
  refine run'_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) (cacheMap e)
    (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ ?_) Y ∅ trivial
  rcases t with n | m
  · have h1 : ∀ {ι : Type} {sp : OracleSpec ι} (c : sp.QueryCache),
        (unifFwdImpl sp n).run c = (·, c) <$> (unifSpec.query n : ProbComp _) := fun c ↦ by
      simpa using unifFwdImpl.simulateQ_run (unifSpec.query n : ProbComp _) c
    simp only [QueryImpl.apply_compose, toK]
    simp only [simulateQ_spec_query, QueryImpl.add_apply_inl, h1, Functor.map_map]
    exact EvalDistEq.rfl
  · simp only [QueryImpl.apply_compose, toK, hashR, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, Functor.map_map]
    rw [OracleSpec.romImpl_apply_inr, OracleSpec.romImpl_apply_inr, randomOracle.run_eq,
      randomOracle.run_eq]
    cases h : c m with
    | some v =>
      have h' : cacheMap e c m = some (e v) := by simp [cacheMap, h]
      simp only [h']
      simp
    | none =>
      have h' : cacheMap e c m = none := by simp [cacheMap, h]
      simp only [h']
      simp only [map_bind, map_pure, Prod.map, id, cacheMap_cacheQuery]
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective)
        (fun u ↦ (pure (u, (cacheMap e c).cacheQuery m u) : ProbComp _)))
      rw [bind_map_left]

/-! ## Hash calls -/

/-- Hash calls of the transfer's ROM, one each. -/
def romCalls : KRom.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Hash calls of the scheme's ROM, one each. -/
def hashCalls : World.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Coins make no hash call. -/
theorem isWeightBound_liftM_probComp_krom {β : Type} (p : ProbComp β) :
    QueryCostAtMost (liftM p : OracleComp KRom β) romCalls 0 :=
  isWeightBound_liftM_probComp romCalls (fun _ ↦ rfl) p

/-- **Each step of the ideal world makes at most one hash call**, none for a coin. -/
theorem isWeightBound_idealImpl (t : KSpecB.Domain) (s : SimState DigestBytes KRest KCap) :
    QueryCostAtMost ((idealImpl keccakPadding t).run s) romCalls (oracleCallsB t) := by
  have hu : QueryCostAtMost (liftM ($ᵗ KState) : OracleComp KRom KState) romCalls 0 :=
    isWeightBound_liftM_probComp_krom _
  rcases t with n | m | q
  · simp only [idealImpl, StateT.run_monadLift, monadLift_self]
    exact (isWeightBound_liftM_probComp_krom _).bind fun _ ↦ isWeightBound_pure _ _ 0
  · simp only [idealImpl, StateT.run_monadLift, monadLift_self]
    exact (isWeightBound_query romCalls (.inr m)).bind fun _ ↦ isWeightBound_pure _ _ 0
  · cases q with
    | forward x =>
      simp only [idealImpl, simulator, StateT.run_mk]
      split
      · trivial
      · split
        · refine (QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ isWeightBound_pure _ _ 0)
          unfold rootedAnswer
          split
          · exact ((isWeightBound_query romCalls (.inr _)).bind fun _ ↦
              (isWeightBound_liftM_probComp_krom _).bind fun _ ↦ isWeightBound_pure _ _ 0)
          · exact (isWeightBound_liftM_probComp_krom _).mono (Nat.zero_le _)
        · exact (hu.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)
    | inverse y =>
      simp only [idealImpl, simulator, StateT.run_mk]
      split
      · trivial
      · exact (hu.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.zero_le _)

/-- A hash-call bound of a game read in the transfer's ROM is one of the game. -/
theorem isWeightBound_of_toK {β : Type} {Y : OracleComp World β} {Q : ℕ}
    (h : QueryCostAtMost (simulateQ (toK e) Y) romCalls Q) : QueryCostAtMost Y (hashCalls) Q := by
  induction Y using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map] at h
    rw [isWeightBound_query_bind_iff]
    rcases t with n | m
    · obtain ⟨h1, h2⟩ := (isWeightBound_query_bind_iff _ _ _ _).mp h
      exact ⟨h1, fun u ↦ ih u (h2 u)⟩
    · simp only [toK, hashR, bind_map_left] at h
      obtain ⟨h1, h2⟩ := (isWeightBound_query_bind_iff _ _ _ _).mp h
      refine ⟨h1, fun u ↦ ih u ?_⟩
      have := h2 (e.symm u)
      rwa [Equiv.apply_symm_apply] at this

/-- **The counted hash calls of a run are at most its bound.** -/
theorem count_le_of_isWeightBound {β : Type} {Y : OracleComp World β} {Q : ℕ}
    (h : QueryCostAtMost Y (hashCalls) Q) (c : SchemeHashSpec.QueryCache) :
    ∀ z ∈ support ((simulateQ (countedImpl) Y).run.run c),
      Multiplicative.toAdd z.1.2 ≤ Q := by
  induction Y using OracleComp.inductionOn generalizing Q c with
  | pure a =>
    intro z hz
    simp at hz
    subst hz
    exact Nat.zero_le _
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind, StateT.run_bind] at hz
    simp only [countedImpl, QueryImpl.withAddCost_apply] at hz
    simp at hz
    obtain ⟨a, b, -, a1, a2, b1, h2, rfl⟩ := hz
    have h3 := ih a (h.2 a) b ((a1, Multiplicative.ofAdd a2), b1) (by simpa [countedImpl] using h2)
    have h4 := h.1
    rcases t with n | m
    · change 0 + a2 ≤ Q
      change a2 ≤ Q - 0 at h3
      omega
    · change 1 + a2 ≤ Q
      simp only [hashCalls] at h3 h4
      change a2 ≤ Q - 1 at h3
      omega

/-! ## The transfer of the game -/

/-- The ideal world of a game of the transfer's shape is its ROM game against `advS`. -/
theorem run'_idealImpl_rpmGame {β γ δ : Type} (pre : OracleComp KRom β)
    (A : β → OracleComp KSpecB γ) (post : β → γ → OracleComp KRom δ) :
    (simulateQ (idealImpl keccakPadding) (Common.rpmGame pre A post)).run'
        (SimState.init KState.zero) =
      pre >>= fun x ↦ advS keccakPadding KState.zero (A x) >>= fun a ↦ post x a := by
  simp only [Common.rpmGame, advS, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    run_idealImpl_liftH, bind_map_left, map_bind, Functor.map_map]
  refine bind_congr fun x ↦ ?_
  simp

theorem fst_map_run_withAddCost {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) (c : spec.Domain → ℕ) {β : Type}
    (oa : OracleComp spec β) :
    Prod.fst <$> (simulateQ (impl.withAddCost c) oa).run = simulateQ impl oa :=
  QueryImpl.fst_map_run_withCost impl _ oa

/-- The ROM experiment's success, its counter dropped. -/
theorem prob_romExperiment (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) :
    Pr{let r ← romExperiment S main}[r.1 = true] =
      Pr{let b ← (simulateQ SchemeHashSpec.romImpl (romGame S main)).run' ∅}[b = true] := by
  have h2 : Prod.fst <$> romExperiment S main =
      (simulateQ SchemeHashSpec.romImpl (romGame S main)).run' ∅ := by
    have h : Prod.fst <$> (simulateQ (countedImpl) (romGame S main)).run =
        simulateQ SchemeHashSpec.romImpl (romGame S main) := fst_map_run_withAddCost _ _ _
    rw [StateT.run'_eq, ← h, StateT.run_map, romExperiment, StateT.run'_eq, Functor.map_map]
    exact Functor.map_map _ _ _
  rw [← h2, prEvent_map]

/-- **The RPM game against the ROM game.** For an RPM adversary whose game makes at most `Q`
permutation calls (`permCallsB`) and at most `q` calls of `H`, `π` and `π⁻¹` (`oracleCallsB`) on
every path, the ROM adversary `romAdv e main` wins the ROM game with probability at least the RPM
one minus `Q² / 2^509`, and its ROM experiment makes at most `q` hash calls on every outcome. -/
theorem rpm_le_romB (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecB + (Req →ₒ Resp)) F) (q Q : ℕ)
    (hq : QueryCostAtMost (rpmGameB e S main) oracleCallsB q)
    (hQ : QueryCostAtMost (rpmGameB e S main) permCallsB Q) :
    Pr{let b ← rpmExperimentB e S main}[b = true] ≤
        Pr{let r ← romExperiment S (romAdv e main)}[r.1 = true] + (Q ^ 2 : ℝ≥0∞) / 2 ^ 509 ∧
      ∀ r ∈ support (romExperiment S (romAdv e main)), r.2 ≤ q := by
  rw [rpmGameB_eq] at hq hQ
  rw [permCallsB_eq] at hQ
  constructor
  · obtain ⟨h1, -⟩ := keccak256_transfer (preR e S) (advK e S main) (postR e S) Q hQ (· = true)
    rw [rpmExperimentB, rpmGameB_eq, prob_romExperiment, ← (romRun_toK e _).prEvent_eq,
      simulateQ_toK_romGame]
    exact h1
  · have h1 : QueryCostAtMost (simulateQ (toK e) (romGame S (romAdv e main))) romCalls q := by
      rw [simulateQ_toK_romGame, ← run'_idealImpl_rpmGame, StateT.run'_eq]
      exact isWeightBound_map _ (isWeightBound_run_simulateQ _ _ _ isWeightBound_idealImpl hq _)
    have h2 := count_le_of_isWeightBound (isWeightBound_of_toK e h1) ∅
    intro r hr
    rw [romExperiment, StateT.run'_eq] at hr
    erw [support_map] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    exact h2 z hz

/-- A call of `H`, `π` or `π⁻¹` makes at least one permutation call. -/
theorem oracleCallsB_le_permCallsB (t : KSpecB.Domain) : oracleCallsB t ≤ permCallsB t := by
  rcases t with n | m | q <;> simp [oracleCallsB, permCallsB]

/-! ## The RPM game with the hash oracle, on lanes

The game (`rpmGameH`) queries `π` and `π⁻¹` on lane states; read on byte states
(`Common.relabel`) it is the game above against the adversary with its permutation queries read
on bytes (`rpmGame_relabel`), with the same distribution (`Common.runK_relabel`) and the same
calls (`Common.isWeightBound_relabel'`). -/

/-- Calls of `H`, `π` and `π⁻¹`, one each. -/
def oracleCalls : KSpecH.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The adversary's oracles read on byte states: its permutation queries through `relabel`,
its signing requests as they are. -/
def relabelS : QueryImpl (KSpecH + (Req →ₒ Resp)) (OracleComp (KSpecB + (Req →ₒ Resp)))
  | .inl t => simulateQ (fun u ↦ liftM ((KSpecB + (Req →ₒ Resp)).query (.inl u)) :
      QueryImpl KSpecB (OracleComp (KSpecB + (Req →ₒ Resp)))) (relabel t)
  | .inr r => liftM ((KSpecB + (Req →ₒ Resp)).query (.inr r))

/-- **A writer layer through a simulation**: simulating a writer's run with `h` is running the
writer `f₂` on the computation simulated with `g`, when it is so query by query. -/
theorem simulateQ_writer_run_comm {ι ι₁ ι₂ ι₃ : Type} {spec : OracleSpec ι}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃} {L α : Type}
    [EmptyCollection L] [Append L] [LawfulAppend L]
    (f₁ : QueryImpl spec (WriterT L (OracleComp spec₁))) (h : QueryImpl spec₁ (OracleComp spec₂))
    (g : QueryImpl spec (OracleComp spec₃)) (f₂ : QueryImpl spec₃ (WriterT L (OracleComp spec₂)))
    (hstep : ∀ t, simulateQ h ((f₁ t).run) = (simulateQ f₂ (g t)).run) (oa : OracleComp spec α) :
    simulateQ h ((simulateQ f₁ oa).run) = (simulateQ f₂ (simulateQ g oa)).run := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind', simulateQ_map, hstep, ih]

/-- The hash of the game with the hash oracle, read on byte states. -/
theorem simulateQ_relabel_hashK {β : Type} (X : OracleComp (SchemeHashSpec) β) :
    simulateQ relabel (simulateQ (hashKH) X) = simulateQ (hashKB digestBytesEquivBitVec) X := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

/-- **The RPM game with the hash oracle, read on byte states, is the game on byte states**,
against the adversary with its permutation queries read on bytes. -/
theorem rpmGame_relabel (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecH + (Req →ₒ Resp)) F) :
    simulateQ relabel (rpmGameH S main) =
      rpmGameB digestBytesEquivBitVec S fun pk ↦ simulateQ relabelS (main pk) := by
  have hmid : ∀ (sk : SK) {α : Type} (oa : OracleComp (KSpecH + (Req →ₒ Resp)) α),
      simulateQ relabel ((simulateQ (QueryImpl.ofLift KSpecH
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) + signingOracleKH S sk) oa).run) =
      (simulateQ (QueryImpl.ofLift KSpecB
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) + signingOracleKB
            digestBytesEquivBitVec S sk)
          (simulateQ relabelS oa)).run := by
    intro sk α oa
    refine simulateQ_writer_run_comm _ _ _ _ (fun t ↦ ?_) oa
    rcases t with t | r
    · have h2 : ((QueryImpl.ofLift KSpecH (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) +
          signingOracleKH S sk) (.inl t)).run =
            (·, ∅) <$> (liftM (KSpecH.query t) : OracleComp KSpecH _) := rfl
      have h5 : (QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) +
          signingOracleKB digestBytesEquivBitVec S sk) ∘ₛ (fun u ↦ liftM ((KSpecB + (Req →ₒ Resp)).query (.inl u)) :
            QueryImpl KSpecB (OracleComp (KSpecB + (Req →ₒ Resp)))) =
          QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) := by
        funext u
        simp only [QueryImpl.apply_compose, simulateQ_spec_query]
        rfl
      rw [h2, simulateQ_map, simulateQ_spec_query, relabelS, ← QueryImpl.simulateQ_compose, h5,
        run_simulateQ_ofLift_writer]
      rfl
    · have h3 : ((QueryImpl.ofLift KSpecH (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) +
          signingOracleKH S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
            simulateQ (hashKH) (S.sign sk r) := by
        simp [signingOracleKH]
      have h3' : ((QueryImpl.ofLift KSpecB (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecB)) +
          signingOracleKB digestBytesEquivBitVec S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
            simulateQ (hashKB digestBytesEquivBitVec) (S.sign sk r) := by
        simp [signingOracleKB]
      rw [h3, simulateQ_map, simulateQ_relabel_hashK, relabelS, simulateQ_spec_query, h3']
  simp only [rpmGameH, rpmGameB, simulateQ_bind, simulateQ_pure, simulateQ_relabel_hashK, hmid]
  rw [simulateQ_liftM_of_coins _ (fun n ↦ rfl)]

/-- The RPM experiment with the hash oracle is the experiment on byte states, in distribution. -/
theorem rpmExperiment_relabel (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (KSpecH + (Req →ₒ Resp)) F) :
    rpmExperimentH S main =ᵈ rpmExperimentB digestBytesEquivBitVec S fun pk ↦ simulateQ relabelS (main pk) := by
  rw [rpmExperimentH, rpmExperimentB, ← rpmGame_relabel]
  exact runK_relabel _

end Common.SufCma
