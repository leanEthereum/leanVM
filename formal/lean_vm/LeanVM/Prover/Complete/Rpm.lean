/-
  LeanVM.Prover.Complete.Rpm

  A winning script's completeness in the random-permutation model, for leanVM's seed: the
  random-oracle bound plus the transfer's.
-/

module

public import LeanVM.Prover.Complete.Rom
public import LeanVM.Protocol.Rpm.Duplex
public import LeanVM.Protocol.Rpm.Embed
public import LeanVM.Protocol.Rpm.RpmRelabel
import LeanVM.Protocol.Rpm.RomRelabel
public import LeanVM.Protocol.Errors

/-!
# The random-permutation model

* `leanVmSeed`: leanVM's seeding (the IV's hash of the tag and the bytecode, then the permutation
  of the IV and the public input), with `seedRun_leanVmSeed` and `verifierComp_leanVm` (restored).
* `duplexP_runFrom`: the run of a script keeps the duplex discipline, its permutation calls each
  from an earlier answer's capacity, its Merkle trees hash calls only (the bus era's
  `duplexP_proveFromM`, with packed messages).
* `rpm_le_of_rom` (restored): a prover then a verifier keeping the discipline and making at most
  `N` permutation calls are rejected in the random-permutation model at most as often as in the
  random-oracle model, plus `rpmError N` (`Common.keccak256_transfer2`).
* `rpmComplete`: so a winning script's proof, from leanVM's seed, is rejected in the
  random-permutation model with probability at most `(QA + QV) · missK B ^ fuel + rpmError N`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Protocol.Verifier LeanVM.Rpm
open OracleComp OracleSpec
open scoped ENNReal

variable {α β : Type}

/-! ## leanVM's seed -/

/-- **The leanVM seeding**: the IV, the hash of the version tag and the bytecode, then the
permutation of the IV and the public input (`spongeSeedWith`). -/
def leanVmSeed (bytecode : List K) (publicInput : Digest) : Seed where
  hs := [fun _ ↦ versionTag ++ bytecode.flatMap K.toBytes]
  fin ds := seedInput (ds.getD 0 default) publicInput

/-- The seeding computes `seedWithHash`, with any hash and permutation in any lawful monad. -/
theorem seedRun_leanVmSeed {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) (bytecode : List K) (publicInput : Digest) :
    (leanVmSeed bytecode publicInput).run H F = seedWithHash H F bytecode publicInput := by
  simp [Seed.run, Seed.hsRun, leanVmSeed, seedWithHash, fiatShamirIvWithHash]

/-- The seeded verifier of the random-oracle theorem at leanVM's seed is the compiled leanVM
verifier with the two calls. -/
theorem verifierComp_leanVm (bytecode : List K) (publicInput : Digest) (π : Proof) :
    verifierComp (leanVmSeed bytecode publicInput) (leanVmVerifierProgram bytecode publicInput) π =
      verifyWithHash callKeccak256 callKeccakF1600 bytecode publicInput π := by
  simp only [verifierComp, Rom.verify, verifyWithHash, seedRun_leanVmSeed]

/-! ## The duplex discipline -/

theorem hOnly_arrayMapM {γ : Type} (f : γ → OracleComp KeccakCalls β) (hf : ∀ c, HOnly (f c))
    (xs : Array γ) : HOnly (xs.mapM f) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp]
  exact (hOnly_mapM f hf _).bind fun _ ↦ trivial

theorem hOnly_parents (level : Array Digest) (n : ℕ) :
    HOnly (parentsWithHash callKeccak256 level n) :=
  hOnly_arrayMapM _ (fun _ ↦ hOnly_queryH _) _

theorem hOnly_levels :
    ∀ (k : ℕ) (level : Array Digest), HOnly (levelsWithHash callKeccak256 k level)
  | 0, _ => trivial
  | k + 1, _ => (hOnly_parents _ _).bind fun _ ↦ (hOnly_levels k _).bind fun _ ↦ trivial

theorem hOnly_buildTree (height : ℕ) (word : Word) :
    HOnly (buildTreeWithHash callKeccak256 height word) :=
  (hOnly_arrayMapM _ (fun _ ↦ hOnly_queryH _) _).bind fun _ ↦
    (hOnly_levels _ _).bind fun _ ↦ trivial

/-- The nonce search keeps the discipline, and the sponge it searches at. -/
theorem duplexP_searchM (bits : ℕ) (o : Bool) {h : List KeccakState} {sp : Sponge}
    (hs : sp.state ∈ h) :
    ∀ (count n : ℕ), DuplexP (searchM callKeccakF1600 bits o sp n count) h fun _ h' ↦ sp.state ∈ h'
  | 0, _ => hs
  | count + 1, n => by
    simp only [searchM]
    refine (duplexP_absorbNonce hs _).grow.bind fun r h' hr ↦ ?_
    split
    · exact hr.2 hs
    · exact duplexP_searchM bits o (hr.2 hs) count (n + 1)

theorem duplexP_findNonceM (bits : ℕ) (o : Bool) {h : List KeccakState} {sp : Sponge}
    (hs : sp.state ∈ h) (fuel : ℕ) :
    DuplexP (findNonceM callKeccakF1600 bits o sp fuel) h fun _ h' ↦ sp.state ∈ h' := by
  simp only [findNonceM]
  exact duplexP_searchM bits o hs _ _

/-- **The run of a script keeps the discipline**, from a sponge whose state is an earlier
answer. -/
theorem duplexP_runFrom (fuel : ℕ) (P : VerifierProgram α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List Tree) (h : List KeccakState),
      sp.state ∈ h →
      DuplexP (runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs) h fun _ _ ↦ True := by
  induction P with
  | ret a => intro S sp cs h _; trivial
  | fail => intro S sp cs h _; trivial
  | read k ih =>
    intro S sp cs h hs
    simp only [runFromWithHash]
    exact (duplexP_absorb hs _ _).bind fun sp' h' hsp ↦
      (ih _ _ _ _ _ hsp).bind fun _ _ _ ↦ trivial
  | sample k ih =>
    intro S sp cs h hs
    simp only [runFromWithHash]
    exact (duplexP_squeeze hs).bind fun r h' hr ↦ ih _ _ _ _ _ hr
  | readPacked n k ih =>
    intro S sp cs h hs
    simp only [runFromWithHash]
    exact (duplexP_observePacked hs _).bind fun sp' h' hsp ↦
      (ih _ _ _ _ _ hsp).bind fun _ _ _ ↦ trivial
  | samplePacked n k ih =>
    intro S sp cs h hs
    simp only [runFromWithHash]
    exact (duplexP_samplesPacked hs _).bind fun r h' hr ↦ ih _ _ _ _ _ hr
  | grind bits k ih =>
    intro S sp cs h hs
    simp only [runFromWithHash]
    refine (duplexP_findNonceM bits _ hs fuel).bind fun r h' hr ↦ ?_
    split
    · trivial
    · exact (duplexP_absorbNonce hr _).bind fun r' h'' hr' ↦
        (ih _ _ _ _ hr').bind fun _ _ _ ↦ trivial
  | commit height width k ih =>
    intro S sp cs h hs
    simp only [runFromWithHash]
    refine ((hOnly_buildTree _ _).duplexP h).bind fun tree h' hh ↦ ?_
    subst hh
    exact (duplexP_absorb hs _ _).bind fun sp0 h0 hs0 ↦ (duplexP_absorb hs0 _ _).bind
      fun sp1 h1 hs1 ↦ (ih _ _ _ _ hs1).bind fun _ _ _ ↦ trivial
  | query i ps k ih =>
    intro S sp cs h hs
    simp only [runFromWithHash]
    split
    · trivial
    · exact (ih _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-- **The honest prover from leanVM's seed keeps the discipline.** -/
theorem duplexVm_honestComp (bytecode : List K) (publicInput : Digest) (P : VerifierProgram Bool)
    (S : Script β) (fuel : ℕ) :
    DuplexVm (honestComp (leanVmSeed bytecode publicInput) P S fuel) [] := by
  rw [duplexVm_iff_duplexP]
  simp only [honestComp, seedRun_leanVmSeed, runScriptWithHash, bind_assoc]
  exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦
    (duplexP_runFrom _ _ _ _ _ _ hs).bind fun _ _ _ ↦ trivial

/-! ## From the random-oracle model -/

/-- The verdict of a prover then a verifier against the random oracles is the random-oracle
experiment's. -/
theorem run'_bind_eq (X : OracleComp KeccakCalls Proof) (V : Proof → OracleComp KeccakCalls Bool) :
    (simulateQ KeccakCalls.randomOracle (X >>= V)).run' ∅ =
      (fun z ↦ z.1.2) <$> romExperiment X V := by
  simp only [romExperiment, simulateQ_map, StateT.run_map, map_bind, simulateQ_bind,
    StateT.run'_eq, StateT.run_bind]
  refine bind_congr fun p ↦ ?_
  simp

/-- **From the random-oracle model to the random-permutation model**, for a prover then a
verifier: if they follow the duplex discipline and make at most `N` permutation calls, the
rejection probability in the random-permutation model is at most the random-oracle experiment's
plus `rpmError N` (`Common.keccak256_transfer2`). -/
theorem rpm_le_of_rom (X : OracleComp KeccakCalls Proof) (V : Proof → OracleComp KeccakCalls Bool)
    {N : ℕ} (hd : DuplexVm (X >>= V) []) (hN : Common.QueryCostAtMost (X >>= V) hashBlocks N)
    {ε : ℝ≥0∞} (hrom : Pr{let z ← romExperiment X V}[z.1.2 = false] ≤ ε) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation (X >>= V)).run' []}[v = false] ≤
      ε + rpmError N := by
  have hG : Common.QueryCostAtMost (honestGame (X >>= V)) gameCost N := by
    rw [honestGame, Common.rpmGame2, simulateQ_pure, pure_bind, simulateQ_pure, pure_bind]
    exact isWeightBound_hfEmbed_toRHF hN
  rw [(rpmHonest_evalDistEq _).prEvent_eq, honestGame]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ (pure () : OracleComp RSpec Unit))
    (fun _ _ ↦ simulateQ toRHF (X >>= V)) (fun _ _ ↦ duplex_toRHF _ [] hd) N hG (· = false)
  refine h1.trans (add_le_add (le_of_eq_of_le ?_ hrom) le_rfl)
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero
        ((fun _ ↦ (pure () : OracleComp RSpec Unit)) x) >>= fun a ↦
          (fun _ _ ↦ simulateQ toRHF (X >>= V)) x a) =
      (simulateQ HFS.romImpl (simulateQ toRHF (X >>= V))).run' ∅ := by
    simp [Common.romRun2, Common.advS2]
  rw [e1, (run'_toRHF _ _).prEvent_eq, cmap_empty, run'_bind_eq, prEvent_map]

/-- **A winning script in the random-permutation model.** From leanVM's seed, a script that wins
leanVM's verifier program with `true`, its proofs of work of at most `B ≤ 64` bits, at a fuel of
`1` to `2^64` nonces: with `QA`, `QV` the prover's and the verifier's queries and `N` their
permutation calls (`hashBlocks`), the verifier rejects the honest proof with probability at most
`(QA + QV) · missK B ^ fuel + rpmError N`. -/
theorem rpmComplete (bytecode : List K) (publicInput : Digest) (S : Script β)
    {B fuel QA QV N : ℕ} (hb : B ≤ 64) (hfuel : fuel ≤ 2 ^ 64) (hfuel0 : fuel ≠ 0)
    (hw : Wins B (fun a _ _ _ ↦ a = true) (leanVmVerifierProgram bytecode publicInput) S false [])
    (hA : IsTotalQueryBound (honestComp (leanVmSeed bytecode publicInput)
      (leanVmVerifierProgram bytecode publicInput) S fuel) QA)
    (hV : ∀ π, IsTotalQueryBound (verifierComp (leanVmSeed bytecode publicInput)
      (leanVmVerifierProgram bytecode publicInput) π) QV)
    (hN : Common.QueryCostAtMost (honestComp (leanVmSeed bytecode publicInput)
      (leanVmVerifierProgram bytecode publicInput) S fuel >>= fun π ↦
        verifyWithHash callKeccak256 callKeccakF1600 bytecode publicInput π) hashBlocks N) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation
        (honestComp (leanVmSeed bytecode publicInput) (leanVmVerifierProgram bytecode publicInput)
          S fuel >>= fun π ↦ verifyWithHash callKeccak256 callKeccakF1600 bytecode publicInput π)).run'
          []}[v = false] ≤
      ((QA + QV : ℕ) : ℝ≥0∞) * missK B ^ fuel + rpmError N := by
  have hd : DuplexVm (honestComp (leanVmSeed bytecode publicInput)
      (leanVmVerifierProgram bytecode publicInput) S fuel >>= fun π ↦
        verifyWithHash callKeccak256 callKeccakF1600 bytecode publicInput π) [] := by
    refine (duplexVm_honestComp bytecode publicInput _ S fuel).bind fun π ↦ ?_
    rw [duplexVm_iff_duplexP]
    simp only [verifyWithHash]
    exact (duplexP_seedWith _ _ []).bind fun seed h' hs ↦ duplexP_runProof _ hs _
  refine rpm_le_of_rom _ _ hd hN ?_
  have hV' : (fun π ↦ verifyWithHash callKeccak256 callKeccakF1600 bytecode publicInput π) =
      verifierComp (leanVmSeed bytecode publicInput) (leanVmVerifierProgram bytecode publicInput) :=
    funext fun π ↦ (verifierComp_leanVm _ _ π).symm
  rw [hV']
  exact romComplete _ S _ hb hfuel hfuel0 hw hA hV

end LeanVM.Prover

end
