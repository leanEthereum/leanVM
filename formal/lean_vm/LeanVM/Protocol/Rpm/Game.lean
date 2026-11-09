/-
  LeanVM.Protocol.Rpm.Game

  The random-permutation experiment of `Statement/LeanVm.lean` as a game of `common`'s
  two-oracle transfer: the honest part before the adversary (nothing), the adversary on byte
  states with its transcript, the verifier with the hash and the direct permutation calls; and
  the random-oracle adversary the transfer gives back, on lane states.
-/

import LeanVM.Protocol.Rpm.Paths
import LeanVM.Facts.Verifier
import LeanVM.Protocol.Verifier.Load
import Statement.Fast.Keccak
import Statement.Fast.CubicExt
import Statement.Fast.FieldWords
import LeanVM.Protocol.Rpm.Coins
import Common.Keccak
import LeanVM.Protocol.WithHash

/-!
# The experiment as a transfer game

`common`'s two-oracle transfer (`Common.keccak256_transfer2`) is stated for games
`rpmGame2 pre A post` on byte states (`Common.KState`), with the hash returning 32 bytes
(`Common.DigestBytes`). Here:

* `relP`, `logRel`, `advR`: the adversary of `Statement/LeanVm.lean`, its queries read on bytes
  (`permQueryToRpm`) and its answers on lanes (`KState.ofRpm`), recording its transcript;
* `toRHF`, `postR`: the verifier, its hash and permutation queries read on bytes;
* `game`: the transfer game (`pre` does nothing);
* `ofRHF`, `romAdv`: the random-oracle adversary of the transfer (`Common.advS2`, the adversary
  with the indifferentiability simulator), its queries read back on lanes, as an adversary with
  coins against the two oracles of `Statement.lean`;
* `cmap`: a cache of the byte oracles read on lanes.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-- The adversary's oracles in `common` (coins, the hash, `π` and `π⁻¹`), on bytes. -/
abbrev RSpec := Common.dSpec Bytes Common.DigestBytes Common.KState

/-- The two random oracles of `common`, on bytes, with coins. -/
abbrev HFSpec := unifSpec + Common.hfSpec Bytes Common.DigestBytes Common.KState

/-- The game's oracles in `common`'s two-oracle model. -/
abbrev D2Spec := Common.dSpec2 Bytes Common.DigestBytes Common.KState

/-- The two random oracles of `common`, on bytes: the hash and the permutation calls. -/
abbrev HFS := Common.hfSpec Bytes Common.DigestBytes Common.KState

/-- The two oracles of `Statement.lean`, with coins. -/
abbrev CSpec := unifSpec + KeccakCalls

/-- A query on lanes, from a query on bytes. -/
def permQueryOfRpm : Common.PermutationQuery Common.KState → Common.PermutationQuery KeccakState
  | .forward x => .forward (KState.ofRpm x)
  | .inverse y => .inverse (KState.ofRpm y)

/-- A permutation query of the adversary, read on bytes. -/
def relP : QueryImpl (Common.permutationOracleSpec KeccakState) (OracleComp RSpec) := fun q ↦
  KState.ofRpm <$> (liftM (RSpec.query (.inr (.inr (permQueryToRpm q)))) :
    OracleComp RSpec Common.KState)

/-- A permutation query of the adversary, read on bytes, recorded in the transcript. -/
def logRel : QueryImpl (Common.permutationOracleSpec KeccakState) (StateT PermutationTranscript (OracleComp RSpec)) := fun q ↦
  StateT.mk fun T ↦ (fun a ↦ (a, T ++ [(q, a)])) <$> relP q

/-- The adversary of the transfer: the adversary on bytes, with its transcript. -/
def advR (A : DetAdversary) : OracleComp RSpec ((ProgramAndInput × Proof) × PermutationTranscript) :=
  (simulateQ logRel A).run []

/-- The two oracles of `Statement.lean`, read on bytes. -/
def toRHF : QueryImpl KeccakCalls (OracleComp HFSpec)
  | .inl m => Digest.ofRpm <$> Common.hQuery (E := Common.KRest) (C := Common.KCap) m
  | .inr s => KState.ofRpm <$> Common.fQuery (Msg := Bytes) (KState.toRpm s)

/-- The verifier on the adversary's statement and proof, its queries read on bytes, with the
adversary's transcript. -/
def postR (z : (ProgramAndInput × Proof) × PermutationTranscript) : OracleComp HFSpec ExperimentOutcomeWithHash :=
  (fun v ↦ ((z.1, v), z.2)) <$> simulateQ toRHF (verifierWithHash callKeccak256 callKeccakF1600 z.1.1.1 z.1.1.2 z.1.2)

/-- **The transfer game** of the random-permutation experiment. -/
def game (A : DetAdversary) : OracleComp D2Spec ExperimentOutcomeWithHash :=
  Common.rpmGame2 (pure ()) (fun _ ↦ advR A) (fun _ z ↦ postR z)

/-- The transfer's oracles read on lanes: coins, the hash (its 32 bytes), the permutation. -/
def ofRHF : QueryImpl HFSpec (OracleComp CSpec)
  | .inl n => liftM (CSpec.query (.inl n))
  | .inr (.inl m) => Digest.toRpm <$> (liftM (CSpec.query (.inr (.inl m))) : OracleComp CSpec Digest)
  | .inr (.inr x) =>
    KState.toRpm <$> (liftM (CSpec.query (.inr (.inr (KState.ofRpm x)))) : OracleComp CSpec KeccakState)

/-- **The random-oracle adversary of the transfer**: the adversary with the indifferentiability
simulator (`Common.advS2`), its oracle queries read on lanes, its transcript dropped. -/
noncomputable def romAdv (A : DetAdversary) : OracleComp CSpec (ProgramAndInput × Proof) :=
  (fun z ↦ z.1) <$> simulateQ ofRHF
    (Common.advS2 Common.keccakPadding Common.KState.zero (advR A))

/-- A cache of the byte oracles, read on lanes. -/
def cmap (c : HFS.QueryCache) :
    KeccakCalls.QueryCache :=
  QueryCache.ofFn fun
    | .inl m => (c (.inl m)).map Digest.ofRpm
    | .inr s => (c (.inr (KState.toRpm s))).map KState.ofRpm

end LeanVM.Rpm
