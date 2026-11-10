import LeanVM.Protocol.Verifier
import LeanVM.Protocol.WithHashBridge

/-!
# The compiled verifier: the Fiat-Shamir sponge against the pinned one's, and garbage rejected

`verify` is the compiled reading of `leanVmVerifierProgram` with Keccak-256 and Keccak-f[1600]. The
honest proofs are the fixtures `tests/fixtures/verifier/*` (accepted by the compiled verifier
`leanvm-verify`, `scripts/fuzz-verifier.py`); this file checks the compiled reading where the
pinned verifier can be run without a proof, on the scalar stream `stream rate n`: the eight announced
sizes (memory `2^16`, the row counts `4, 2, 2, 4, 4, 8`, the rate exponent), two root halves, then
`n` scalars `fe(10 + k)`.

* The seed and the sponge: the first two steps of the program (`readAnnouncedSizes`, `commitStack`)
  and five challenges, in the compiled reading, give the challenges and the sponge state the
  verifier's `Transcript` gives on the same stream after `next_scalars(8)`, `Digest::from_halves`
  of `next_scalars(2)` and `samples(5)` (the verifier at leanVM's `f128` branch, `98ceacf2c`, a
  driver of the port's scratch). This binds the IV's preimage (the version tag, then the
  bytecode), the seed permutation of the IV and the public input, the duplex absorbs with their
  domain tags, the squeezes, the order of the reads, and the stack root's shape.
* Garbage proofs run to a rejection: the empty proof and the stream cut after the root (the
  verifier: `proof stream exhausted`), a hundred scalars after it (the verifier: `invalid grinding
  nonce`, the stack's out-of-domain grind), and a rate exponent of `5` (`invalid PCS inverse
  rate`).
-/

namespace LeanVMTests.Protocol.Verifier.Compiled

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its two limbs. -/
def e (c0 c1 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1)

/-- The driver's `fe(k)`. -/
def fe (i : ℕ) : E := e (fw i 0) (fw i 1)

/-- The bytecode: 32 words. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The public input: the 32 bytes `fw(i, 10) mod 256`. -/
def samplePublicInput : Digest :=
  digestOfBytes ((List.range 32).map fun i ↦ (fw i 10 % 256).toUInt8)

/-- The sample row counts: `xor, mul, set, deref, jump, keccak`. -/
def sampleRows : List ℕ := [4, 2, 2, 4, 4, 8]

/-- The sizes, the root halves, then `n` scalars. -/
def stream (rate n : ℕ) : List E :=
  [eOfNat 16] ++ sampleRows.map eOfNat ++ [eOfNat rate] ++
    [e (fw 8 0) (fw 8 1), e (fw 9 0) (fw 9 1)] ++ (List.range n).map fun k ↦ fe (10 + k)

/-- The first two steps of the program, then five challenges. -/
def prefixProgram : VerifierProgram (List E) := do
  let (layout, rate) ← readAnnouncedSizes sampleBytecode
  commitStack layout.stackLog rate
  VerifierProgram.sampleChallenges 5

/-- The compiled reading of `prefixProgram` on a stream, from the deployed seed. -/
def prefixRun (s : List E) : Option (List E × VerifierProgramState) :=
  Id.run (Compile.run (m := Id) keccakF1600 prefixProgram
    ⟨⟨seed sampleBytecode samplePublicInput, [], none⟩, s, [], []⟩)

/-! ## The sponge agrees with the pinned verifier's -/

#guard ((prefixRun (stream 4 0)).map (·.1)) =
    some [(e 0x76cab5c46908a6e3 0x9f181ecbe76275b1), (e 0xf9194a2a1e2d0d6c 0x7bbc1deff5f4dc6d),
     (e 0xfb6dc5c12b3900be 0xb2092b8150b236f5), (e 0x73259fba69ae5358 0x11bfca90fb00349b),
     (e 0x9b3200d078d47019 0x62b965389bbb4e49)]

#guard ((prefixRun (stream 4 0)).map fun r ↦ (r.2.sponge.state.toList, r.2.sponge.pending.length)) =
    some ([0x9b3200d078d47019, 0x62b965389bbb4e49, 0xf57085b9e4651c61, 0xb1484e8bde27e39d,
      0x44efeab650789cde, 0x4e27247d2d610549, 0xd92c47fef3c79ed, 0xc9d261e57715fe8b,
      0x42ee445bb8e2f3a6, 0xf3fa10fa300924da, 0xb0b97f2d3e92fdb4, 0xf7639b34004e4baf,
      0xf3859d8e9a8fe3db, 0x34f02e7a301daeee, 0x80ee193a1c62fd5, 0x515009f201dd757c,
      0xe622fa19cca68986, 0xf79fd1193220fca4, 0x7e46e300dc243e6c, 0x8acc56faa906dbee,
      0xb7008d591670d327, 0x6130e0da364e4521, 0x31b93326d2b0ddcc, 0x8d2b0d0b07870a40,
      0xbfc73c4740cd253e], 0)

/- The stack root is commitment `0`, of `2^(18 - 6 + 4)` leaves of `2^6` words. -/
#guard ((prefixRun (stream 4 0)).map fun r ↦ r.2.roots.map fun c ↦ (c.2.1, c.2.2)) =
    some [(16, 64)]

/-! ## Garbage is rejected -/

#guard verify sampleBytecode samplePublicInput ⟨[], []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 4 0, []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 4 100, []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 5 100, []⟩ = false

/-- The deployed verifier is the one over a permutation, at `Id` and Keccak-f[1600]. -/
example (π : Proof) :
    Id.run (verifyWith (m := Id) keccakF1600 sampleBytecode samplePublicInput π) =
      verify sampleBytecode samplePublicInput π := by
  rw [verifyWith_eq_withHash, keccak256With_keccakF1600]
  rfl

end LeanVMTests.Protocol.Verifier.Compiled
