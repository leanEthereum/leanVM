import LeanVM.Protocol.Verifier

/-!
# The compiled verifier: the Fiat-Shamir chain against the Python's, and garbage rejected

`verify` is the compiled reading of `leanVmProgram` with BLAKE2s. There is no honest proof to run
it on (no prover fixture at the pin is available here), so this file checks the compiled reading
where the Python can be run without one, on the scalar stream `stream rate n`: the eight
announced sizes (memory `2^16`, the sample heights, the rate exponent), two canonical root
halves, then `n` scalars `fe(10 + k)`.

* The seed and the chain: the first two steps of the program (`readSizes`, `commitStack`) and
  five challenges, in the compiled reading, give the challenges and the chain state the Python's
  `Transcript` gives on the same stream after `next_scalars(8)`, `from_halves(next_scalars(2))`
  and `samples(5)` (`python-verifier/verifier.py` at leanVM
  `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, run with CPython's `hashlib`). This binds the IV
  preimage, `compress(IV, public_input)`, the absorb and squeeze blocks, the order of the reads,
  and the stack root's shape.
* A non-canonical root half is rejected, as `Digest.from_halves` rejects it.
* Garbage proofs run to a rejection: the empty proof and the stream cut after the root (the
  Python: `proof stream exhausted`), a hundred scalars after it (the Python: `GKR layer 17:
  children do not match the sumcheck`), and a rate exponent of `5` (`invalid PCS inverse rate`).
-/

namespace LeanVMTests.Protocol.Verifier.Compiled

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash

/-- The driver's 64-bit word generator. -/
def fw (k lane : ℕ) : ℕ :=
  ((k + 1) * 0x9E3779B97F4A7C15 + lane * 0xD1B54A32D192ED03 + 0x632BE59BD9B4E019) % 2 ^ 64

/-- An `E` element from its three limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- The driver's `fe(k)`. -/
def fe (i : ℕ) : E := e (fw i 0) (fw i 1) (fw i 2)

/-- The bytecode: 32 words. -/
def sampleBytecode : List K := (List.range 32).map fun i ↦ K.ofBits (fw i 9)

/-- The public input: the 32 bytes `fw(i, 10) mod 256`. -/
def samplePublicInput : Digest :=
  let b := fun i ↦ (fw i 10 % 256).toUInt8
  Vector.ofFn fun j : Fin 8 ↦ leWord (b (4 * j)) (b (4 * j + 1)) (b (4 * j + 2)) (b (4 * j + 3))

/-- The sample heights: `xor, mul, set, deref, jump, blake2s`. -/
def sampleHeights : List ℕ := [2, 1, 1, 2, 2, 3]

/-- The sizes, the root halves (`top` the root's second half's top limb), then `n` scalars. -/
def stream (rate n : ℕ) (top : ℕ := 0) : List E :=
  [eOfNat 16] ++ sampleHeights.map eOfNat ++ [eOfNat rate] ++
    [e (fw 8 0) (fw 8 1) 0, e (fw 9 0) (fw 9 1) top] ++ (List.range n).map fun k ↦ fe (10 + k)

/-- The first two steps of the program, then five challenges. -/
def prefixProgram : Prog (List E) := do
  let (layout, rate) ← readSizes sampleBytecode
  commitStack layout.stackLog rate
  Prog.sampleN 5

/-- The compiled reading of `prefixProgram` on a stream, from the deployed seed. -/
def prefixRun (s : List E) : Option (List E × St) :=
  Id.run (Compile.run blake2sBytes prefixProgram ⟨seed sampleBytecode samplePublicInput, s, [], []⟩)

/-! ## The chain agrees with the Python's -/

#guard ((prefixRun (stream 4 0)).map (·.1)) =
    some [(e 0x49c3f8d1720dff9b 0x382aa5d71af750da 0xc57ac64729d3e017),
     (e 0xa4b3b2a6b883ed1b 0xea41a6d30e4fa3eb 0x110eb885b1dcb1e9),
     (e 0x432df42014671f6f 0x1ede886b2aa71166 0x98505ae017cd1060),
     (e 0xa123eedde292fe6d 0xa8bc1aca282ada7a 0xc31658a81e7b803c),
     (e 0x927f9c92a81872da 0x1c102d2f788e221a 0x11c427e299119a45)]

#guard ((prefixRun (stream 4 0)).map (·.2.cv.toList)) =
    some [0xa81872da, 0x927f9c92, 0x788e221a, 0x1c102d2f, 0x99119a45, 0x11c427e2, 0x8a023397,
     0xa7ad156f]

/- The stack root is commitment `0`, of `2^(19 - 6 + 4)` leaves of `2^6` words. -/
#guard ((prefixRun (stream 4 0)).map fun r ↦ r.2.roots.map fun c ↦ (c.2.1, c.2.2)) =
    some [(17, 64)]

/- A root half with a nonzero top limb. -/
#guard (prefixRun (stream 4 0 1)).isNone

/-! ## Garbage is rejected -/

#guard verify sampleBytecode samplePublicInput ⟨[], []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 4 0, []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 4 100, []⟩ = false
#guard verify sampleBytecode samplePublicInput ⟨stream 5 100, []⟩ = false

/-- The deployed verifier is the hash-parametric one at `Id` and BLAKE2s. -/
example (π : Proof) :
    Id.run (verifyWith blake2sBytes sampleBytecode samplePublicInput π) =
      verify sampleBytecode samplePublicInput π :=
  verifyWith_blake2sBytes _ _ _

end LeanVMTests.Protocol.Verifier.Compiled
