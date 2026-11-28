/-
  LeanVM.Wire.Honest

  The honest prover's proofs survive their encoding: `WireDecodable` with the hash they were
  proved with, so the round trip (`LeanVM.Wire.roundTrip`) applies to them.
-/

module

public import LeanVM.Wire.HonestScript
import LeanVM.Protocol.WithHashBridge

/-!
# The honest prover's proofs are decodable

`Prover.proveWithHash` runs the honest script (`honestScript`) against the verifier's own program
(`leanVmVerifierProgram`) from the seed, from no commitment (`runScriptWithHash`). Its proof is
`WireDecodable` (`runFrom_wire`) as soon as the program's openings and stream are within the wire
bounds (`Wired`, from no commitment with `wireMaxPhases` openings and fewer than `2^32` stream
elements) and the script's committed words are well shaped (`WordsOK`):
`proveWithHash_wireDecodable_of`. Both hold: `wired_leanVmProgram` (`LeanVM.Wire.HonestShape`, at
most `leanVmStream` stream elements) and `wordsOK_honestScript` (`LeanVM.Wire.HonestScript`). So:

* `proveWithHash_wireDecodable`: a proof of `Prover.proveWithHash (m := Id) h F` is
  `WireDecodable h`;
* `prove_wireDecodable`: a proof of the statement's honest prover `Prover.prove (m := Id) F` is
  `WireDecodable` with Keccak-256 over `F`.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover (Witness honestScript runScriptWithHash)

/-- **The honest prover's proofs are decodable**, given the program's and the script's shapes: a
proof of `Prover.proveWithHash (m := Id) h F` is `WireDecodable h` when every verifier program
`leanVmVerifierProgram` is `Wired` from no commitment with `wireMaxPhases` openings and `C < 2^32`
stream elements, and every honest script's committed words are well shaped. -/
theorem proveWithHash_wireDecodable_of {C : ℕ} (hC : C < 2 ^ 32)
    (hW : ∀ bytecode publicInput, Wired (leanVmVerifierProgram bytecode publicInput) []
      wireMaxPhases C fun _ _ _ ↦ True)
    (hS : ∀ (W : Witness) (ρ : ℕ) (publicInput : Digest), WordsOK (honestScript W ρ publicInput))
    {h : Bytes → Digest} {F : KeccakState → KeccakState} {prog : LeanIsaProgram}
    {input : PublicInput} {t : Execution prog} {ρ fuel : ℕ} {p : Proof}
    (hp : Prover.proveWithHash (m := Id) h F prog input t ρ fuel = some p) :
    WireDecodable h p := by
  unfold Prover.proveWithHash at hp
  split at hp
  · cases hp
  · next W _ =>
    split at hp
    · simp only [runScriptWithHash, bind, pure] at hp
      rw [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs, os⟩, hr, rfl⟩ := hp
      obtain ⟨hxs, hos, hph⟩ := runFrom_wire h F fuel _ (some (honestScript W ρ _)) _ []
        wireMaxPhases C (fun _ h ↦ by cases h) (hW _ _) (hS W ρ _) hr
      exact ⟨by simp only; omega, hos, hph⟩
    · cases hp

/-- **The honest prover's proofs are decodable** with the hash they were proved with. -/
theorem proveWithHash_wireDecodable {h : Bytes → Digest} {F : KeccakState → KeccakState}
    {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ fuel : ℕ} {p : Proof}
    (hp : Prover.proveWithHash (m := Id) h F prog input t ρ fuel = some p) : WireDecodable h p :=
  proveWithHash_wireDecodable_of leanVmStream_lt wired_leanVmProgram wordsOK_honestScript hp

/-- **The statement's honest prover's proofs are decodable**, with Keccak-256 over the
permutation they were proved with. -/
theorem prove_wireDecodable {F : KeccakState → KeccakState} {prog : LeanIsaProgram}
    {input : PublicInput} {t : Execution prog} {ρ fuel : ℕ} {p : Proof}
    (hp : Prover.prove (m := Id) F prog input t ρ fuel = some p) :
    WireDecodable (keccak256With (m := Id) F) p := by
  rw [Prover.prove_eq_withHash] at hp
  exact proveWithHash_wireDecodable hp

end LeanVM.Wire

end
