/-
  Rv64mc.Final.LeanVm

  How `Sound` composes with the knowledge-soundness theorem, which is about `leanVmVerifier π program input`
  (`Statement/LeanVm.lean`), defined as `verifyWith π (bytecodeWords program) (publicInputDigest input)`. `Sound`
  speaks of `verifyWith keccakF1600 bytecode publicInput` for the decoded words instead. The public input is no gap:
  every digest is `publicInputDigest` of an input (`publicInputDigest_ofDigest`). The bytecode is: `Sound` does not
  say that the accepted words are `bytecodeWords program` for some `program`. The guest checks more than the
  statement here (`Bytecode::new` rejects words failing `is_valid_encoding_of_a_leanisa_program`,
  `crates/verifier/src/bytecode.rs`), but nothing yet proves that the words that check accepts are exactly the
  image of `bytecodeWords`; `Model/Bytecode.lean` mirrors the check without that lemma. `sound_leanVm` is the
  composition, with the program a hypothesis. It is stated with `verifyWith`, which `leanVmVerifier (m := Id)
  keccakF1600 program input proof` is by definition, so that this module need not build `Statement/LeanVm.lean`'s
  probabilistic imports.
-/

import Rv64mc.Bridge

namespace Rv64mc

open RiscvZkvm.Rv64 LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier

/-- Every digest is the digest of a public input. -/
theorem publicInputDigest_ofDigest (d : Digest) : publicInputDigest (PublicInput.ofDigest d) = d := by
  apply Vector.ext
  intro i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- **`Sound`, composed with the knowledge-soundness theorem's verifier**: an accepting run read a proof that
    `leanVmVerifier keccakF1600 program input` accepts, for the input its public words encode and any program whose
    bytecode is the words it read. -/
theorem sound_leanVm {img : Image} (h : Sound img) {words : List Word} {s : MachineState} {n : Nat}
    (hl : Loaded img words s) (hh : Halts s n 0) :
    ∃ bytecode publicInput proof, decodeInput words = some (bytecode, publicInput, proof) ∧
      ∀ program : LeanIsaProgram, bytecodeWords program = bytecode →
        Id.run (verifyWith (m := Id) keccakF1600 (bytecodeWords program)
          (publicInputDigest (PublicInput.ofDigest publicInput)) proof) = true := by
  obtain ⟨bc, pi, proof, hd, hv⟩ := h words s n hl hh
  exact ⟨bc, pi, proof, hd, fun program hp => by rw [hp, publicInputDigest_ofDigest]; exact hv⟩

end Rv64mc
