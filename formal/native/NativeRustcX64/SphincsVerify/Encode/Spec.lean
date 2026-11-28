module

public import NativeRustcX64.SphincsVerify.Encode.Sum

/-!
# Region 5a: a layer's encoding

From layer `l`'s state at `b104` with message `s` (`AtLayer l s`): the key and the encoder's
address (`b104_spec`), the encoder's digest (`hash_spec`), its 64 digits (`loop_run`), their sum
and the codeword's copy (`sum_spec`). The machine returns 0 where `encode` gives no codeword,
else reaches the chains at `b117` with the codeword (`encode_spec : EncodeSpec`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym

public section

/-- **Region 5a, a layer's encoding** (`EncodeSpec`): from `b104` with layer `l`'s state, the
machine returns 0 if `encode` gives no codeword, else reaches `b117` with the codeword at
`3080`. -/
theorem encode_spec [Host] : EncodeSpec := by
  intro l s r hp hc hpre m h
  have hl : l < 3 := h.1
  refine Eventually.bind (b104_spec r hp hc hpre h) fun st1 ⟨hpc1, hB1, hA1, hH1⟩ ↦
    goto hpc1 ?_
  refine Eventually.bind (hash_spec r hp hc hpre hB1 hA1 hH1)
    fun st2 ⟨hpc2, ⟨c', hB2⟩, hV, h7, h6⟩ ↦ goto hpc2 ?_
  generalize hVdef : beNat (encodeDigest r.seed (r.key l) s (r.layerSig l).counter) = V at hV
  refine Eventually.bind (loop_run r hp hpre V 31 0 rfl st2.data hB2.2.2.1 h7 h6 hV
    fun t ht ↦ absurd ht (by omega)) fun st3 ⟨hpc3, hF3, hS3, hout3, hd3⟩ ↦ goto hpc3 ?_
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hout3
  obtain ⟨-, hs, -, hD⟩ := hB2
  have hD3 : r.EncData l s c' st3.data :=
    r.encData_of_bytes hD hs
      (fun hp' hb ↦ bytesAt_of_sameOutside hb hout3 fun i hi ↦ by
        rw [Run.off_add]
        unfold Run.EncPlace at hp'
        exact r.not_inRange_off hpre (by omega) (by omega) (by omega))
      fun x hx ↦ hS3.1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine Eventually.mono (sum_spec r hp hpre hl hF3 hD3.1 hD3.2.1
    (Run.EncData.memcpy r hD3) hd3) fun st h' ↦ ?_
  show (encode r.seed (r.key l) s (r.layerSig l).counter = none ∧ r.Done false st) ∨
    ∃ x, encode r.seed (r.key l) s (r.layerSig l).counter = some x ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b117Offset ∧
      r.AtChains l x st.data
  rw [encode_eq]
  simp only [hVdef]
  rcases h' with ⟨hne, hd⟩ | ⟨heq, hpc, hch⟩
  · exact .inl ⟨by rw [Sym.ite_neg hne], hd⟩
  · exact .inr ⟨digits V, by rw [Sym.ite_pos heq], hpc, hch⟩

end

end NativeRustcX64.SphincsVerifyProof
