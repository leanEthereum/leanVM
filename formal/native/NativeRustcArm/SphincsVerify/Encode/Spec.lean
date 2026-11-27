module

public import NativeRustcArm.SphincsVerify.Encode.Sum

/-!
# Region 5a: a layer's encoding

From layer `l`'s state at `b92` with message `s` (`AtLayer l s`): the key and the encoder's
address (`b92_spec`), the encoder's digest (`hash_spec`), its 64 digits (`loop_run`), their sum
and the codeword's copy (`sum_spec`). The machine returns 0 where `encode` gives no codeword,
else reaches the chains at `b105` with the codeword (`encode_spec : EncodeSpec`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

public section

/-- **Region 5a, a layer's encoding** (`EncodeSpec`): from `b92` with layer `l`'s state, the
machine returns 0 if `encode` gives no codeword, else reaches `b105` with the codeword at
`15936`. -/
theorem encode_spec [ElfHost] : EncodeSpec := by
  intro l s r hp hc hpre m h
  have hl : l < 3 := h.1
  refine Eventually.bind_elf (b92_spec r hp hc hpre h) fun st1 ⟨hpc1, hB1, hA1, hH1⟩ ↦
    goto hpc1 ?_
  refine Eventually.bind_elf (hash_spec r hp hc hpre hB1 hA1 hH1) fun st2 ⟨hpc2, hB2, hV, h8, h11⟩ ↦
    goto hpc2 ?_
  generalize hVdef : beNat (encodeDigest r.seed (r.key l) s (r.layerSig l).counter) = V at hV
  refine Eventually.bind_elf (loop_run r hp hpre V 15 0 rfl st2.data hB2.2.2.1 h8 h11 hV
    fun t ht ↦ absurd ht (by omega)) fun st3 ⟨hpc3, hF3, hS3, hout3, hd3⟩ ↦ goto hpc3 ?_
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hout3
  have hout3' : SameOutside st2.data.dmem st3.data.dmem (r.CallOut st2.data 19008 64 0) :=
    SameOutside.mono hout3 fun _ hp' ↦ .inl hp'
  have hB3 : r.EncBase l s (r.layerSig l).counter st3.data :=
    r.encBase_of_bytes hB2 hF3
      (fun ho hr hb ↦ r.bytesAt_of_call hpre hB2.2.2.1 (by omega) (Nat.zero_le _) hout3' ho
        (by omega) hb)
      fun x hx ↦ hS3.1 x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  obtain ⟨-, -, -, hI3, hL3, -, h21, -, h25, h19, h27, -, -⟩ := hB3
  refine Eventually.mono_elf (sum_spec r hp hpre hl hF3 hI3 hL3 h19 h21 h25 h27 hd3) fun st h' ↦ ?_
  show (encode r.seed (r.key l) s (r.layerSig l).counter = none ∧ r.Done false st) ∨
    ∃ x, encode r.seed (r.key l) s (r.layerSig l).counter = some x ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b105Offset ∧
      r.AtChains l x st.data
  rw [encode_eq]
  simp only [hVdef]
  rcases h' with ⟨hne, hd⟩ | ⟨heq, hpc, hch⟩
  · exact .inl ⟨by rw [NativeRustcArm.Sym.ite_neg hne], hd⟩
  · exact .inr ⟨digits V, by rw [NativeRustcArm.Sym.ite_pos heq], hpc, hch⟩

end

end NativeRustcArm.SphincsVerifyProof
