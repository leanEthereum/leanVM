import Rv64Verifier.Proofs.Hash.KeccakHash
import Rv64Verifier.Proofs.Runtime.All

/-!
# The Keccak functions, composed

`memcpy`'s and `memset`'s contracts as `Contracts.lean` states them, from the runtime's
(`Runtime/All.lean`): the same preconditions, and frames on doublewords from the runtime's frames
on bytes. Then `keccak_f` and `keccak_hash` with no hypothesis.
-/

namespace Rv64Verifier.Hash
open RiscvZkvm.Rv64 Rv64Verifier.Contracts

/-- A byte frame of a range and the stack is a frame of the doublewords that miss both. -/
theorem frame2_of {s t : MachineState} {lo : Word} {n : Nat}
    (h : Runtime.ByteFrame s t fun a ↦ Within a lo n ∨ Within a (stackLo s 16) 16)
    (hst : StackOk s 16) : Frame2 s t lo n (stackLo s memStack) memStack := by
  have hb := hst.bounds (by decide) (by decide)
  intro a ha hs
  by_cases h8 : a.toNat % 8 = 0
  · refine h.getMem fun i hi hw ↦ ?_
    simp only [memStack] at hs
    rcases hw with hw | hw <;> addr_omega [ha, hs, hw, hb, hi, h8]
  · exact h.unaligned a h8

theorem memcpy : MemcpySpec := by
  intro s hpc hpre
  obtain ⟨t, hr, h⟩ := Runtime.memcpy s hpc ⟨hpre.dst, hpre.src, hpre.apart, hpre.stack,
    hpre.dstStack, hpre.srcStack⟩
  refine ⟨t, hr, h.imp_left fun ⟨hpc', hpres, hpost⟩ ↦ ⟨hpc', hpres, hpost.bytes,
    frame2_of hpost.frame hpre.stack, fun a h1 h2 ↦ hpost.frame.byte a ?_⟩⟩
  rintro (h' | h')
  · exact h1 h'
  · exact h2 h'

theorem memset : MemsetSpec := by
  intro s hpc hpre
  obtain ⟨t, hr, h⟩ := Runtime.memset s hpc hpre.dst
  refine ⟨t, hr, h.imp_left fun ⟨hpc', hpres, hpost⟩ ↦ ⟨hpc', hpres, ?_,
    frame2_of (hpost.frame.mono fun _ h ↦ Or.inl h) hpre.stack,
    fun a h1 _ ↦ hpost.frame.byte a h1⟩⟩
  rw [← BitVec.truncate_eq_setWidth]
  exact hpost.bytes

theorem keccakF : KeccakFSpec := KeccakF.keccak_f_spec memcpy memset

theorem keccakHash : KeccakHashSpec :=
  KeccakHash.keccak_hash_spec XorBlock.xor_block_spec keccakF memcpy memset

end Rv64Verifier.Hash

/-- info: 'Rv64Verifier.Hash.keccakF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Hash.keccakF

/-- info: 'Rv64Verifier.Hash.keccakHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Hash.keccakHash
