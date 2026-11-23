module

public import NativeRustcX64.SphincsVerify.Parse.WordsB

/-!
# The parse, part 4: the raw signature (`b2 .. b8`, x86-64)

From `AtW` at `b2` the word loops and the counter blocks write the raw signature `sigBytes w` at
the frame's `12416`; at `b9` (directive 106): `WS (sigBytes w)` (`words_spec`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustc.Sphincs.ParseMem NativeRustcX64.Sym
  NativeRustcX64.Sphincs.SphincsVerify LeanVM.Protocol.KeccakHash

public section

theorem sigBytes_words (w : Nat → UInt64) :
    ((((P1 w ++ wb w 539 (4 * 36)) ++ be32 (w 683).toUInt32) ++ wb w 684 (4 * 36)) ++
      be32 (w 828).toUInt32) ++ wb w 829 (4 * 37) = sigBytes w := by
  rw [sigBytes_runs, P1]
  simp only [List.append_assoc]

variable (r : Run) [Host]

/-- **The raw signature**: from `b2` to `b9`. -/
theorem words_spec (hp : Placed code r.k) (hpre : r.Pre) {m : MachineData} (h : AtW r m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b9Offset ∧ WS r (sigBytes r.w) st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b2Offset⟩ := by
  have l1 : (P1 r.w).length = 4244 := length_P1 r.w
  have l2 : (P1 r.w ++ wb r.w 539 (4 * 36)).length = 5396 := by
    rw [List.length_append, l1, length_wb]
  have l3 : (P1 r.w ++ wb r.w 539 (4 * 36) ++ be32 (r.w 683).toUInt32).length = 5400 := by
    rw [List.length_append, l2]; rfl
  have l4 : (P1 r.w ++ wb r.w 539 (4 * 36) ++ be32 (r.w 683).toUInt32 ++
      wb r.w 684 (4 * 36)).length = 6552 := by
    rw [List.length_append, l3, length_wb]
  have l5 : (P1 r.w ++ wb r.w 539 (4 * 36) ++ be32 (r.w 683).toUInt32 ++ wb r.w 684 (4 * 36) ++
      be32 (r.w 828).toUInt32).length = 6556 := by
    rw [List.length_append, l4]; rfl
  refine Eventually.bind (b2_loop r hp hpre h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (b3_spec r hp hpre h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (rax_loop r hp hpre b4_in_code rfl (hp.label NativeRustcX64.Sphincs.SphincsVerify.label_3_at) 539 4244 36
    run_b4 rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) l1 h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (counter_block r hp hpre b5_in_code rfl run_b5 683 5396 6520 (by decide)
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) rfl l2 h)
    fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (rax_loop r hp hpre b6_in_code rfl (hp.label NativeRustcX64.Sphincs.SphincsVerify.label_5_at) 684 5400 36
    run_b6 rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) l3 h) fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.bind (counter_block r hp hpre b7_in_code rfl run_b7 828 6552 7680 (by decide)
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) rfl l4 h)
    fun ⟨m, pc⟩ ⟨hpc, h⟩ ↦ ?_
  simp only at hpc
  subst hpc
  refine Eventually.mono (rax_loop r hp hpre b8_in_code rfl (hp.label NativeRustcX64.Sphincs.SphincsVerify.label_7_at) 829 6556 37
    run_b8 rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) l5 h) fun st ⟨hpc, h⟩ ↦ ⟨hpc, ?_⟩
  rwa [sigBytes_words] at h

end

end NativeRustcX64.SphincsVerifyProof.Parse
