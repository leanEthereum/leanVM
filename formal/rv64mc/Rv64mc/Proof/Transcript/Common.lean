/-
  Rv64mc.Proof.Transcript.Common

  What the transcript's proofs share: the frame of stores into a caller's frame (an `sret` slot, the transcript's
  fields), what they keep of a transcript, and the transcript's own fields updated one at a time
  (`TranscriptAt.setStream`), each in the address forms `rv_sym` computes.
-/

import Rv64mc.Spec.Transcript.Repr

namespace Rv64mc.Proof.Transcript

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64mc.Spec.Transcript

variable {env : Env}

/-! ## Stores into a caller's frame -/

theorem ne_next {b top : Word} (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat) :
    b ≠ env.nextAddr := fun h => by have := env.layout; rw [h] at hb; omega

/-- A store into the call's `out` at or above its stack top is in its frame. -/
theorem frame_store_out {top b v : Word} {out : Word → Prop} {m M : MachineState} (h : env.Frame top out m M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat) (ho : out b) :
    env.Frame top out m (M.setMem b v) :=
  h.trans (Env.Frame.setMem_out h.2.1 ho (ne_next hlim hb)) (Nat.le_refl _)
    fun _ ha => Or.inr (Or.inr (Or.inr ha))

theorem static_store {top b v : Word} {M : MachineState} (hs : env.Static M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat) : env.Static (M.setMem b v) :=
  Env.static_setMem_stack hs (by omega)

theorem heapKept_store {top b v : Word} {m M : MachineState} (h : HeapKept env m M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : top.toNat ≤ b.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : HeapKept env m (M.setMem b v) := by
  have hn : env.next (M.setMem b v) = env.next M := by
    simp [Env.next, MachineState.getMem, MachineState.setMem, Ne.symm (ne_next hlim hb)]
  refine ⟨by rw [hn]; exact h.1, fun c hc => ?_⟩
  have : c ≠ b := fun he => by have := env.layout; rw [he] at hc; omega
  rw [MachineState.getMem_setMem_ne this]; exact h.2 c hc

theorem heapKept_refl {m : MachineState} : HeapKept env m m := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem keeps_store {m M : MachineState} {a c v : Word} {n : Nat} (h : Keeps m M a n) (hc : ¬ InRange a n c) :
    Keeps m (M.setMem c v) a n :=
  h.trans (Keeps.setMem hc)

theorem keeps_refl {m : MachineState} {a : Word} {n : Nat} : Keeps m m a n := fun _ _ => rfl

/-- `a + k`, `k` below `n`, is in `[a, a + n)`. -/
theorem inRange_add {a : Word} {n k : Nat} (ha : a.toNat + n < 2 ^ 64) (hk : k < n) :
    InRange a n (a + BitVec.ofNat 64 k) := by
  constructor <;> rw [toNat_add_ofNat (by omega)] <;> omega

theorem inRange_self {a : Word} {n : Nat} (hn : 0 < n) : InRange a n a := ⟨Nat.le_refl _, by omega⟩

/-- A word of `[b, b + k)` is outside a footprint `[a, a + n)` apart from it. -/
theorem not_inRange_apart {a b : Word} {n k j : Nat} (h : Apart a n b k) (hb : b.toNat + k < 2 ^ 64) (hj : j < k) :
    ¬ InRange a n (b + BitVec.ofNat 64 j) := by
  rw [InRange, toNat_add_ofNat (by omega)]; unfold Apart at h; omega

theorem not_inRange_apart' {a b : Word} {n k j : Nat} (h : Apart b k a n) (hb : b.toNat + k < 2 ^ 64) (hj : j < k) :
    ¬ InRange a n (b + BitVec.ofNat 64 j) := by
  rw [InRange, toNat_add_ofNat (by omega)]; unfold Apart at h; omega

theorem toNat_le_add {a : Word} {k n : Nat} (ha : a.toNat + n < 2 ^ 64) (hk : k ≤ n) :
    a.toNat ≤ (a + BitVec.ofNat 64 k).toNat := by
  rw [toNat_add_ofNat (by omega)]; omega

/-- A `usize` the code shifts by four, as the address of element `o`. -/
theorem shl4 (o : Nat) : BitVec.ofNat 64 o <<< 4 = BitVec.ofNat 64 (16 * o) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod]

theorem ofNat_lt_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a < BitVec.ofNat 64 b ↔ a < b := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_le_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ≤ BitVec.ofNat 64 b ↔ a ≤ b := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_succ (o : Nat) : BitVec.ofNat 64 o + 1#64 = BitVec.ofNat 64 (o + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## A transcript's fields -/

/-- Two offsets of a footprint that does not wrap name different words. -/
theorem add_ne_add {a : Word} {j k n : Nat} (ha : a.toNat + n < 2 ^ 64) (hj : j < n) (hk : k < n) (h : j ≠ k) :
    a + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 k := fun he => by
  rw [← BitVec.toNat_inj, toNat_add_ofNat (by omega), toNat_add_ofNat (by omega)] at he; exact h (by omega)

theorem ne_add_self {a : Word} {k n : Nat} (ha : a.toNat + n < 2 ^ 64) (hk : 0 < k) (hkn : k < n) :
    a ≠ a + BitVec.ofNat 64 k := fun he => by
  have := congrArg BitVec.toNat he; rw [toNat_add_ofNat (by omega)] at this; omega

/-- The base of a footprint `[b, b + k)` is outside a footprint `[a, a + n)` apart from it. -/
theorem not_inRange_apart0 {a b : Word} {n k : Nat} (h : Apart b k a n) (hk : 0 < k) : ¬ InRange a n b := by
  unfold InRange; unfold Apart at h; omega

/-- A store into a footprint in the stack keeps the heap below `NEXT`. -/
theorem heapKept_stack {m : MachineState} {b v : Word} (hlim : env.stackLimit.toNat ≤ b.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) : HeapKept env m (m.setMem b v) := by
  have hb : b ≠ env.nextAddr := fun h => by have := env.layout; rw [h] at hlim; omega
  have hn : env.next (m.setMem b v) = env.next m := by
    simp [Env.next, MachineState.getMem, MachineState.setMem, Ne.symm hb]
  refine ⟨by rw [hn], fun c hc => ?_⟩
  have : c ≠ b := fun he => by have := env.layout; rw [he] at hc; omega
  rw [MachineState.getMem_setMem_ne this]

/-- **The stream offset written**: the transcript at `a`, in the stack, with `streamOffset` replaced. -/
theorem _root_.Rv64mc.Spec.Transcript.TranscriptAt.setStream {m : MachineState} {a : Word} {t : Model.TState} (ht : TranscriptAt env m a t)
    (ha : a.toNat + Layouts.Transcript.byteSize < 2 ^ 64) (hlim : env.stackLimit.toNat ≤ a.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) {o : Nat} (ho : o ≤ t.proof.stream.length) :
    TranscriptAt env (m.setMem (a + BitVec.ofNat 64 Layouts.Transcript.stream_offset) (BitVec.ofNat 64 o)) a
      { t with streamOffset := o } := by
  simp only [Layouts.Transcript.byteSize] at ha
  obtain ⟨-, hb2, hs, hp, h1, h2, h3⟩ := ht
  have h336 : (a + BitVec.ofNat 64 336).toNat = a.toNat + 336 := toNat_add_ofNat (by omega)
  have hk : Keeps m (m.setMem (a + BitVec.ofNat 64 336) (BitVec.ofNat 64 o)) (a + BitVec.ofNat 64 0) 328 :=
    Keeps.setMem fun h => by unfold InRange at h; rw [h336] at h; simp at h
  refine ⟨ho, hb2, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Layouts.Transcript.sponge, Layouts.Transcript.proof, Layouts.Transcript.stream_offset,
      Layouts.Transcript.opening_offset, Layouts.Transcript.checked] at hs hp h1 h2 h3 ⊢
  · exact hs.keep (by rw [show a + BitVec.ofNat 64 0 = a by simp]; simp only [Layouts.Sponge.byteSize]; omega) hk
  · rw [MachineState.getMem_setMem_ne (add_ne_add (n := 360) ha (by decide) (by decide) (by decide))]
    exact hp.keep (heapKept_stack (by omega) hnx)
  · simp
  · rw [MachineState.getMem_setMem_ne (add_ne_add (n := 360) ha (by decide) (by decide) (by decide))]; exact h2
  · rw [getByte_setMem_ne]; exact h3
    intro h
    have := congrArg BitVec.toNat h
    rw [h336, toNat_alignToDword, toNat_add_ofNat (by omega)] at this
    omega

/-! ## The proof's stream -/

/-- The stream's length, at the address the code reads it. -/
theorem _root_.Rv64mc.Spec.Transcript.ProofAt.stream_len {m : MachineState} {q : Word} {pf : Proof} (h : ProofAt env m q pf) :
    m.getMem (q + 16#64) = BitVec.ofNat 64 pf.stream.length ∧ pf.stream.length < 2 ^ 63 := by
  obtain ⟨ptr, cap, hv, -⟩ := h.stream
  have hl := hv.len_eq; have := hv.len_le; have := hv.cap_lt
  simp only [vecLen, Layouts.Proof.stream, Layouts.Vec.len, List.length_map] at *
  refine ⟨by simpa using hl, by omega⟩

/-- The number of phases of openings, at the address the code reads it. -/
theorem _root_.Rv64mc.Spec.Transcript.ProofAt.openings_len {m : MachineState} {q : Word} {pf : Proof}
    (h : ProofAt env m q pf) :
    m.getMem (q + 40#64) = BitVec.ofNat 64 pf.openings.length ∧ pf.openings.length < 2 ^ 63 := by
  obtain ⟨ptr, cap, hv, -⟩ := h.openings
  have hl := hv.len_eq; have := hv.len_le; have := hv.cap_lt
  simp only [vecLen, Layouts.Proof.merkle_openings, Layouts.Vec.len] at *
  refine ⟨by rw [← hl, BitVec.add_assoc]; rfl, by omega⟩

/-- Element `o` of the stream, at the addresses the code reads it: the buffer's pointer at `q + 8`, the element at
    `o <<< 4` past it. -/
theorem _root_.Rv64mc.Spec.Transcript.ProofAt.stream_elem {m : MachineState} {q : Word} {pf : Proof} (h : ProofAt env m q pf) {o : Nat}
    (ho : o < pf.stream.length) :
    m.getMem (m.getMem (q + 8#64) + BitVec.ofNat 64 o <<< 4) = (Model.limbs pf.stream[o]).1 ∧
      m.getMem (m.getMem (q + 8#64) + BitVec.ofNat 64 o <<< 4 + 8#64) = (Model.limbs pf.stream[o]).2 := by
  obtain ⟨ptr, cap, hv, -⟩ := h.stream
  have hp := hv.ptr_eq
  have he := hv.elems.2 o (by simpa using ho)
  simp only [vecPtr, Layouts.Proof.stream, Layouts.Vec.ptr, EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize,
    List.getElem_map] at hp he
  rw [show q + BitVec.ofNat 64 0 + BitVec.ofNat 64 8 = q + 8#64 by simp] at hp
  rw [hp, shl4]
  simpa using he

end Rv64mc.Proof.Transcript
