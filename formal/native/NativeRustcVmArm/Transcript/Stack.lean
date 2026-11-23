module

public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVm.Transcript.Frame

/-!
# Stacks of nested calls

A function with `n` bytes of stack, its frame `F` bytes below SP, calls a callee with `n - F`
bytes: the callee's stack is the same bytes as the caller's (`stackBelow_call`), so what is apart
from the caller's stack is apart from the callee's (`Apart.stack_call`), the stack is fine there
(`StackOk.call`), and the round constants are still at their label (`RcAt.call`). Intervals within
others (`Apart.sub`, `inRange_sub`).
-/

namespace NativeRustcVmArm.Transcript

open NativeRustcArm NativeRustcVm.Transcript

public section

theorem Apart.sub {a b b' : BitVec 64} {n N N' : Nat} (h : NativeRustcVm.Apart a n b N)
    (h1 : b.toNat ≤ b'.toNat) (h2 : b'.toNat + N' ≤ b.toNat + N) :
    NativeRustcVm.Apart a n b' N' := by
  unfold NativeRustcVm.Apart at h ⊢
  omega

theorem Apart.symm' {a b : BitVec 64} {n N : Nat} (h : NativeRustcVm.Apart a n b N) :
    NativeRustcVm.Apart b N a n := by
  unfold NativeRustcVm.Apart at h ⊢
  omega

theorem inRange_sub {a b q : BitVec 64} {n N : Nat} (hb : b.toNat + N ≤ 2 ^ 64)
    (h1 : b.toNat ≤ a.toNat) (h2 : a.toNat + n ≤ b.toNat + N) (h : NativeRustcVm.InRange a n q) :
    NativeRustcVm.InRange b N q := by
  have ha : NativeRustcVm.NoWrap a n := by unfold NativeRustcVm.NoWrap; omega
  rw [inRange_iff' ha] at h
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
  omega

theorem toNat_stackBelow {m : MachineData} {n : Nat} (h : n ≤ m.regs.SP.toNat) :
    (stackBelow m n).toNat = m.regs.SP.toNat - n := by
  unfold stackBelow
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
  have := m.regs.SP.toNat_lt
  omega

section
variable {m m' : MachineData} {n F : Nat}

/-- The callee's stack is the caller's, below its frame. -/
theorem stackBelow_call (hn : n ≤ m.regs.SP.toNat) (hF : F ≤ n)
    (hsp : m'.regs.SP.toNat = m.regs.SP.toNat - F) :
    (stackBelow m' (n - F)).toNat = (stackBelow m n).toNat := by
  rw [toNat_stackBelow (by omega), toNat_stackBelow hn, hsp]
  omega

theorem Apart.stack_call {a : BitVec 64} {l : Nat} (h : NativeRustcVm.Apart a l (stackBelow m n) n)
    (hn : n ≤ m.regs.SP.toNat) (hF : F ≤ n) (hsp : m'.regs.SP.toNat = m.regs.SP.toNat - F) :
    NativeRustcVm.Apart a l (stackBelow m' (n - F)) (n - F) :=
  Apart.sub h (by rw [stackBelow_call hn hF hsp]) (by rw [stackBelow_call hn hF hsp]; omega)

theorem StackOk.call (h : StackOk m n) (hk : Kept m.dmem m'.dmem) (hF : F ≤ n) (h16 : F % 16 = 0)
    (hsp : m'.regs.SP.toNat = m.regs.SP.toNat - F) : StackOk m' (n - F) := by
  obtain ⟨hal, hn, hmap⟩ := h
  refine ⟨by rw [hsp]; omega, by rw [hsp]; omega, fun i hi ↦ ?_⟩
  have e : m'.regs.SP.toBitVec - BitVec.ofNat 64 (n - F) + BitVec.ofNat 64 i =
      m.regs.SP.toBitVec - BitVec.ofNat 64 n + BitVec.ofNat 64 i := by
    apply BitVec.eq_of_toNat_eq
    have h1 := stackBelow_call (m := m) (m' := m') hn hF hsp
    unfold stackBelow at h1
    rw [BitVec.toNat_add, BitVec.toNat_add, h1]
  rw [e]
  exact hk _ (hmap i (by omega))

/-- The `F`-byte frame below SP is within the stack. -/
theorem frame_toNat (hn : n ≤ m.regs.SP.toNat) (hF : F ≤ n) :
    (m.regs.SP.toBitVec - BitVec.ofNat 64 F).toNat = m.regs.SP.toNat - F := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
  have := m.regs.SP.toNat_lt
  omega

variable [Labels]

/-- The round constants for the callee, kept where its caller's memory changed. -/
theorem RcAt.call (h : RcAt m n) (hd : ∀ i < 192, m'.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m.dmem.get? (rcAddr + BitVec.ofNat 64 i))
    (hn : n ≤ m.regs.SP.toNat) (hF : F ≤ n) (hsp : m'.regs.SP.toNat = m.regs.SP.toNat - F) :
    RcAt m' (n - F) := by
  obtain ⟨hw, hnw, hap⟩ := h
  refine ⟨bytesAt_congr hw fun i hi ↦ hd i ?_, hnw, Apart.stack_call hap hn hF hsp⟩
  have : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 := by
    rw [length_flatMap_wordBytes]; rfl
  omega

/-- The round constants, kept where the memory changed only apart from them. -/
theorem rc_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hR : ∀ q, R q → ¬ NativeRustcVm.InRange rcAddr 192 q) :
    ∀ i < 192, d'.get? (rcAddr + BitVec.ofNat 64 i) = d.get? (rcAddr + BitVec.ofNat 64 i) :=
  fun i hi ↦ hs _ fun h ↦ hR _ h (inRange_off_self hi (by omega))

/-- The round constants for a callee using `n'` bytes of stack below an `F`-byte frame. -/
theorem RcAt.callee (h : RcAt m n) (hd : ∀ i < 192, m'.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m.dmem.get? (rcAddr + BitVec.ofNat 64 i))
    (hn : n ≤ m.regs.SP.toNat) (hF : F ≤ n) (hsp : m'.regs.SP.toNat = m.regs.SP.toNat - F)
    {n' : Nat} (hn' : n' ≤ n - F) : RcAt m' n' := by
  obtain ⟨hw, hnw, hap⟩ := RcAt.call h hd hn hF hsp
  refine ⟨hw, hnw, Apart.sub hap ?_ ?_⟩
  · rw [toNat_stackBelow (by omega), toNat_stackBelow (by omega)]; omega
  · rw [toNat_stackBelow (by omega), toNat_stackBelow (by omega)]; omega

end

end

end NativeRustcVmArm.Transcript
