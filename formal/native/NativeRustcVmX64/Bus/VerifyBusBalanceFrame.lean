module

public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcVmX64.Sumcheck.Common

/-!
# Frames of functions passing stack arguments (x86-64)

A function pushing a callee's stack arguments calls it with RSP below its body's: its frame
(`Frame m0 F slots o d`, `NativeRustcVmX64.Transcript.Frame`) reaches down to the deepest
return address, and a call happens at any offset `o` of it.

- `Frame.of_same`: the frame kept by a change of state that writes neither a slot nor the return
  address and keeps the other callee-saved registers;
- `Frame.call_at`: a callee entered at offset `o` returns at `o + 8` with the frame kept.
-/

namespace NativeRustcVmX64.Bus.BusFrame

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript

public section

variable {m0 d d' : MachineData} {F : Nat} {slots : Slots}

/-- **The frame kept** by a change of state writing neither a slot nor the return address and
keeping the callee-saved registers outside the slots. -/
theorem Frame.of_same {o o' : Nat} (hf : Frame m0 F slots o d)
    (hsp : rspOf d' = off (stackBelow m0 F) o')
    (hregs : ∀ r, calleeSaved r = true → slots.any (·.2 == r) = false → reg d' r = reg d r)
    (hk : Kept d.dmem d'.dmem) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F slots o' d' := by
  refine ⟨hsp, fun p hp ↦ ?_, fun j hj ↦ ?_, kept_trans hf.kept hk, fun r hr hsl ↦ ?_⟩
  · refine bytesAt_congr (hf.slot p hp) fun i hi ↦ ?_
    have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
    rw [off_add]
    exact hso _ (hR p hp i hi')
  · rw [hso _ (hRr j hj)]
    exact hf.ret j hj
  · exact (hregs r hr hsl).trans (hf.regs r hr hsl)

/-- **A call at offset `o`** of the frame keeps it where the callee changes none of its slots' or
the return address's bytes; RSP is at `o + 8` after it. -/
theorem Frame.call_at {o : Nat} (hf : Frame m0 F slots o d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ p ∈ slots, ∀ i < 8, ¬ R (off (stackBelow m0 F) (p.1 + i)))
    (hRr : ∀ j < 8, ¬ R (off (stackBelow m0 F) (F + j))) : Frame m0 F slots (o + 8) d' :=
  Frame.of_same hf (by rw [hrsp, hf.sp, off_add]) (fun r hr _ ↦ hs.1 r hr) hs.2 hso hR hRr

/-- The frame's offset `o` is `F - o` below the entry's RSP. -/
theorem off_frame_eq {o : Nat} (ho : o ≤ F) :
    off (stackBelow m0 F) o = stackBelow m0 (F - o) := by
  unfold stackBelow
  rw [off]
  have e : BitVec.ofNat 64 F = BitVec.ofNat 64 (F - o) + BitVec.ofNat 64 o := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel ho]
  rw [e]
  bv_omega

end

end NativeRustcVmX64.Bus.BusFrame
