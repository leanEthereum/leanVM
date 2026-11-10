import Rv64Verifier.Proofs.Walk.Begin

/-!
# `walk`: leaving, and the announced sizes' `next_scalars`

`exit`: from the epilogue at `0x800012e4` the function returns with its contract's post, given
what the result's first word means (`Ok` only when the mirror returns). `errExit` is every `Err`
path: the first word is `errNiche`.

`announcedCall`: `next_scalars(8)` into `S - 928`; its `Err` copied to the result
(`0x800011a8`), or, at `0x8000116c`, the code runs `walkRust` past the scalars, which the memory
at `S - 928` holds.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Leaving -/

theorem slot {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {i : Nat} (hi : i < 13) :
    u.getReg .x2 + BitVec.ofNat 64 (2648 - 8 * i) = s.getReg .x2 - BitVec.ofNat 64 (8 * i + 8) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi]

theorem saved' {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {i : Nat} (hi : i < 13) :
    u.getMem (u.getReg .x2 + BitVec.ofNat 64 (2648 - 8 * i)) = s.getReg (savedRegs.getD i .x0) := by
  rw [slot hpre h hi]; exact h.saved i hi

set_option maxRecDepth 8192 in
/-- The epilogue: the function returns, `ok` saying what its result's first word means. -/
theorem exit {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    (hpre : WalkPre s) (h : Inv s u) (hpc : u.pc = 0x800012e4)
    (hok : u.getMem (s.getReg .x10) ≠ errNiche → ∀ proof, ProofIn OI s (s.getReg .x13) proof →
      ∃ summary, verifyExecutionRust (Proofs.Bytecode.readBytecode s (s.getReg .x11))
        (bytesAt s (s.getReg .x12) 32) proof = some summary) :
    ∃ t, Reaches Image.code u t ∧ Done OI s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := h.sp
  obtain ⟨t, hr, h₁⟩ := Sym.BlockSpec.reaches b800012e4_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have hm := b800012e4_mem_same h₁
  have r (i : Nat) (hi : i < 13) (k : Word) (hk : k = BitVec.ofNat 64 (2648 - 8 * i)) :
      u.getMem (u.getReg .x2 + k) = s.getReg (savedRegs.getD i .x0) := by
    rw [hk]; exact saved' hpre h hi
  have hn : heapNext t = heapNext u := by simp only [heapNext, hm]
  refine ⟨t, hr, ?_, ?_, ⟨⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn ▸ h.mono, fun hne ↦ hok (by rwa [← hm]),
    (h.frame.trans (DFrame.of_same hm _) fun _ h ↦ h).mono fun _ ha ↦ WalkW.mono hn.ge ha⟩⟩
  · rw [b800012e4_pc h₁, r 0 (by decide) 2648 rfl, returnAddress_eq]
    rfl
  · refine preserves_of ?_ ?_ ?_ ?_ ?_ fun x hx ↦ ?_
    · rw [b800012e4_x2 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    · rw [b800012e4_x8 h₁, r 1 (by decide) 2640 rfl]; rfl
    · rw [b800012e4_x9 h₁, r 2 (by decide) 2632 rfl]; rfl
    · rw [b800012e4_x18 h₁, r 3 (by decide) 2624 rfl]; rfl
    · rw [b800012e4_x19 h₁, r 4 (by decide) 2616 rfl]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [b800012e4_x20 h₁, r 5 (by decide) 2608 rfl]; rfl
      · rw [b800012e4_x21 h₁, r 6 (by decide) 2600 rfl]; rfl
      · rw [b800012e4_x22 h₁, r 7 (by decide) 2592 rfl]; rfl
      · rw [b800012e4_x23 h₁, r 8 (by decide) 2584 rfl]; rfl
      · rw [b800012e4_x24 h₁, r 9 (by decide) 2576 rfl]; rfl
      · rw [b800012e4_x25 h₁, r 10 (by decide) 2568 rfl]; rfl
      · rw [b800012e4_x26 h₁, r 11 (by decide) 2560 rfl]; rfl
      · rw [b800012e4_x27 h₁, r 12 (by decide) 2552 rfl]; rfl

/-- Every `Err` path: the result's first word is `errNiche`. -/
theorem errExit {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    (hpre : WalkPre s) (h : Inv s u) (hpc : u.pc = 0x800012e4)
    (he : u.getMem (s.getReg .x10) = errNiche) : ∃ t, Reaches Image.code u t ∧ Done OI s t :=
  exit hpre h hpc fun hne ↦ absurd he hne

end Rv64Verifier.Proofs.Walk
