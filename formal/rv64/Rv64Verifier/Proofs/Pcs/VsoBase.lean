import Rv64Verifier.Proofs.Pcs.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.Transcript.Frames
import Rv64Verifier.Blocks.F38

/-!
# `verify_stacked_opening`: the frame and the exit

Compiled at `0x80009db8` (`Blocks/F38.lean`), with `S` the entry's `sp`: `0x80009db8` saves `ra`,
`s0`..`s11` in a 1040-byte frame, and every return goes through `0x8000a0bc`, which restores them
and returns `a0` (`-1` for `Ok`). In between, the function writes only its stack, `NEXT`, the heap
it allocates and the transcript's sponge and offsets (`Inv`); `exit` turns that into the contract's
frame.

Registers through the function: `s11` the transcript, `s0` the root (by reference), `s10`
`stack_log`, `s5` `log_inv_rate`, `s6`/`s4` the claims until the configuration is derived.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19),
  (48, .x20), (56, .x21), (64, .x22), (72, .x23), (80, .x24), (88, .x25), (96, .x26), (104, .x27)]

/-- What the function may write besides its stack, `NEXT` and the heap: the transcript's sponge and
offsets. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop := Within a (s.getReg .x10 + 8) 352

/-- Inside the function, `w` written besides the stack, `NEXT` and the heap. -/
abbrev InvW (w : Word → Prop) (s u : MachineState) (nx : Word) : Prop :=
  PInv s u 1040 vsoStack slots [] w nx

/-- Inside the function. -/
abbrev Inv (s u : MachineState) (nx : Word) : Prop := InvW (W s) s u nx

/-- Before the first transcript call nothing but the stack, `NEXT` and the heap is written. -/
abbrev Inv0 (s u : MachineState) (nx : Word) : Prop := InvW (fun _ ↦ False) s u nx

theorem Inv0.toInv {s u : MachineState} {nx : Word} (h : Inv0 s u nx) : Inv s u nx := by
  refine ⟨h.sp, h.slots, h.kept, h.mem.mono fun a ha ↦ ?_, h.next, h.mono, h.fits⟩
  rcases ha with ha | ha
  · exact ha.elim
  · exact Or.inr ha

theorem bounds {s : MachineState} (h : VsoPre s) :
    0x78000000 + 2464 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
    shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack, stackLo,
    heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- The transcript lies apart from the stack and above the free heap. -/
theorem self_bounds {s : MachineState} (h : VsoPre s) :
    0x20 ≤ (s.getReg .x10).toNat ∧ (s.getReg .x10).toNat + 368 ≤ 0xc0000000 ∧
      (s.getReg .x10).toNat % 8 = 0 :=
  Region.bounds h.self.ok.self

theorem Inv.step' {s u v : MachineState} {nx nx' : Word} {X w : Word → Prop}
    (hpre : VsoPre s) (h : InvW w s u nx) (hX : DFrame u v X)
    (hXsub : ∀ a, X a → Wr s vsoStack w nx' a)
    (hXslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 104) 104)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) : InvW w s v nx' :=
  h.step 104 (by decide) (by have := bounds hpre; omega) hX hXsub hXslot hnx hle hend hsp
    (fun _ hr ↦ by cases hr)

theorem Inv.same' {s u v : MachineState} {nx : Word} {w : Word → Prop} (h : InvW w s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2) : InvW w s v nx :=
  h.same hm hsp fun _ hr ↦ by cases hr

theorem Inv0.same' {s u v : MachineState} {nx : Word} (h : Inv0 s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2) : Inv0 s v nx :=
  Inv.same' h hm hsp

/-- The stack's bytes the function writes in its own frame, below the saved registers. -/
theorem frame_wr {s : MachineState} (hpre : VsoPre s) {a : Word} {nx : Word} {w : Word → Prop}
    (ha : Within a (s.getReg .x2 - 1040) 936) : Wr s vsoStack w nx a := by
  have hb := bounds hpre
  exact Or.inr (Or.inl (by
    simp only [vsoStack, basisStack, ringEvalStack, mulStack, roundPolyStack, nextScalarsStack,
      shuntNextStack, nextScalarStack, absorbStack, duplexStack, keccakFStack, memStack, stackLo]
    addr_omega [ha, hb]))

theorem frame_slot {s : MachineState} (hpre : VsoPre s) {a : Word}
    (ha : Within a (s.getReg .x2 - 1040) 936) :
    ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 104) 104 := by
  have hb := bounds hpre
  addr_omega [ha, hb]

/-- **The exit**: from `0x8000a0bc` the function returns `a0` with the saved registers restored,
memory changed only where the contract allows. -/
theorem exit {s u : MachineState} {nx : Word} (hpre : VsoPre s) (h : Inv s u nx)
    (hpc : u.pc = 0x8000a0bc) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getReg .x10 = u.getReg .x10 ∧ HeapOk t ∧ heapNext s ≤ heapNext t ∧
      DFrame s t fun a ↦ Within a (s.getReg .x10 + 8) 352 ∨
        Within a (stackLo s vsoStack) vsoStack ∨ Within a nextAddr 8 ∨ Fresh s t a := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.sp
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000a0bc_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hst.valid [hb])
  have hm := b8000a0bc_mem_same ht
  have hrest (o : Nat) (r : Reg) (ho : (o, r) ∈ slots) (k : Word)
      (hk : u.getReg .x2 + k = s.getReg .x2 - BitVec.ofNat 64 o) :
      u.getMem (u.getReg .x2 + k) = s.getReg r := by
    rw [hk]; exact h.slots _ ho
  have hn : heapNext t = heapNext u := by simp only [heapNext, hm]
  have hnu : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  have hu := h.heap hpre.heap
  refine ⟨t, hr, ?_, ?_, ?_, ⟨by rw [hn]; exact hu.lo, by rw [hn]; exact hu.hi⟩,
    by rw [hn, hnu]; exact h.mono, ?_⟩
  · rw [b8000a0bc_pc ht, returnAddress_eq, hrest 8 .x1 (by decide) _ (by rw [hsp]; rv_eval [])]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b8000a0bc_x2 ht, hsp]; rv_eval []
    · rw [b8000a0bc_x8 ht]; exact hrest 16 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x9 ht]; exact hrest 24 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x18 ht]; exact hrest 32 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x19 ht]; exact hrest 40 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x20 ht]; exact hrest 48 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x21 ht]; exact hrest 56 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x22 ht]; exact hrest 64 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x23 ht]; exact hrest 72 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x24 ht]; exact hrest 80 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x25 ht]; exact hrest 88 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x26 ht]; exact hrest 96 _ (by decide) _ (by rw [hsp]; rv_eval [])
    · rw [b8000a0bc_x27 ht]; exact hrest 104 _ (by decide) _ (by rw [hsp]; rv_eval [])
  · exact b8000a0bc_keeps ht .x10 (by decide)
  · intro a ha
    rw [hm a]
    refine h.frame a fun i hi hw ↦ ha i hi ?_
    simpa only [Fresh, hn, W] using hw

/-- What the function reads in place misses what a function that writes no transcript writes. -/
theorem src_misses {s : MachineState} {nx : Word} (hfit : nx.toNat ≤ heapEnd) {a : Word} {n : Nat}
    (hst : Apart a n (stackLo s vsoStack) vsoStack) (hf : Outside s a n) :
    Misses (Wr s vsoStack (fun _ ↦ False) nx) a n := by
  simp only [Outside] at hf
  intro y hy hW
  rcases hW with hW | hW | hW | hW
  · exact hW
  · addr_omega [hy, hW, hst]
  · addr_omega [hy, hW, hf.2]
  · rcases hf.1 with h1 | h1
    · addr_omega [hy, hW.1, h1]
    · addr_omega [hy, hW.2, h1, hfit]

/-- Before the first transcript call, the transcript stands for what it stood for. -/
theorem Inv0.transcriptAt {s u : MachineState} {nx : Word} (hpre : VsoPre s) (h : Inv0 s u nx)
    {T : Model.TState} (hT : TranscriptAt s (s.getReg .x10) T) : TranscriptAt u (s.getReg .x10) T := by
  have hI := hpre.self
  have hS := hI.ok.self
  have hP := hI.ok.proof
  have hfit := h.fits
  have hs := src_misses hfit hI.stack hI.free
  refine h.mem.transcriptAt hT hI.ok (fun y hy ↦ hs y (by addr_omega [hy, hS]))
    (src_misses hfit hI.proofStack.1 hI.proofFree) (src_misses hfit hI.proofStack.2 hI.streamFree)
    (fun y hy ↦ hs y (by addr_omega [hy, hS]))

end Rv64Verifier.Proofs.Pcs.Vso
