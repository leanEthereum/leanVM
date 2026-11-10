import Rv64Verifier.Proofs.Walk.R16A
import Rv64Verifier.Proofs.Bus.VbbBc

/-!
# `BcWalk` for `verify_bus_balance`'s `BcOk`

`walk`'s frame keeps doublewords, so the `Bytecode` is kept from `walk`'s entry when every aligned
doubleword holding one of its bytes lies below `NEXT` there, or above the heap (`BcCover`). The
`Bytecode`'s own bytes and its `Block` and word buffers are doubleword-aligned and always are
(`ReadOnly`); its two `u16` buffers are whenever `NEXT` is aligned at the entry
(`bcCover_of_aligned`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript Rv64Verifier.Bus
open Rv64Verifier.Proofs.Bus.VerifyBusBalance (BcOk bevOf readBytecode_congr bcParts_end)

/-- Every aligned doubleword holding a byte of the `Bytecode` lies below `NEXT` or above the heap. -/
def BcCover (s : MachineState) : Prop :=
  ∀ q ∈ bcParts s (s.getReg .x11), ∀ a, Meets a q.1 q.2 →
    a.toNat + 8 ≤ heapNext s ∨ heapEnd ≤ a.toNat

theorem bcCover_of_aligned {s : MachineState} (hpre : WalkPre s) (h8 : heapNext s % 8 = 0) :
    BcCover s := by
  intro q hq a ha
  have ho := (bcIn_parts hpre.bytecode q hq).1.1
  simp only [Meets] at ha
  simp only [heapEnd] at ho ⊢
  rcases ho with h0 | h0
  · left; omega
  · right; omega

/-- `BcWalk`'s two facts at a state past `walk`'s entry, the `Bytecode` covered there. -/
theorem bcWalk_of {s c : MachineState} (hpre : WalkPre s) (hc : BcCover s) (I : Inv s c) :
    BcOk c busBalanceStack (s.getReg .x11) ∧
      bevOf c (s.getReg .x11) = evaluateRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hm := hpre.bytecode.mem
  have hend := bcParts_end hm
  have hk : ∀ q ∈ bcParts s (s.getReg .x11), ∀ a, Meets a q.1 q.2 → c.getMem a = s.getMem a := by
    intro q hq a ha
    have hn : 0 < q.2 := ha.2.2.2
    exact bcKeep hpre I (bcIn_parts hpre.bytecode q hq) ((hend q hq).resolve_left (by omega)) ha
      (hc q hq a ha)
  obtain ⟨hrd, hpa, ⟨p0, l0⟩, ⟨p1, l1⟩, ⟨p2, l2⟩, ⟨p3, l3⟩⟩ := readBytecode_congr hm hk
  have hmU : Proofs.Bytecode.BytecodeMem c (s.getReg .x11) := {
    self := hm.self
    align := hm.align
    blocks := p0 ▸ l0 ▸ hm.blocks
    blocksAlign := p0 ▸ hm.blocksAlign
    words := p1 ▸ l1 ▸ hm.words
    wordsAlign := p1 ▸ hm.wordsAlign
    positions := p2 ▸ l2 ▸ hm.positions
    positionsAlign := p2 ▸ hm.positionsAlign
    bytes := p3 ▸ l3 ▸ hm.bytes
    bytesAlign := p3 ▸ hm.bytesAlign }
  have hsl := stackLo_callee I busBalanceStack
  have hmo := I.mono
  refine ⟨⟨hmU, fun q hq ↦ ?_⟩, ?_⟩
  · rw [hpa] at hq
    have hro := bcIn_parts hpre.bytecode q hq
    have hs := hro.2.1
    rw [stackLo_eq, stack_eq] at hs
    rw [hsl]
    refine ⟨⟨⟨hro.1.1.imp_left fun h ↦ Nat.le_trans h hmo, hro.1.2⟩, by addr_omega [hs, hb1]⟩,
      fun a ha ↦ ?_⟩
    obtain ⟨hs', -, hn'⟩ := bcDword hpre hro ha
    exact ⟨⟨(hc q hq a ha).imp_left fun h ↦ Nat.le_trans h hmo, hn'⟩, by addr_omega [hs', hb1]⟩
  · funext pt; unfold bevOf; rw [hrd]

/-- **`BcWalk` for `BcOk`**, the `Bytecode` covered at `walk`'s entry. -/
theorem bcWalk (h : ∀ s, WalkPre s → BcCover s) : BcWalk BcOk bevOf :=
  fun s _ hpre I ↦ bcWalk_of hpre (h s hpre) I

end Rv64Verifier.Proofs.Walk
