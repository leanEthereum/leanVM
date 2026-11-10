import Rv64Verifier.Proofs.Pcs.RingSwitchCoeff

/-!
# `ring_switch`: from the coefficients to the images loop

`toImages`: `0x8000994c` moves the coefficients' `Vec` to `F + 152` and calls
`try_allocate_in(F + 240, n, 0, 8, 24)`, `0x80009980` traps on `Err`, `0x80009988` makes the images'
`Vec` at `F + 216` (and saves `point` at `F`), `reserve(n)` returns at once, `0x800099b0` saves the
buffer `I` at `F + 24` and skips the loop when `n = 0`. At its end `Ctx2` holds what the rest reads.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `s.len()`. -/
@[rv_addr] def nS (s : MachineState) : Nat := (s.getReg .x13).toNat

/-- What the rest reads and never writes, at the images loop's base `B2`. -/
structure Ctx2 (s B2 : MachineState) (C chP I : Word) (ch : List E) : Prop where
  sp : B2.getReg .x2 = s.getReg .x2 - 464
  heap : HeapOk B2
  mono : heapNext s ≤ heapNext B2
  frame : DFrame s B2 fun a ↦ W0 s a ∨ Fresh s B2 a
  slots : ∀ p ∈ slots, B2.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  pt : B2.getMem (s.getReg .x2 - 464) = s.getReg .x11
  out : B2.getMem (s.getReg .x2 - 456) = s.getReg .x10
  sP : B2.getMem (s.getReg .x2 - 448) = s.getReg .x12
  iP : B2.getMem (s.getReg .x2 - 440) = I
  sLen : B2.getMem (s.getReg .x2 - 432) = s.getReg .x13
  chPm : B2.getMem (s.getReg .x2 - 424) = chP
  six : B2.getMem (s.getReg .x2 - 416) = 6
  c0 : B2.getMem (s.getReg .x2 - 312) = 64
  c1 : B2.getMem (s.getReg .x2 - 304) = C
  c2 : B2.getMem (s.getReg .x2 - 296) = 64
  coeffs : ∀ l < 64, eAt B2 (C + BitVec.ofNat 64 (24 * l)) = cacc ch l 6
  chLen : ch.length = 6
  chs : eListAt B2 chP 6 = ch
  chA : chP.toNat % 8 = 0
  chLo : heapNext s ≤ chP.toNat
  chC : chP.toNat + 144 ≤ C.toNat
  cA : C.toNat % 8 = 0
  cHi : C.toNat + 1536 ≤ heapNext B2
  iA : I.toNat % 8 = 0
  iR : nS s = 0 ∨ (C.toNat + 1536 ≤ I.toNat ∧ I.toNat + 24 * nS s ≤ heapNext B2)
  tok : TranscriptOk B2 (s.getReg .x14)
  trEq : proofAt B2 (s.getReg .x14) = proofAt s (s.getReg .x14) ∧
    streamPtr B2 (s.getReg .x14) = streamPtr s (s.getReg .x14) ∧
    streamLen B2 (s.getReg .x14) = streamLen s (s.getReg .x14)
  value : ∀ T, TranscriptAt s (s.getReg .x14) T → ∃ T',
    (Model.TM.samples 6).run T = some (ch, T') ∧ TranscriptAt B2 (s.getReg .x14) T'
  slices : eListAt B2 (s.getReg .x12) (nS s) = eListAt s (s.getReg .x12) (nS s)

/-- What the images loop writes besides the stack below `sp`: its scratch `F + 176 .. F + 360`
and the buffer `I`. -/
def w2 (s : MachineState) (I : Word) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 288) 184 ∨ Within a I (24 * nS s)

theorem Ph.widen {B u : MachineState} {w w' : Word → Prop} {nx : Word} (h : Ph B u w nx)
    (hw : ∀ a, w a → w' a) : Ph B u w' nx :=
  ⟨h.sp, h.mem.mono fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl (hw a ha)
    · exact Or.inr ha, h.next, h.mono, h.fits⟩

/-- The transcript across a frame from `B` on that misses it: `w` only in the stack frame or the
heap allocated since `s`. -/
theorem tr_move {s B B' : MachineState} {w : Word → Prop} {nx : Word} (hpre : RingSwitchPre s)
    (hs : heapNext s ≤ heapNext B) (hf : DFrame B B' (Wr B 1120 w nx))
    (hspB : B.getReg .x2 = s.getReg .x2 - 464) (hfit : nx.toNat ≤ heapEnd)
    (hw : ∀ a, w a → ((s.getReg .x2).toNat - 464 ≤ a.toNat ∧ a.toNat < (s.getReg .x2).toNat) ∨
      (heapNext s ≤ a.toNat ∧ a.toNat < heapEnd))
    (heq : proofAt B (s.getReg .x14) = proofAt s (s.getReg .x14) ∧
      streamPtr B (s.getReg .x14) = streamPtr s (s.getReg .x14) ∧
      streamLen B (s.getReg .x14) = streamLen s (s.getReg .x14))
    (hok : TranscriptOk B (s.getReg .x14)) :
    TranscriptOk B' (s.getReg .x14) ∧ (proofAt B' (s.getReg .x14) = proofAt s (s.getReg .x14) ∧
      streamPtr B' (s.getReg .x14) = streamPtr s (s.getReg .x14) ∧
      streamLen B' (s.getReg .x14) = streamLen s (s.getReg .x14)) ∧
      ∀ T, TranscriptAt B (s.getReg .x14) T → TranscriptAt B' (s.getReg .x14) T := by
  have hb := bounds hpre
  have hTi := hpre.self
  have hP := Region.bounds hTi.ok.self
  have hQ := Region.bounds hTi.ok.proof
  simp only [transcriptSize] at hP
  have hTS := hTi.stack
  have hPS := hTi.proofStack
  have hfree := hTi.free
  have hpfree := hTi.proofFree
  have hsfree := hTi.streamFree
  simp only [Outside] at hfree hpfree hsfree
  have hmiss (x : Word) (h1 : x.toNat < (s.getReg .x2).toNat - 1584 ∨ (s.getReg .x2).toNat ≤ x.toNat)
      (h2 : x.toNat < heapNext s ∨ heapEnd ≤ x.toNat) (h3 : ¬ Within x nextAddr 8) :
      ¬ Wr B 1120 w nx x := by
    rintro (hW | hW | hW | hW)
    · rcases hw x hW with hW | hW
      · omega
      · omega
    · simp only [stackLo, hspB] at hW; addr_omega [hW, h1, hb]
    · exact h3 hW
    · omega
  obtain ⟨h1, h2, h3⟩ := heq
  have hq : ∀ i < 48, ¬ Wr B 1120 w nx (proofAt B (s.getReg .x14) + BitVec.ofNat 64 i) := by
    intro i hi; rw [h1]
    exact hmiss _ (by addr_omega [hi, hQ, hPS.1, hb]) (by addr_omega [hi, hQ, hpfree.1])
      (by addr_omega [hi, hQ, hpfree.2])
  have hp : ∀ i < 8, ¬ Wr B 1120 w nx (s.getReg .x14 + BitVec.ofNat 64 i) := fun i hi ↦
    hmiss _ (by addr_omega [hi, hP, hTS, hb]) (by addr_omega [hi, hP, hfree.1])
      (by addr_omega [hi, hP, hfree.2])
  obtain ⟨hok', e1, e2, e3⟩ := transcriptOk_frame hf hok hp hq
  refine ⟨hok', ⟨e1.trans h1, e2.trans h2, e3.trans h3⟩, fun T hT ↦ transcriptAt_frame hf hT hok
    (fun x hx ↦ hmiss x (by addr_omega [hx, hP, hTS, hb]) (by addr_omega [hx, hP, hfree.1])
      (by addr_omega [hx, hP, hfree.2]))
    (fun x hx ↦ by
      rw [h1] at hx
      exact hmiss x (by addr_omega [hx, hQ, hPS.1, hb]) (by addr_omega [hx, hQ, hpfree.1])
        (by addr_omega [hx, hQ, hpfree.2]))
    (fun x hx ↦ by
      rw [h2, h3] at hx
      exact hmiss x (by addr_omega [hx, hPS.2, hb]) (by addr_omega [hx, hsfree.1])
        (by addr_omega [hx, hsfree.2]))⟩

/-- The transcript's proof as at entry, at the coefficient loop's base. -/
theorem tr_ctx {s B1 : MachineState} {C chP : Word} {ch : List E} (hpre : RingSwitchPre s)
    (hctx : Ctx s B1 C chP ch) :
    proofAt B1 (s.getReg .x14) = proofAt s (s.getReg .x14) ∧
      streamPtr B1 (s.getReg .x14) = streamPtr s (s.getReg .x14) ∧
      streamLen B1 (s.getReg .x14) = streamLen s (s.getReg .x14) := by
  have hb := bounds hpre
  have hTi := hpre.self
  have hok := hTi.ok
  have hP := Region.bounds hok.self
  have hQ := Region.bounds hok.proof
  simp only [transcriptSize] at hP
  have hTS := hTi.stack
  have hPS := hTi.proofStack
  have hfree := hTi.free
  have hpfree := hTi.proofFree
  simp only [Outside] at hfree hpfree
  have hmB := hctx.mono
  have hH := hctx.heap.hi
  exact (transcriptOk_frame hctx.frame hok
    (fun i hi hX ↦ by
      rcases hX with (hX | hX | hX) | hX
      · addr_omega [hX, hi, hP]
      · addr_omega [hX, hi, hP, hTS, hb]
      · addr_omega [hX, hi, hP, hfree.2]
      · simp only [Fresh] at hX; addr_omega [hX, hi, hP, hfree.1, hmB, hH])
    (fun i hi hX ↦ by
      rcases hX with (hX | hX | hX) | hX
      · addr_omega [hX, hi, hQ, hok.apart.1]
      · addr_omega [hX, hi, hQ, hPS.1, hb]
      · addr_omega [hX, hi, hQ, hpfree.2]
      · simp only [Fresh] at hX; addr_omega [hX, hi, hQ, hpfree.1, hmB, hH])).2

theorem trap : Image.code.fetch 0x80009b90 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- The slices, unchanged from entry to `B`. -/
theorem slices_frame {s B : MachineState} (hpre : RingSwitchPre s) (hm : heapNext s ≤ heapNext B)
    (hH : HeapOk B) (hf : DFrame s B fun a ↦ W0 s a ∨ Fresh s B a) :
    eListAt B (s.getReg .x12) (nS s) = eListAt s (s.getReg .x12) (nS s) := by
  have hb := bounds hpre
  have hsl := hpre.slices
  have hR := hsl.region
  have hS := hsl.stack
  have hF := hsl.free
  have hsp := hpre.slicesSponge
  have hHi := hH.hi
  simp only [Outside] at hF
  rcases hR with h0 | hR
  · simp only [nS]; rw [show (s.getReg .x13).toNat = 0 by omega]; rfl
  have hRb := Region.bounds hR
  refine hf.eList (fun x hx hW ↦ ?_) (Or.inr (by simp only [nS]; addr_omega [hRb]))
  simp only [nS] at hx
  rcases hW with (hW | hW | hW) | hW
  · addr_omega [hx, hW, hsp]
  · addr_omega [hx, hW, hS, hb]
  · addr_omega [hx, hW, hF.2]
  · simp only [Fresh] at hW; addr_omega [hx, hW, hF.1, hm, hHi]

end Rv64Verifier.Proofs.Pcs.RingSwitch
