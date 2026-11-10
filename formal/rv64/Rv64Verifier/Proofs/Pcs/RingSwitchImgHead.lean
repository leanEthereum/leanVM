import Rv64Verifier.Proofs.Pcs.RingSwitchToImg

/-!
# `ring_switch`: the images loop's states and head

`IHead i` is `0x80009a24` before value `i`; `IStage i j` is `0x80009a90` before stage `j` of it,
the value in `s9`, `s0`, `s2`; `IPush i` is `0x800099f4`, its six stages done; `IExit` is
`0x80009b00`, the `n` images in `I`.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Value `i` of `s`. -/
def sv (s : MachineState) (i : Nat) : E := eAt s (s.getReg .x12 + BitVec.ofNat 64 (24 * i))

/-- Registers fixed through the images loop. -/
structure IRegs (s u : MachineState) : Prop where
  x9 : u.getReg .x9 = 1
  x19 : u.getReg .x19 = 1
  x27 : u.getReg .x27 = s.getReg .x2 - 192

/-- At `0x80009a24`, before value `i`. -/
structure IHead (s B2 u : MachineState) (I : Word) (ch : List E) (nx : Word) (i : Nat) : Prop
    extends IRegs s u where
  ph : Ph B2 u (w2 s I) nx
  pc : u.pc = 0x80009a24
  lt : i < nS s
  x21 : u.getReg .x21 = BitVec.ofNat 64 i
  x26 : u.getReg .x26 = BitVec.ofNat 64 i
  buf : ∀ l < i, eAt u (I + BitVec.ofNat 64 (24 * l)) = ringMapRust (sv s l) ch

/-- At `0x80009a90`, before stage `j` of value `i`. -/
structure IStage (s B2 u : MachineState) (chP I : Word) (ch : List E) (nx : Word) (i j : Nat) :
    Prop extends IRegs s u where
  ph : Ph B2 u (w2 s I) nx
  pc : u.pc = 0x80009a90
  lt : i < nS s
  ltj : j < 6
  x21 : u.getReg .x21 = BitVec.ofNat 64 i
  x26 : u.getReg .x26 = BitVec.ofNat 64 i
  x20 : u.getReg .x20 = BitVec.ofNat 64 (7 - j)
  x10 : u.getReg .x10 = s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * j)
  x22 : u.getReg .x22 = chP + BitVec.ofNat 64 (24 * j)
  val : Model.limbs (img ch (sv s i) j) = (u.getReg .x25, u.getReg .x8, u.getReg .x18)
  shifts : ∀ i < 6, u.getMem (s.getReg .x2 - 192 + BitVec.ofNat 64 (8 * i)) = shiftW i
  buf : ∀ l < i, eAt u (I + BitVec.ofNat 64 (24 * l)) = ringMapRust (sv s l) ch

/-- At `0x800099f4`: value `i` mapped. -/
structure IPush (s B2 u : MachineState) (I : Word) (ch : List E) (nx : Word) (i : Nat) : Prop
    extends IRegs s u where
  ph : Ph B2 u (w2 s I) nx
  pc : u.pc = 0x800099f4
  lt : i < nS s
  x21 : u.getReg .x21 = BitVec.ofNat 64 i
  x26 : u.getReg .x26 = BitVec.ofNat 64 i
  val : Model.limbs (img ch (sv s i) 6) = (u.getReg .x25, u.getReg .x8, u.getReg .x18)
  buf : ∀ l < i, eAt u (I + BitVec.ofNat 64 (24 * l)) = ringMapRust (sv s l) ch

/-- At `0x80009b00`: the `n` images in `I`. -/
structure IExit (s B2 u : MachineState) (I : Word) (ch : List E) (nx : Word) : Prop where
  ph : Ph B2 u (w2 s I) nx
  pc : u.pc = 0x80009b00
  x21 : u.getReg .x21 = BitVec.ofNat 64 (nS s)
  buf : ∀ l < nS s, eAt u (I + BitVec.ofNat 64 (24 * l)) = ringMapRust (sv s l) ch

/-! ## Words the images loop never writes -/

section
variable {s B2 u : MachineState} {C chP I nx : Word} {ch : List E}

theorem keepF2 (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) (h : Ph B2 u (w2 s I) nx)
    {a : Word} (h1 : (s.getReg .x2).toNat - 464 ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 288 ∨
      (s.getReg .x2).toNat - 104 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat) :
    u.getMem a = B2.getMem a := by
  have hb := bounds hpre
  have hH := hctx.heap.hi
  have hI := hctx.iR
  have hfit := h.fits
  refine DFrame.word h.mem (fun x hx hW ↦ ?_) (by addr_omega [h2, hb])
  rcases hW with (hW | hW) | hW | hW | hW
  · addr_omega [hW, hx, h1, h2, hb]
  · simp only [nS] at hI hW
    rcases hI with hI | hI
    · simp only [hI] at hW; addr_omega [hW]
    · addr_omega [hW, hx, h1, hI.2, hH, hb]
  · simp only [stackLo, hctx.sp] at hW; addr_omega [hW, hx, h1, h2, hb]
  · addr_omega [hW, hx, h1, hb]
  · addr_omega [hW.2, hx, h1, hfit, hb]

theorem keepH2 (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) (h : Ph B2 u (w2 s I) nx)
    {a : Word} (h1 : a.toNat + 8 ≤ C.toNat + 1536) : u.getMem a = B2.getMem a := by
  have hb := bounds hpre
  have hH := hctx.heap.hi
  have hC := hctx.cHi
  have hI := hctx.iR
  refine DFrame.word h.mem (fun x hx hW ↦ ?_) (by addr_omega [h1, hC, hH])
  rcases hW with (hW | hW) | hW | hW | hW
  · addr_omega [hW, hx, h1, hC, hH, hb]
  · simp only [nS] at hI hW
    rcases hI with hI | hI
    · simp only [hI] at hW; addr_omega [hW]
    · addr_omega [hW, hx, h1, hI.1]
  · simp only [stackLo, hctx.sp] at hW; addr_omega [hW, hx, h1, hC, hH, hb]
  · addr_omega [hW, hx, h1, hC, hH]
  · addr_omega [hW.1, hx, h1, hC]

theorem keepCh2 (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) (h : Ph B2 u (w2 s I) nx)
    {j : Nat} (hj : j < 6) : eAt u (chP + BitVec.ofNat 64 (24 * j)) = ch.getD j 0 := by
  have hcC := hctx.chC
  have hC := hctx.cHi
  have hH := hctx.heap.hi
  have e : ch.getD j 0 = eAt B2 (chP + BitVec.ofNat 64 (24 * j)) := by
    rw [← hctx.chs, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hj), eListAt_getElem]
  rw [e]
  unfold eAt
  rw [keepH2 hpre hctx h (by addr_omega [hj, hcC, hC, hH]),
    keepH2 hpre hctx h (by addr_omega [hj, hcC, hC, hH]),
    keepH2 hpre hctx h (by addr_omega [hj, hcC, hC, hH])]

/-- Value `i` of `s`, unchanged. -/
theorem keepSl (hpre : RingSwitchPre s) (hctx : Ctx2 s B2 C chP I ch) (h : Ph B2 u (w2 s I) nx)
    {i : Nat} (hi : i < nS s) : eAt u (s.getReg .x12 + BitVec.ofNat 64 (24 * i)) = sv s i := by
  have hb := bounds hpre
  have hsl := hpre.slices
  have hR := hsl.region.resolve_left (by simp only [nS] at hi; omega)
  have hRb := Region.bounds hR
  have hS := hsl.stack
  have hF := hsl.free
  simp only [Outside] at hF
  have hH := hctx.heap.hi
  have hI := hctx.iR
  have hcL := hctx.chLo
  have hcC := hctx.chC
  have hfit := h.fits
  have hmo := hctx.mono
  simp only [nS] at hi hI
  have e : sv s i = eAt B2 (s.getReg .x12 + BitVec.ofNat 64 (24 * i)) := by
    have := congrArg (fun l ↦ l.getD i 0) hctx.slices
    rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hi),
      List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hi), eListAt_getElem,
      eListAt_getElem] at this
    exact this.symm
  rw [e]
  refine h.mem.eAt' (fun x hx hW ↦ ?_) (by addr_omega [hRb, hi])
  rcases hW with (hW | hW) | hW | hW | hW
  · addr_omega [hW, hx, hi, hRb, hS, hb]
  · rcases hI with hI | hI
    · omega
    · rcases hF.1 with hF1 | hF1
      · addr_omega [hW, hx, hi, hRb, hF1, hI.1, hcL, hcC]
      · addr_omega [hW, hx, hi, hRb, hF1, hI.2, hH]
  · simp only [stackLo, hctx.sp] at hW; addr_omega [hW, hx, hi, hRb, hS, hb]
  · addr_omega [hW, hx, hi, hRb, hF.2]
  · rcases hF.1 with hF1 | hF1
    · addr_omega [hW.1, hx, hi, hRb, hF1, hmo]
    · addr_omega [hW.2, hx, hi, hRb, hF1, hfit]

end

end Rv64Verifier.Proofs.Pcs.RingSwitch
