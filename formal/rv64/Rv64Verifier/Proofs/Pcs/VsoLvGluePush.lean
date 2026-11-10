import Rv64Verifier.Proofs.Pcs.VsoLvGlueGrow

/-!
# `verify_stacked_opening`'s glue: the glued claim pushed

From `0x8000b67c` (`GAt67`): `memcpy` of the staged claim to `glued`'s next slot, `fold_start`
stored, the length counted (`0x8000b6a4`), to the next pending claim or the exit (`GEnd`,
`gpushA`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `glued`'s next slot at `w`. -/
@[rv_addr] def gDest (s u w : MachineState) : Word :=
  vecPtr w (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * (vecLen u (s.getReg .x2 - 664)).toNat)

/-- After `0x8000b6a4`, the staged claim at `gDest`, from `w`. -/
structure GEnd (s u w z : MachineState) : Prop where
  sp : z.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ r ∈ [Reg.x9, .x20, .x23, .x24, .x25, .x26, .x27], z.getReg r = u.getReg r
  x18 : z.getReg .x18 = u.getReg .x18 + 80
  inv : InvR s z (z.getMem nextAddr)
  nx : z.getMem nextAddr = w.getMem nextAddr
  fr : DFrame w z fun a ↦ Within a (gDest s u w) 88 ∨ Within a (s.getReg .x2 - 648) 8 ∨
    Within a (s.getReg .x2 - 2464) 1424
  words : ∀ k < 10, z.getMem (gDest s u w + BitVec.ofNat 64 (8 * k)) =
    w.getMem (s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * k))
  fold : z.getMem (gDest s u w + 80) = u.getReg .x20
  len : vecLen z (s.getReg .x2 - 664) = vecLen u (s.getReg .x2 - 664) + 1
  pc0 : u.getReg .x18 + 80 = u.getReg .x24 → z.pc = 0x8000b510
  pc1 : u.getReg .x18 + 80 ≠ u.getReg .x24 → z.pc = 0x8000b6b4

/-- `gDest`'s slot lies in `glued`'s buffer. -/
theorem GAt67.dest {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u w : MachineState}
    (hw : GAt67 s g lam Wl pend i u w) :
    (vecPtr w (s.getReg .x2 - 664)).toNat % 8 = 0 ∧
    heapStart ≤ (vecPtr w (s.getReg .x2 - 664)).toNat ∧
    (gDest s u w).toNat = (vecPtr w (s.getReg .x2 - 664)).toNat +
      88 * (vecLen u (s.getReg .x2 - 664)).toNat ∧
    (gDest s u w).toNat + 88 ≤ (vecPtr w (s.getReg .x2 - 664)).toNat +
      (vecCap w (s.getReg .x2 - 664)).toNat * 88 ∧
    (vecPtr w (s.getReg .x2 - 664)).toNat + (vecCap w (s.getReg .x2 - 664)).toNat * 88 ≤
      heapNext w := by
  have hraw := hw.gv.raw
  simp only [RawVecOk, Buf] at hraw
  have hr := hw.room
  have hh := hw.heap.hi
  simp only [heapEnd] at hh
  rcases hraw.2 with h0 | h0
  · omega
  have e : (gDest s u w).toNat = (vecPtr w (s.getReg .x2 - 664)).toNat +
      88 * (vecLen u (s.getReg .x2 - 664)).toNat := by
    simp only [gDest]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact ⟨hraw.1, h0.1, e, by omega, h0.2⟩

/-- `glued`'s buffer lies above the entry's heap. -/
theorem GAt67.lo {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u w : MachineState}
    (hg : GlueIn s g lam Wl pend) (hw : GAt67 s g lam Wl pend i u w) :
    heapNext s ≤ (vecPtr w (s.getReg .x2 - 664)).toNat := by
  have hr := hw.room
  have hsg : heapNext s ≤ heapNext g := hg.inv.mono
  rcases hw.gbuf with ⟨e1, e2⟩ | h0
  · rw [e1]
    rcases hg.glued.2.2 with h1 | h1
    · rw [e2, h1] at hr; simp at hr
    · exact h1
  · simp only [NewBuf] at h0
    rcases h0.2 with h1 | h1
    · omega
    · omega

/-- **The claim pushed**, from `0x8000b67c` to `0x8000b6a4`'s exit. -/
theorem gpushA (hMc : Runtime.MemcpySpec 0x800126e4) {s g : MachineState} {lam : E}
    {Wl : Model.Pcs.WhirLocals} {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ}
    {u w : MachineState} (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend)
    (hw : GAt67 s g lam Wl pend i u w) :
    ∃ z, Reaches Image.code w z ∧ (Dead Image.code z ∨ GEnd s u w z) := by
  have hps := hw.lo hg
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hp8, hp0, hde, hd88, hdc⟩ := hw.dest
  have hwh := hw.heap.hi
  simp only [heapEnd] at hwh
  simp only [heapStart] at hp0
  have hsw : heapNext s ≤ heapNext w := hw.inv.mono
  have hsp := hw.sp
  -- `0x8000b67c`
  obtain ⟨w1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b67c_spec hw.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have k1 := b8000b67c_keeps h1
  have m1 := b8000b67c_mem_same h1
  have hL88 : 88 * (vecLen u (s.getReg .x2 - 664)).toNat < 2 ^ 64 := by omega
  have x10₁ : w1.getReg .x10 = gDest s u w := by
    rw [b8000b67c_x10 h1, hsp, show s.getReg .x2 - 1040 + 384 = s.getReg .x2 - 664 + 8 by
      rv_eval [], hw.x8]
    simp only [gDest, vecPtr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (88 : Word).toNat = 88 from rfl]
    omega
  have sp1 : w1.getReg .x2 = s.getReg .x2 - 1040 := by rw [k1 .x2 (by decide), hsp]
  obtain ⟨w2, r2, h2⟩ := callMemcpy80 hMc hpre (b8000b67c_pc h1) sp1 x10₁
    (by rw [b8000b67c_x11 h1, hsp]; rv_eval []) (b8000b67c_x12 h1)
    ⟨by omega, by simp only [heapEnd]; omega⟩
  rcases h2 with hd | ⟨hpc2, hpres2, hbytes2, hfr2⟩
  · exact ⟨w2, r1.trans r2, Or.inl hd⟩
  have sp2 : w2.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres2 .x2 (by decide), sp1]
  have x21₂ : w2.getReg .x21 = gDest s u w := by rw [hpres2 .x21 (by decide), b8000b67c_x21 h1,
    ← b8000b67c_x10 h1, x10₁]
  have inv1 : InvR s w1 (w1.getMem nextAddr) := by
    rw [m1]; exact Inv.same' hw.inv m1 (by rw [sp1, hsp])
  obtain ⟨nx2, inv2⟩ := invR_step hpre inv1 ⟨by simp only [heapNext, m1]; exact hw.heap.lo,
    by simp only [heapNext, m1]; exact hw.heap.hi⟩ hfr2 (fun a ha ↦ by
      rcases ha with ha | ha
      · simp only [Within] at ha
        refine Or.inr ⟨by omega, ?_⟩
        rw [show heapNext w1 = heapNext w by simp only [heapNext, m1]]; omega
      · exact Or.inl (by addr_omega [ha, hb])) (by rw [sp2, sp1])
  -- `0x8000b6a4`
  obtain ⟨z, r3, h3⟩ := Sym.BlockSpec.reaches b8000b6a4_spec (by
    rw [hpc2, returnAddress_eq, b8000b67c_x1 h1]; decide) (by
    rv_eval [sp2, x21₂]
    and_intros
    · valid_access hst.valid [hb]
    · exact Region.valid (heap_region (a := gDest s u w + 80) (n := 8) (by addr_omega [hde, hp0, hd88, hdc, hwh])
        (by simp only [heapEnd]; addr_omega [hde, hd88, hdc, hwh]) (by addr_omega [hde, hp8, hd88, hdc, hwh]))
        (by addr_omega []) (by addr_omega []) (by addr_omega [hde, hp8, hd88, hdc, hwh])
    · addr_omega [hb, hde, hdc, hwh, hd88])
  have k3 := b8000b6a4_keeps h3
  have f3 : DFrame w2 z fun a ↦ Within a (gDest s u w + 80) 8 ∨ Within a (s.getReg .x2 - 648) 8 :=
    (holds_dframe h3).mono fun a ⟨k, hk, hw'⟩ ↦ by
      simp only [b8000b6a4, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp2, x21₂] at hw' <;> first
        | exact Or.inr (by addr_omega [hw', hb])
        | exact Or.inl (by addr_omega [hw', hde, hd88, hdc, hwh])
  have sp3 : z.getReg .x2 = s.getReg .x2 - 1040 := by rw [k3 .x2 (by decide), sp2]
  have hn2 : heapNext w2 = heapNext w := by simp only [heapNext, nx2, m1]
  obtain ⟨nx3, inv3⟩ := invR_step hpre inv2 ⟨by rw [hn2]; exact hw.heap.lo,
    by rw [hn2]; exact hw.heap.hi⟩ f3 (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr ⟨by addr_omega [ha, hde, hps, hd88, hdc, hwh], by
          rw [hn2]; addr_omega [ha, hde, hd88, hdc, hwh]⟩
      · exact Or.inl (by addr_omega [ha, hb])) (by rw [sp3, sp2])
  have hx8 : w2.getReg .x8 = vecLen u (s.getReg .x2 - 664) := by
    rw [hpres2 .x8 (by decide), k1 .x8 (by decide), hw.x8]
  have hreg (r : Reg) (hr : r ∈ [Reg.x9, .x20, .x23, .x24, .x25, .x26, .x27]) :
      w2.getReg r = u.getReg r := by
    rw [hpres2 r (by revert hr; decide +revert), k1 r (by revert hr; decide +revert),
      hw.regs r (by simp only [ZK]; revert hr; decide +revert)]
  have hx18 : w2.getReg .x18 = u.getReg .x18 + 80 := by
    rw [hpres2 .x18 (by decide), b8000b67c_x18 h1, hw.regs .x18 (by decide)]
  refine ⟨z, r1.trans (r2.trans r3), Or.inr {
    sp := sp3
    regs := fun r hr ↦ by
      rw [k3 r (by revert hr; decide +revert)]; exact hreg r hr
    x18 := by rw [k3 .x18 (by decide), hx18]
    inv := inv3
    nx := by rw [nx3, nx2, m1]
    fr := ((DFrame.of_same m1 _).trans hfr2 fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; omega)
      · exact Or.inr (Or.inr (by addr_omega [ha, hb]))).trans f3 fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl (by addr_omega [ha, hde, hd88, hdc, hwh])
        · exact Or.inr (Or.inl ha)
    words := fun k hk ↦ by
      rw [f3 _ fun j hj hx ↦ by
          rcases hx with hx | hx
          · addr_omega [hx, hj, hk, hde, hd88, hdc, hwh, hb]
          · addr_omega [hx, hj, hk, hde, hd88, hdc, hwh, hb],
        getMem_eq_of_bytesAt hbytes2 (by omega) (by addr_omega [hb]) (by omega) (by omega), m1]
    fold := by
      have e := b8000b6a4_m_x21_80 h3
      rw [x21₂] at e
      rw [e, hreg .x20 (by decide)]
    len := by
      have e := b8000b6a4_m_x2_392 h3
      rw [sp2, show s.getReg .x2 - 1040 + 392 = s.getReg .x2 - 664 + 16 by rv_eval [], hx8] at e
      exact e
    pc0 := fun h ↦ b8000b6a4_pc_taken h3 (by rw [hx18, hreg .x24 (by decide)]; exact h)
    pc1 := fun h ↦ b8000b6a4_pc_not_taken h3 (by rw [hx18, hreg .x24 (by decide)]; exact h) }⟩

end Rv64Verifier.Proofs.Pcs.Vso
