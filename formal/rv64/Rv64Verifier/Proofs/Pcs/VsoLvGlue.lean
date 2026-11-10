import Rv64Verifier.Proofs.Pcs.VsoLvGlueNext

/-!
# `verify_stacked_opening`'s glue, whole

`0x8000b650` enters the loop with no claim glued (`gentry`); each pending claim takes the loop once
(`gstep`), the last one leaving at `0x8000b510`. **`glueSpec`**: `GlueSpec` from `E::mul`,
`memcpy` and `grow_one`'s contracts.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem mul_shift_add {a : Word} {c d : ℕ} (hc : c < 2 ^ 64) (hd : d < 2 ^ 64)
    (h : (c + d) * a.toNat < 2 ^ 64) :
    a * BitVec.ofNat 64 c + a * BitVec.ofNat 64 d = BitVec.ofNat 64 ((c + d) * a.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hd]
  rw [Nat.mod_eq_of_lt (show a.toNat * c < 2 ^ 64 by nlinarith),
    Nat.mod_eq_of_lt (show a.toNat * d < 2 ^ 64 by nlinarith),
    Nat.mod_eq_of_lt (show a.toNat * c + a.toNat * d < 2 ^ 64 by nlinarith),
    Nat.mod_eq_of_lt h]
  ring

/-- **Into the glue**: `0x8000b650` to the loop's head, no claim glued. -/
theorem gentry {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} (hpre : VsoPre s)
    (hg : GlueIn s g lam Wl pend) :
    ∃ u, Reaches Image.code g u ∧ GInv s g lam Wl pend 0 u ∧ u.pc = 0x8000b6b4 ∧
      u.getReg .x18 = pAddr g s 0 := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hn := pend_len hg.pnd
  obtain ⟨-, -, hPn⟩ := hg.pbuf
  have hgh := hg.heap.hi
  simp only [heapEnd] at hgh
  obtain ⟨u, r, h⟩ := Sym.BlockSpec.reaches b8000b650_spec hg.pc (by
    rv_eval [hg.sp]; and_intros <;> valid_access hst.valid [hb])
  have k := b8000b650_keeps h
  have m := b8000b650_mem_same h
  have hlen := congrArg List.length hg.glued.2.1
  simp only [gluedListAt, List.length_map, List.length_range] at hlen
  have hm24 : 24 * (g.getReg .x23).toNat < 2 ^ 64 := by
    rcases hg.quad.2.2 with h0 | h0 <;> omega
  refine ⟨u, r, {
    sp := by rw [k .x2 (by decide), hg.sp]
    regs := fun q hq ↦ k q (by revert hq; decide +revert)
    x20 := by rw [b8000b650_x20 h, hg.sp]; congr 1; rv_eval []
    x24 := by
      rw [b8000b650_x24 h, hg.x18, hg.x22, show (64 : Word) = BitVec.ofNat 64 64 from rfl,
        show (16 : Word) = BitVec.ofNat 64 16 from rfl, mul_shift_add (by decide) (by decide)
          (by rw [hn]; omega), hn]
    x27 := by
      rw [b8000b650_x27 h, show (16 : Word) = BitVec.ofNat 64 16 from rfl,
        show (8 : Word) = BitVec.ofNat 64 8 from rfl, mul_shift_add (by decide) (by decide)
          (by omega), hg.sp, show s.getReg .x2 - 1040 + (144 : Word) = s.getReg .x2 - 896 by
          rv_eval []]
    inv := by rw [m]; exact Inv.same' hg.inv m (by rw [k .x2 (by decide)])
    heap := ⟨by simp only [heapNext, m]; exact hg.heap.lo, by simp only [heapNext, m]; exact hg.heap.hi⟩
    mono := by simp only [heapNext, m]; exact le_rfl
    fr := DFrame.of_same m _
    sc := by rw [gacc_zero]; simp only [eAt, m]; exact hg.one
    quad := by rw [gacc_zero]; simp only [eListAt, eAt, m]; exact hg.quad.1
    gv := vecOk_of_eq hg.glued.1 (m _) (m _) (m _) (by simp only [heapNext, m]; exact le_rfl)
    glen := by
      rw [show vecLen u (s.getReg .x2 - 664) = vecLen g (s.getReg .x2 - 664) from m _, hlen]
      omega
    gl := by
      rw [gacc_zero]
      have e := hg.glued.2.1
      simp only [gluedListAt, gluedAt, weightAt, vecEs, vecWords, eListAt, eAt, vecPtr, vecLen,
        readWords_eq_map] at e ⊢
      simpa only [m] using e
    gbuf := Or.inl ⟨m _, m _⟩
    bufs := fun j hj y hy ↦ by
      refine Or.inr (Or.inr ⟨j, by rwa [show vecLen u (s.getReg .x2 - 664) =
        vecLen g (s.getReg .x2 - 664) from m _] at hj, ?_⟩)
      simp only [InBufs, gAddr, vecPtr, vecLen, m] at hy ⊢
      exact hy
    aligned := fun j hj ↦ by
      have h := hg.galigned j (by rwa [show vecLen u (s.getReg .x2 - 664) =
        vecLen g (s.getReg .x2 - 664) from m _] at hj)
      simp only [WeightAligned, gAddr, vecPtr, m] at h ⊢
      exact h }, b8000b650_pc h, by rw [k .x18 (by decide), hg.x18]; simp [pAddr]⟩

/-- **One pending claim**, from the loop's head. -/
theorem gstep (hM : MulSpec) (hMc : Runtime.MemcpySpec 0x800126e4)
    (hG : GrowOneFreshSpec 0x8000db78 88 8) {s g : MachineState} {lam : E}
    {Wl : Model.Pcs.WhirLocals} {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ}
    {u : MachineState} (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend)
    (hu : GInv s g lam Wl pend i u) (hpc : u.pc = 0x8000b6b4) (hx18 : u.getReg .x18 = pAddr g s i)
    (hi : i < pend.length) :
    ∃ z, Reaches Image.code u z ∧ (Dead Image.code z ∨ (GInv s g lam Wl pend (i + 1) z ∧
      ((i + 1 < pend.length ∧ z.pc = 0x8000b6b4 ∧ z.getReg .x18 = pAddr g s (i + 1)) ∨
        (i + 1 = pend.length ∧ z.pc = 0x8000b510)))) := by
  obtain ⟨t, r1, h1⟩ := gfront hM hpre hg hu hpc hx18 hi
  rcases h1 with hd | h1
  · exact ⟨t, r1, Or.inl hd⟩
  obtain ⟨w7, r2, h2⟩ := gstage7 hpre hg hu h1
  obtain ⟨w, r3, h3⟩ := gstage hG hpre hg hu h2
  rcases h3 with hd | h3
  · exact ⟨w, r1.trans (r2.trans r3), Or.inl hd⟩
  obtain ⟨z, r4, h4⟩ := gpushA hMc hpre hg h3
  rcases h4 with hd | h4
  · exact ⟨z, r1.trans (r2.trans (r3.trans r4)), Or.inl hd⟩
  have hz := gpushB hpre hg hu hi h3 h4
  have hn := pend_len hg.pnd
  obtain ⟨-, -, hPn⟩ := hg.pbuf
  rw [hn] at hPn
  have hgh := hg.heap.hi
  simp only [heapEnd] at hgh
  have e18 : u.getReg .x18 + 80 = pAddr g s (i + 1) := by
    rw [hx18]; simp only [pAddr]; addr_omega [hPn, hi, hgh]
  refine ⟨z, r1.trans (r2.trans (r3.trans r4)), Or.inr ⟨hz, ?_⟩⟩
  by_cases hlast : i + 1 = pend.length
  · exact Or.inr ⟨hlast, h4.pc0 (by rw [e18, hu.x24]; simp only [pAddr]; rw [hlast])⟩
  · refine Or.inl ⟨by omega, h4.pc1 (by
      rw [e18, hu.x24]; simp only [pAddr]; intro he
      have := congrArg BitVec.toNat he
      addr_omega [this, hPn, hi, hgh, hlast]), by rw [h4.x18, e18]⟩

theorem gloop (hM : MulSpec) (hMc : Runtime.MemcpySpec 0x800126e4)
    (hG : GrowOneFreshSpec 0x8000db78 88 8) {s g : MachineState} {lam : E}
    {Wl : Model.Pcs.WhirLocals} {pend : List (List E × Model.Pcs.GluedWeightRust)}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) :
    ∀ k i (u : MachineState), pend.length - i = k → GInv s g lam Wl pend i u →
      u.pc = 0x8000b6b4 → u.getReg .x18 = pAddr g s i → i < pend.length →
      ∃ z, Reaches Image.code u z ∧ (Dead Image.code z ∨
        (GInv s g lam Wl pend pend.length z ∧ z.pc = 0x8000b510)) := by
  intro k
  induction k with
  | zero => intro i u hk _ _ _ hi; omega
  | succ k ih =>
    intro i u hk hu hpc hx18 hi
    obtain ⟨z, r, h⟩ := gstep hM hMc hG hpre hg hu hpc hx18 hi
    rcases h with hd | ⟨hz, ⟨hlt, hpc', hx⟩ | ⟨heq, hpc'⟩⟩
    · exact ⟨z, r, Or.inl hd⟩
    · obtain ⟨z', r', h'⟩ := ih (i + 1) z (by omega) hz hpc' hx hlt
      exact ⟨z', r.trans r', h'⟩
    · exact ⟨z, r, Or.inr ⟨heq ▸ hz, hpc'⟩⟩

/-- **The glue's contract.** -/
theorem glueSpec (hM : MulSpec) (hMc : Runtime.MemcpySpec 0x800126e4)
    (hG : GrowOneFreshSpec 0x8000db78 88 8) : GlueSpec := by
  intro s g lam Wl pend hpre hg
  obtain ⟨u, r, hu, hpc, hx18⟩ := gentry hpre hg
  obtain ⟨z, r', h⟩ := gloop hM hMc hG hpre hg pend.length 0 u (by simp) hu hpc hx18 hg.npos
  rcases h with hd | ⟨hz, hpc'⟩
  · exact ⟨z, r.trans r', Or.inl hd⟩
  refine ⟨z, r.trans r', Or.inr {
    pc := hpc'
    sp := hz.sp
    regs := fun q hq ↦ hz.regs q (by revert hq; decide +revert)
    inv := hz.inv
    heap := hz.heap
    mono := hz.mono
    fr := hz.fr
    quad := by rw [hz.quad, glue_eq]
    glued := ⟨hz.gv, by rw [hz.gl, glue_eq], hz.gbuf⟩
    bufs := hz.bufs
    aligned := hz.aligned }⟩

end Rv64Verifier.Proofs.Pcs.Vso
