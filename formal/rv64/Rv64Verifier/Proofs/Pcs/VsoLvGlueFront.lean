import Rv64Verifier.Proofs.Pcs.VsoLvGlueStep

/-!
# `verify_stacked_opening`'s glue: a pending claim's weight, scalar and intro

From `0x8000b6b4` before pending claim `i` to `0x8000b7b8` (`gfront`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem zipAddScaled_nil (c : List E) (sc : E) : Model.Pcs.zipAddScaled [] c sc = [] := by
  simp [Model.Pcs.zipAddScaled]


/-- Pending claim `i`'s doublewords, kept since `g`. -/
theorem GInv.pw {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u : MachineState}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u)
    (hi : i < pend.length) (k : ℕ) (hk : k < 10) :
    u.getMem (pAddr g s i + BitVec.ofNat 64 (8 * k)) =
      g.getMem (pAddr g s i + BitVec.ofNat 64 (8 * k)) := by
  have hn := pend_len hg.pnd
  obtain ⟨-, -, hPn⟩ := hg.pbuf
  rw [hn] at hPn
  have hgh := hg.heap.hi
  simp only [heapEnd] at hgh
  refine hu.fr _ fun j hj hw ↦ (hg.rd hpre (z := u) (Or.inl ?_)).1 hw
  rw [hn]; simp only [pAddr]; addr_omega [hPn, hi, hk, hj, hgh]

/-- A stack slot outside what the glue writes, kept since `g`. -/
theorem GInv.keepS {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u : MachineState}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u) (y : Word)
    (hy : ∀ j < 8, ¬ (Within (y + BitVec.ofNat 64 j) (s.getReg .x2 - 664) 24 ∨
      Within (y + BitVec.ofNat 64 j) (s.getReg .x2 - 464) 160 ∨
      Within (y + BitVec.ofNat 64 j) (s.getReg .x2 - 160) 24 ∨
      Within (y + BitVec.ofNat 64 j) (s.getReg .x2 - 2464) 1424))
    (hy2 : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
    u.getMem y = g.getMem y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  refine hu.fr y fun j hj hw ↦ ?_
  rcases GlueW.split hg hu.heap.hi hw with h | h | h | h | h | h
  · exact hy j hj (Or.inl h)
  · exact hy j hj (Or.inr (Or.inl h))
  · exact hy j hj (Or.inr (Or.inr (Or.inl h)))
  · exact hy j hj (Or.inr (Or.inr (Or.inr h)))
  · addr_omega [h, hj, hy2, hb, hnx]
  · simp only [heapEnd] at h; addr_omega [h, hj, hy2, hb]

/-- At `E::mul`'s entry from `0x8000b6c0`, claim `i`'s weight copied to `S - 464`, `lam` to
`S - 160`. -/
structure GAt2 (s g : MachineState) (lam : E) (i : ℕ) (u t : MachineState) : Prop where
  pc : t.pc = 0x80008c48
  sp : t.getReg .x2 = s.getReg .x2 - 1040
  x1 : t.getReg .x1 = 0x8000b72c
  x10 : t.getReg .x10 = s.getReg .x2 - 384
  x11 : t.getReg .x11 = s.getReg .x2 - 408
  x12 : t.getReg .x12 = s.getReg .x2 - 160
  regs : ∀ r ∈ ZK, t.getReg r = u.getReg r
  x8 : t.getReg .x8 = vecLen g (pAddr g s i)
  x19 : t.getReg .x19 = vecPtr g (pAddr g s i)
  inv : InvR s t (t.getMem nextAddr)
  nx : t.getMem nextAddr = u.getMem nextAddr
  fr : DFrame u t fun a ↦ Within a (s.getReg .x2 - 464) 56 ∨ Within a (s.getReg .x2 - 160) 24
  wt : WordsEq t (s.getReg .x2 - 464) g (pAddr g s i + 24) 7
  lam : eAt t (s.getReg .x2 - 160) = lam

theorem gfrontA {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u : MachineState}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u)
    (hpc : u.pc = 0x8000b6b4) (hx18 : u.getReg .x18 = pAddr g s i) (hi : i < pend.length) :
    ∃ t, Reaches Image.code u t ∧ GAt2 s g lam i u t := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hu.sp
  have hn := pend_len hg.pnd
  obtain ⟨hP8, hP0, hPn⟩ := hg.pbuf
  rw [hn] at hPn
  have hgh := hg.heap.hi
  simp only [heapEnd] at hgh
  simp only [heapStart] at hP0
  have hRP : Region (vecPtr g (s.getReg .x2 - 616)) (80 * pend.length) :=
    heap_region (by omega) (by simp only [heapEnd]; omega) hP8
  have pw := hu.pw hpre hg hi
  have keepS := hu.keepS hpre hg
  have hIv := hg.intro i (by rw [hn]; exact hi)
  have hraw := hIv.raw
  simp only [RawVecOk, Buf] at hraw
  have hcap : vecCap g (pAddr g s i) ≠ 0xffffffffffffffff := by
    intro he
    rw [he, show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl] at hraw
    omega
  -- `0x8000b6b4`
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b6b4_spec hpc (by
    rv_eval [hx18]
    exact Region.valid hRP (by simp only [pAddr]; addr_omega [hPn, hi, hgh])
      (by simp only [pAddr]; addr_omega [hPn, hi, hgh])
      (by simp only [pAddr]; addr_omega [hP8, hPn, hi, hgh]))
  have hpc1 := b8000b6b4_pc_not_taken h1 (by
    rw [hx18, show pAddr g s i = pAddr g s i + BitVec.ofNat 64 (8 * 0) by simp, pw 0 (by decide)]
    simpa [vecCap] using hcap)
  have k1 := b8000b6b4_keeps h1
  have m1 := b8000b6b4_mem_same h1
  have hm1 (a : Word) : t1.getMem a = u.getMem a := m1 a
  have sp1 : t1.getReg .x2 = s.getReg .x2 - 1040 := by rw [k1 .x2 (by decide), hsp]
  have x18₁ : t1.getReg .x18 = pAddr g s i := by rw [k1 .x18 (by decide), hx18]
  -- `0x8000b6c0`
  obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000b6c0_spec hpc1 (by
    rv_eval [sp1, x18₁]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRP (by simp only [pAddr]; addr_omega [hPn, hi, hgh])
          (by simp only [pAddr]; addr_omega [hPn, hi, hgh])
          (by simp only [pAddr]; addr_omega [hP8, hPn, hi, hgh])
      | (simp only [pAddr]; addr_omega [hb, hPn, hi, hgh]))
  have k2 := b8000b6c0_keeps h2
  have X2 : DFrame t1 t2 fun a ↦ Within a (s.getReg .x2 - 464) 56 ∨ Within a (s.getReg .x2 - 160) 24 :=
    (holds_dframe h2).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000b6c0, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rv_eval [sp1] at hw <;> first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (by addr_omega [hw, hb])
  have sp2 : t2.getReg .x2 = s.getReg .x2 - 1040 := by rw [k2 .x2 (by decide), sp1]
  -- the weight copied, `lam` copied
  have wt2 : WordsEq t2 (s.getReg .x2 - 464) g (pAddr g s i + 24) 7 := by
    intro k hk
    interval_cases k
    · have e := b8000b6c0_m_x2_576 h2
      rw [sp1, x18₁] at e
      rw [show s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 0) = s.getReg .x2 - 1040 + 576 by
        addr_omega [hb], e, hm1,
        show pAddr g s i + 24 + BitVec.ofNat 64 (8 * 0) = pAddr g s i + BitVec.ofNat 64 (8 * 3) by
          rw [BitVec.add_assoc]; rfl,
        show pAddr g s i + 24 = pAddr g s i + BitVec.ofNat 64 (8 * 3) from rfl]
      exact pw 3 (by decide)
    · have e := b8000b6c0_m_x2_584 h2
      rw [sp1, x18₁] at e
      rw [show s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 1) = s.getReg .x2 - 1040 + 584 by
        addr_omega [hb], e, hm1,
        show pAddr g s i + 24 + BitVec.ofNat 64 (8 * 1) = pAddr g s i + BitVec.ofNat 64 (8 * 4) by
          rw [BitVec.add_assoc]; rfl,
        show pAddr g s i + 32 = pAddr g s i + BitVec.ofNat 64 (8 * 4) from rfl]
      exact pw 4 (by decide)
    · have e := b8000b6c0_m_x2_592 h2
      rw [sp1, x18₁] at e
      rw [show s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 2) = s.getReg .x2 - 1040 + 592 by
        addr_omega [hb], e, hm1,
        show pAddr g s i + 24 + BitVec.ofNat 64 (8 * 2) = pAddr g s i + BitVec.ofNat 64 (8 * 5) by
          rw [BitVec.add_assoc]; rfl,
        show pAddr g s i + 40 = pAddr g s i + BitVec.ofNat 64 (8 * 5) from rfl]
      exact pw 5 (by decide)
    · have e := b8000b6c0_m_x2_600 h2
      rw [sp1, x18₁] at e
      rw [show s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 3) = s.getReg .x2 - 1040 + 600 by
        addr_omega [hb], e, hm1,
        show pAddr g s i + 24 + BitVec.ofNat 64 (8 * 3) = pAddr g s i + BitVec.ofNat 64 (8 * 6) by
          rw [BitVec.add_assoc]; rfl,
        show pAddr g s i + 48 = pAddr g s i + BitVec.ofNat 64 (8 * 6) from rfl]
      exact pw 6 (by decide)
    · have e := b8000b6c0_m_x2_608 h2
      rw [sp1, x18₁] at e
      rw [show s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 4) = s.getReg .x2 - 1040 + 608 by
        addr_omega [hb], e, hm1,
        show pAddr g s i + 24 + BitVec.ofNat 64 (8 * 4) = pAddr g s i + BitVec.ofNat 64 (8 * 7) by
          rw [BitVec.add_assoc]; rfl,
        show pAddr g s i + 56 = pAddr g s i + BitVec.ofNat 64 (8 * 7) from rfl]
      exact pw 7 (by decide)
    · have e := b8000b6c0_m_x2_616 h2
      rw [sp1, x18₁] at e
      rw [show s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 5) = s.getReg .x2 - 1040 + 616 by
        addr_omega [hb], e, hm1,
        show pAddr g s i + 24 + BitVec.ofNat 64 (8 * 5) = pAddr g s i + BitVec.ofNat 64 (8 * 8) by
          rw [BitVec.add_assoc]; rfl,
        show pAddr g s i + 64 = pAddr g s i + BitVec.ofNat 64 (8 * 8) from rfl]
      exact pw 8 (by decide)
    · have e := b8000b6c0_m_x2_624 h2
      rw [sp1, x18₁] at e
      rw [show s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 6) = s.getReg .x2 - 1040 + 624 by
        addr_omega [hb], e, hm1,
        show pAddr g s i + 24 + BitVec.ofNat 64 (8 * 6) = pAddr g s i + BitVec.ofNat 64 (8 * 9) by
          rw [BitVec.add_assoc]; rfl,
        show pAddr g s i + 72 = pAddr g s i + BitVec.ofNat 64 (8 * 9) from rfl]
      exact pw 9 (by decide)
  have hlam : eAt t2 (s.getReg .x2 - 160) = lam := by
    apply eAt_eq_of_limbs
    rw [← hg.lam]
    have e0 := b8000b6c0_m_x2_880 h2
    have e1 := b8000b6c0_m_x2_888 h2
    have e2 := b8000b6c0_m_x2_896 h2
    rw [sp1] at e0 e1 e2
    have ks (c : ℕ) (hc : c = 976 ∨ c = 984 ∨ c = 992) :
        u.getMem (s.getReg .x2 - BitVec.ofNat 64 c) = g.getMem (s.getReg .x2 - BitVec.ofNat 64 c) :=
      keepS _ (fun j hj hw ↦ by
        rcases hc with rfl | rfl | rfl <;> rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hb])
        (by rcases hc with rfl | rfl | rfl <;> addr_omega [hb])
    rw [show s.getReg .x2 - 160 = s.getReg .x2 - 1040 + 880 by rv_eval [], e0,
      show s.getReg .x2 - 1040 + 880 + 8 = s.getReg .x2 - 1040 + 888 by rv_eval [], e1,
      show s.getReg .x2 - 1040 + 880 + 16 = s.getReg .x2 - 1040 + 896 by rv_eval [], e2, hm1, hm1, hm1,
      show s.getReg .x2 - 1040 + 64 = s.getReg .x2 - BitVec.ofNat 64 976 by rv_eval [],
      show s.getReg .x2 - 1040 + 56 = s.getReg .x2 - BitVec.ofNat 64 984 by rv_eval [],
      show s.getReg .x2 - 1040 + 48 = s.getReg .x2 - BitVec.ofNat 64 992 by rv_eval [],
      ks 976 (by decide), ks 984 (by decide), ks 992 (by decide)]
    rfl
  have Y2 : DFrame u t2 fun a ↦ Within a (s.getReg .x2 - 464) 56 ∨ Within a (s.getReg .x2 - 160) 24 :=
    (DFrame.of_same m1 _).trans X2 fun _ h ↦ h
  obtain ⟨nx2, inv2⟩ := invR_step hpre hu.inv hu.heap Y2 (fun a ha ↦ Or.inl (by
    rcases ha with ha | ha <;> addr_omega [ha, hb])) (by rw [sp2, hsp])
  exact ⟨t2, r1.trans r2, {
    pc := b8000b6c0_pc h2
    sp := sp2
    x1 := b8000b6c0_x1 h2
    x10 := by rw [b8000b6c0_x10 h2, sp1]; rv_eval []
    x11 := by rw [b8000b6c0_x11 h2, sp1]; rv_eval []
    x12 := by rw [b8000b6c0_x12 h2, sp1]; rv_eval []
    regs := fun r hr ↦ by
      rw [k2 r (by simp only [ZK] at hr; revert hr; decide +revert),
        k1 r (by simp only [ZK] at hr; revert hr; decide +revert)]
    x8 := by
      rw [b8000b6c0_x8 h2, x18₁, hm1,
        show pAddr g s i + 16 = pAddr g s i + BitVec.ofNat 64 (8 * 2) from rfl, pw 2 (by decide)]
      rfl
    x19 := by
      rw [b8000b6c0_x19 h2, x18₁, hm1,
        show pAddr g s i + 8 = pAddr g s i + BitVec.ofNat 64 (8 * 1) from rfl, pw 1 (by decide)]
      rfl
    inv := inv2
    nx := nx2
    fr := Y2
    wt := wt2
    lam := hlam }⟩

/-- At `0x8000b72c`'s exit, the scalar times `lam` at `S - 408`, `x19` the quadratic, `x12`
the intro, `x8` its length. -/
structure GAt4 (s g : MachineState) (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (i : ℕ) (u t : MachineState) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ r ∈ ZK, t.getReg r = u.getReg r
  x19 : t.getReg .x19 = g.getMem (s.getReg .x2 - 896)
  x12 : t.getReg .x12 = vecPtr g (pAddr g s i)
  x8 : t.getReg .x8 = vecLen g (pAddr g s i)
  inv : InvR s t (t.getMem nextAddr)
  heap : HeapOk t
  nx : t.getMem nextAddr = u.getMem nextAddr
  fr : DFrame u t fun a ↦ Within a (s.getReg .x2 - 464) 160 ∨
    Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x2 - 2464) 1424
  sc : eAt t (s.getReg .x2 - 408) = (gacc lam Wl pend (i + 1)).2
  wt : WordsEq t (s.getReg .x2 - 464) g (pAddr g s i + 24) 7
  pc0 : g.getReg .x23 = 0 → t.pc = 0x8000b7b8
  pc1 : g.getReg .x23 ≠ 0 → t.pc = 0x8000b750

theorem gfrontB (hM : MulSpec) {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u t2 : MachineState}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u)
    (hi : i < pend.length) (ht : GAt2 s g lam i u t2) :
    ∃ t, Reaches Image.code t2 t ∧ (Dead Image.code t ∨ GAt4 s g lam Wl pend i u t) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have sp2 := ht.sp
  obtain ⟨v, r3, hv⟩ := callMul hM hpre ht.inv ht.pc (o := s.getReg .x2 - 384)
    (a := s.getReg .x2 - 408) (b := s.getReg .x2 - 160) ht.x10 ht.x11 ht.x12
    (by addr_omega [hb]) (by addr_omega [hb])
    (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  rcases hv with hd | ⟨hpc3, hpres3, hfr3, hval3⟩
  · exact ⟨v, r3, Or.inl hd⟩
  have hpc3' : v.pc = 0x8000b72c := by rw [hpc3, returnAddress_eq, ht.x1]; decide
  have sp3 : v.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres3 .x2 (by decide), sp2]
  have hn2 : heapNext t2 = heapNext u := by simp only [heapNext, ht.nx]
  obtain ⟨nx3, inv3⟩ := invR_step hpre ht.inv ⟨by rw [hn2]; exact hu.heap.lo,
    by rw [hn2]; exact hu.heap.hi⟩ hfr3 (fun a ha ↦ Or.inl (by
      rcases ha with ha | ha <;> addr_omega [ha, hb])) (by rw [sp3, sp2])
  obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000b72c_spec hpc3' (by
    rv_eval [sp3]; and_intros <;> valid_access hst.valid [hb])
  have k4 := b8000b72c_keeps h4
  have f4 : DFrame v t4 (Within · (s.getReg .x2 - 408) 24) := by
    have := DFrame.of_memFrame (b8000b72c_frame h4 (by rw [sp3]; addr_omega [hb]))
    rwa [sp3, show s.getReg .x2 - 1040 + 632 = s.getReg .x2 - 408 by rv_eval []] at this
  have sp4 : t4.getReg .x2 = s.getReg .x2 - 1040 := by rw [k4 .x2 (by decide), sp3]
  have hn3 : heapNext v = heapNext u := by simp only [heapNext, nx3, ht.nx]
  obtain ⟨nx4, inv4⟩ := invR_step hpre inv3 ⟨by rw [hn3]; exact hu.heap.lo,
    by rw [hn3]; exact hu.heap.hi⟩ f4 (fun a ha ↦ Or.inl (by
      addr_omega [ha, hb])) (by rw [sp4, sp3])
  have hnx4 : t4.getMem nextAddr = u.getMem nextAddr := by rw [nx4, nx3, ht.nx]
  have Y4 : DFrame u t4 fun a ↦ Within a (s.getReg .x2 - 464) 160 ∨
      Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x2 - 2464) 1424 :=
    ((ht.fr.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl ha)).trans hfr3 fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inr (Or.inr (by addr_omega [ha, hb]))).trans f4 fun a ha ↦
      Or.inl (by addr_omega [ha, hb])
  have hsc4 : eAt t4 (s.getReg .x2 - 408) = (gacc lam Wl pend (i + 1)).2 := by
    rw [gacc_succ hi]
    have e : eAt t4 (s.getReg .x2 - 408) = eAt v (s.getReg .x2 - 384) := by
      apply eAt_congr
      · have := b8000b72c_m_x2_632 h4; rw [sp3] at this
        rw [show s.getReg .x2 - 408 = s.getReg .x2 - 1040 + 632 by rv_eval [], this,
          show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []]
      · have := b8000b72c_m_x2_640 h4; rw [sp3] at this
        rw [show s.getReg .x2 - 408 + 8 = s.getReg .x2 - 1040 + 640 by rv_eval [], this,
          show s.getReg .x2 - 1040 + 664 = s.getReg .x2 - 384 + 8 by rv_eval []]
      · have := b8000b72c_m_x2_648 h4; rw [sp3] at this
        rw [show s.getReg .x2 - 408 + 16 = s.getReg .x2 - 1040 + 648 by rv_eval [], this,
          show s.getReg .x2 - 1040 + 672 = s.getReg .x2 - 384 + 16 by rv_eval []]
    have e2 : eAt t2 (s.getReg .x2 - 408) = eAt u (s.getReg .x2 - 408) :=
      ht.fr.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb]
    rw [e, hval3, ht.lam, e2, hu.sc]
    rfl
  have x23v : v.getReg .x23 = g.getReg .x23 := by
    rw [hpres3 .x23 (by decide), ht.regs .x23 (by decide), hu.regs .x23 (by decide)]
  refine ⟨t4, r3.trans r4, Or.inr {
    sp := sp4
    regs := fun r hr ↦ by
      have hr' : r ∈ calleeSaved := by simp only [ZK] at hr; revert hr; decide +revert
      rw [k4 r (by simp only [ZK] at hr; revert hr; decide +revert), hpres3 r hr', ht.regs r hr]
    x19 := by
      rw [b8000b72c_x19 h4, sp3, show s.getReg .x2 - 1040 + 144 = s.getReg .x2 - 896 by rv_eval [],
        hfr3 _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb],
        ht.fr _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb]]
      exact hu.keepS hpre hg _ (fun j hj hw ↦ by
        rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hb]) (by addr_omega [hb])
    x12 := by rw [b8000b72c_x12 h4, hpres3 .x19 (by decide), ht.x19]
    x8 := by rw [k4 .x8 (by decide), hpres3 .x8 (by decide), ht.x8]
    inv := inv4
    heap := ⟨by simp only [heapNext, hnx4]; exact hu.heap.lo,
      by simp only [heapNext, hnx4]; exact hu.heap.hi⟩
    nx := hnx4
    fr := Y4
    sc := hsc4
    wt := fun k hk ↦ by
      rw [← ht.wt k hk]
      refine (f4 _ fun j hj hw ↦ ?_).trans (hfr3 _ fun j hj hw ↦ ?_)
      · addr_omega [hw, hj, hk, hb]
      · rcases hw with hw | hw <;> addr_omega [hw, hj, hk, hb]
    pc0 := fun h0 ↦ b8000b72c_pc_taken h4 (by rw [x23v, h0])
    pc1 := fun h0 ↦ b8000b72c_pc_not_taken h4 (by rw [x23v]; exact h0) }⟩

theorem gfrontC (hM : MulSpec) {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u t4 : MachineState}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u)
    (hi : i < pend.length) (ht : GAt4 s g lam Wl pend i u t4) :
    ∃ t, Reaches Image.code t4 t ∧ (Dead Image.code t ∨ GMid s g lam Wl pend i u t) := by
  have hb := bounds hpre
  have hn := pend_len hg.pnd
  have hgh := hg.heap.hi
  simp only [heapEnd] at hgh
  have hQ := hg.quad
  have hIv := hg.intro i (by rw [hn]; exact hi)
  have hraw := hIv.raw
  have hil := hIv.len
  simp only [RawVecOk, Buf] at hraw
  have hQb : (g.getReg .x23).toNat = 0 ∨ heapNext s ≤ (g.getMem (s.getReg .x2 - 896)).toNat ∧
      (g.getMem (s.getReg .x2 - 896)).toNat + 24 * (g.getReg .x23).toNat ≤ heapNext g := hQ.2.2
  have hIb : (vecPtr g (pAddr g s i)).toNat % 8 = 0 ∧ ((vecLen g (pAddr g s i)).toNat = 0 ∨
      0x20000000 ≤ (vecPtr g (pAddr g s i)).toNat ∧
      (vecPtr g (pAddr g s i)).toNat + 24 * (vecLen g (pAddr g s i)).toNat ≤ heapNext g) := by
    refine ⟨hraw.1, ?_⟩
    rcases hraw.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by simp only [heapStart] at h0; omega, by omega⟩
  have quad4 : eListAt t4 (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat =
      (gacc lam Wl pend i).1.runningQuad := by
    rw [← hu.quad]
    refine ht.fr.eListAt fun j hj hw ↦ ?_
    rcases hQb with h0 | h0
    · omega
    · rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hb, h0, hgh]
  have intro4 : eListAt t4 (vecPtr g (pAddr g s i)) (vecLen g (pAddr g s i)).toNat =
      pend[i].1 := by
    rw [pend_get hg.pnd hi]
    show _ = eListAt g _ _
    rw [ht.fr.eListAt fun j hj hw ↦ by
      rcases hIb.2 with h0 | h0
      · omega
      · rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hb, h0, hgh]]
    refine hu.fr.eListAt fun j hj hw ↦ (hg.rd hpre (z := u)
      (Or.inr (Or.inl ⟨i, by rw [hn]; exact hi, Or.inl ?_⟩))).1 hw
    rcases hIb.2 with h0 | h0
    · omega
    · addr_omega [hj, h0, hgh]
  by_cases h0 : g.getReg .x23 = 0
  · -- no coefficient to update
    have hm0 : (g.getReg .x23).toNat = 0 := by rw [h0]; rfl
    refine ⟨t4, .refl _, Or.inr {
      pc := ht.pc0 h0
      sp := ht.sp
      regs := ht.regs
      inv := ht.inv
      heap := ht.heap
      nx := ht.nx
      fr := ht.fr.mono fun a ha ↦ Or.inr ha
      sc := ht.sc
      quad := ?_
      wt := ht.wt }⟩
    rw [gacc_succ hi]
    have e0 : (gacc lam Wl pend i).1.runningQuad = [] := by
      rw [← quad4, hm0]; rfl
    show _ = Model.Pcs.zipAddScaled _ _ _
    rw [e0, zipAddScaled_nil, hm0]; rfl
  · have hm0 : (g.getReg .x23).toNat ≠ 0 := fun h ↦ h0 (BitVec.eq_of_toNat_eq h)
    obtain ⟨t5, r5, h5⟩ := Sym.BlockSpec.reaches b8000b750_spec (ht.pc1 h0) trivial
    have k5 := b8000b750_keeps h5
    have m5 := b8000b750_mem_same h5
    have hl24 : 24 * (vecLen g (pAddr g s i)).toNat < 2 ^ 64 := by
      rcases hIb.2 with h1 | h1 <;> omega
    have hq1 := hQb.resolve_left hm0
    have hmo := hu.mono
    have hn4 : heapNext t4 = heapNext u := by simp only [heapNext, ht.nx]
    have hz : ZBufs s t4 (g.getMem (s.getReg .x2 - 896)) (vecPtr g (pAddr g s i))
        (g.getReg .x23).toNat (vecLen g (pAddr g s i)).toNat := {
      q := ⟨hq1.1, by rw [hn4]; omega, hQ.2.1⟩
      i := ⟨hIb.1, by
        rcases hIb.2 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨by omega, by simp only [heapEnd]; omega⟩⟩
      ap := apart_of_forall fun y hyq hyi ↦
        (hg.reads y (Or.inr (Or.inl ⟨i, by rw [hn]; exact hi, Or.inl hyi⟩))).2.2.1 hyq
      len := hl24 }
    have hzi : ZInv s t4 t5 (g.getMem (s.getReg .x2 - 896)) (vecPtr g (pAddr g s i))
        (g.getReg .x23).toNat (vecLen g (pAddr g s i)).toNat 0 := {
      pc := b8000b750_pc h5
      sp := by rw [k5 .x2 (by decide), ht.sp]
      keep := fun r hr ↦ k5 r (by simp only [ZK] at hr; revert hr; decide +revert)
      x8 := by
        rw [b8000b750_x8 h5, ht.x8, Nat.sub_zero]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
        rw [show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
        omega
      x19 := by rw [k5 .x19 (by decide), ht.x19]; simp
      x12 := by rw [k5 .x12 (by decide), ht.x12]; simp
      x27 := by rw [ht.regs .x27 (by decide), hu.x27]
      jm := Nat.pos_of_ne_zero hm0
      jl := Nat.zero_le _
      inv := by rw [m5]; exact Inv.same' ht.inv m5 (k5 .x2 (by decide))
      heap := ⟨by simp only [heapNext, m5]; exact ht.heap.lo, by simp only [heapNext, m5]; exact ht.heap.hi⟩
      nx := m5 _
      fr := DFrame.of_same m5 _
      quad := fun k hk ↦ by simp only [Nat.not_lt_zero, ite_false, eAt, m5] }
    obtain ⟨t6, r6, h6⟩ := zloop hM hpre hz _ 0 t5 rfl hzi
    rcases h6 with hd | ho
    · exact ⟨t6, r5.trans r6, Or.inl hd⟩
    have hQe := hq1.2
    refine ⟨t6, r5.trans r6, Or.inr {
      pc := ho.pc
      sp := ho.sp
      regs := fun r hr ↦ (ho.keep r hr).trans (ht.regs r hr)
      inv := ho.inv
      heap := ho.heap
      nx := ho.nx.trans ht.nx
      fr := (ht.fr.mono fun a ha ↦ Or.inr ha).trans ho.fr fun a ha ↦ by
        rcases ha with ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
        · exact Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb])))
      sc := by
        rw [← ht.sc]
        exact ho.fr.eAt fun j hj hw ↦ by
          rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hb, hQe, hgh]
      quad := by
        rw [ho.quad.eList, quad4, intro4, ht.sc, gacc_succ hi]
        rfl
      wt := fun k hk ↦ by
        rw [← ht.wt k hk]
        exact ho.fr _ fun j hj hw ↦ by
          rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hk, hb, hQe, hgh] }⟩

/-- **Pending claim `i`**, from `0x8000b6b4` to `0x8000b7b8`. -/
theorem gfront (hM : MulSpec) {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u : MachineState}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u)
    (hpc : u.pc = 0x8000b6b4) (hx18 : u.getReg .x18 = pAddr g s i) (hi : i < pend.length) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ GMid s g lam Wl pend i u t) := by
  obtain ⟨t2, r2, h2⟩ := gfrontA hpre hg hu hpc hx18 hi
  obtain ⟨t4, r4, h4⟩ := gfrontB hM hpre hg hu hi h2
  rcases h4 with hd | h4
  · exact ⟨t4, r2.trans r4, Or.inl hd⟩
  obtain ⟨t, r, h⟩ := gfrontC hM hpre hg hu hi h4
  exact ⟨t, r2.trans (r4.trans r), h⟩

end Rv64Verifier.Proofs.Pcs.Vso
