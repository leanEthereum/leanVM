import Rv64Verifier.Proofs.Pcs.VsoLvGlueBack

/-!
# `verify_stacked_opening`'s glue: room in `glued`

From `GAt7`: straight to `0x8000b67c` when `glued` has room, else through `grow_one`
(`0x8000b818`, `0x8000db78`, `0x8000b824`), its old claims copied (`gstage`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A step writing the frame below `S - 104`, `NEXT` and the heap it allocates keeps the
invariant. -/
theorem invR_alloc {s c c' : MachineState} {X : Word → Prop} (hpre : VsoPre s)
    (h : InvR s c (c.getMem nextAddr)) (hX : DFrame c c' X)
    (hXs : ∀ a, X a → Within a (s.getReg .x2 - 2464) 2360 ∨ Within a nextAddr 8 ∨ Fresh c c' a)
    (hheap : HeapOk c') (hmono : heapNext c ≤ heapNext c') (hsp : c'.getReg .x2 = c.getReg .x2) :
    InvR s c' (c'.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := hheap.hi
  have hsc : heapNext s ≤ heapNext c := h.mono
  refine Inv.step' hpre h hX (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hhi hsp
  · rcases hXs a ha with hw | hw | hw
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [hw, hb])))
    · exact Or.inr (Or.inr (Or.inl hw))
    · simp only [Fresh] at hw
      exact Or.inr (Or.inr (Or.inr ⟨by omega, hw.2⟩))
  · rcases hXs a ha with hw | hw | hw
    · addr_omega [hw, hb]
    · addr_omega [hw, hb, hnx]
    · simp only [Fresh, heapEnd] at hw hhi; addr_omega [hw.2, hb, hhi]

theorem vecOk_of_eq {u w : MachineState} {A : Word} {size : ℕ}
    (h : VecOk u A size 8) (hc : vecCap w A = vecCap u A) (hp : vecPtr w A = vecPtr u A)
    (hl : vecLen w A = vecLen u A) (hn : heapNext u ≤ heapNext w) : VecOk w A size 8 := by
  have hr := h.raw
  have hle := h.len
  simp only [RawVecOk, Buf] at hr
  refine ⟨?_, by rw [hc, hl]; exact hle⟩
  simp only [RawVecOk, Buf, hc, hp]
  refine ⟨hr.1, ?_⟩
  rcases hr.2 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ⟨h0.1, by omega⟩

/-- **Room in `glued`**, from `GAt7` to `0x8000b67c`. -/
theorem gstage (hG : GrowOneFreshSpec 0x8000db78 88 8) {s g : MachineState} {lam : E}
    {Wl : Model.Pcs.WhirLocals} {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ}
    {u w7 : MachineState} (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend)
    (hu : GInv s g lam Wl pend i u) (hw : GAt7 s g lam Wl pend i u w7) :
    ∃ w, Reaches Image.code w7 w ∧ (Dead Image.code w ∨ GAt67 s g lam Wl pend i u w) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hgh := hg.heap.hi
  simp only [heapEnd] at hgh
  have hmo := hu.mono
  have hn7 : heapNext w7 = heapNext u := by simp only [heapNext, hw.nx]
  have heap7 : HeapOk w7 := ⟨by rw [hn7]; exact hu.heap.lo, by rw [hn7]; exact hu.heap.hi⟩
  have gv7 : VecOk w7 (s.getReg .x2 - 664) 88 8 :=
    vecOk_of_eq hu.gv hw.ecap hw.eptr hw.elen (by rw [hn7])
  have hlc := hu.gv.len
  by_cases hfull : vecLen u (s.getReg .x2 - 664) = vecCap u (s.getReg .x2 - 664)
  swap
  · have hlt : (vecLen u (s.getReg .x2 - 664)).toNat < (vecCap u (s.getReg .x2 - 664)).toNat := by
      have : (vecLen u (s.getReg .x2 - 664)).toNat ≠ (vecCap u (s.getReg .x2 - 664)).toNat :=
        fun h ↦ hfull (BitVec.eq_of_toNat_eq h)
      omega
    refine ⟨w7, .refl _, Or.inr {
      pc := hw.pcA hfull
      sp := hw.sp
      regs := hw.regs
      x8 := hw.x8
      inv := hw.inv
      heap := heap7
      mono := by rw [hn7]
      fr := hw.fr
      gv := gv7
      glen := hw.elen
      room := by rw [hw.ecap]; exact hlt
      old := hw.old
      gbuf := by
        rw [hw.eptr, hw.ecap]
        rcases hu.gbuf with h0 | h0
        · exact Or.inl h0
        · refine Or.inr ?_
          simp only [NewBuf] at h0 ⊢
          rw [hn7]; exact h0
      stage := hw.stage
      scal := hw.scal
      sc := hw.sc
      quad := hw.quad }⟩
  -- full: `grow_one`
  obtain ⟨t8, r8, h8⟩ := Sym.BlockSpec.reaches b8000b818_spec (hw.pcB hfull) trivial
  have k8 := b8000b818_keeps h8
  have m8 := b8000b818_mem_same h8
  have sp8 : t8.getReg .x2 = s.getReg .x2 - 1040 := by rw [k8 .x2 (by decide), hw.sp]
  have hn8 : heapNext t8 = heapNext u := by simp only [heapNext, m8]; exact hn7
  have gv8 : VecOk t8 (s.getReg .x2 - 664) 88 8 :=
    vecOk_of_eq gv7 (m8 _) (m8 _) (m8 _) (by rw [hn8, hn7])
  have inv8 : InvR s t8 (t8.getMem nextAddr) := by
    rw [m8]; exact Inv.same' hw.inv m8 (by rw [sp8, hw.sp])
  have h8h : heapNext t8 ≤ 2013265920 := by have := hu.heap.hi; simp only [heapEnd] at this; omega
  obtain ⟨t9, r9, h9⟩ := callGrow88 hG hpre inv8 ⟨by rw [hn8]; exact hu.heap.lo, by rw [hn8]; exact hu.heap.hi⟩
    (b8000b818_pc h8) (by rw [b8000b818_x10 h8, hw.sp]; rv_eval []) (by addr_omega [hb]) gv8
  rcases h9 with hd | ⟨hpc9, hpres9, hheap9, hmono9, hfr9, hlen9, hcap9, hraw9, hnew9, hbytes9⟩
  · exact ⟨t9, r8.trans r9, Or.inl hd⟩
  obtain ⟨w, rw', hw'⟩ := Sym.BlockSpec.reaches b8000b824_spec (by
    rw [hpc9, returnAddress_eq, b8000b818_x1 h8]; decide) trivial
  have kw := b8000b824_keeps hw'
  have mw := b8000b824_mem_same hw'
  have sp9 : t9.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres9 .x2 (by decide), sp8]
  have hnw : heapNext w = heapNext t9 := by simp only [heapNext, mw]
  have hh9 := hheap9.hi
  simp only [heapEnd] at hh9
  have inv9 : InvR s t9 (t9.getMem nextAddr) := by
    refine invR_alloc hpre inv8 hfr9
      (fun a ha ↦ ?_) hheap9 hmono9 (by rw [sp9, sp8])
    rcases ha with ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ha)
  -- what the grow keeps: the stack above `S - 1040` but `glued`'s header, the heap below `t8`'s
  have keep9 (a : Word) (ha : ∀ j < 8, ¬ Within (a + BitVec.ofNat 64 j) (s.getReg .x2 - 664) 16 ∧
      ((s.getReg .x2 - 1040).toNat ≤ (a + BitVec.ofNat 64 j).toNat ∧
        (a + BitVec.ofNat 64 j).toNat < (s.getReg .x2).toNat ∨
        (a + BitVec.ofNat 64 j).toNat < heapNext t8)) : t9.getMem a = t8.getMem a :=
    hfr9 a fun j hj hx ↦ by
      obtain ⟨h1, h2⟩ := ha j hj
      rcases hx with hx | hx | hx | hx
      · exact h1 hx
      · rcases h2 with h2 | h2 <;> addr_omega [hx, h2, hb, hh9, h8h]
      · rcases h2 with h2 | h2 <;> addr_omega [hx, h2, hb, hnx, hh9, h8h]
      · simp only [Fresh] at hx; rcases h2 with h2 | h2 <;> addr_omega [hx.1, hx.2, h2, hb, hh9]
  have Y : DFrame w7 w fun a ↦ Within a (s.getReg .x2 - 664) 16 ∨
      Within a (s.getReg .x2 - 1200) 160 ∨ Within a nextAddr 8 ∨ Fresh t8 t9 a :=
    ((DFrame.of_same m8 _).trans hfr9 fun _ h ↦ h).trans (DFrame.of_same mw _) fun _ h ↦ h
  have hQb := hg.quad.2.2
  have hg8 : heapNext g ≤ heapNext t8 := by rw [hn8]; exact hmo
  have nY {a : Word} {n : ℕ} (ha : (s.getReg .x2 - 408).toNat ≤ a.toNat ∧
      a.toNat + n ≤ (s.getReg .x2 - 304).toNat ∨ a.toNat + n ≤ heapNext g) :
      ∀ j < n, ¬ (Within (a + BitVec.ofNat 64 j) (s.getReg .x2 - 664) 16 ∨
        Within (a + BitVec.ofNat 64 j) (s.getReg .x2 - 1200) 160 ∨
        Within (a + BitVec.ofNat 64 j) nextAddr 8 ∨ Fresh t8 t9 (a + BitVec.ofNat 64 j)) := by
    intro j hj hy
    rcases hy with hy | hy | hy | hy
    · rcases ha with ha | ha <;> addr_omega [hy, ha, hj, hb, hgh]
    · rcases ha with ha | ha <;> addr_omega [hy, ha, hj, hb, hgh]
    · rcases ha with ha | ha <;> addr_omega [hy, ha, hj, hb, hgh, hnx]
    · simp only [Fresh] at hy
      rcases ha with ha | ha <;> addr_omega [hy.1, hy.2, ha, hj, hb, hgh, hg8, hh9]
  have hcap8 : (vecCap t8 (s.getReg .x2 - 664)).toNat = (vecLen u (s.getReg .x2 - 664)).toNat := by
    rw [show vecCap t8 (s.getReg .x2 - 664) = vecCap w7 (s.getReg .x2 - 664) from m8 _, hw.ecap,
      hfull]
  have hlen8 : vecLen t8 (s.getReg .x2 - 664) = vecLen u (s.getReg .x2 - 664) := by
    rw [show vecLen t8 (s.getReg .x2 - 664) = vecLen w7 (s.getReg .x2 - 664) from m8 _, hw.elen]
  have ecw : vecCap w (s.getReg .x2 - 664) = vecCap t9 (s.getReg .x2 - 664) := mw _
  have epw : vecPtr w (s.getReg .x2 - 664) = vecPtr t9 (s.getReg .x2 - 664) := mw _
  have elw : vecLen w (s.getReg .x2 - 664) = vecLen t9 (s.getReg .x2 - 664) := mw _
  have hgv9 : VecOk t9 (s.getReg .x2 - 664) 88 8 := ⟨hraw9, by rw [hlen9, hlen8]; omega⟩
  have hp8 := gv8.raw.1
  refine ⟨w, r8.trans (r9.trans rw'), Or.inr {
    pc := b8000b824_pc hw'
    sp := by rw [kw .x2 (by decide), sp9]
    regs := fun r hr ↦ by
      have hr' : r ∈ calleeSaved := by simp only [ZK] at hr; revert hr; decide +revert
      rw [kw r (by simp only [ZK] at hr; revert hr; decide +revert), hpres9 r hr',
        k8 r (by simp only [ZK] at hr; revert hr; decide +revert), hw.regs r hr]
    x8 := by rw [kw .x8 (by decide), hpres9 .x8 (by decide), k8 .x8 (by decide), hw.x8]
    inv := by rw [mw]; exact Inv.same' inv9 mw (kw .x2 (by decide))
    heap := ⟨by rw [hnw]; exact hheap9.lo, by rw [hnw]; exact hheap9.hi⟩
    mono := by rw [hnw]; omega
    fr := ((hw.fr.mono fun a ha ↦ GlueW.mono (by rw [hnw, hn7]; omega) ha).trans Y) fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,
          by rw [hnw]; exact ha.2⟩))))))
    gv := vecOk_of_eq hgv9 ecw epw elw (by rw [hnw])
    glen := by rw [elw, hlen9, hlen8]
    room := by rw [ecw]; omega
    old := fun j hj k hk ↦ by
      rw [epw, add_add_ofNat, mw, getMem_eq_of_bytesAt hbytes9 hnew9.1 hp8 (by omega)
        (by rw [hcap8]; omega), ← add_add_ofNat,
        show vecPtr t8 (s.getReg .x2 - 664) = vecPtr w7 (s.getReg .x2 - 664) from m8 _, m8]
      exact hw.old j hj k hk
    gbuf := by
      refine Or.inr ?_
      rw [epw, ecw]
      simp only [NewBuf] at hnew9 ⊢
      rw [hnw]
      rcases hnew9.2 with h0 | h0
      · exact ⟨hnew9.1, Or.inl h0⟩
      · exact ⟨hnew9.1, Or.inr ⟨by omega, h0.2⟩⟩
    stage := fun k hk ↦ by
      rw [← hw.stage k hk]
      exact Y _ (nY (n := 8) (Or.inl (by addr_omega [hb, hk])))
    scal := by
      rw [← hw.scal]
      exact Y.eAt (nY (Or.inl (by addr_omega [hb])))
    sc := by
      rw [← hw.sc]
      exact Y.eAt (nY (Or.inl (by addr_omega [hb])))
    quad := by
      rw [← hw.quad]
      refine Y.eListAt fun j hj ↦ ?_
      rcases hQb with h0 | h0
      · omega
      · exact nY (n := 24 * (g.getReg .x23).toNat) (Or.inr h0.2) j hj }⟩

end Rv64Verifier.Proofs.Pcs.Vso
