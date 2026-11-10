import Rv64Verifier.Proofs.Pcs.VsoKernel

/-!
# `verify_stacked_opening`'s level loop: `eq_kernel` of the level's folds

At `0x8000b13c` the level's folds (`Vec<E>` at `S - 640`, kept since the fold rounds' end,
`Merkled.keep`, `Slices.keep`) go to `eq_kernel` (`0x8000cb38`), its `Vec` at `S - 536`
(`callEqKernel`); `kernel` returns at `0x8000b150` (`Kerneled`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `eq_kernel` of the `x12` elements at `x11` (allocated since the entry) into `S - 536`. -/
theorem callEqKernel (hE : MultilinearContracts.EqKernelSpec) {s t : MachineState} {nx : Word}
    (hpre : VsoPre s) (hinv : InvR s t nx) (hpc : t.pc = 0x8000cb38)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 536)
    (hpt : (t.getReg .x12).toNat = 0 ∨ Region (t.getReg .x11) (24 * (t.getReg .x12).toNat) ∧
      (t.getReg .x11).toNat + 24 * (t.getReg .x12).toNat ≤ heapNext t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      NewVecE t v (s.getReg .x2 - 536)
        (Model.eqKernelRust (eListAt t (t.getReg .x11) (t.getReg .x12).toNat)) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 536) 24 ∨ Within a (s.getReg .x2 - 2272) 1232 ∨
        Within a nextAddr 8 ∨ Fresh t v a)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsm := stack_mapped hpre
  obtain ⟨hnx, hrs⟩ := sfacts hpre
  have hsp := hinv.sp
  have hu := hinv.heap hpre.heap
  have hhi := hu.hi
  have hsl : stackLo t MultilinearContracts.eqKernelStack = s.getReg .x2 - 2272 := by
    simp only [stackLo, MultilinearContracts.eqKernelStack, mulStack, hsp, Nat.reduceAdd]; rv_eval []
  have hpreE : MultilinearContracts.EqKernelPre t := {
    heap := hu
    out := by rw [hx10]; simp only [Region, Mapped]; addr_omega [hsm]
    point := by
      rcases hpt with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [hx10]; simp only [Outside]; addr_omega [hsm, hnx]
    pointFree := by
      rcases hpt with h | ⟨h1, h2⟩
      · exact Or.inl h
      · have := Region.bounds h1
        exact Or.inr (by simp only [Outside]; addr_omega [this, h2, hhi])
    outStack := by rw [hx10, hsl]; addr_omega [hsm]
    pointStack := by
      rw [hsl]
      rcases hpt with h | ⟨h1, h2⟩
      · simp only [Apart, h, Nat.mul_zero, true_or]
      · have := Region.bounds h1; addr_omega [this, h2, hhi, hsm]
    pointOut := by
      rw [hx10]
      rcases hpt with h | ⟨h1, h2⟩
      · simp only [Apart, h, Nat.mul_zero, true_or]
      · have := Region.bounds h1; addr_omega [this, h2, hhi, hsm]
    rodata := hinv.rodata' hpre
    outRodata := by rw [hx10]; addr_omega [hsm, hrs] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hE.call (Reaches.refl t) hpc hpreE
  · have hval := hpost.value
    have hfr := hpost.frame
    rw [hx10] at hval
    rw [hx10, hsl] at hfr
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hval, hfr⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- At `0x8000b150`, `eq_kernel` returned, from the slices' end `t`: its `Vec` at `S - 536`. -/
structure Kerneled (s t k : MachineState) (lf : List E) : Prop where
  pc : k.pc = 0x8000b150
  sp : k.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ r ∈ calleeSaved, k.getReg r = t.getReg r
  inv : InvR s k (k.getMem nextAddr)
  heap : HeapOk k
  mono : heapNext t ≤ heapNext k
  ker : NewVecE t k (s.getReg .x2 - 536) (Model.eqKernelRust lf)
  fr : DFrame t k fun a ↦ Within a (s.getReg .x2 - 536) 24 ∨ Within a (s.getReg .x2 - 2272) 1232 ∨
    Within a nextAddr 8 ∨ Fresh t k a

/-- **`eq_kernel` of the level's folds**, from the slices' end. -/
theorem kernel (hE : MultilinearContracts.EqKernelSpec) {s : MachineState} {x : LCtx}
    {h t u v w m t' : MachineState} {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') :
    ∃ k, Reaches Image.code t' k ∧ (Dead Image.code k ∨ Kerneled s t' k lf) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hsl.sp
  obtain ⟨T0, hl⟩ := hm.lo
  have htm : heapNext t ≤ heapNext m := hm.op.mono.trans (hm.qo.mono.trans (hl.mono.trans hm.mo.mono))
  have hht := (hm.op.fo.heap).hi
  have hsh : heapNext s ≤ heapNext h :=
    (hm.op.fo.head.cfg.inv.mono).trans hm.op.fo.head.mono
  have keep (y : Word) (hy : OldAt s t y) : t'.getMem y = t.getMem y :=
    (hsl.keep hpre htm hy).trans (hm.keep hpre hy)
  obtain ⟨hLv, hLe, hLn⟩ := hm.op.fo.LF
  have hraw := hLv.raw
  have hlen := hLv.len
  simp only [RawVecOk, Buf] at hraw
  simp only [NewBuf] at hLn
  have e8 : t'.getMem (s.getReg .x2 - 632) = vecPtr t (s.getReg .x2 - 640) := by
    rw [keep _ (Or.inl (by addr_omega [hb]))]
    simp only [vecPtr]
    congr 1
    rv_eval []
  have e16 : t'.getMem (s.getReg .x2 - 624) = vecLen t (s.getReg .x2 - 640) := by
    rw [keep _ (Or.inl (by addr_omega [hb]))]
    simp only [vecLen]
    congr 1
    rv_eval []
  -- the old heap is kept
  have D : DFrame t t' fun y ↦ ¬ (heapNext s ≤ y.toNat ∧ y.toNat < heapNext t) := fun a ha ↦ by
    have h0 := ha 0 (by decide)
    have h7 := ha 7 (by decide)
    simp only [not_not] at h0 h7
    refine keep a (Or.inr ⟨?_, ?_⟩)
    · have := h0.1; rw [add_ofNat_zero] at this; exact this
    · have hlo := h0.1
      rw [add_ofNat_zero] at hlo
      have := hpre.heap.lo
      have e7 : (a + BitVec.ofNat 64 7).toNat = (a.toNat + 7) % 2 ^ 64 := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h71 := h7.1
      have h72 := h7.2
      simp only [heapStart] at this
      omega
  have hpt : eListAt t' (vecPtr t (s.getReg .x2 - 640)) (vecLen t (s.getReg .x2 - 640)).toNat = lf := by
    rw [← hLe]
    refine D.eListAt fun i hi hX ↦ hX ?_
    rcases hraw.2 with h0 | ⟨h1, h2⟩
    · omega
    rcases hLn.2 with h0 | ⟨h3, h4⟩
    · omega
    addr_omega [hi, h1, h2, h3, h4, hlen, hsh]
  -- the block at `0x8000b13c`
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b13c_spec hsl.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k1 := b8000b13c_keeps h1
  have m1 := b8000b13c_mem_same h1
  have x11 : t1.getReg .x11 = vecPtr t (s.getReg .x2 - 640) := by
    rw [b8000b13c_x11 h1, hsp, show s.getReg .x2 - 1040 + 408 = s.getReg .x2 - 632 by rv_eval [], e8]
  have x12 : t1.getReg .x12 = vecLen t (s.getReg .x2 - 640) := by
    rw [b8000b13c_x12 h1, hsp, show s.getReg .x2 - 1040 + 416 = s.getReg .x2 - 624 by rv_eval [], e16]
  have hn1 : heapNext t1 = heapNext t' := by simp only [heapNext, m1]
  have hinv1 : InvR s t1 (t'.getMem nextAddr) := Inv.same' hsl.inv m1 (k1 .x2 (by decide))
  obtain ⟨t2, r2, hv2⟩ := callEqKernel hE hpre hinv1 (b8000b13c_pc h1)
    (by rw [b8000b13c_x10 h1, hsp]; rv_eval []) (by
      rw [x11, x12, hn1]
      rcases hraw.2 with h0 | ⟨h1', h2'⟩
      · exact Or.inl (by omega)
      · refine Or.inr ⟨⟨by simp only [Mapped]; addr_omega [h1', h2', hlen, hht], hraw.1⟩, ?_⟩
        have := hsl.mono
        omega)
  rcases hv2 with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, hker₂, hfr₂⟩
  · exact ⟨t2, r1.trans r2, Or.inl hd⟩
  have hel : eListAt t1 (t1.getReg .x11) (t1.getReg .x12).toNat = lf := by
    rw [x11, x12, ← hpt]
    simp only [eListAt, eAt, m1]
  rw [hel] at hker₂
  have sp1 : t1.getReg .x2 = s.getReg .x2 - 1040 := (k1 .x2 (by decide)).trans hsp
  have sp2 : t2.getReg .x2 = t1.getReg .x2 := hpres₂ .x2 (by decide)
  have hhi₂ := hheap₂.hi
  have fresh (a : Word) (ha : Fresh t1 t2 a) : Fresh t' t2 a := by
    simp only [Fresh, hn1] at ha ⊢; exact ha
  have hlo1 : heapNext s ≤ heapNext t1 := by rw [hn1]; exact hinv1.mono
  refine ⟨t2, r1.trans r2, Or.inr {
    pc := by rw [hpc₂, returnAddress_eq, b8000b13c_x1 h1]; decide
    sp := sp2.trans sp1
    regs := fun r hr ↦ (hpres₂ r hr).trans (k1 r (mem_of_calleeSaved hr _))
    inv := Inv.step' hpre hinv1 hfr₂ (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl
      (by have := hmono₂; simp only [heapNext] at this hn1; omega) hhi₂ sp2
    heap := hheap₂
    mono := by rw [← hn1]; exact hmono₂
    ker := { vec := hker₂.vec
             buf := by have := hker₂.buf; simp only [NewBuf, hn1] at this ⊢; exact this
             elems := hker₂.elems }
    fr := (DFrame.of_same m1 _).trans (hfr₂.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (fresh a ha)))) fun _ h ↦ h }⟩
  · rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, ha2⟩))
  · rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
    · addr_omega [ha, hb]
    · addr_omega [ha, hb]
    · addr_omega [ha, hb, hnx]
    · addr_omega [ha2, hb, hhi₂]

/-- The level at `S - 856`, kept from the Merkle checks' start to `eq_kernel`'s return. -/
theorem Kerneled.lvl {s : MachineState} {x : LCtx} {h t u v w m t' k : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q res : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (hm : Merkled s x h t u v w m ℓ Wl lf q res pend d qs)
    (hsl : Slices s m t') (hk : Kerneled s t' k lf) :
    k.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hS := Region.bounds hpre.self.ok.self
  have hIs := hpre.self.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hmh := (hm.mo.inv.heap hpre.heap).hi
  have hth := hsl.heap.hi
  have hkh := hk.heap.hi
  have e1 : k.getMem (s.getReg .x2 - 856) = t'.getMem (s.getReg .x2 - 856) :=
    hk.fr _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, hw⟩
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb, hnx]
      · addr_omega [hw, hi, hb, hkh]
  have e2 : t'.getMem (s.getReg .x2 - 856) = m.getMem (s.getReg .x2 - 856) :=
    hsl.fr _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | ⟨-, hw⟩
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb, hnx]
      · addr_omega [hw, hi, hb, hth]
  have e3 : m.getMem (s.getReg .x2 - 856) = w.getMem (s.getReg .x2 - 856) :=
    hm.mo.fr _ fun i hi hw ↦ by
      rcases hw with (hw | hw | hw) | ((hw | hw | hw | hw) | hw | hw | ⟨-, hw⟩)
      · addr_omega [hw, hi, hb, hS, hIs]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb]
      · addr_omega [hw, hi, hb, hnx]
      · addr_omega [hw, hi, hb, hmh]
  rw [e1, e2, e3, hm.mi.front.lvl]

/-- **The branch at `0x8000b150`** on the level: `base_dot` rows at level `0`, `ext_row` deeper. -/
theorem rowsBranch {s t' k : MachineState} {lf : List E} {ℓ : ℕ} (hpre : VsoPre s)
    (hk : Kerneled s t' k lf) (hl : k.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ)
    (hℓ : ℓ < 2 ^ 64) :
    ∃ k', Reaches Image.code k k' ∧ (∀ a, k'.getMem a = k.getMem a) ∧
      (∀ r ∈ calleeSaved, k'.getReg r = k.getReg r) ∧
      ((ℓ = 0 ∧ k'.pc = 0x8000b2e0) ∨ (ℓ ≠ 0 ∧ k'.pc = 0x8000b158)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨k', r, h⟩ := Sym.BlockSpec.reaches b8000b150_spec hk.pc (by
    rv_eval [hk.sp]; valid_access hst.valid [hb])
  have e : k.getMem (k.getReg .x2 + 184) = BitVec.ofNat 64 ℓ := by
    rw [hk.sp, show s.getReg .x2 - 1040 + 184 = s.getReg .x2 - 856 by rv_eval [], hl]
  refine ⟨k', r, b8000b150_mem_same h, fun q hq ↦ b8000b150_keeps h q (mem_of_calleeSaved hq _), ?_⟩
  · by_cases h0 : ℓ = 0
    · exact Or.inl ⟨h0, b8000b150_pc_taken h (by rw [e, h0]; rfl)⟩
    · exact Or.inr ⟨h0, b8000b150_pc_not_taken h (by
        rw [e]; intro he; exact h0 (by have := congrArg BitVec.toNat he; simp at this; omega))⟩

end Rv64Verifier.Proofs.Pcs.Vso
