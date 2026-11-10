import Rv64Verifier.Proofs.Pcs.VsoFinalSpec
import Rv64Verifier.Proofs.Pcs.VsoGrind
import Rv64Verifier.Proofs.Multilinear.Contracts

/-!
# `verify_stacked_opening`'s final level: the terminal check

At `0x8000bfe8` the terminal weight is at `S - 184`, the tail's challenges in `s0`/`s3`:
`multilinear_eval(S - 384, residual, tail)` returns at `0x8000c004` (its `Err` cannot happen: the
residual has `2 ^ ml` values), `0x8000c01c` moves the value to `S - 384` and multiplies it by the
weight into `S - 464`, `0x8000c048` compares the product with the running target (limbs at
`S - 904`, `S - 920`, `S - 864`): `-1` (`Ok`) when equal, `18` (`WhirTerminal`) otherwise, returned
through `0x8000b844`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What is left of the mirror at the terminal check: the residual at the tail, times the weight,
against the running target. -/
def terminalCheckM (residual tf : List E) (w rt : E) : Model.TM Unit := do
  let residualValue ← Model.TM.ofOption (Model.multilinearEvalRust residual tf)
  Model.TM.require (w * residualValue = rt)

/-- At `0x8000bfe8`: the tail's `ml` challenges `tf` at `s0` (length in `s3`), the residual at
`S - 968` (length at `S - 960`), the weight `w` at `S - 184`, the running target `rt`. -/
structure TC (OA : MachineState → Word → Model.TState → Prop) (s u : MachineState) (ml : ℕ)
    (residual tf : List E) (w rt : E) : Prop where
  inv : InvR s u (u.getMem nextAddr)
  heap : HeapOk u
  pc : u.pc = 0x8000bfe8
  ml64 : ml < 64
  x19 : u.getReg .x19 = BitVec.ofNat 64 ml
  tail : eListAt u (u.getReg .x8) ml = tf ∧ (u.getReg .x8).toNat % 8 = 0 ∧
    (ml = 0 ∨ heapNext s ≤ (u.getReg .x8).toNat ∧ (u.getReg .x8).toNat + 24 * ml ≤ heapNext u)
  res : eListAt u (u.getMem (s.getReg .x2 - 968)) (u.getMem (s.getReg .x2 - 960)).toNat =
      residual ∧ (u.getMem (s.getReg .x2 - 968)).toNat % 8 = 0 ∧
    ((u.getMem (s.getReg .x2 - 960)).toNat = 0 ∨ heapNext s ≤ (u.getMem (s.getReg .x2 - 968)).toNat ∧
      (u.getMem (s.getReg .x2 - 968)).toNat + 24 * (u.getMem (s.getReg .x2 - 960)).toNat ≤
        heapNext u)
  rlen : residual.length = 2 ^ ml
  wt : eAt u (s.getReg .x2 - 184) = w
  trg : E.ofLimbs (BF64.ofBitVec (u.getMem (s.getReg .x2 - 904)))
    (BF64.ofBitVec (u.getMem (s.getReg .x2 - 920))) (BF64.ofBitVec (u.getMem (s.getReg .x2 - 864))) = rt
  value : RunsF OA s u (terminalCheckM residual tf w rt)

/-- `multilinear_eval(o, mle, point)` from the frame, both slices in the heap. -/
theorem callMle (hMle : MultilinearContracts.MleEvalSpec) {s t : MachineState} {nx o p q : Word}
    {n m : Word} {rv : E} (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t)
    (hpc : t.pc = 0x8000d28c) (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = p)
    (hx12 : t.getReg .x12 = n) (hx13 : t.getReg .x13 = q)
    (hx14 : t.getReg .x14 = m)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 32 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0)
    (hp : n.toNat = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + 24 * n.toNat ≤ heapNext t) (hp8 : p.toNat % 8 = 0)
    (hq : m.toNat = 0 ∨ heapStart ≤ q.toNat ∧ q.toNat + 24 * m.toNat ≤ heapNext t) (hq8 : q.toNat % 8 = 0)
    (hv : Model.multilinearEvalRust (eListAt t p n.toNat) (eListAt t q m.toNat) = some rv) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a o 32 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
        Within a nextAddr 8 ∨ Fresh t v a) ∧
      v.getMem o = 0 ∧ eAt v (o + 8) = rv)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hinv.sp
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hhi := hheap.hi
  have hab := hst.above
  rw [stackLo_vso] at hab
  have hsl : stackLo t MultilinearContracts.mleEvalStack = s.getReg .x2 - 2272 := by
    simp only [stackLo, MultilinearContracts.mleEvalStack, mulStack, hsp, Nat.reduceAdd]; rv_eval []
  have hpreM : MultilinearContracts.MleEvalPre t := {
    heap := hheap
    out := by rw [hx10]; exact stack_region hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb]) ho.2.2
    mle := by
      rw [hx11, hx12]
      rcases hp with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (heap_region (by simp only [heapStart] at h0; omega)
          (by simp only [heapEnd] at hhi ⊢; omega) hp8)
    point := by
      rw [hx13, hx14]
      rcases hq with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (heap_region (by simp only [heapStart] at h0; omega)
          (by simp only [heapEnd] at hhi ⊢; omega) hq8)
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10]
      exact ⟨Or.inr (by simp only [heapEnd] at hab ⊢; addr_omega [ho, hb, hab]), by addr_omega [ho, hb, hnx]⟩
    mleFree := by
      rw [hx11, hx12]
      rcases hp with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨Or.inl h0.2, by addr_omega [h0.2, hhi, hnx, hb, hab]⟩
    pointFree := by
      rw [hx13, hx14]
      rcases hq with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨Or.inl h0.2, by addr_omega [h0.2, hhi, hnx, hb, hab]⟩
    outStack := by rw [hx10, hsl]; addr_omega [ho, hb]
    mleStack := by
      rw [hx11, hx12, hsl]
      rcases hp with h0 | h0
      · exact Or.inl (by omega)
      · simp only [heapEnd] at hhi hab; addr_omega [h0.2, hhi, hb, hab]
    pointStack := by
      rw [hx13, hx14, hsl]
      rcases hq with h0 | h0
      · exact Or.inl (by omega)
      · simp only [heapEnd] at hhi hab; addr_omega [h0.2, hhi, hb, hab]
    mleOut := by
      rw [hx11, hx12, hx10]
      rcases hp with h0 | h0
      · exact Or.inl (by omega)
      · simp only [heapEnd] at hhi hab; addr_omega [h0.2, hhi, ho, hb, hab]
    pointOut := by
      rw [hx13, hx14, hx10]
      rcases hq with h0 | h0
      · exact Or.inl (by omega)
      · simp only [heapEnd] at hhi hab; addr_omega [h0.2, hhi, ho, hb, hab]
    rodata := hinv.rodata' hpre
    outRodata := by
      rw [hx10]
      have := hst.rodata
      rw [stackLo_vso, vso_stack] at this
      addr_omega [this, ho, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hMle.call (Reaches.refl t) hpc hpreM
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10, hx11, hx12, hx13, hx14, hv] at hval
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ha)), hval.1, hval.2⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `E::mul(o, a, b)`, all three in the frame. -/
theorem callMul (hM : MulSpec) {s t : MachineState} {nx o a b : Word} (hpre : VsoPre s)
    (hinv : InvR s t nx) (hpc : t.pc = 0x80008c48) (hx10 : t.getReg .x10 = o)
    (hx11 : t.getReg .x11 = a) (hx12 : t.getReg .x12 = b)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0)
    (ha : (s.getReg .x2 - 1040).toNat ≤ a.toNat ∧ a.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      a.toNat % 8 = 0)
    (hb' : (s.getReg .x2 - 1040).toNat ≤ b.toNat ∧ b.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      b.toNat % 8 = 0)
    (hoa : Apart o 24 a 24) (hob : Apart o 24 b 24) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      DFrame t v (fun y ↦ Within y o 24 ∨ Within y (s.getReg .x2 - 2064) 1024) ∧
      eAt v o = eAt t a * eAt t b)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := hinv.sp
  have hro := hst.rodata
  rw [stackLo_vso] at hro
  have hsl : stackLo t mulStack = s.getReg .x2 - 2064 := by
    simp only [stackLo, hsp, mulStack]; rv_eval []
  have hpreM : MulPre t := {
    out := by rw [hx10]; valid_sub hst.valid [hb, ho]
    lhs := by rw [hx11]; valid_sub hst.valid [hb, ha]
    rhs := by rw [hx12]; valid_sub hst.valid [hb, hb']
    stack := ⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp]; addr_omega [hb]⟩
    outLhs := by rw [hx10, hx11]; exact hoa
    outRhs := by rw [hx10, hx12]; exact hob
    outStack := by rw [hx10, hsl]; addr_omega [hb, ho]
    lhsStack := by rw [hx11, hsl]; addr_omega [hb, ha]
    rhsStack := by rw [hx12, hsl]; addr_omega [hb, hb']
    rodata := hinv.rodata' hpre
    stackRodata := by rw [hsl]; addr_omega [hro, hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hM.call (Reaches.refl t) hpc hpreM
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10, hx11, hx12] at hval
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, DFrame.of_two hfr, hval⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- `0x8000c048`'s verdict: `-1` only when the three limbs match. -/
theorem cmp_ok {a0 a1 a2 b0 b1 b2 : Word}
    (h : ((if BitVec.ult 0 (((a0 ^^^ b0) ||| (a1 ^^^ b1)) ||| (a2 ^^^ b2)) then (1 : Word) else 0) -
      1) ||| 18 = okTag) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  by_cases hD : ((a0 ^^^ b0) ||| (a1 ^^^ b1)) ||| (a2 ^^^ b2) = 0
  · obtain ⟨h01, h2⟩ := BitVec.or_eq_zero_iff.mp hD
    obtain ⟨h0, h1⟩ := BitVec.or_eq_zero_iff.mp h01
    exact ⟨BitVec.xor_eq_zero_iff.mp h0, BitVec.xor_eq_zero_iff.mp h1, BitVec.xor_eq_zero_iff.mp h2⟩
  · generalize ((a0 ^^^ b0) ||| (a1 ^^^ b1)) ||| (a2 ^^^ b2) = D at hD h
    have h0 : D.toNat ≠ 0 := fun h0 ↦ hD (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
    have hu : BitVec.ult 0 D = true := by
      unfold BitVec.ult; exact decide_eq_true (by rw [show (0 : Word).toNat = 0 from rfl]; omega)
    simp only [hu, ↓reduceIte] at h
    exact absurd h (by decide)

/-- `Ok` at `0x8000b844`, to the exit. -/
theorem ok844 {s t : MachineState} {nx : Word} (hinv : InvR s t nx) (hpc : t.pc = 0x8000b844)
    (hok : t.getReg .x1 = okTag) : ∃ w, Reaches Image.code t w ∧ w.pc = 0x8000a0bc ∧
      w.getReg .x10 = okTag ∧ InvR s w nx ∧ ∀ a, w.getMem a = t.getMem a := by
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b844_spec hpc trivial
  obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000b84c_spec (b8000b844_pc h1) trivial
  have hm (a : Word) : t2.getMem a = t.getMem a := by
    rw [b8000b84c_mem_same h2, b8000b844_mem_same h1]
  exact ⟨t2, r1.trans r2, b8000b84c_pc h2, by rw [b8000b84c_x10 h2, b8000b844_x22 h1]; exact hok,
    Inv.same' hinv hm (by rw [b8000b84c_keeps h2 .x2 (by decide), b8000b844_keeps h1 .x2 (by decide)]),
    hm⟩

end Rv64Verifier.Proofs.Pcs.Vso
