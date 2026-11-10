import Rv64Verifier.Proofs.Pcs.VsoFinalRounds
import Rv64Verifier.Proofs.Pcs.VsoGrind
import Rv64Verifier.Proofs.Multilinear.Contracts

/-!
# `verify_stacked_opening`'s final level: the terminal point

`0x8000ba14` reads the transcript's checked byte (`1`: a replay would return `Ok` at once);
`0x8000ba20` concatenates `folds` and the tail folds into the point (a `Vec<E>` at `S - 280`);
`0x8000ba50` compares its length with the first level's fold count (`[s1]`, `6`), and
`0x8000ba5c` concatenates the point rotated by it into `S - 464`, which `0x8000ba98` hands to
`StackBasis::evaluate`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem pt_drop (s : MachineState) (p : Word) (n k : Nat) :
    (eListAt s p n).drop k = eListAt s (p + BitVec.ofNat 64 (24 * k)) (n - k) := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  simp only [List.getElem_drop, eListAt_getElem]
  rw [add_ofNat_add, Nat.mul_add]

theorem pt_take (u : MachineState) (p : Word) {k n : Nat} (h : k ≤ n) :
    (eListAt u p n).take k = eListAt u p k := by
  apply List.ext_getElem (by simp [eListAt_length, h])
  intro i h1 h2
  simp only [List.getElem_take, eListAt_getElem]

/-- A heap slice since the entry, as `slice_concat`'s part. -/
theorem part_ok {s t : MachineState} (hpre : VsoPre s) (hheap : HeapOk t) {p o : Word} {n : ℕ}
    (hb : n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + 24 * n ≤ heapNext t) (h8 : p.toNat % 8 = 0)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat) :
    n = 0 ∨ (Region p (24 * n) ∧ Outside t p (24 * n) ∧
      Apart p (24 * n) (s.getReg .x2 - 2464) 2464 ∧ Apart p (24 * n) o 24) := by
  have hbd := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  have hhs := hpre.heap.lo
  have hhi := hheap.hi
  rcases hb with h0 | h0
  · exact Or.inl h0
  refine Or.inr ⟨heap_region (by simp only [heapStart, heapNext] at hhs h0 ⊢; omega)
    (by omega) h8, ⟨Or.inl h0.2, ?_⟩, ?_, ?_⟩
  · simp only [heapEnd] at hhi; addr_omega [h0.2, hhi, hnx, hab, hbd]
  · simp only [heapEnd] at hhi hab; addr_omega [h0.2, hhi, hab, hbd]
  · simp only [heapEnd] at hhi hab; addr_omega [h0.2, hhi, hab, hbd, ho]

/-- `slice_concat` of two slices into the frame. -/
theorem callConcat2 (hC : MultilinearContracts.SliceConcatSpec) {s t : MachineState}
    {nx o A p0 p1 : Word} {n0 n1 : ℕ} (hpre : VsoPre s) (hinv : InvR s t nx) (hheap : HeapOk t)
    (hpc : t.pc = 0x8000cfc4) (hx10 : t.getReg .x10 = o) (hx11 : t.getReg .x11 = A)
    (hx12 : t.getReg .x12 = 2)
    (ho : (s.getReg .x2 - 1040).toNat ≤ o.toNat ∧ o.toNat + 24 ≤ (s.getReg .x2 - 104).toNat ∧
      o.toNat % 8 = 0)
    (hA : (s.getReg .x2 - 1040).toNat ≤ A.toNat ∧ A.toNat + 32 ≤ (s.getReg .x2 - 104).toNat ∧
      A.toNat % 8 = 0)
    (hoA : Apart A 32 o 24)
    (h0p : t.getMem A = p0) (h0n : (t.getMem (A + 8)).toNat = n0) (h1p : t.getMem (A + 16) = p1)
    (h1n : (t.getMem (A + 24)).toNat = n1)
    (hb0 : n0 = 0 ∨ heapNext s ≤ p0.toNat ∧ p0.toNat + 24 * n0 ≤ heapNext t) (h80 : p0.toNat % 8 = 0)
    (hb1 : n1 = 0 ∨ heapNext s ≤ p1.toNat ∧ p1.toNat + 24 * n1 ≤ heapNext t) (h81 : p1.toNat % 8 = 0) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧ Preserves t v ∧
      HeapOk v ∧ heapNext t ≤ heapNext v ∧
      DFrame t v (fun a ↦ Within a o 24 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
        Within a nextAddr 8 ∨ Fresh t v a) ∧
      NewVecE t v o (eListAt t p0 n0 ++ eListAt t p1 n1))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hsp := hinv.sp
  have hsl : stackLo t MultilinearContracts.sliceConcatStack = s.getReg .x2 - 1264 := by
    simp only [stackLo, MultilinearContracts.sliceConcatStack, Runtime.reserveStack, hsp]
    addr_omega [hb]
  have h2 : (t.getReg .x12).toNat = 2 := by rw [hx12]; rfl
  have e0 : A + BitVec.ofNat 64 (16 * 0) = A := by simp
  have e1 : A + BitVec.ofNat 64 (16 * 0) + 8 = A + 8 := by rw [e0]
  have e2 : A + BitVec.ofNat 64 (16 * 1) = A + 16 := rfl
  have e3 : A + BitVec.ofNat 64 (16 * 1) + 8 = A + 24 := by addr_omega [hA]
  have pp0 : MultilinearContracts.partPtr t 0 = p0 := by
    simp only [MultilinearContracts.partPtr, hx11, e0, h0p]
  have pl0 : MultilinearContracts.partLen t 0 = n0 := by
    simp only [MultilinearContracts.partLen, hx11, e1, h0n]
  have pp1 : MultilinearContracts.partPtr t 1 = p1 := by
    simp only [MultilinearContracts.partPtr, hx11, e2, h1p]
  have pl1 : MultilinearContracts.partLen t 1 = n1 := by
    simp only [MultilinearContracts.partLen, hx11, e3, h1n]
  have hpre' : MultilinearContracts.SliceConcatPre t := {
    heap := hheap
    out := by rw [hx10]; exact stack_region hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb]) ho.2.2
    count := by rw [h2]; decide
    slices := by
      rw [hx11, h2]; exact stack_region hpre (by addr_omega [hA, hb]) (by addr_omega [hA, hb]) hA.2.2
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [hx10]; exact stack_outside hpre (by addr_omega [ho, hb]) (by addr_omega [ho, hb])
    outStack := by rw [hx10, hsl]; addr_omega [ho, hb]
    slicesFree := by
      rw [hx11, h2]; exact stack_outside hpre (by addr_omega [hA, hb]) (by addr_omega [hA, hb])
    slicesStack := by rw [hx11, h2, hsl]; addr_omega [hA, hb]
    slicesOut := by rw [hx11, h2, hx10]; exact hoA
    part := by
      intro i hi
      rw [h2] at hi
      have hpart (p : Word) (n : ℕ) (hbn : n = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + 24 * n ≤ heapNext t)
          (h8 : p.toNat % 8 = 0) : n = 0 ∨ (Region p (24 * n) ∧ Outside t p (24 * n) ∧
            Apart p (24 * n) (stackLo t MultilinearContracts.sliceConcatStack)
              MultilinearContracts.sliceConcatStack ∧ Apart p (24 * n) (t.getReg .x10) 24) := by
        rcases part_ok hpre hheap hbn h8 ⟨ho.1, ho.2.1⟩ with h0 | ⟨r1, r2, r3, r4⟩
        · exact Or.inl h0
        · refine Or.inr ⟨r1, r2, ?_, by rw [hx10]; exact r4⟩
          rw [hsl]; simp only [MultilinearContracts.sliceConcatStack, Runtime.reserveStack]
          addr_omega [r3, hb]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · rw [pp0, pl0]; exact hpart p0 n0 hb0 h80
      · rw [pp1, pl1]; exact hpart p1 n1 hb1 h81 }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost⟩ | hdead⟩ := hC.call (Reaches.refl t) hpc hpre'
  · have hfr := hpost.frame
    have hval := hpost.value
    rw [hx10, hsl] at hfr
    rw [hx10] at hval
    have hparts : (MultilinearContracts.parts t).flatten = eListAt t p0 n0 ++ eListAt t p1 n1 := by
      simp only [MultilinearContracts.parts, h2, show List.range 2 = [0, 1] from rfl, List.map_cons,
        List.map_nil, pp0, pl0, pp1, pl1, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hparts] at hval
    exact ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, hfr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by simp only [MultilinearContracts.sliceConcatStack,
          Runtime.reserveStack] at ha; addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ha)), hval⟩⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- The first level's fold count, `[s1]`. -/
theorem VsoFinalIn.fold0 {OA : MachineState → Word → Model.TState → Prop} {s : MachineState}
    {x : LCtx} {u : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E}
    (hpre : VsoPre s) (h : VsoFinalIn OA s x u Wl residual) :
    u.getMem x.FP = 6 ∧ heapNext s ≤ x.FP.toNat ∧ x.FP.toNat + 8 ≤ heapNext u ∧
      x.FP.toNat % 8 = 0 := by
  have hc := h.cfg
  have hm := h.mark
  have hbf := hc.bufs
  have hn := hc.nxs
  have hmo := h.mono
  have hend := h.heap.hi
  have hL : x.L ≤ heapEnd := by omega
  have hwF := LM.words hpre h.fr (by omega) hm.1 hL
  rw [hc.folds] at hwF
  have e := readWords_get hwF (show 0 < K0 s + 2 by omega)
  rw [lw_getD] at e
  simp only [Nat.mul_zero, add_ofNat_zero] at e
  exact ⟨e, by omega, by omega, hbf.2.2.1⟩

/-- At `0x8000ba98`: the point `Wl.folds ++ tf` at `S - 280`, rotated by `6` at `S - 464`. -/
structure TV (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (tf : List E) (rt : E) :
    Prop extends TI OA s x u v Wl residual where
  pc : v.pc = 0x8000ba98
  tfl : tf.length = mlF s Wl
  x8 : v.getReg .x8 = vecPtr v (s.getReg .x2 - 304)
  x19 : v.getReg .x19 = BitVec.ofNat 64 (mlF s Wl)
  tail : TailV s u v tf
  trg : E.ofLimbs (BF64.ofBitVec (v.getMem (s.getReg .x2 - 904)))
    (BF64.ofBitVec (v.getMem (s.getReg .x2 - 920))) (BF64.ofBitVec (v.getMem (s.getReg .x2 - 864))) = rt
  six : 6 ≤ (Wl.folds ++ tf).length
  point : VecOk v (s.getReg .x2 - 280) 24 8 ∧ vecEs v (s.getReg .x2 - 280) = Wl.folds ++ tf ∧
    NewBuf u v (vecPtr v (s.getReg .x2 - 280)) ((vecCap v (s.getReg .x2 - 280)).toNat * 24) 8
  rot : VecOk v (s.getReg .x2 - 464) 24 8 ∧
    vecEs v (s.getReg .x2 - 464) = (Wl.folds ++ tf).drop 6 ++ (Wl.folds ++ tf).take 6 ∧
    NewBuf u v (vecPtr v (s.getReg .x2 - 464)) ((vecCap v (s.getReg .x2 - 464)).toNat * 24) 8
  value : RunsF OA s v (afterTail (cfgOf s) (basisOf s x) residual Wl tf rt)

/-- **The terminal point**: from `0x8000ba14` to `0x8000ba98`, or a dead end. -/
theorem tPoint (hC : MultilinearContracts.SliceConcatSpec)
    {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} {tf : List E} {rt : E}
    (hpre : VsoPre s) (ha : TA OA s x u v Wl residual tf rt) :
    ∃ w, Reaches Image.code v w ∧ (Dead Image.code w ∨ TV OA s x u w Wl residual tf rt) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hst.above
  rw [stackLo_vso] at hab
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hsp := ha.sp
  have hfin := ha.toTI.fin
  have hsu := hfin.su
  have hhs := hpre.heap.lo
  -- `0x8000ba14`: the checked byte
  have hbyte := checked_one hpre (ha.toTI.inv hpre)
  have m224 := ha.m224
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000ba14_spec ha.pc (by
    rv_eval [hsp, m224]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact hS.2.2
      | exact v1of8 (Region.valid (x := s.getReg .x10 + 360) hI.ok.self (by addr_omega [hS])
          (by addr_omega [hS]) (by addr_omega [hS])))
  have hp₁ := h₁.1
  rv_eval [hsp, m224, hbyte] at hp₁
  have pc₁ : t₁.pc = 0x8000ba20 := by rw [hp₁]; rfl
  have k₁ := b8000ba14_keeps h₁
  have hm₁ := b8000ba14_mem_same h₁
  obtain ⟨T₁, n₁⟩ := ha.toTI.stepS hpre (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₁ .x2 (by decide))
  -- `0x8000ba20`: `concat([folds, tail])`
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000ba20_spec pc₁ (by
    rv_eval [k₁ .x2 (by decide), hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₂ := b8000ba20_keeps h₂
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₁.sp
  have X₂ : DFrame t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 384) 32 := by
    have := DFrame.of_memFrame (b8000ba20_frame h₂ (by rw [sp₁]; addr_omega [hb]))
    rw [sp₁] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  obtain ⟨T₂, n₂⟩ := T₁.stepS hpre X₂ (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])))
    (k₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₂.sp
  -- the folds, kept since `u`
  have hF := hfin.folds
  have hFraw := hF.vec.raw
  have hFl := hF.vec.len
  simp only [RawVecOk, Buf] at hFraw
  have kF (y : Word) (hy : (s.getReg .x2 - 776).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat) : t₁.getMem y = u.getMem y :=
    T₁.keepStk hpre (Or.inr hy)
  have hFp : vecPtr t₁ (s.getReg .x2 - 688) = vecPtr u (s.getReg .x2 - 688) :=
    kF _ (by addr_omega [hb])
  have hFn : vecLen t₁ (s.getReg .x2 - 688) = vecLen u (s.getReg .x2 - 688) :=
    kF _ (by addr_omega [hb])
  have hFb : (vecLen u (s.getReg .x2 - 688)).toNat = 0 ∨
      heapNext s ≤ (vecPtr u (s.getReg .x2 - 688)).toNat ∧
      (vecPtr u (s.getReg .x2 - 688)).toNat + 24 * (vecLen u (s.getReg .x2 - 688)).toNat ≤
        heapNext u := by
    rcases hF.lo with h0 | h0
    · left; rw [h0] at hFl; simpa using hFl
    · rcases hFraw.2 with h1 | h1
      · left; omega
      · right; have := hfin.hs; exact ⟨by omega, by omega⟩
  have hFe : eListAt t₂ (vecPtr u (s.getReg .x2 - 688)) (vecLen u (s.getReg .x2 - 688)).toNat =
      Wl.folds := by
    rw [T₂.eList hpre hFb]; exact hF.elems
  -- the tail
  obtain ⟨hTv, hTe, hTn⟩ := ha.tail
  have hTl := TailV.len ha.tail
  rw [ha.tfl] at hTl
  have hTc := hTv.len
  have hTb : mlF s Wl = 0 ∨ heapNext s ≤ (vecPtr v (s.getReg .x2 - 304)).toNat ∧
      (vecPtr v (s.getReg .x2 - 304)).toNat + 24 * mlF s Wl ≤ heapNext t₂ := by
    rcases hTn.2 with h0 | h0
    · left; omega
    · right; have := T₂.mono; have := T₁.mono; exact ⟨by omega, by simp only [heapNext, n₂, n₁] at *; omega⟩
  have hhv₂ := T₂.heap.hi
  simp only [heapEnd] at hhv₂ hab
  have hTe₂ : eListAt t₂ (vecPtr v (s.getReg .x2 - 304)) (mlF s Wl) = tf := by
    rw [← hTe]; simp only [vecEs]; rw [hTl]
    rcases hTb with h0 | h0
    · rw [h0]; rfl
    · exact DFrame.eList ((DFrame.of_same hm₁ _).trans X₂ fun _ h ↦ h) (fun y hy hx ↦ by
        simp only [Within] at hy; addr_omega [hy.1, hy.2, hx, h0.2, hhv₂, hab, hb]) (Or.inr (by omega))
  have hpT : vecPtr v (s.getReg .x2 - 304) = vecPtr t₁ (s.getReg .x2 - 304) := by
    simp only [vecPtr]; rw [hm₁]
  obtain ⟨t₃, r₃, hv₃⟩ := callConcat2 (o := s.getReg .x2 - 280) (A := s.getReg .x2 - 384)
    (p0 := vecPtr u (s.getReg .x2 - 688)) (n0 := (vecLen u (s.getReg .x2 - 688)).toNat)
    (p1 := vecPtr v (s.getReg .x2 - 304)) (n1 := mlF s Wl) hC hpre
    (T₂.inv hpre) T₂.heap (b8000ba20_pc h₂) (by rw [b8000ba20_x10 h₂, sp₁]; addr_omega [hb])
    (by rw [b8000ba20_x11 h₂, sp₁]; addr_omega [hb]) (b8000ba20_x12 h₂)
    (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    (by
      rw [show s.getReg .x2 - 384 = t₁.getReg .x2 + 656 by rw [sp₁]; addr_omega [hb],
        b8000ba20_m_x2_656 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 360 =
          s.getReg .x2 - 688 + 8 by addr_omega [hb]]
      exact hFp)
    (by
      rw [show s.getReg .x2 - 384 + 8 = t₁.getReg .x2 + 664 by rw [sp₁]; addr_omega [hb],
        b8000ba20_m_x2_664 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 368 =
          s.getReg .x2 - 688 + 16 by addr_omega [hb]]
      exact congrArg BitVec.toNat hFn)
    (by
      rw [show s.getReg .x2 - 384 + 16 = t₁.getReg .x2 + 672 by rw [sp₁]; addr_omega [hb],
        b8000ba20_m_x2_672 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 744 =
          s.getReg .x2 - 304 + 8 by addr_omega [hb]]
      exact hpT.symm)
    (by
      rw [show s.getReg .x2 - 384 + 24 = t₁.getReg .x2 + 680 by rw [sp₁]; addr_omega [hb],
        b8000ba20_m_x2_680 h₂, k₁ .x19 (by decide), ha.x19, BitVec.toNat_ofNat]
      have := (s.getReg .x12).isLt; simp only [mlF]; omega)
    (by
      rcases hFb with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by have := T₂.mono; have := T₁.mono; simp only [heapNext, n₂, n₁] at *; omega⟩)
    (by have := hFraw.1; exact this)
    hTb (hTn.1)
  rcases hv₃ with hd | ⟨hpc₃, hpres₃, hheap₃, hmono₃, X₃, hnew₃⟩
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl hd⟩
  rw [hFe, hTe₂] at hnew₃
  have hhi₃ := hheap₃.hi
  simp only [heapEnd] at hhi₃
  have T₃ : TI OA s x u t₃ Wl residual := T₂.trans X₃ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_trans T₂.mono ha.1, ha.2⟩)))))
    hheap₃ hmono₃ (hpres₃ .x2 (by decide))
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₃.sp
  -- `0x8000ba50`: the point's length against the first fold count
  obtain ⟨hf6, hfs, hfu, hf8⟩ := hfin.fold0 hpre
  have hFP : t₃.getMem x.FP = 6 := by rw [T₃.keepHeap hpre hfs hfu, hf6]
  have x9₃ : t₃.getReg .x9 = x.FP := by
    rw [hpres₃ .x9 (by decide), k₂ .x9 (by decide), k₁ .x9 (by decide), ha.x9]
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000ba50_spec
    (by rw [hpc₃, returnAddress_eq, b8000ba20_x1 h₂]; decide) (by
      rv_eval [sp₃, x9₃]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid (x := x.FP) (heap_region (n := 8)
            (by simp only [heapStart, heapNext] at hhs hfs ⊢; omega)
            (by have := T₃.mono; have := hheap₃.hi; simp only [heapEnd] at *; omega) hf8)
            (by omega) (by omega) hf8)
  have hP := hnew₃.vec
  have hPe := hnew₃.elems
  have hPn := hnew₃.buf
  have hPl : (vecLen t₃ (s.getReg .x2 - 280)).toNat = (Wl.folds ++ tf).length := by
    rw [← hPe]; simp only [vecEs, eListAt_length]
  have h776 : t₃.getMem (t₃.getReg .x2 + 776) = vecLen t₃ (s.getReg .x2 - 280) := by
    simp only [vecLen]
    rw [sp₃, show s.getReg .x2 - BitVec.ofNat 64 1040 + 776 = s.getReg .x2 - 280 + 16 by addr_omega [hb]]
  have hx9m : t₃.getMem (t₃.getReg .x9) = 6 := by rw [x9₃, hFP]
  by_cases hlt : (Wl.folds ++ tf).length < 6
  · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inl (dead_of_fetch (by
      rw [b8000ba50_pc_taken h₄ (by rw [hx9m, h776, hPl]; exact hlt)]; exact trap))⟩
  have pc₄ : t₄.pc = 0x8000ba5c :=
    b8000ba50_pc_not_taken h₄ (by rw [hx9m, h776, hPl]; show 6 ≤ _; omega)
  have hm₄ := b8000ba50_mem_same h₄
  have k₄ := b8000ba50_keeps h₄
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := by rw [k₄ .x2 (by decide), sp₃]
  have x10₄ : t₄.getReg .x10 = 6 := by rw [b8000ba50_x10 h₄, hx9m]
  -- `0x8000ba5c`: `concat([point[6..], point[..6]])`
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b8000ba5c_spec pc₄ (by
    rv_eval [sp₄]; and_intros <;> valid_access hst.valid [hb])
  have k₅ := b8000ba5c_keeps h₅
  have X₅ : DFrame t₄ t₅ fun a ↦ Within a (s.getReg .x2 - 384) 32 := by
    have := DFrame.of_memFrame (b8000ba5c_frame h₅ (by rw [sp₄]; addr_omega [hb]))
    rw [sp₄] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  have hPraw := hP.raw
  simp only [RawVecOk, Buf] at hPraw
  have hPc := hP.len
  set P := vecPtr t₃ (s.getReg .x2 - 280) with hPdef
  set n := (Wl.folds ++ tf).length with hndef
  obtain ⟨hPlo, hPhi⟩ : heapNext t₂ ≤ P.toNat ∧
      P.toNat + (vecCap t₃ (s.getReg .x2 - 280)).toNat * 24 ≤ heapNext t₃ := by
    rcases hPn.2 with h0 | h0
    · omega
    · exact h0
  have hsu₂ := T₂.su
  have hn₄ : heapNext t₄ = heapNext t₃ := by simp only [heapNext, hm₄]
  have h768 : t₄.getMem (t₄.getReg .x2 + 768) = P := by
    rw [hm₄, sp₄, show s.getReg .x2 - BitVec.ofNat 64 1040 + 768 = s.getReg .x2 - 280 + 8 by
      addr_omega [hb]]; rfl
  have h144 : (6 : Word) * 16 + 6 * 8 = BitVec.ofNat 64 (24 * 6) := by decide
  have h776' : t₄.getReg .x11 = vecLen t₃ (s.getReg .x2 - 280) := by rw [b8000ba50_x11 h₄, h776]
  obtain ⟨T₄, -⟩ := T₃.stepS hpre (DFrame.of_same hm₄ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₄ .x2 (by decide))
  obtain ⟨T₅, n₅⟩ := T₄.stepS hpre X₅ (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])))
    (k₅ .x2 (by decide))
  have m656 := b8000ba5c_m_x2_656 h₅
  have m664 := b8000ba5c_m_x2_664 h₅
  have m672 := b8000ba5c_m_x2_672 h₅
  have m680 := b8000ba5c_m_x2_680 h₅
  rw [h768, x10₄, h144] at m656
  rw [h776', x10₄] at m664
  rw [h768] at m672
  rw [x10₄] at m680
  rw [sp₄] at m656 m664 m672 m680
  have hn6 : 6 ≤ n := by omega
  have hn₅ : heapNext t₅ = heapNext t₃ := by simp only [heapNext, n₅, hm₄]
  have hLn : (vecLen t₃ (s.getReg .x2 - 280)).toNat = n := hPl
  have hPh := hPhi
  have hhi₃' := hheap₃.hi
  simp only [heapEnd] at hhi₃'
  obtain ⟨t₆, r₆, hv₆⟩ := callConcat2 (o := s.getReg .x2 - 464) (A := s.getReg .x2 - 384)
    (p0 := P + BitVec.ofNat 64 (24 * 6)) (n0 := n - 6) (p1 := P) (n1 := 6) hC hpre
    (T₅.inv hpre) T₅.heap (b8000ba5c_pc h₅)
    (by rw [b8000ba5c_x10 h₅, sp₄]; addr_omega [hb]) (by rw [b8000ba5c_x11 h₅, sp₄]; addr_omega [hb])
    (b8000ba5c_x12 h₅) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    (by rw [show s.getReg .x2 - 384 = s.getReg .x2 - BitVec.ofNat 64 1040 + 656 by addr_omega [hb]]
        exact m656)
    (by
      rw [show s.getReg .x2 - 384 + 8 = s.getReg .x2 - BitVec.ofNat 64 1040 + 664 by addr_omega [hb],
        m664]
      addr_omega [hLn, hn6])
    (by rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - BitVec.ofNat 64 1040 + 672 by
        addr_omega [hb]]; exact m672)
    (by rw [show s.getReg .x2 - 384 + 24 = s.getReg .x2 - BitVec.ofNat 64 1040 + 680 by
        addr_omega [hb], m680]; rfl)
    (Or.inr ⟨by addr_omega [hPlo, hsu₂, hPh, hhi₃', hPc, hLn, hn6],
      by rw [hn₅]; addr_omega [hPh, hhi₃', hPc, hLn, hn6]⟩)
    (by addr_omega [hPraw.1, hPh, hhi₃', hPc, hLn, hn6])
    (Or.inr ⟨by omega, by rw [hn₅]; omega⟩) hPraw.1
  rcases hv₆ with hd | ⟨hpc₆, hpres₆, hheap₆, hmono₆, X₆, hnew₆⟩
  · exact ⟨t₆, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), Or.inl hd⟩
  have r₁₆ := r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆))))
  have hhi₆ := hheap₆.hi
  simp only [heapEnd] at hhi₆
  have hm₂ := T₂.mono
  have hm₁' := T₁.mono
  have hm3 := hmono₃
  -- everything written since `v`
  have hv1 : heapNext v = heapNext t₁ := by simp only [heapNext, hm₁]
  have h12 : heapNext t₁ = heapNext t₂ := by simp only [heapNext, n₂]
  have X : DFrame v t₆ fun a ↦ Within a (s.getReg .x2 - 384) 32 ∨
      Within a (s.getReg .x2 - 280) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨
      (heapNext v ≤ a.toNat ∧ a.toNat < heapNext t₆) := by
    refine ((((((DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ Or.inl ha).trans X₃ fun a ha ↦ ?_).trans
      (DFrame.of_same hm₄ _) fun _ h ↦ h).trans X₅ fun a ha ↦ Or.inl ha).trans X₆ fun a ha ↦ ?_)
    · rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
    · rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · simp only [Fresh] at ha
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
  have hvn : heapNext v ≤ heapNext t₆ := by
    have : heapNext t₅ ≤ heapNext t₆ := hmono₆
    have : heapNext t₂ ≤ heapNext t₃ := hmono₃
    omega
  have T₆ : TI OA s x u t₆ Wl residual := ha.toTI.trans X (fun a ha' ↦ by
      rcases ha' with ha' | ha' | ha' | ha' | ha' | ha'
      · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
      · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
      · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
      · exact Or.inr (Or.inr (Or.inl ha'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_trans ha.mono ha'.1, ha'.2⟩)))))
    hheap₆ hvn (by rw [hpres₆ .x2 (by decide), k₅ .x2 (by decide), sp₄, hsp])
  have hXh (a : Word) (ha' : Within a (s.getReg .x2 - 384) 32 ∨
      Within a (s.getReg .x2 - 280) 24 ∨ Within a (s.getReg .x2 - 464) 24 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨
      (heapNext v ≤ a.toNat ∧ a.toNat < heapNext t₆)) :
      ¬ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext v) := by
    have hhv := ha.heap.hi
    simp only [heapEnd] at hhv
    rcases ha' with ha' | ha' | ha' | ha' | ha' | ha'
    · exact SS.heap hpre (Or.inr (Or.inl (by addr_omega [ha', hb]))) ha.heap.hi
    · exact SS.heap hpre (Or.inr (Or.inl (by addr_omega [ha', hb]))) ha.heap.hi
    · exact SS.heap hpre (Or.inr (Or.inl (by addr_omega [ha', hb]))) ha.heap.hi
    · exact SS.heap hpre (Or.inr (Or.inr (Or.inl ha'))) ha.heap.hi
    · intro ⟨_, h2⟩; addr_omega [ha', h2, hhv, hnx, hab, hb]
    · intro ⟨_, h2⟩; omega
  have kw (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 464).toNat ∨ (s.getReg .x2 - 440).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 384).toNat ∨ (s.getReg .x2 - 352).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 280).toNat) : t₆.getMem y = v.getMem y :=
    X.word (fun a ha' hx ↦ by
      rcases hy with hy | hy | hy <;> rcases hx with hx | hx | hx | hx | hx | hx
      all_goals first
        | addr_omega [ha', hx, hy, hb]
        | addr_omega [ha', hx, hy, hb, hnx]
        | addr_omega [ha', hx.2, hy, hb, hhi₆, hab]) (by rcases hy with hy | hy | hy <;> addr_omega [hy, hb])
  -- the point, kept since `t₃`
  have Y : DFrame t₃ t₆ fun a ↦ Within a (s.getReg .x2 - 384) 32 ∨
      (Within a (s.getReg .x2 - 464) 24 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
        Within a nextAddr 8 ∨ Fresh t₅ t₆ a) :=
    (((DFrame.of_same hm₄ _).trans X₅ fun a h ↦ Or.inl h)).trans X₆ fun a h ↦ Or.inr h
  have hPk := vecE_keep Y hP (fun a ha' ↦ ⟨fun hw ↦ by
      rcases ha' with ha' | ha' | ha' | ha' | ha'
      · addr_omega [ha', hw, hb]
      · addr_omega [ha', hw, hb]
      · addr_omega [ha', hw, hb]
      · addr_omega [ha', hw, hb, hnx]
      · simp only [Fresh] at ha'; addr_omega [ha'.2, hw, hb, hhi₆, hab], fun hw ↦ by
      simp only [Within] at hw
      rw [← hPdef] at hw
      rcases ha' with ha' | ha' | ha' | ha' | ha'
      · addr_omega [ha', hw.1, hw.2, hb, hPh, hhi₃', hab]
      · addr_omega [ha', hw.1, hw.2, hb, hPh, hhi₃', hab]
      · addr_omega [ha', hw.1, hw.2, hb, hPh, hhi₃', hab]
      · addr_omega [ha', hw.1, hw.2, hnx, hPh, hhi₃', hab, hb]
      · simp only [Fresh] at ha'; rw [hn₅] at ha'; omega⟩)
    (by addr_omega [hb]) (by rw [← hn₅]; exact hmono₆) hheap₃
  have e35 (q : Word) (m : ℕ) (hq : q.toNat + 24 * m ≤ heapNext t₃) :
      eListAt t₅ q m = eListAt t₃ q m :=
    DFrame.eList ((DFrame.of_same hm₄ _).trans X₅ fun _ h ↦ h) (fun y hy hx ↦ by
      simp only [Within] at hy; addr_omega [hy.1, hy.2, hx, hq, hhi₃', hab, hb]) (Or.inr (by omega))
  have hpt : eListAt t₃ P n = Wl.folds ++ tf := by rw [← hPe, ← hLn]; rfl
  refine ⟨t₆, r₁₆, Or.inr {
    toTI := T₆
    pc := by rw [hpc₆, returnAddress_eq, b8000ba5c_x1 h₅]; decide
    tfl := ha.tfl
    x8 := by
      rw [hpres₆ .x8 (by decide), k₅ .x8 (by decide), k₄ .x8 (by decide), hpres₃ .x8 (by decide),
        b8000ba20_x8 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 744 = s.getReg .x2 - 304 + 8 by
          addr_omega [hb]]
      simp only [vecPtr]
      rw [kw _ (Or.inr (Or.inr (by addr_omega [hb]))), hm₁]
    x19 := by
      rw [hpres₆ .x19 (by decide), k₅ .x19 (by decide), k₄ .x19 (by decide), hpres₃ .x19 (by decide),
        k₂ .x19 (by decide), k₁ .x19 (by decide), ha.x19]
    tail := ha.tail.keep ha.heap ha.toTI.fin.su X (fun a ha' hw ↦ by
        rcases ha' with ha' | ha' | ha' | ha' | ha' | ha'
        · addr_omega [ha', hw, hb]
        · addr_omega [ha', hw, hb]
        · addr_omega [ha', hw, hb]
        · addr_omega [ha', hw, hb]
        · addr_omega [ha', hw, hb, hnx]
        · addr_omega [ha'.2, hw, hb, hhi₆, hab]) hXh (by addr_omega [hb]) hvn
    trg := by
      rw [kw _ (Or.inl (by addr_omega [hb])), kw _ (Or.inl (by addr_omega [hb])),
        kw _ (Or.inl (by addr_omega [hb]))]
      exact ha.trg
    six := by omega
    point := ⟨hPk.1, by rw [hPk.2.1]; exact hPe, by
      rw [hPk.2.2.1, hPk.2.2.2.1]
      exact NewBuf.grow (NewBuf.widen hPn (by have := T₁.mono; omega)) (by omega)⟩
    rot := by
      refine ⟨hnew₆.vec, ?_, NewBuf.widen hnew₆.buf (by omega)⟩
      rw [hnew₆.elems, e35 _ _ (by addr_omega [hPh, hPc, hLn, hn6, hhi₃']),
        e35 _ _ (by omega), ← hpt, pt_drop, pt_take _ _ hn6]
    value := ha.value.keep hpre (ha.toTI.inv hpre) X fun a ha' ↦ by
      have hsv := ha.toTI.su
      rcases ha' with ha' | ha' | ha' | ha' | ha' | ha'
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inl (by addr_omega [ha', hb])
      · exact Or.inr (Or.inl ha')
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by simp only [heapEnd]; omega⟩)) }⟩

end Rv64Verifier.Proofs.Pcs.Vso
