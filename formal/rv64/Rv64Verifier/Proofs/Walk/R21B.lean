import Rv64Verifier.Proofs.Walk.R21H

/-!
# `walk` R21: `ring_switch`

`r21ring`: from `AtR21`, `0x80003ff8` calls `ring_switch` with the point's `Vec` (`S - 1728`),
the slices and the transcript; it returns at `0x8000400c` with the target at `S - 928` and the
weight at `S - 904` (`RingR21`): the point's `Vec` moved there, the coefficients' new.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.PcsContracts Rv64Verifier.Pcs Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000400c`, `ring_switch` returned: the target at `S - 928`, the weight at `S - 904`. -/
structure RingR21 (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t v : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (cl : List ColumnClaim) (ks ke : ℕ) : Prop
    extends CoreT OI s u₀ w t v layout lir evs P C L.toNat cl
      (afterRing layout rows lir bus cl ks ke
        (eAt v (s.getReg .x2 - 928), ringWeightAt v (s.getReg .x2 - 904))) where
  pc : v.pc = 0x8000400c
  x18 : v.getReg .x18 = P
  x22 : v.getReg .x22 = lir
  x23 : v.getReg .x23 = s.getReg .x10
  x24 : v.getReg .x24 = s.getReg .x2 - 512
  x25 : v.getReg .x25 = L
  /-- The weight's point and coefficients, allocated by `walk`. -/
  pointOld : Old s v (vecPtr v (s.getReg .x2 - 904)) (24 * (vecLen v (s.getReg .x2 - 904)).toNat)
  coeffsOld : Old s v (vecPtr v (s.getReg .x2 - 880)) (24 * (vecLen v (s.getReg .x2 - 880)).toNat)
  /-- The point's capacity, the `PlacedRing` niche's tag. -/
  cap : (vecCap v (s.getReg .x2 - 904)).toNat < 2 ^ 62

theorem ringSwitch_coeffs {pt sl : List E} {T T' : TState} {r : E × Pcs.RingWeightRust}
    (h : (Pcs.ringSwitchRust pt sl).run T = some (r, T')) : r.2.coefficients.length = 64 := by
  simp only [Pcs.ringSwitchRust, StateT.run_bind] at h
  cases hs : (TM.samples Pcs.ringMapShiftsRust.length).run T with
  | none => simp [hs] at h
  | some p =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    simp only [StateT.run_pure, Option.pure_def, Option.some.injEq] at h
    simp only [Prod.mk.injEq] at h
    rw [← h.1]
    simp [Pcs.ringCoefficientsRust, Pcs.kBitsRust]

theorem apart_comm {a b : Word} {n m : Nat} (h : Apart a n b m) : Apart b m a n := by
  simp only [Apart] at h ⊢; omega

section Ring
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {cl : List ColumnClaim}
  {pt sl : List E} {ks ke : ℕ}

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- `ring_switch`, to its return at `0x8000400c`, or a dead end. -/
theorem r21ring (hRS : RingSwitchSpec) (hpre : WalkPre s)
    (A : AtR21 OI s u₀ w t u layout rows lir bus evs P C L cl pt sl ks ke) :
    ∃ v, Reaches Image.code u v ∧
      (RingR21 OI s u₀ w t v layout rows lir bus evs P C L cl ks ke ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := A.toCoreT
  have I := H.rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd, heapStart] at hh hs0 hab
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003ff8_spec A.pc (by rv_eval [])
  have m₁ := b80003ff8_mem_same h₁
  have k₁ := b80003ff8_keeps h₁
  have I₁ : Inv s u₁ := I.same m₁ (k₁ .x2 (by decide))
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have ptr₁ : u₁.getMem (tp s) = s.getReg .x13 := by rw [m₁]; exact H.proofPtr
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 928 := by rw [b80003ff8_x10 h₁, sp]; bv_omega
  have x11₁ : u₁.getReg .x11 = s.getReg .x2 - 1728 := by rw [b80003ff8_x11 h₁, sp]; bv_omega
  have x14₁ : u₁.getReg .x14 = tp s := by rw [b80003ff8_x14 h₁, sp, tp]; bv_omega
  have x12₁ : u₁.getReg .x12 = u.getReg .x12 := k₁ .x12 (by decide)
  have x13₁ : u₁.getReg .x13 = u.getReg .x13 := k₁ .x13 (by decide)
  have hrs : ringSwitchStack = 1584 := by decide
  have hk : ringSwitchStack ≤ 8736 := by rw [hrs]; omega
  have hEnd : heapEnd ≤ (stackLo u₁ ringSwitchStack).toNat := by
    rw [stackLo_callee I₁, hrs]; simp only [heapEnd]; addr_omega [hab, hb1]
  have ePt : vecPtr u₁ (s.getReg .x2 - 1728) = vecPtr u (s.getReg .x2 - 1728) := m₁ _
  have eLn : vecLen u₁ (s.getReg .x2 - 1728) = vecLen u (s.getReg .x2 - 1728) := m₁ _
  have hbP : HeapBuf u₁ (vecPtr u₁ (s.getReg .x2 - 1728))
      (24 * (vecLen u₁ (s.getReg .x2 - 1728)).toNat) := by
    rw [ePt, eLn]; exact (A.pointOld.heapBuf hpre.heap).mono hn₁.ge
  have hbS : HeapBuf u₁ (u₁.getReg .x12) (24 * (u₁.getReg .x13).toNat) := by
    rw [x12₁, x13₁]; exact (A.slices.heapBuf hpre.heap).mono hn₁.ge
  have fo (c : Word) (k n : Nat) (hc : c.toNat = k) (hk1 : 104 + n ≤ k) (hk2 : k ≤ 2656) :=
    fr_ok hpre I₁ (c := c) (k := k) (n := n) (m := ringSwitchStack) hc hk1 hk2 hk
  have pre : RingSwitchPre u₁ := {
    heap := I₁.heap
    stack := hpre.stack.sub 2656 I₁.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    rodata := I₁.rodata hpre
    out := by
      rw [x10₁]
      obtain ⟨o1, o2, o3⟩ := fo 928 928 72 rfl (by omega) (by omega)
      exact ⟨by addr_omega [hb1, hb2, hb3], o2, o1, o3⟩
    point := by
      rw [x11₁]
      obtain ⟨o1, o2, -⟩ := fo 1728 1728 24 rfl (by omega) (by omega)
      exact ⟨Or.inr (by addr_omega [hb1, hb2, hb3]), o2, o1⟩
    pointBuf := by rw [x11₁]; exact hbP.src I₁.heap hEnd
    slices := hbS.src I₁.heap hEnd
    self := by rw [x14₁]; exact tin hpre I₁ ptr₁ hk
    outSelf := by rw [x10₁, x14₁, tp]; addr_omega [hb1]
    outProof := by
      rw [x14₁, x10₁]; exact proofApart_fr hpre I₁ ptr₁ (k := 928) (n := 72) (by omega) (by omega)
    outPoint := by rw [x10₁, x11₁]; addr_omega [hb1]
    outPointBuf := by
      rw [x10₁, x11₁]
      exact apart_comm (hbP.apart I₁.heap (by simp only [heapEnd]; addr_omega [hab, hb1]))
    outSlices := by
      rw [x10₁]
      exact apart_comm (hbS.apart I₁.heap (by simp only [heapEnd]; addr_omega [hab, hb1]))
    pointSponge := by rw [x11₁, x14₁, tp]; addr_omega [hb1]
    pointBufSponge := by
      rw [x11₁, x14₁]
      exact hbP.apart I₁.heap (by rw [tp]; simp only [heapEnd]; addr_omega [hab, hb1])
    slicesSponge := by
      rw [x14₁]; exact hbS.apart I₁.heap (by rw [tp]; simp only [heapEnd]; addr_omega [hab, hb1]) }
  obtain ⟨v, hr, ⟨hpc, hp, post⟩ | hd⟩ := hRS.call (Reaches.refl u₁) (b80003ff8_pc h₁) pre
  swap
  · exact ⟨v, hr₁.trans hr, Or.inr hd⟩
  have fr := post.frame
  rw [x10₁, x14₁] at fr
  have st : StepW s u₁ v (Within · (s.getReg .x2 - 928) 72) True := by
    refine ⟨fr.mono fun a ha ↦ ?_, post.heap, post.mono, hp .x2 (by decide)⟩
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, by simp only [Within] at ha ⊢; omega⟩)))
    · rw [stackLo_callee I₁, hrs] at ha
      exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  have C₁ := H.same hpre m₁ (k₁ .x2 (by decide))
  obtain ⟨T₀, hT₀⟩ := transcriptAt_exists u₁ (tp s)
  obtain ⟨r₀, T₀', hrun₀, -, -, w24, w32, w40, nv, -⟩ := post.value T₀ (by rw [x14₁]; exact hT₀)
  have h64 := ringSwitch_coeffs hrun₀
  rw [x10₁, x11₁] at w24 w32 w40
  rw [x10₁] at nv
  have e904 : s.getReg .x2 - 928 + 24 = s.getReg .x2 - 904 := by bv_omega
  have e880 : s.getReg .x2 - 928 + 48 = s.getReg .x2 - 880 := by bv_omega
  rw [e904] at w24
  rw [e880] at nv
  have wP : vecPtr v (s.getReg .x2 - 904) = vecPtr u (s.getReg .x2 - 1728) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 904 + 8 = s.getReg .x2 - 928 + 32 by bv_omega, w32, m₁]
  have wL : vecLen v (s.getReg .x2 - 904) = vecLen u (s.getReg .x2 - 1728) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 904 + 16 = s.getReg .x2 - 928 + 40 by bv_omega, w40, m₁]
  have wC : vecCap v (s.getReg .x2 - 904) = vecCap u (s.getReg .x2 - 1728) := by
    simp only [vecCap]; rw [w24, m₁]
  have htr : TracksR OI s v
      (digestAt u₀ (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat)
      (afterRing layout rows lir bus cl ks ke
        (eAt v (s.getReg .x2 - 928), ringWeightAt v (s.getReg .x2 - 904))) := by
    refine C₁.tracks.bind (keeps_ringSwitchRust pt sl) fun T hT ↦ ?_
    obtain ⟨r, T', hrun, e1, e2, -, -, -, -, hT'⟩ := post.value T (by rw [x14₁]; exact hT)
    rw [x11₁, x12₁, x13₁] at hrun
    rw [x10₁] at e1 e2
    rw [x14₁] at hT'
    rw [e904] at e2
    have ept : vecEs u₁ (s.getReg .x2 - 1728) = pt := by
      rw [← A.point.elems]; simp only [vecEs, ePt, eLn]
      exact Bus.eListAt_congr fun i _ ↦ by simp only [eAt, m₁]
    have esl : eListAt u₁ (u.getReg .x12) (u.getReg .x13).toNat = sl := by
      rw [← A.slicesVal]; exact Bus.eListAt_congr fun i _ ↦ by simp only [eAt, m₁]
    rw [ept, esl] at hrun
    refine ⟨T', ?_, hT'⟩
    rw [hrun, show r = (eAt v (s.getReg .x2 - 928), ringWeightAt v (s.getReg .x2 - 904)) from
      Prod.ext e1.symm e2.symm]
  have C₂ := C₁.step hpre st (fun a ha ↦ by
      obtain ⟨o1, o2⟩ := range_ok hpre C₁.rest (c := 928) (k := 928) (n := 72) rfl (by omega)
        (by omega) ha
      refine ⟨o1, o2, ?_⟩
      rw [tp]; simp only [Within] at ha ⊢; addr_omega [ha, hb1])
    (fun a ha ↦ by simp only [Within] at ha ⊢; refine ⟨?_, ?_⟩ <;> addr_omega [ha, hb1]) htr
  have hm := post.mono
  have po := A.pointOld
  have rw₁ := A.point.vec.raw
  simp only [RawVecOk, Buf] at rw₁
  have nl : (vecLen v (s.getReg .x2 - 880)).toNat = 64 := by
    have := congrArg List.length nv.elems
    rw [h64] at this
    simpa only [vecEs, eListAt_length] using this
  have nvl := nv.vec.len
  have nb := nv.buf
  have m₀ := I.mono
  simp only [NewBuf] at nb
  refine ⟨v, hr₁.trans hr, Or.inl {
    toCoreT := C₂
    pc := by rw [hpc, returnAddress_eq, b80003ff8_x1 h₁]; decide
    x18 := by rw [hp .x18 (by decide), k₁ .x18 (by decide), A.x18]
    x22 := by rw [hp .x22 (by decide), k₁ .x22 (by decide), A.x22]
    x23 := by rw [hp .x23 (by decide), k₁ .x23 (by decide), A.x23]
    x24 := by rw [hp .x24 (by decide), k₁ .x24 (by decide), A.x24]
    x25 := by rw [hp .x25 (by decide), k₁ .x25 (by decide), A.x25]
    pointOld := by
      rw [wP, wL]; simp only [Old] at po ⊢; rw [hn₁] at hm; omega
    coeffsOld := by
      simp only [Old]; rw [nl]; rw [nl] at nvl; rw [hn₁] at nb; omega
    cap := by rw [wC]; simp only [heapNext, heapStart] at rw₁ hh; omega }⟩

end Ring

end Rv64Verifier.Proofs.Walk
