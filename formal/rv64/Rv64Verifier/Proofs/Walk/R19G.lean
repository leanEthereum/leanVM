import Rv64Verifier.Proofs.Walk.R19F

/-!
# `walk` R19, the public input's claims: `r19pB1`, the two-element `Vec` and `Scaler::new`
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x80003c54`, `Scaler::new` returned `Plain(c)` at `S - 1344`. -/
structure AtB1 (s u z : MachineState) (i : Nat) (c : E) (n : Nat) (L Q : Word) : Prop where
  st : StepW s u z (IW s) False
  pc : z.pc = 0x80003c54
  qa : Q.toNat % 8 = 0
  q0 : heapNext u ≤ Q.toNat
  q1 : (vecPtr z (s.getReg .x2 - 1488)).toNat + 24 * n ≤ Q.toNat
  q2 : Q.toNat + 48 ≤ heapNext z
  cpa : (vecPtr z (s.getReg .x2 - 1488)).toNat % 8 = 0
  cp1 : heapNext u ≤ (vecPtr z (s.getReg .x2 - 1488)).toNat
  cl : vecLen z (s.getReg .x2 - 1488) = BitVec.ofNat 64 n
  ce : vecEs z (s.getReg .x2 - 1488) = c :: List.replicate (n - 1) 0
  w0 : z.getMem Q = pubLo s i
  w8 : z.getMem (Q + 8) = 0
  w16 : z.getMem (Q + 16) = 0
  w24 : z.getMem (Q + 24) = pubHi s i
  w32 : z.getMem (Q + 32) = 0
  w40 : z.getMem (Q + 40) = 0
  tag : z.getMem (s.getReg .x2 - 1344) = 1
  sc : eAt z (s.getReg .x2 - 1336) = c
  x18 : z.getReg .x18 = 1
  x21 : z.getReg .x21 = 0
  x23 : z.getReg .x23 = BitVec.ofNat 64 i
  x25 : z.getReg .x25 = Q
  s160 : z.getMem (s.getReg .x2 - 2496) = L + BitVec.ofNat 64 i
  s192 : z.getMem (s.getReg .x2 - 2464) = BitVec.ofNat 64 i

section Iter
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {i : Nat} {c : E}
  {pt : Word}

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- From `0x80003bdc` through `reserve`, the two values, and `Scaler::new`, or the run dies. -/
theorem r19pB1 (hR : ReserveFastSpec 0x80008a10) (hS : MultilinearContracts.ScalerSpec)
    (hpre : WalkPre s) (Hd : HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt)
    {x : MachineState} {Q : Word} (A : AtA s u x i c layout.logMemory L Q) :
    ∃ z, Reaches Image.code x z ∧ (AtB1 s u z i c layout.logMemory L Q ∨ Dead Image.code z) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have hw : ∀ a, IW s a → InF s a := fun a ha ↦ (IW_ok hpre Hd.rest ha).1
  have I := (Hd.core hpre A.st).rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hl := Hd.rest.inv.heap.lo
  simp only [heapEnd, heapStart] at hh hl
  have qa := A.qa
  have q2 := A.q2
  have q0 : heapNext u ≤ Q.toNat := by have := A.q1; have := A.cp1; omega
  -- `0x80003bdc`
  obtain ⟨x₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003bdc_spec A.pc (by
    rv_eval [sp, A.x24]; and_intros <;> first | valid_access hval [hb1, hb3] | addr_omega [hb1])
  have k₁ := b80003bdc_keeps h₁
  have fr₁ : DFrame x x₁ fun a ↦ Within a (s.getReg .x2 - 512) 24 ∨
      Within a (s.getReg .x2 - 2496) 8 := h₁.dframe (by
    rv_eval [sp, A.x24]; and_intros <;> simp only [Within] <;> addr_omega [hb1])
  have st₁ : StepW s x x₁ (IW s) False := StepW.ofFrame hpre I.heap (fr₁.mono fun a ha ↦ by
      simp only [IW, Within] at ha ⊢; addr_omega [ha, hb1]) hw (k₁ .x2 (by decide))
  have stx₁ := (A.st.trans st₁).weaken (fun a ha ↦ ha.elim id id) (fun h ↦ h.elim id id)
  have I₁ := (Hd.core hpre stx₁).rest.inv
  have x24₁ : x₁.getReg .x24 = s.getReg .x2 - 512 := by rw [k₁ .x24 (by decide), A.x24]
  have e0 : x₁.getMem (s.getReg .x2 - 512) = 2 := by
    rw [← A.x24, b80003bdc_m_x24_0 h₁]
  have e8 : x₁.getMem (s.getReg .x2 - 512 + 8) = Q := by
    rw [← A.x24, b80003bdc_m_x24_8 h₁, A.x10]
  have e16 : x₁.getMem (s.getReg .x2 - 512 + 16) = 0 := by
    rw [← A.x24, b80003bdc_m_x24_16 h₁]
  have e160 : x₁.getMem (s.getReg .x2 - 2496) = L + BitVec.ofNat 64 i := by
    rw [← spAdd hpre sp 160 2496 rfl, b80003bdc_m_x2_160 h₁, A.x25]
  -- `reserve`
  have x10₁ : x₁.getReg .x10 = s.getReg .x2 - 512 := by
    rw [b80003bdc_x10 h₁, spAdd hpre sp 2144 512 rfl]
  obtain ⟨v, hrv, ⟨hpcv, hp, pv10, pvm⟩ | hd⟩ := hR.call hr₁ (b80003bdc_pc h₁)
    ⟨by rw [x10₁]; valid_sub hval [hb1, hb3], by
      rw [x10₁, b80003bdc_x11 h₁]; simp only [vecLen, vecCap, e0, e16]; decide⟩
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have st₂ : StepW s x₁ v (IW s) False := StepW.same I₁.heap pvm (hp .x2 (by decide)) _ _
  have stv := (stx₁.trans st₂).weaken (fun a ha ↦ ha.elim id id) (fun h ↦ h.elim id id)
  have Iv := (Hd.core hpre stv).rest.inv
  have spv := Iv.sp
  have x24v : v.getReg .x24 = s.getReg .x2 - 512 := by rw [hp .x24 (by decide), x24₁]
  have pcv : v.pc = 0x80003c04 := by rw [hpcv, returnAddress, b80003bdc_x1 h₁]; decide
  have e8v : v.getMem (s.getReg .x2 - 512 + 8) = Q := by rw [pvm]; exact e8
  have e16v : v.getMem (s.getReg .x2 - 512 + 16) = 0 := by rw [pvm]; exact e16
  have e8w : v.getMem (s.getReg .x2 - 504) = Q := by
    rw [show s.getReg .x2 - 504 = s.getReg .x2 - 512 + 8 by bv_omega]; exact e8v
  have e16w : v.getMem (s.getReg .x2 - 496) = 0 := by
    rw [show s.getReg .x2 - 496 = s.getReg .x2 - 512 + 16 by bv_omega]; exact e16v
  have hv := stv.mono
  -- `0x80003c04`
  obtain ⟨z₁, hrz₁, hz₁⟩ := Sym.BlockSpec.reaches b80003c04_spec pcv (by
    rv_eval [spv, x24v, e8v, e16v, e8w, e16w]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [qa, q0, q2, hv, hh, hl]))
  have k₂ := b80003c04_keeps hz₁
  have frc : DFrame v z₁ fun a ↦ False ∨ Within a Q 48 := hz₁.dframe (by
    rv_eval [spv, x24v, e8v, e16v, e8w, e16w]
    and_intros <;> (right; simp only [Within]; constructor <;> addr_omega [q2, hh]))
  have st₃ : StepW s u z₁ (IW s) False := (stv.thenW hpre Hd.rest.inv.heap (W' := fun _ ↦ False)
    (fun _ h ↦ h.elim) frc q0 (by have := st₁.mono; have := st₂.mono; omega)
    (k₂ .x2 (by decide))).weaken
    (fun a ha ↦ ha.elim id False.elim) id
  have Iz := (Hd.core hpre st₃).rest.inv
  have q5 := b80003c04_m5 hz₁
  have q4 := b80003c04_m4 hz₁
  have q3 := b80003c04_m3 hz₁
  have q2' := b80003c04_m2 hz₁
  have q1' := b80003c04_m1 hz₁
  have q0' := b80003c04_m0 hz₁
  rw [x24v, e8v, e16v] at q5 q4 q3 q2' q1' q0'
  simp only [zero_mul, add_zero] at q5 q4 q3 q2' q1' q0'
  -- `Scaler::new`
  have x10z : z₁.getReg .x10 = s.getReg .x2 - 1344 := by
    rw [b80003c04_x10 hz₁, spAdd hpre spv 1312 1344 rfl]
  have x11z : z₁.getReg .x11 = s.getReg .x2 - 416 := by
    rw [b80003c04_x11 hz₁, spAdd hpre spv 2240 416 rfl]
  have x12z : z₁.getReg .x12 = 1 := by rw [b80003c04_x12 hz₁, x24v, e16v]; rfl
  have hss : MultilinearContracts.scalerStack ≤ 8736 := by decide
  have pre : MultilinearContracts.ScalerPre z₁ := {
    heap := Iz.heap
    out := by rw [x10z]; valid_sub hval [hb1, hb3]
    r := by rw [x11z]; valid_sub hval [hb1, hb3]
    stack := hpre.stack.sub 2656 Iz.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by
      rw [x10z]
      exact (fr_ok hpre Iz (c := 1344) (k := 1344) (n := 32) (m := 0) rfl (by omega) (by omega)
        (by omega)).1
    outStack := by
      rw [x10z]
      exact (fr_ok hpre Iz (c := 1344) (k := 1344) (n := 32) rfl (by omega) (by omega) hss).2.1
    rFree := by
      rw [x11z]
      exact (fr_ok hpre Iz (c := 416) (k := 416) (n := 24) (m := 0) rfl (by omega) (by omega)
        (by omega)).1
    rStack := by
      rw [x11z]
      exact (fr_ok hpre Iz (c := 416) (k := 416) (n := 24) rfl (by omega) (by omega) hss).2.1
    rOut := by rw [x11z, x10z]; simp only [Apart]; right; right; right; addr_omega [hb1]
    rodata := Iz.rodata hpre }
  obtain ⟨z₂, hrz₂, ⟨hpcz₂, hpz, post⟩ | hd⟩ := hS.call hrz₁ (b80003c04_pc hz₁) pre
  swap
  · exact ⟨z₂, hrv.trans hrz₂, Or.inr hd⟩
  have frs := post.frame
  rw [x10z] at frs
  have st₄ : StepW s z₁ z₂ (IW s) False :=
    (StepW.ofCall hpre Iz hss (DFrame.of_byteFrame frs) post.heap post.mono
      (hpz .x2 (by decide))).weaken (fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inl ha)))) id
  obtain ⟨pl1, pl2⟩ := post.plain (by rw [x12z]; decide)
  rw [x10z] at pl1 pl2
  rw [x11z] at pl2
  have hz1 := st₄.mono
  have hsl := stackLo_callee Iz MultilinearContracts.scalerStack
  -- what the steps from `x` keep
  have hx1 := st₁.mono
  have hx2 := st₂.mono
  have hz0 := st₃.mono
  have fall : DFrame x z₂ fun a ↦ Within a (s.getReg .x2 - 512) 24 ∨
      Within a (s.getReg .x2 - 2496) 8 ∨ Within a Q 48 ∨ Within a (s.getReg .x2 - 1344) 32 ∨
      Within a (stackLo z₁ MultilinearContracts.scalerStack) MultilinearContracts.scalerStack ∨
      Within a nextAddr 8 ∨ Fresh z₁ z₂ a :=
    (((fr₁.mono fun a ha ↦ ha.elim Or.inl fun h ↦ Or.inr (Or.inl h)).trans
      (DFrame.of_same pvm _) fun _ h ↦ h).trans
      (frc.mono fun a ha ↦ ha.elim False.elim fun h ↦ Or.inr (Or.inr (Or.inl h))) fun _ h ↦ h).trans
      ((DFrame.of_byteFrame frs).mono fun a ha ↦ Or.inr (Or.inr (Or.inr ha))) fun _ h ↦ h
  have hz2h := post.heap.hi
  simp only [heapEnd] at hz2h
  have hvz : heapNext z₁ = heapNext v := by
    simp only [heapNext]
    rw [frc nextAddr fun j hj hw' ↦ by
      rcases hw' with hw' | hw'
      · exact hw'
      · simp only [Within, nextAddr] at hw'; addr_omega [hw', hj, q2, hh]]
  have gxF (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648)
      (hk1 : k ≤ 480 ∨ (520 ≤ k ∧ k ≤ 1312) ∨ (1352 ≤ k ∧ k ≤ 2488) ∨ 2504 ≤ k) :
      z₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = x.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    fall _ fun j hj hw' ↦ by
      have k1 := hk.1
      have k2 := hk.2
      rw [hsl] at hw'
      simp only [Within, Fresh, nextAddr] at hw'
      rcases hw' with hw' | hw' | hw' | hw' | hw' | hw' | hw' <;>
        rcases hk1 with q | ⟨q, q'⟩ | ⟨q, q'⟩ | q <;>
        first
          | addr_omega [hw', hj, hb1, q, k1, k2, hh, q2, hz0, hz1, hss, hz2h]
          | addr_omega [hw', hj, hb1, q, q', k1, k2, hh, q2, hz0, hz1, hss, hz2h]
  have gxH (y : Word) (y1 : y.toNat + 8 ≤ Q.toNat) (y2 : 0x20000000 ≤ y.toNat) :
      z₂.getMem y = x.getMem y :=
    fall _ fun j hj hw' ↦ by
      rw [hsl] at hw'
      simp only [Within, Fresh, nextAddr] at hw'
      rcases hw' with hw' | hw' | hw' | hw' | hw' | hw' | hw' <;>
        addr_omega [hw', hj, hb1, y1, y2, hh, q2, hx1, hx2, hvz, hz1, hss, hab, hz2h]
  have frs' := DFrame.of_byteFrame frs
  have fzF (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) (hk1 : k ≤ 1312 ∨ 1352 ≤ k) :
      z₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = z₁.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    frs' _ fun j hj hw' ↦ by
      have k1 := hk.1
      have k2 := hk.2
      rw [hsl] at hw'
      simp only [Within, Fresh, nextAddr] at hw'
      rcases hw' with hw' | hw' | hw' | hw' <;> rcases hk1 with q | q <;>
        addr_omega [hw', hj, hb1, q, k1, k2, hss, hz2h]
  have fzH (y : Word) (y1 : y.toNat + 8 ≤ heapNext z₁) (y2 : 0x20000000 ≤ y.toNat) :
      z₂.getMem y = z₁.getMem y :=
    frs' _ fun j hj hw' ↦ by
      rw [hsl] at hw'
      simp only [Within, Fresh, nextAddr] at hw'
      have hz1h := Iz.heap.hi
      simp only [heapEnd] at hz1h
      rcases hw' with hw' | hw' | hw' | hw' <;>
        addr_omega [hw', hj, hb1, y1, y2, hss, hab, hz1h]
  have fcF (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) :
      z₁.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    frc _ fun j hj hw' ↦ by
      have k1 := hk.1
      have k2 := hk.2
      rcases hw' with hw' | hw'
      · exact hw'
      · simp only [Within] at hw'; addr_omega [hw', hj, hb1, k1, k2, q2, hh]
  have eP : vecPtr z₂ (s.getReg .x2 - 1488) = vecPtr x (s.getReg .x2 - 1488) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 1488 + 8 = s.getReg .x2 - BitVec.ofNat 64 1480 by bv_omega,
      gxF 1480 (by omega) (by omega)]
  have eL : vecLen z₂ (s.getReg .x2 - 1488) = vecLen x (s.getReg .x2 - 1488) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 1488 + 16 = s.getReg .x2 - BitVec.ofNat 64 1472 by bv_omega,
      gxF 1472 (by omega) (by omega)]
  have aq1 := A.q1
  have acp := A.cp1
  have hn64 : layout.logMemory < 2 ^ 64 := by
    have := (vecLen x (s.getReg .x2 - 1488)).isLt; rw [A.cl, BitVec.toNat_ofNat] at this; omega
  have hlt : (vecLen x (s.getReg .x2 - 1488)).toNat = layout.logMemory := by
    rw [A.cl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have reg (r : Reg) (hr : r ∈ calleeSaved) (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9,
      .x13, .x14, .x15, .x16, .x17, .x19, .x20, .x22, .x23, .x24, .x26, .x27, .x28, .x29, .x30,
      .x31] : List Reg)) : z₂.getReg r = x.getReg r := by
    rw [hpz r hr, k₂ r h2, hp r hr, k₁ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp)]
  have hQ : Q.toNat + 48 ≤ heapNext z₁ := by rw [hvz]; omega
  have hQ0 : 0x20000000 ≤ Q.toNat := by omega
  have cz : eAt z₁ (s.getReg .x2 - 416) = c := by
    refine eAt_eq_of_limbs ?_
    rw [show s.getReg .x2 - 416 + 8 = s.getReg .x2 - BitVec.ofNat 64 408 by bv_omega,
      show s.getReg .x2 - 416 + 16 = s.getReg .x2 - BitVec.ofNat 64 400 by bv_omega,
      show s.getReg .x2 - 416 = s.getReg .x2 - BitVec.ofNat 64 416 from rfl,
      ← fzF 416 (by omega) (by omega), ← fzF 408 (by omega) (by omega),
      ← fzF 400 (by omega) (by omega), gxF 416 (by omega) (by omega),
      gxF 408 (by omega) (by omega), gxF 400 (by omega) (by omega)]
    exact (congrArg₂ Prod.mk A.r0 (congrArg₂ Prod.mk A.r1 A.r2)).trans rfl
  refine ⟨z₂, hrv.trans hrz₂, Or.inl {
    st := (st₃.trans st₄).weaken (fun a ha ↦ ha.elim id id) (fun h ↦ h.elim id id)
    pc := by rw [hpcz₂, returnAddress, b80003c04_x1 hz₁]; decide
    qa := qa
    q0 := q0
    q1 := by rw [eP]; exact aq1
    q2 := by omega
    cpa := by rw [eP]; exact A.cpa
    cp1 := by rw [eP]; exact acp
    cl := by rw [eL]; exact A.cl
    ce := by
      rw [vecEs, eP, eL, ← A.ce, vecEs]
      refine Bus.eListAt_congr fun j hj ↦ ?_
      rw [hlt] at hj
      exact eAt_congr (gxH _ (by addr_omega [aq1, hj, acp, hl]) (by addr_omega [aq1, hj, acp, hl]))
        (gxH _ (by addr_omega [aq1, hj, acp, hl]) (by addr_omega [aq1, hj, acp, hl]))
        (gxH _ (by addr_omega [aq1, hj, acp, hl]) (by addr_omega [aq1, hj, acp, hl]))
    w0 := by rw [fzH _ (by omega) hQ0, q5, hp .x19 (by decide), k₁ .x19 (by decide), A.x19]
    w8 := by rw [fzH _ (by addr_omega [hQ]) (by addr_omega [hQ, hQ0]), q4]
    w16 := by rw [fzH _ (by addr_omega [hQ]) (by addr_omega [hQ, hQ0]), q3]
    w24 := by
      rw [fzH _ (by addr_omega [hQ]) (by addr_omega [hQ, hQ0]), q2', hp .x18 (by decide),
        k₁ .x18 (by decide), A.x18]
    w32 := by rw [fzH _ (by addr_omega [hQ]) (by addr_omega [hQ, hQ0]), q1']
    w40 := by rw [fzH _ (by addr_omega [hQ]) (by addr_omega [hQ, hQ0]), q0']
    tag := pl1
    sc := by rw [show s.getReg .x2 - 1336 = s.getReg .x2 - 1344 + 8 by bv_omega, pl2, cz]
    x18 := by rw [hpz .x18 (by decide), b80003c04_x18 hz₁, x24v, e16v]; rfl
    x21 := by rw [hpz .x21 (by decide), b80003c04_x21 hz₁, x24v, e16v]
    x23 := by rw [reg .x23 (by decide) (by decide), A.x23]
    x25 := by rw [hpz .x25 (by decide), b80003c04_x25 hz₁, x24v, e8v]
    s160 := by
      rw [show (2496 : Word) = BitVec.ofNat 64 2496 from rfl, fzF 2496 (by omega) (by omega),
        fcF 2496 (by omega), pvm]
      exact e160
    s192 := by
      rw [show (2464 : Word) = BitVec.ofNat 64 2464 from rfl, gxF 2464 (by omega) (by omega)]
      exact A.s192 }⟩

end Iter

end Rv64Verifier.Proofs.Walk
