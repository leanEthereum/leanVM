import Rv64Verifier.Proofs.Walk.R19J

/-!
# `walk` R19, the public input's claims: room for the claim

`r19pC1`: from `0x80003e58` (`AtB`): the clone's header to `S - 1344`, the value into registers,
and room for one more claim (`grow_one` when the `Vec` is full), to `0x80003b14` (`AtC`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x80003b14`, room for claim `L + i` in the buffer `P₁` (capacity `C₁`); the point's clone
at `cp`. -/
structure AtC (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t u y : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (L : Word) (i : Nat)
    (c : E) (pt P₁ C₁ cp : Word) : Prop where
  st : StepW s u y (fun a ↦ IW s a ∨ Within a (s.getReg .x2 - 1632) 16) False
  core : CoreT OI s u₀ w t y layout lir evs P₁ C₁ (L.toNat + i)
    (bus.claims ++ tableClaimsRust evs ++
      (pubClaims layout (bytesAt s (s.getReg .x12) 32) c).take i)
    (afterPublic layout rows lir bus evs (bus.claims ++ tableClaimsRust evs)
      (pubClaims layout (bytesAt s (s.getReg .x12) 32) c))
  pc : y.pc = 0x80003b14
  room : L.toNat + i < C₁.toNat
  x14 : y.getReg .x14 = P₁
  x26 : y.getReg .x26 = L + BitVec.ofNat 64 i
  val : (y.getReg .x18, y.getReg .x19, y.getReg .x20) = Model.limbs (pubVal s i c)
  h1320 : y.getMem (s.getReg .x2 - 1336) = cp
  h1328 : y.getMem (s.getReg .x2 - 1328) = BitVec.ofNat 64 layout.logMemory
  cpa : cp.toNat % 8 = 0
  cp1 : heapNext u ≤ cp.toNat
  cp2 : cp.toNat + 24 * layout.logMemory ≤ heapNext y
  cpe : eListAt y cp layout.logMemory = c :: List.replicate (layout.logMemory - 1) 0
  cpApart : Apart cp (24 * layout.logMemory) P₁ (56 * C₁.toNat)
  ptApart : Apart pt (24 * layout.logMemory) P₁ (56 * C₁.toNat)
  s152 : y.getMem (s.getReg .x2 - 2504) = BitVec.ofNat 64 i
  s192 : y.getMem (s.getReg .x2 - 2464) = BitVec.ofNat 64 i + 1

section Iter
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {i : Nat} {c : E}
  {pt : Word}

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- From `0x80003e58` to the claim's store at `0x80003b14`, or the run dies. -/
theorem r19pC1 (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hpre : WalkPre s)
    (Hd : HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt)
    {y : MachineState} {Q : Word} (B : AtB s u y i c layout.logMemory L Q) :
    ∃ y₃, Reaches Image.code y y₃ ∧ ((∃ P₁ C₁ cp, AtC OI s u₀ w t u y₃ layout rows lir bus evs L i c
      pt P₁ C₁ cp) ∨ Dead Image.code y₃) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have hw : ∀ a, IW s a → InF s a := fun a ha ↦ (IW_ok hpre Hd.rest ha).1
  have Cy := Hd.core hpre B.st
  have I := Cy.rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hl := Hd.rest.inv.heap.lo
  simp only [heapEnd, heapStart] at hh hl
  have qa := B.qa
  have q2 := B.q2
  have q1 := B.q1
  have cp1 := B.cp1
  have hn := Hd.hn
  have hi := Hd.hi
  have hC := Cy.n_lt
  have hLC := Cy.len
  -- `0x80003e58`
  obtain ⟨y₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003e58_spec B.pc (by
    rv_eval [sp, B.x25]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [qa, q1, q2, hh, hl, cp1]))
  have k₁ := b80003e58_keeps h₁
  have fr₁ : DFrame y y₁ (Within · (s.getReg .x2 - 1344) 24) := by
    have := DFrame.of_memFrame (b80003e58_frame h₁ (by rw [sp]; addr_omega [hb1, hb2]))
    rwa [spAdd hpre sp 1312 1344 rfl] at this
  have st₁ : StepW s y y₁ (IW s) False := StepW.ofFrame hpre I.heap (fr₁.mono fun a ha ↦
    Or.inr (Or.inr (Or.inr (Or.inl (within_le ha (by omega)))))) hw (k₁ .x2 (by decide))
  have stu₁ : StepW s u y₁ (IW s) False := (B.st.trans st₁).weaken (fun a ha ↦ ha.elim id id)
    (fun h ↦ h.elim id id)
  have C₁ := Hd.core hpre stu₁
  have sp₁ : y₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), sp]
  have val₁ : (y₁.getReg .x18, y₁.getReg .x19, y₁.getReg .x20) = Model.limbs (pubVal s i c) := by
    rw [← B.val, limbs_eAt, b80003e58_x18 h₁, b80003e58_x19 h₁, b80003e58_x20 h₁, B.x25]
  have e160 : y.getMem (s.getReg .x2 - 2496) = L + BitVec.ofNat 64 i := B.s160
  have x26₁ : y₁.getReg .x26 = L + BitVec.ofNat 64 i := by
    rw [b80003e58_x26 h₁, spAdd hpre sp 160 2496 rfl, e160]
  have e184 : y.getMem (s.getReg .x2 - 2472) = P := by
    rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, IW_slot hpre B.st (by omega)
      (by omega)]
    exact Hd.ptr184
  have x14₁ : y₁.getReg .x14 = P := by rw [b80003e58_x14 h₁, spAdd hpre sp 184 2472 rfl, e184]
  have h1320 : y₁.getMem (s.getReg .x2 - 1336) = vecPtr y (s.getReg .x2 - 1488) := by
    rw [← spAdd hpre sp 1320 1336 rfl, b80003e58_m_x2_1320 h₁, spAdd hpre sp 1176 1480 rfl]
    simp only [vecPtr]; congr 1; bv_omega
  have h1328 : y₁.getMem (s.getReg .x2 - 1328) = BitVec.ofNat 64 layout.logMemory := by
    rw [← spAdd hpre sp 1328 1328 rfl, b80003e58_m_x2_1328 h₁, spAdd hpre sp 1184 1472 rfl, ← B.cl]
    simp only [vecLen]; congr 1; bv_omega
  -- the clone's elements
  have hn64 : layout.logMemory < 2 ^ 64 := by
    have := (vecLen y (s.getReg .x2 - 1488)).isLt; rw [B.cl, BitVec.toNat_ofNat] at this; omega
  have hlt : (vecLen y (s.getReg .x2 - 1488)).toNat = layout.logMemory := by
    rw [B.cl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have cpe : eListAt y (vecPtr y (s.getReg .x2 - 1488)) layout.logMemory =
      c :: List.replicate (layout.logMemory - 1) 0 := by
    rw [← B.ce, vecEs, hlt]
  have bP := Cy.buf.2.1
  have pto := Hd.ptOld
  have bPu := Hd.buf.2.1
  have f152 : y₁.getMem (s.getReg .x2 - 2504) = BitVec.ofNat 64 i := by
    rw [fr₁ _ fun j hj h' ↦ by simp only [Within] at h'; addr_omega [h', hj, hb1]]; exact B.s152
  have f192 : y₁.getMem (s.getReg .x2 - 2464) = BitVec.ofNat 64 i + 1 := by
    rw [fr₁ _ fun j hj h' ↦ by simp only [Within] at h'; addr_omega [h', hj, hb1]]; exact B.s192
  have hy1 := st₁.mono
  have hLi : (L + BitVec.ofNat 64 i).toNat = L.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have reg₁ (r : Reg) (h4 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x21,
      .x22, .x23, .x24, .x25, .x27, .x28, .x29, .x30, .x31] : List Reg)) : y₁.getReg r = y.getReg r :=
    k₁ r h4
  by_cases hfull : L + BitVec.ofNat 64 i = C
  swap
  · have pc₁ := b80003e58_pc_taken h₁ (by
      rw [spAdd hpre sp 160 2496 rfl, spAdd hpre sp 1024 1632 rfl, e160, Cy.capSlot]; exact hfull)
    refine ⟨y₁, hr₁, Or.inl ⟨P, C, vecPtr y (s.getReg .x2 - 1488), {
      st := stu₁.weaken (fun a ha ↦ Or.inl ha) id
      core := C₁
      pc := pc₁
      room := Nat.lt_of_le_of_ne hLC fun h ↦ hfull (BitVec.eq_of_toNat_eq (by rw [hLi]; exact h))
      x14 := x14₁
      x26 := x26₁
      val := val₁
      h1320 := h1320
      h1328 := h1328
      cpa := B.cpa
      cp1 := cp1
      cp2 := by omega
      cpe := by rw [st₁.eListH hpre hw (by omega)]; exact cpe
      cpApart := Or.inr (Or.inr (Or.inr (by omega)))
      ptApart := Hd.ptApart
      s152 := f152
      s192 := f192 }⟩⟩
  have pc₁ := b80003e58_pc_not_taken h₁ (by
    rw [spAdd hpre sp 160 2496 rfl, spAdd hpre sp 1024 1632 rfl, e160, Cy.capSlot]; exact hfull)
  have hfull' : L.toNat + i = C.toNat := by rw [← hLi, hfull]
  -- `0x80003e8c`, `grow_one`
  obtain ⟨y₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003e8c_spec pc₁ (by rv_eval [])
  have k₂ := b80003e8c_keeps h₂
  have m₂ := b80003e8c_mem_same h₂
  have C₂ := C₁.same hpre m₂ (k₂ .x2 (by decide))
  have x10₂ : y₂.getReg .x10 = s.getReg .x2 - 1632 := by
    rw [b80003e8c_x10 h₂, spAdd hpre sp₁ 1024 1632 rfl]
  obtain ⟨v, hrv, ⟨hpcv, hp, stg, P', C', Cv, hM', hP'⟩ | hd⟩ :=
    C₂.growOneF hG hpre hfull' (hr₁.trans hr₂) (b80003e8c_pc h₂) x10₂
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have pcv : v.pc = 0x80003e98 := by rw [hpcv, returnAddress, b80003e8c_x1 h₂]; decide
  have spv := Cv.rest.inv.sp
  -- `0x80003e98`
  obtain ⟨y₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003e98_spec pcv (by
    rv_eval [spv]; valid_access hval [hb1, hb3])
  have k₃ := b80003e98_keeps h₃
  have m₃ := b80003e98_mem_same h₃
  have st₂ : StepW s y₁ y₂ (fun a ↦ IW s a ∨ Within a (s.getReg .x2 - 1632) 16) False :=
    StepW.same st₁.heap m₂ (k₂ .x2 (by decide)) _ _
  have st₃ : StepW s v y₃ (fun a ↦ IW s a ∨ Within a (s.getReg .x2 - 1632) 16) False :=
    StepW.same stg.heap m₃ (k₃ .x2 (by decide)) _ _
  have st₁₃ : StepW s y₁ y₃ (fun a ↦ IW s a ∨ Within a (s.getReg .x2 - 1632) 16) False :=
    ((st₂.trans stg).trans st₃).weaken (fun a ha ↦ by
      rcases ha with (ha | ha) | ha
      · exact ha
      · exact Or.inr ha
      · exact ha) (fun h ↦ by rcases h with (h | h) | h <;> exact h)
  have hw' : ∀ a, (IW s a ∨ Within a (s.getReg .x2 - 1632) 16) → InF s a := fun a ha ↦
    ha.elim (hw a) fun h ↦ (range_ok hpre Hd.rest (c := 1632) (k := 1632) (n := 16) rfl (by omega)
      (by omega) h).1
  have st₀₃ : StepW s y y₃ (fun a ↦ IW s a ∨ Within a (s.getReg .x2 - 1632) 16) False :=
    (st₁.trans st₁₃).weaken (fun a ha ↦ ha.elim Or.inl id) (fun h ↦ h.elim id id)
  have stN : StepW s y₁ y₃ (Within · (s.getReg .x2 - 1632) 16) False :=
    (((StepW.same st₁.heap m₂ (k₂ .x2 (by decide)) (fun _ ↦ False) False).trans stg).trans
      (StepW.same stg.heap m₃ (k₃ .x2 (by decide)) (fun _ ↦ False) False)).weaken
      (fun a ha ↦ by rcases ha with (ha | ha) | ha; exact ha.elim; exact ha; exact ha.elim)
      (fun h ↦ by rcases h with (h | h) | h <;> exact h)
  have reg (r : Reg) (hr : r ∈ calleeSaved) (h3 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9,
      .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27, .x28, .x29, .x30, .x31] : List Reg)) (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9,
      .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27, .x28, .x29, .x30, .x31] : List Reg)) : y₃.getReg r = y₁.getReg r := by
    rw [k₃ r h3, hp r hr, k₂ r h2]
  have hvg := stg.mono
  have hy2 : heapNext y₂ = heapNext y₁ := by simp only [heapNext, m₂]
  refine ⟨y₃, hrv.trans hr₃, Or.inl ⟨P', C', vecPtr y (s.getReg .x2 - 1488), {
    st := (stu₁.trans st₁₃).weaken (fun a ha ↦ ha.elim Or.inl id) (fun h ↦ h.elim id id)
    core := Cv.same hpre m₃ (k₃ .x2 (by decide))
    pc := b80003e98_pc h₃
    room := hM'
    x14 := by
      rw [b80003e98_x14 h₃, spAdd hpre spv 1032 1624 rfl]; exact Cv.ptrSlot
    x26 := by rw [reg .x26 (by decide) (by decide) (by decide), x26₁]
    val := by
      rw [reg .x18 (by decide) (by decide) (by decide), reg .x19 (by decide) (by decide) (by decide),
        reg .x20 (by decide) (by decide) (by decide), val₁]
    h1320 := by
      rw [show (1336 : Word) = BitVec.ofNat 64 1336 from rfl, stN.getF hpre (by addr_omega [hb1])
        (fun j hj h' ↦ by simp only [Within] at h'; addr_omega [h', hj, hb1]) (fun h ↦ h.elim)]
      exact h1320
    h1328 := by
      rw [show (1328 : Word) = BitVec.ofNat 64 1328 from rfl, stN.getF hpre (by addr_omega [hb1])
        (fun j hj h' ↦ by simp only [Within] at h'; addr_omega [h', hj, hb1]) (fun h ↦ h.elim)]
      exact h1328
    cpa := B.cpa
    cp1 := cp1
    cp2 := by have := st₁₃.mono; omega
    cpe := by rw [st₀₃.eListH hpre hw' (by omega)]; exact cpe
    cpApart := Or.inr (Or.inr (Or.inl (by omega)))
    ptApart := Or.inr (Or.inr (Or.inl (by have := pto.1.2.1; have := B.st.mono; omega)))
    s152 := by
      rw [show (2504 : Word) = BitVec.ofNat 64 2504 from rfl, stN.getF hpre (by addr_omega [hb1])
        (fun j hj h' ↦ by simp only [Within] at h'; addr_omega [h', hj, hb1]) (fun h ↦ h.elim)]
      exact f152
    s192 := by
      rw [show (2464 : Word) = BitVec.ofNat 64 2464 from rfl, stN.getF hpre (by addr_omega [hb1])
        (fun j hj h' ↦ by simp only [Within] at h'; addr_omega [h', hj, hb1]) (fun h ↦ h.elim)]
      exact f192 }⟩⟩

end Iter

end Rv64Verifier.Proofs.Walk
