import Rv64Verifier.Proofs.Walk.R19D

/-!
# `walk` R19, the public input's claims: `r19pA`, the clone and the allocation
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section Iter
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {i : Nat} {c : E}
  {pt : Word}

theorem HeadR19.core (hpre : WalkPre s)
    (Hd : HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt) {x : MachineState}
    (st : StepW s u x (IW s) False) :
    CoreT OI s u₀ w t x layout lir evs P C (L.toNat + i)
      (bus.claims ++ tableClaimsRust evs ++
        (pubClaims layout (bytesAt s (s.getReg .x12) 32) c).take i)
      (afterPublic layout rows lir bus evs (bus.claims ++ tableClaimsRust evs)
        (pubClaims layout (bytesAt s (s.getReg .x12) 32) c)) :=
  Hd.toCoreT.stepW hpre st (fun _ ha ↦ ⟨(IW_ok hpre Hd.rest ha).1, (IW_ok hpre Hd.rest ha).2.1,
    (IW_ok hpre Hd.rest ha).2.2.1⟩) fun _ ha ↦ (IW_ok hpre Hd.rest ha).2.2.2

theorem within_le {a b : Word} {n m : Nat} (h : Within a b n) (hm : n ≤ m) : Within a b m :=
  ⟨h.1, by have := h.2; omega⟩

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- From the head through the clone and the allocation to `0x80003bdc`, or the run dies. -/
theorem r19pA (hCl : CloneSpecE) (hA : AllocSpec) (hpre : WalkPre s)
    (Hd : HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt) :
    ∃ x, Reaches Image.code u x ∧ ((∃ Q, AtA s u x i c layout.logMemory L Q) ∨
      Dead Image.code x) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have I := Hd.rest.inv
  have sp := I.sp
  have hi := Hd.hi
  have hn := Hd.hn
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  simp only [heapEnd, heapStart] at hh hs0
  obtain ⟨⟨pa, p2, p3⟩, pt1⟩ := Hd.ptOld
  have p3' : heapNext s ≤ pt.toNat := by rcases p3 with h0 | h0 <;> omega
  have hw : ∀ a, IW s a → InF s a := fun a ha ↦ (IW_ok hpre Hd.rest ha).1
  -- `0x80003b80`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003b80_spec Hd.pc (by
    have x12 := Hd.x12
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
      (rv_eval [sp, x12]; and_intros <;> first | valid_access hval [hb1, hb3] | addr_omega [hb1]))
  have k₁ := b80003b80_keeps h₁
  have fr₁ : DFrame u u₁ (Within · (s.getReg .x2 - 2464) 8) := by
    have := DFrame.of_memFrame (b80003b80_frame h₁ (by rw [sp]; addr_omega [hb1, hb2]))
    rwa [spAdd hpre sp 192 2464 rfl] at this
  have st₁ : StepW s u u₁ (IW s) False := StepW.ofFrame hpre I.heap
    (fr₁.mono fun a ha ↦ Or.inr (Or.inl (within_le ha (by omega)))) hw (k₁ .x2 (by decide))
  have I₁ := (Hd.core hpre st₁).rest.inv
  have hn₁ : heapNext u₁ = heapNext u := le_antisymm (by
    simp only [heapNext]
    rw [fr₁ nextAddr fun i hi hw ↦ by simp only [Within] at hw; addr_omega [hw, hi, hb1]]) st₁.mono
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1488 := by
    rw [b80003b80_x10 h₁, spAdd hpre sp 1168 1488 rfl]
  have x11₁ : u₁.getReg .x11 = pt := by
    rw [b80003b80_x11 h₁, spAdd hpre sp 136 2520 rfl, Hd.ptSlot]
  have x12₁ : (u₁.getReg .x12).toNat = layout.logMemory := by
    rw [b80003b80_x12 h₁, spAdd hpre sp 144 2512 rfl, Hd.nSlot]
  have x18₁ : u₁.getReg .x18 = pubHi s i := by
    rw [b80003b80_x18 h₁, show u.getReg .x2 + 1744 + u.getReg .x12 * 16 + 8 =
      s.getReg .x2 - 904 + BitVec.ofNat 64 (16 * i) by rw [sp, Hd.x12]; bv_omega]
    exact (Hd.pairs i hi).2
  have x19₁ : u₁.getReg .x19 = pubLo s i := by
    rw [b80003b80_x19 h₁, show u.getReg .x2 + 1744 + u.getReg .x12 * 16 =
      s.getReg .x2 - 912 + BitVec.ofNat 64 (16 * i) by rw [sp, Hd.x12]; bv_omega]
    exact (Hd.pairs i hi).1
  have x23₁ : u₁.getReg .x23 = BitVec.ofNat 64 i := by
    rw [b80003b80_x23 h₁, show u.getReg .x2 + 1808 + u.getReg .x12 * 8 =
      s.getReg .x2 - 848 + BitVec.ofNat 64 (8 * i) by rw [sp, Hd.x12]; bv_omega]
    exact Hd.cols i hi
  have m192 : u₁.getMem (s.getReg .x2 - 2464) = BitVec.ofNat 64 i := by
    rw [← spAdd hpre sp 192 2464 rfl, b80003b80_m_x2_192 h₁, Hd.x12]
  -- `clone`
  have ptu : eListAt u₁ pt layout.logMemory = c :: List.replicate (layout.logMemory - 1) 0 := by
    rw [st₁.eListH hpre hw (by omega)]; exact Hd.ptVal
  have hcs : MultilinearContracts.cloneStack ≤ 8736 := by decide
  have pre : ClonePreE u₁ := {
    heap := I₁.heap
    out := by rw [x10₁]; valid_sub hval [hb1, hb3]
    src := fun _ ↦ by rw [x11₁, x12₁]; exact Or.inl ⟨by omega, by omega⟩
    srcAlign := by rw [x11₁]; exact pa
    stack := hpre.stack.sub 2656 I₁.sp (by rw [stack_eq]; decide) (by decide) (by decide)
      (by decide) (by decide)
    outFree := by
      rw [x10₁]
      exact (fr_ok hpre I₁ (c := 1488) (k := 1488) (n := 24) (m := 0) rfl (by omega) (by omega)
        (by omega)).1
    outStack := by
      rw [x10₁]
      exact (fr_ok hpre I₁ (c := 1488) (k := 1488) (n := 24) rfl (by omega) (by omega) hcs).2.1
    srcFree := fun _ ↦ by rw [x11₁, x12₁]; exact (heap_ok I₁.heap (by rw [hn₁]; omega)).1
    srcOut := by
      rw [x11₁, x10₁, x12₁]; simp only [Apart]; right; right; left; addr_omega [p2, hb1, hab, hh]
    srcStack := by
      rw [x11₁, x12₁, stackLo_callee I₁]
      simp only [Apart]; right; right; left; addr_omega [p2, hb1, hab, hh, hcs] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hCl.call hr₁ (b80003b80_pc h₁) pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr := post.frame
  rw [x10₁] at fr
  have st₂r : StepW s u₁ v (Within · (s.getReg .x2 - 1488) 24) False :=
    StepW.ofCall hpre I₁ hcs (DFrame.of_byteFrame fr) post.heap post.mono (hp .x2 (by decide))
  have st₂ : StepW s u₁ v (IW s) False :=
    st₂r.weaken (fun a ha ↦ Or.inr (Or.inr (Or.inl ha))) id
  have el := post.elems
  have ln := post.len
  have fs := post.fresh
  rw [x10₁, x11₁] at el
  rw [x10₁] at ln fs
  rw [x12₁] at el fs
  rw [ptu] at el
  simp only [NewBuf] at fs
  obtain ⟨fa, f0 | ⟨f1, f2⟩⟩ := fs
  · omega
  have I₂ := (Hd.core hpre (st₁.trans st₂ |>.weaken (fun a ha ↦ ha.elim id id) (fun h ↦ h.elim id id))).rest.inv
  have spv := I₂.sp
  have x24v : v.getReg .x24 = s.getReg .x2 - 512 := by
    rw [hp .x24 (by decide), k₁ .x24 (by decide), Hd.x24]
  have pcv : v.pc = 0x80003bbc := by rw [hpcv, returnAddress, b80003b80_x1 h₁]; decide
  -- `0x80003bbc`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003bbc_spec pcv (by
    rv_eval [x24v]; and_intros <;> valid_access hval [hb1, hb3])
  have k₂ := b80003bbc_keeps h₂
  have fr₂ : DFrame v u₂ (Within · (s.getReg .x2 - 416) 24) := by
    have := DFrame.of_memFrame (b80003bbc_frame h₂ (by rw [x24v]; addr_omega [hb1, hb2]))
    rwa [x24v, show s.getReg .x2 - 512 + 96 = s.getReg .x2 - 416 by bv_omega] at this
  have st₃r : StepW s v u₂ (Within · (s.getReg .x2 - 416) 24) False := StepW.ofFrame hpre I₂.heap
    fr₂ (fun a ha ↦ hw a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))) (k₂ .x2 (by decide))
  have st₃ : StepW s v u₂ (IW s) False :=
    st₃r.weaken (fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))) id
  have st₀₂ := ((st₁.trans st₂).trans st₃).weaken (W' := IW s) (T' := False)
    (fun a ha ↦ by rcases ha with (ha | ha) | ha <;> exact ha) (fun h ↦ by
      rcases h with (h | h) | h <;> exact h)
  have I₃ := (Hd.core hpre st₀₂).rest.inv
  -- `alloc`
  obtain ⟨v₂, hrv₂, ⟨hpcv₂, hp₂, st₄, qa, q1, q2⟩ | hd⟩ :=
    allocW hA I₃ (hrv.trans hr₂) (b80003bbc_pc h₂) (b80003bbc_x10 h₂)
  swap
  · exact ⟨v₂, hrv₂, Or.inr hd⟩
  rw [b80003bbc_x11 h₂] at q2
  have pc₅ : v₂.pc = 0x80003bd8 := by rw [hpcv₂, returnAddress, b80003bbc_x1 h₂]; decide
  have hl3 := I₃.heap.lo
  simp only [heapStart] at hl3
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003bd8_spec pc₅ (by rv_eval [])
  have pc₆ := b80003bd8_pc_not_taken h₃ (by
    intro h0; rw [h0] at q1; simp at q1; omega)
  have m₃ := b80003bd8_mem_same h₃
  have k₃ := b80003bd8_keeps h₃
  have st₅ : StepW s v₂ u₃ (fun _ ↦ False) False :=
    StepW.same st₄.heap m₃ (k₃ .x2 (by decide)) _ _
  have stA : StepW s u u₃ (IW s) False := ((st₀₂.trans st₄).trans st₅).weaken
    (fun a ha ↦ by rcases ha with (ha | ha) | ha; exact ha; exact ha.elim; exact ha.elim)
    (fun h ↦ by rcases h with (h | h) | h <;> exact h)
  have stv3 : StepW s v u₃ (Within · (s.getReg .x2 - 416) 24) False := ((st₃r.trans st₄).trans st₅).weaken
    (fun a ha ↦ by rcases ha with (ha | ha) | ha; exact ha; exact ha.elim; exact ha.elim)
    (fun h ↦ by rcases h with (h | h) | h <;> exact h)
  have st13 : StepW s u₁ u₃ (fun a ↦ Within a (s.getReg .x2 - 1488) 24 ∨
      Within a (s.getReg .x2 - 416) 24) False := (st₂r.trans stv3).weaken (fun _ ha ↦ ha)
    (fun h ↦ by rcases h with h | h <;> exact h)
  have st₂₃' : StepW s u₂ u₃ (fun _ ↦ False) False := (st₄.trans st₅).weaken
    (fun a ha ↦ by rcases ha with ha | ha <;> exact ha) (fun h ↦ by rcases h with h | h <;> exact h)
  have fv (k : Nat) (hk : k = 1488 ∨ k = 1480 ∨ k = 1472) :
      u₃.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    stv3.getF hpre (by rcases hk with rfl | rfl | rfl <;> addr_omega [hb1]) (fun i hi hw ↦ by
      simp only [Within] at hw; rcases hk with rfl | rfl | rfl <;> addr_omega [hw, hi, hb1])
      (fun h ↦ h.elim)
  have eP : vecPtr u₃ (s.getReg .x2 - 1488) = vecPtr v (s.getReg .x2 - 1488) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 1488 + 8 = s.getReg .x2 - BitVec.ofNat 64 1480 by bv_omega,
      fv 1480 (by omega)]
  have eL : vecLen u₃ (s.getReg .x2 - 1488) = vecLen v (s.getReg .x2 - 1488) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 1488 + 16 = s.getReg .x2 - BitVec.ofNat 64 1472 by bv_omega,
      fv 1472 (by omega)]
  have hn64 : layout.logMemory < 2 ^ 64 := by
    have := (u₁.getReg .x12).isLt; omega
  have eLn : vecLen v (s.getReg .x2 - 1488) = BitVec.ofNat 64 layout.logMemory := by
    rw [ln]; apply BitVec.eq_of_toNat_eq; rw [x12₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have reg (r : Reg) (hr : r ∈ calleeSaved) : u₃.getReg r = u₁.getReg r := by
    rw [k₃ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp), hp₂ r hr, k₂ r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp), hp r hr]
  have g2 (a : Word) (ha : (s.getReg .x2 - 2656).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat) :
      u₃.getMem a = u₂.getMem a :=
    st₂₃'.getF hpre ha (fun _ _ h ↦ h) (fun h ↦ h.elim)
  have hv2 : heapNext v ≤ heapNext u₂ := st₃.mono
  refine ⟨u₃, hrv₂.trans hr₃, Or.inl ⟨v₂.getReg .x10, {
    st := stA
    pc := pc₆
    qa := qa
    q1 := by rw [eP]; exact (f2.trans hv2).trans q1
    q2 := by have := st₅.mono; have e : (48 : Word).toNat = 48 := rfl; omega
    x10 := k₃ .x10 (by decide)
    cpa := by rw [eP]; exact fa
    cp1 := by rw [eP, ← hn₁]; exact f1
    cl := by rw [eL, eLn]
    ce := by
      rw [← el, vecEs, vecEs, eP, eL]
      exact stv3.eListH hpre (fun a ha ↦ hw a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ha))))))) (by rw [eLn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]; omega)
    s192 := by
      rw [show (2464 : Word) = BitVec.ofNat 64 2464 from rfl, st13.getF hpre (by addr_omega [hb1])
        (fun i hi hw ↦ by simp only [Within] at hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hb1])
        (fun h ↦ h.elim)]
      exact m192
    x18 := by rw [reg .x18 (by decide), x18₁]
    x19 := by rw [reg .x19 (by decide), x19₁]
    x23 := by rw [reg .x23 (by decide), x23₁]
    x20 := by rw [reg .x20 (by decide), k₁ .x20 (by decide), Hd.x20]
    x21 := by rw [reg .x21 (by decide), k₁ .x21 (by decide), Hd.x21]
    x27 := by rw [reg .x27 (by decide), k₁ .x27 (by decide), Hd.x27]
    x24 := by rw [reg .x24 (by decide), k₁ .x24 (by decide), Hd.x24]
    x25 := by rw [reg .x25 (by decide), k₁ .x25 (by decide), Hd.x25]
    r0 := by
      rw [g2 _ (by addr_omega [hb1]), show s.getReg .x2 - 416 = v.getReg .x24 + 96 by
        rw [x24v]; bv_omega, b80003bbc_m_x24_96 h₂, hp .x20 (by decide), k₁ .x20 (by decide),
        Hd.x20]
    r1 := by
      rw [g2 _ (by addr_omega [hb1]), show s.getReg .x2 - 408 = v.getReg .x24 + 104 by
        rw [x24v]; bv_omega, b80003bbc_m_x24_104 h₂, hp .x21 (by decide), k₁ .x21 (by decide),
        Hd.x21]
    r2 := by
      rw [g2 _ (by addr_omega [hb1]), show s.getReg .x2 - 400 = v.getReg .x24 + 112 by
        rw [x24v]; bv_omega, b80003bbc_m_x24_112 h₂, hp .x27 (by decide), k₁ .x27 (by decide),
        Hd.x27] }⟩⟩

end Iter

end Rv64Verifier.Proofs.Walk
