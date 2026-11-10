import Rv64Verifier.Proofs.Walk.R19G

/-!
# `walk` R19, the public input's claims: `r19pB2`, `lo + (hi + lo) * c`
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

theorem limbs_ofK_word (x : Word) : Model.limbs (ofK (BF64.ofBitVec x)) = (x, 0, 0) := by
  rw [limbs_ofK]; rfl

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- From `0x80003c54` through the length checks and `mul` to `0x80003e58`, or the run dies. -/
theorem r19pB2 (hM : Contracts.MulSpec) (hpre : WalkPre s)
    (Hd : HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt)
    {z : MachineState} {Q : Word} (B : AtB1 s u z i c layout.logMemory L Q) :
    ∃ y, Reaches Image.code z y ∧ (AtB s u y i c layout.logMemory L Q ∨ Dead Image.code y) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have hw : ∀ a, IW s a → InF s a := fun a ha ↦ (IW_ok hpre Hd.rest ha).1
  have I := (Hd.core hpre B.st).rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hl := Hd.rest.inv.heap.lo
  simp only [heapEnd, heapStart] at hh hl
  have qa := B.qa
  have q0 := B.q0
  have q2 := B.q2
  -- `0x80003c54`
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003c54_spec B.pc (by
    rv_eval [sp]; valid_access hval [hb1, hb3])
  have k₁ := b80003c54_keeps h₁
  have pc₁ := b80003c54_pc_not_taken h₁ (by rw [B.x18]; decide)
  have fr₁ : DFrame z z₁ (Within · (s.getReg .x2 - 2456) 8) := by
    have := DFrame.of_memFrame (b80003c54_frame h₁ (by rw [sp]; addr_omega [hb1, hb2]))
    rwa [spAdd hpre sp 200 2456 rfl] at this
  have st₁ : StepW s z z₁ (IW s) False := StepW.ofFrame hpre I.heap (fr₁.mono fun a ha ↦ by
    simp only [IW, Within] at ha ⊢; addr_omega [ha, hb1]) hw (k₁ .x2 (by decide))
  have s200 : z₁.getMem (s.getReg .x2 - 2456) = 1 := by
    rw [← spAdd hpre sp 200 2456 rfl, b80003c54_m_x2_200 h₁, B.x18]
  -- `0x80003c5c`
  have sp₁ : z₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), sp]
  obtain ⟨z₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003c5c_spec pc₁ (by
    rv_eval [sp₁]; and_intros <;> valid_access hval [hb1, hb3])
  have k₂ := b80003c5c_keeps h₂
  have fr₂ : DFrame z₁ z₂ fun a ↦ Within a (s.getReg .x2 - 2464) 8 ∨
      Within a (s.getReg .x2 - 2504) 8 := h₂.dframe (by
    rv_eval [sp₁]; and_intros <;> simp only [Within] <;> addr_omega [hb1])
  have st₂ : StepW s z₁ z₂ (IW s) False := StepW.ofFrame hpre st₁.heap (fr₂.mono fun a ha ↦ by
    simp only [IW, Within] at ha ⊢; addr_omega [ha, hb1]) hw (k₂ .x2 (by decide))
  have s192 : z₂.getMem (s.getReg .x2 - 2464) = BitVec.ofNat 64 i + 1 := by
    rw [← spAdd hpre sp₁ 192 2464 rfl, b80003c5c_m_x2_192 h₂, spAdd hpre sp₁ 192 2464 rfl,
      fr₁ _ fun j hj hw' ↦ by simp only [Within] at hw'; addr_omega [hw', hj, hb1], B.s192]
  have s152 : z₂.getMem (s.getReg .x2 - 2504) = BitVec.ofNat 64 i := by
    rw [← spAdd hpre sp₁ 152 2504 rfl, b80003c5c_m_x2_152 h₂, k₁ .x23 (by decide), B.x23]
  have x19₂ : z₂.getReg .x19 = 0 := b80003c5c_x19 h₂
  have x26₂ : z₂.getReg .x26 = 1 := by
    rw [b80003c5c_x26 h₂, k₁ .x21 (by decide), B.x21]; rfl
  have x28₂ : z₂.getReg .x28 = 1 := by
    rw [b80003c5c_x28 h₂, spAdd hpre sp₁ 1312 1344 rfl,
      fr₁ _ fun j hj hw' ↦ by simp only [Within] at hw'; addr_omega [hw', hj, hb1], B.tag]
  have x25₂ : z₂.getReg .x25 = Q := by rw [k₂ .x25 (by decide), k₁ .x25 (by decide), B.x25]
  -- `0x80003d14`
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003d14_spec (b80003c5c_pc h₂) (by rv_eval [])
  have k₃ := b80003d14_keeps h₃
  have m₃ := b80003d14_mem_same h₃
  have pc₃ := b80003d14_pc_not_taken h₃ (by rw [x19₂, x26₂]; decide)
  -- `0x80003d18`
  have sp₃ : z₃.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₃ .x2 (by decide), k₂ .x2 (by decide), sp₁]
  have x25₃ : z₃.getReg .x25 = Q := by rw [k₃ .x25 (by decide), x25₂]
  have x19₃ : z₃.getReg .x19 = 0 := by rw [k₃ .x19 (by decide), x19₂]
  have hz₂ := st₂.mono
  have hz₁ := st₁.mono
  obtain ⟨z₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80003d18_spec pc₃ (by
    rv_eval [sp₃, x25₃, x19₃]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [qa, q0, q2, hh, hl]))
  have k₄ := b80003d18_keeps h₄
  have pc₄ := b80003d18_pc_taken h₄ (by rw [k₃ .x28 (by decide), x28₂]; decide)
  have fr₄ : DFrame z₃ z₄ (Within · (s.getReg .x2 - 512) 24) := by
    have := DFrame.of_memFrame (b80003d18_frame h₄ (by rw [sp₃]; addr_omega [hb1, hb2]))
    rwa [spAdd hpre sp₃ 2144 512 rfl] at this
  -- the buffer `Q` at `z₃`
  have gQ3 (y : Word) (y1 : y.toNat + 8 ≤ 0x78000000) : z₃.getMem y = z.getMem y := by
    rw [m₃, fr₂ y fun j hj hw' ↦ by simp only [Within] at hw'; rcases hw' with hw' | hw' <;>
        addr_omega [hw', hj, hb1, y1],
      fr₁ y fun j hj hw' ↦ by simp only [Within] at hw'; addr_omega [hw', hj, hb1, y1]]
  have hQ8 : (Q + 8).toNat = Q.toNat + 8 := by addr_omega [q2, hh]
  have hQ16 : (Q + 16).toNat = Q.toNat + 16 := by addr_omega [q2, hh]
  have hQ24 : (Q + 24).toNat = Q.toNat + 24 := by addr_omega [q2, hh]
  have hQ32 : (Q + 32).toNat = Q.toNat + 32 := by addr_omega [q2, hh]
  have hQ40 : (Q + 40).toNat = Q.toNat + 40 := by addr_omega [q2, hh]
  have w0 : z₃.getMem Q = pubLo s i := by rw [gQ3 _ (by omega)]; exact B.w0
  have w8 : z₃.getMem (Q + 8) = 0 := by rw [gQ3 _ (by omega)]; exact B.w8
  have w16 : z₃.getMem (Q + 16) = 0 := by rw [gQ3 _ (by omega)]; exact B.w16
  have w24 : z₃.getMem (Q + 24) = pubHi s i := by rw [gQ3 _ (by omega)]; exact B.w24
  have w32 : z₃.getMem (Q + 32) = 0 := by rw [gQ3 _ (by omega)]; exact B.w32
  have w40 : z₃.getMem (Q + 40) = 0 := by rw [gQ3 _ (by omega)]; exact B.w40
  have d30 := b80003d18_x30 h₄
  have d31 := b80003d18_x31 h₄
  have d21 := b80003d18_x21 h₄
  have d27 := b80003d18_x27 h₄
  have d44 := b80003d18_m_x2_2144 h₄
  have d52 := b80003d18_m_x2_2152 h₄
  have d60 := b80003d18_m_x2_2160 h₄
  rw [x25₃, x19₃] at d30 d31 d21 d44 d52 d60
  rw [x19₃] at d27
  simp only [zero_mul, add_zero] at d30 d31 d21 d27 d44 d52 d60
  rw [w0] at d30 d44
  rw [w8] at d31 d52
  rw [w16] at d21 d60
  rw [w24] at d44
  rw [w32] at d52
  rw [w40] at d60
  rw [spAdd hpre sp₃ 2144 512 rfl] at d44
  rw [spAdd hpre sp₃ 2152 504 rfl] at d52
  rw [spAdd hpre sp₃ 2160 496 rfl] at d60
  -- `0x80003c88`
  obtain ⟨z₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80003c88_spec pc₄ (by rv_eval [])
  have k₅ := b80003c88_keeps h₅
  have m₅ := b80003c88_mem_same h₅
  have st₃ : StepW s z₂ z₃ (IW s) False := StepW.same st₂.heap m₃ (k₃ .x2 (by decide)) _ _
  have st₄ : StepW s z₃ z₄ (IW s) False := StepW.ofFrame hpre st₃.heap (fr₄.mono fun a ha ↦
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))) hw (k₄ .x2 (by decide))
  have st₅ : StepW s z₄ z₅ (IW s) False := StepW.same st₄.heap m₅ (k₅ .x2 (by decide)) _ _
  have stu5 : StepW s u z₅ (IW s) False :=
    (((((B.st.trans st₁).trans st₂).trans st₃).trans st₄).trans st₅).weaken
      (fun a ha ↦ by rcases ha with ((((ha | ha) | ha) | ha) | ha) | ha <;> exact ha)
      (fun h ↦ by rcases h with ((((h | h) | h) | h) | h) | h <;> exact h)
  have I₅ := (Hd.core hpre stu5).rest.inv
  have sp₅ := I₅.sp
  have x10₅ : z₅.getReg .x10 = s.getReg .x2 - 224 := by
    rw [b80003c88_x10 h₅, k₄ .x2 (by decide), spAdd hpre sp₃ 2432 224 rfl]
  have x11₅ : z₅.getReg .x11 = s.getReg .x2 - 512 := by
    rw [b80003c88_x11 h₅, k₄ .x2 (by decide), spAdd hpre sp₃ 2144 512 rfl]
  have x12₅ : z₅.getReg .x12 = s.getReg .x2 - 1336 := by
    rw [b80003c88_x12 h₅, k₄ .x2 (by decide), spAdd hpre sp₃ 1320 1336 rfl]
  have hms : Contracts.mulStack ≤ 8736 := by decide
  have hsl := stackLo_callee I₅ Contracts.mulStack
  have pre : Contracts.MulPre z₅ := {
    out := by rw [x10₅]; valid_sub hval [hb1, hb3]
    lhs := by rw [x11₅]; valid_sub hval [hb1, hb3]
    rhs := by rw [x12₅]; valid_sub hval [hb1, hb3]
    stack := calleeStack hpre I₅ hms (by decide)
    outLhs := by rw [x10₅, x11₅]; simp only [Apart]; right; right; right; addr_omega [hb1]
    outRhs := by rw [x10₅, x12₅]; simp only [Apart]; right; right; right; addr_omega [hb1]
    outStack := by rw [x10₅, hsl]; simp only [Apart, Contracts.mulStack]; right; right; right; addr_omega [hb1]
    lhsStack := by rw [x11₅, hsl]; simp only [Apart, Contracts.mulStack]; right; right; right; addr_omega [hb1]
    rhsStack := by rw [x12₅, hsl]; simp only [Apart, Contracts.mulStack]; right; right; right; addr_omega [hb1]
    rodata := I₅.rodata hpre
    stackRodata := stack_apart_rodata (by rw [sp₅]; simp only [Contracts.mulStack]; addr_omega [hb1]) }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hM.call (hr₄.trans hr₅) (b80003c88_pc h₅) pre
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans (hr₃.trans hrv)), Or.inr hd⟩
  have frm : DFrame z₅ v fun a ↦ Within a (s.getReg .x2 - 224) 24 ∨
      Within a (stackLo z₅ Contracts.mulStack) Contracts.mulStack := fun a ha ↦ post.frame a
    (fun h ↦ ha 0 (by decide) (Or.inl (by rw [add_ofNat_zero, ← x10₅]; exact h)))
    (fun h ↦ ha 0 (by decide) (Or.inr (by rw [add_ofNat_zero]; exact h)))
  have hnv : heapNext v = heapNext z₅ := by
    simp only [heapNext]
    rw [frm nextAddr fun j hj hw' ↦ by
      rw [hsl] at hw'; simp only [Within, nextAddr, Contracts.mulStack] at hw'
      rcases hw' with hw' | hw' <;> addr_omega [hw', hj, hb1]]
  have st₆ : StepW s z₅ v (IW s) False :=
    StepW.ofCall hpre I₅ hms (frm.mono fun a ha ↦ ha.elim
        (fun h ↦ Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))) fun h ↦ Or.inr (Or.inl h))
      ⟨hnv ▸ I₅.heap.lo, hnv ▸ I₅.heap.hi⟩ hnv.ge (hp .x2 (by decide))
  have pv := post.value
  rw [x10₅, x11₅, x12₅] at pv
  have x23v : v.getReg .x23 = s.getReg .x2 - 512 := by
    rw [hp .x23 (by decide), k₅ .x23 (by decide), b80003d18_x23 h₄, spAdd hpre sp₃ 2144 512 rfl]
  have pcv : v.pc = 0x80003cb8 := by rw [hpcv, returnAddress, b80003c88_x1 h₅]; decide
  -- `0x80003cb8`
  obtain ⟨z₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80003cb8_spec pcv (by
    rv_eval [x23v]; and_intros <;> valid_access hval [hb1, hb3])
  have k₆ := b80003cb8_keeps h₆
  have m₆ := b80003cb8_mem_same h₆
  have x10₆ : z₆.getReg .x10 = v.getMem (s.getReg .x2 - 224) := by
    rw [b80003cb8_x10 h₆, x23v, show s.getReg .x2 - 512 + 288 = s.getReg .x2 - 224 by bv_omega]
  have x12₆ : z₆.getReg .x12 = v.getMem (s.getReg .x2 - 224 + 8) := by
    rw [b80003cb8_x12 h₆, x23v, show s.getReg .x2 - 512 + 296 = s.getReg .x2 - 224 + 8 by bv_omega]
  have x13₆ : z₆.getReg .x13 = v.getMem (s.getReg .x2 - 224 + 16) := by
    rw [b80003cb8_x13 h₆, x23v,
      show s.getReg .x2 - 512 + 304 = s.getReg .x2 - 224 + 16 by bv_omega]
  have x30₆ : z₆.getReg .x30 = pubLo s i := by
    rw [b80003cb8_x30 h₆, hp .x21 (by decide), b80003c88_x21 h₅, d30]
  have x31₆ : z₆.getReg .x31 = 0 := by
    rw [b80003cb8_x31 h₆, hp .x8 (by decide), b80003c88_x8 h₅, d31]
  have x21₆ : z₆.getReg .x21 = 0 := by
    rw [b80003cb8_x21 h₆, hp .x9 (by decide), b80003c88_x9 h₅, d21]
  have x25₆ : z₆.getReg .x25 = Q := by
    rw [b80003cb8_x25 h₆, hp .x18 (by decide), b80003c88_x18 h₅, k₄ .x25 (by decide), x25₃]
  have x27₆ : z₆.getReg .x27 = 0 := by
    rw [k₆ .x27 (by decide), hp .x27 (by decide), k₅ .x27 (by decide), d27]
  have x19₆ : z₆.getReg .x19 = 0 := by
    rw [k₆ .x19 (by decide), hp .x19 (by decide), k₅ .x19 (by decide), k₄ .x19 (by decide), x19₃]
  have sp₆ : z₆.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [k₆ .x2 (by decide), hp .x2 (by decide), k₅ .x2 (by decide), k₄ .x2 (by decide), sp₃]
  -- frames from `z₂`
  have fz26 : DFrame z₂ z₆ fun a ↦ Within a (s.getReg .x2 - 512) 24 ∨
      Within a (s.getReg .x2 - 224) 24 ∨ Within a (stackLo z₅ Contracts.mulStack) Contracts.mulStack ∨
      Within a Q 24 :=
    (((((DFrame.of_same m₃ _).trans (fr₄.mono fun a ha ↦ Or.inl ha) fun _ h ↦ h).trans
      (DFrame.of_same m₅ _) fun _ h ↦ h).trans
      (frm.mono fun a ha ↦ Or.inr (ha.elim Or.inl fun h ↦ Or.inr (Or.inl h))) fun _ h ↦ h).trans
      (DFrame.of_same m₆ _) fun _ h ↦ h)
  have hz5h := I₅.heap.hi
  simp only [heapEnd] at hz5h
  have g26 (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) (hk1 : k ≤ 200 ∨ (232 ≤ k ∧ k ≤ 488) ∨ 520 ≤ k) :
      z₆.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = z₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    fz26 _ fun j hj hw' ↦ by
      have k1 := hk.1
      have k2 := hk.2
      rw [hsl] at hw'
      simp only [Within, Contracts.mulStack] at hw'
      rcases hw' with hw' | hw' | hw' | hw' <;> rcases hk1 with q | ⟨q, q'⟩ | q <;>
        first
          | addr_omega [hw', hj, hb1, q, k1, k2, q2, hh]
          | addr_omega [hw', hj, hb1, q, q', k1, k2, q2, hh]
  have s200₆ : z₆.getMem (z₆.getReg .x2 + 200) = 1 := by
    rw [spAdd hpre sp₆ 200 2456 rfl, show (2456 : Word) = BitVec.ofNat 64 2456 from rfl,
      g26 2456 (by omega) (by omega), fr₂ _ fun j hj hw' ↦ by
        simp only [Within] at hw'; rcases hw' with hw' | hw' <;> addr_omega [hw', hj, hb1]]
    exact s200
  -- `0x80003ce0`
  have hz6 : heapNext z₅ ≤ heapNext z₆ := by
    have e : heapNext z₆ = heapNext v := by simp only [heapNext, m₆]
    rw [e, hnv]
  have hQz : Q.toNat + 48 ≤ heapNext z₅ := by
    have := st₁.mono; have := st₂.mono; have := st₃.mono; have := st₄.mono; have := st₅.mono; omega
  obtain ⟨y, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80003ce0_spec (b80003cb8_pc h₆) (by
    rv_eval [sp₆, x25₆, x27₆, x19₆]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [qa, q0, q2, hh, hl])
      | addr_omega [qa, q0, q2, hh, hl, hb1])
  have k₇ := b80003ce0_keeps h₇
  have pc₇ := b80003ce0_pc_taken h₇ (by rw [x19₆, s200₆]; rfl)
  have frce : DFrame z₆ y fun a ↦ False ∨ Within a Q 24 := h₇.dframe (by
    rv_eval [sp₆, x25₆, x27₆, x19₆]
    and_intros <;> (right; simp only [Within]; constructor <;> addr_omega [q2, hh]))
  have stu6 : StepW s u z₆ (IW s) False :=
    ((stu5.trans st₆).trans (StepW.same st₆.heap m₆ (k₆ .x2 (by decide)) _ _)).weaken
      (fun a ha ↦ by rcases ha with (ha | ha) | ha <;> exact ha)
      (fun h ↦ by rcases h with (h | h) | h <;> exact h)
  have stu7 : StepW s u y (IW s) False := (stu6.thenW hpre Hd.rest.inv.heap (W' := fun _ ↦ False)
    (fun _ h ↦ h.elim) frce q0 (by omega) (k₇ .x2 (by decide))).weaken
    (fun a ha ↦ ha.elim id False.elim) id
  have fz2y : DFrame z₂ y fun a ↦ Within a (s.getReg .x2 - 512) 24 ∨
      Within a (s.getReg .x2 - 224) 24 ∨ Within a (stackLo z₅ Contracts.mulStack) Contracts.mulStack ∨
      Within a Q 24 :=
    fz26.trans (frce.mono fun a ha ↦ ha.elim False.elim fun h ↦ Or.inr (Or.inr (Or.inr h)))
      fun _ h ↦ h
  have hyh : heapNext y = heapNext z₆ := by
    simp only [heapNext]
    rw [frce nextAddr fun j hj hw' ↦ by
      rcases hw' with hw' | hw'
      · exact hw'
      · simp only [Within, nextAddr] at hw'; addr_omega [hw', hj, q2, hh]]
  have g2y (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) (hk1 : k ≤ 200 ∨ (232 ≤ k ∧ k ≤ 488) ∨ 520 ≤ k) :
      y.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = z₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) :=
    fz2y _ fun j hj hw' ↦ by
      have k1 := hk.1
      have k2 := hk.2
      rw [hsl] at hw'
      simp only [Within, Contracts.mulStack] at hw'
      rcases hw' with hw' | hw' | hw' | hw' <;> rcases hk1 with q | ⟨q, q'⟩ | q <;>
        first
          | addr_omega [hw', hj, hb1, q, k1, k2, q2, hh]
          | addr_omega [hw', hj, hb1, q, q', k1, k2, q2, hh]
  have g2yH (a : Word) (a1 : a.toNat + 8 ≤ Q.toNat) (a2 : 0x20000000 ≤ a.toNat) :
      y.getMem a = z₂.getMem a :=
    fz2y _ fun j hj hw' ↦ by
      rw [hsl] at hw'
      simp only [Within, Contracts.mulStack] at hw'
      rcases hw' with hw' | hw' | hw' | hw' <;> addr_omega [hw', hj, hb1, a1, a2, q2, hh]
  have gz2 (a : Word) (ha : (a.toNat + 8 ≤ Q.toNat ∧ 0x20000000 ≤ a.toNat) ∨
      ((s.getReg .x2 - 2656).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2 - 2504).toNat) ∨
      ((s.getReg .x2 - 2496).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2 - 2464).toNat) ∨
      ((s.getReg .x2 - 2448).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat)) :
      z₂.getMem a = z.getMem a := by
    rw [fr₂ a fun j hj hw' ↦ by
        simp only [Within] at hw'
        rcases hw' with hw' | hw' <;> rcases ha with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          addr_omega [hw', hj, hb1, a1, a2, q2, hh],
      fr₁ a fun j hj hw' ↦ by
        simp only [Within] at hw'
        rcases ha with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          addr_omega [hw', hj, hb1, a1, a2, q2, hh]]
  -- the value
  have e512 : eAt z₅ (s.getReg .x2 - 512) =
      ofK (BF64.ofBitVec (pubHi s i)) + ofK (BF64.ofBitVec (pubLo s i)) := by
    refine eAt_eq_of_limbs ?_
    rw [limbs_add, limbs_ofK_word, limbs_ofK_word, m₅, m₅, m₅,
      show s.getReg .x2 - 512 + 8 = s.getReg .x2 - 504 by bv_omega,
      show s.getReg .x2 - 512 + 16 = s.getReg .x2 - 496 by bv_omega, d44, d52, d60]
  have e1336 : eAt z₅ (s.getReg .x2 - 1336) = c := by
    rw [← B.sc]
    have g (k : Nat) (hk : k = 1336 ∨ k = 1328 ∨ k = 1320) :
        z₅.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = z.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
      rw [m₅, fr₄ _ fun j hj hw' ↦ by
          simp only [Within] at hw'; rcases hk with rfl | rfl | rfl <;> addr_omega [hw', hj, hb1],
        m₃, gz2 _ (Or.inr (Or.inr (Or.inr ⟨by rcases hk with rfl | rfl | rfl <;> addr_omega [hb1],
          by rcases hk with rfl | rfl | rfl <;> addr_omega [hb1]⟩)))]
    exact eAt_congr (g 1336 (by omega))
      (by rw [show s.getReg .x2 - 1336 + 8 = s.getReg .x2 - BitVec.ofNat 64 1328 by bv_omega]
          exact g 1328 (by omega))
      (by rw [show s.getReg .x2 - 1336 + 16 = s.getReg .x2 - BitVec.ofNat 64 1320 by bv_omega]
          exact g 1320 (by omega))
  have ev : eAt y Q = eAt v (s.getReg .x2 - 224) + ofK (BF64.ofBitVec (pubLo s i)) := by
    refine eAt_eq_of_limbs ?_
    rw [limbs_add, limbs_eAt, limbs_ofK_word]
    have m2 := b80003ce0_m2 h₇
    have m1 := b80003ce0_m1 h₇
    have m0 := b80003ce0_m0 h₇
    rw [x25₆, x27₆, x19₆] at m2 m1 m0
    simp only [zero_mul, add_zero] at m2 m1 m0
    rw [m2, m1, m0, x10₆, x12₆, x13₆, x30₆, x31₆, x21₆]
  have gzz (k : Nat) (hk : k = 1480 ∨ k = 1472) :
      y.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = z.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    rw [g2y k (by omega) (by omega), gz2 _ (Or.inr (Or.inr (Or.inr
      ⟨by rcases hk with rfl | rfl <;> addr_omega [hb1], by rcases hk with rfl | rfl <;> addr_omega [hb1]⟩)))]
  have eP : vecPtr y (s.getReg .x2 - 1488) = vecPtr z (s.getReg .x2 - 1488) := by
    simp only [vecPtr]
    rw [show s.getReg .x2 - 1488 + 8 = s.getReg .x2 - BitVec.ofNat 64 1480 by bv_omega,
      gzz 1480 (by omega)]
  have eL : vecLen y (s.getReg .x2 - 1488) = vecLen z (s.getReg .x2 - 1488) := by
    simp only [vecLen]
    rw [show s.getReg .x2 - 1488 + 16 = s.getReg .x2 - BitVec.ofNat 64 1472 by bv_omega,
      gzz 1472 (by omega)]
  have bq1 := B.q1
  have bcp := B.cp1
  have hn64 : layout.logMemory < 2 ^ 64 := by
    have := (vecLen z (s.getReg .x2 - 1488)).isLt; rw [B.cl, BitVec.toNat_ofNat] at this; omega
  have hlt : (vecLen z (s.getReg .x2 - 1488)).toNat = layout.logMemory := by
    rw [B.cl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  refine ⟨y, hr₁.trans (hr₂.trans (hr₃.trans (hrv.trans (hr₆.trans hr₇)))), Or.inl {
    st := stu7
    pc := pc₇
    qa := qa
    q1 := by rw [eP]; exact bq1
    q2 := by rw [hyh]; omega
    cpa := by rw [eP]; exact B.cpa
    cp1 := by rw [eP]; exact bcp
    cl := by rw [eL]; exact B.cl
    ce := by
      rw [vecEs, eP, eL, ← B.ce, vecEs]
      refine Bus.eListAt_congr fun j hj ↦ ?_
      rw [hlt] at hj
      have r (a : Word) (a1 : a.toNat + 8 ≤ Q.toNat) (a2 : 0x20000000 ≤ a.toNat) :
          y.getMem a = z.getMem a := by
        rw [g2yH a a1 a2, gz2 a (Or.inl ⟨a1, a2⟩)]
      exact eAt_congr (r _ (by addr_omega [bq1, hj, bcp, hl]) (by addr_omega [bq1, hj, bcp, hl]))
        (r _ (by addr_omega [bq1, hj, bcp, hl]) (by addr_omega [bq1, hj, bcp, hl]))
        (r _ (by addr_omega [bq1, hj, bcp, hl]) (by addr_omega [bq1, hj, bcp, hl]))
    val := by rw [ev, pv, e512, e1336, pubVal]; ring
    x25 := by rw [k₇ .x25 (by decide), x25₆]
    s160 := by
      rw [show (2496 : Word) = BitVec.ofNat 64 2496 from rfl, g2y 2496 (by omega) (by omega),
        gz2 _ (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb1], by addr_omega [hb1]⟩)))]
      exact B.s160
    s152 := by
      rw [show (2504 : Word) = BitVec.ofNat 64 2504 from rfl, g2y 2504 (by omega) (by omega)]
      exact s152
    s192 := by
      rw [show (2464 : Word) = BitVec.ofNat 64 2464 from rfl, g2y 2464 (by omega) (by omega)]
      exact s192 }⟩

end Iter

end Rv64Verifier.Proofs.Walk
