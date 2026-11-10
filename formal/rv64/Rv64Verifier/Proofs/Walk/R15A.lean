import Rv64Verifier.Proofs.Walk.Lay14
import Rv64Verifier.Proofs.Walk.TailModel

/-!
# `walk` R15: the stack's root, `next_scalars(2)` and its checks

From `AtR15` (`0x800034c0`): `next_scalars(2)` into `S - 928` (`r15call`), then its `Err` (copied to
the result, `0x800039cc`), the length's traps and the high limbs' check (`Err` at `0x800039dc`),
to `0x80003514` (`r15branch`, `Mid15`). The steps from `AtR15` on write the frame only at `S - 928`
(the scalars, then the bus's result) and `S - 1800` (the root): `W15`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What R15 and R16 write in the frame: the result at `S - 928`, the root at `S - 1800`. -/
@[rv_addr] def W15 (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 928) 120 ∨ Within a (s.getReg .x2 - 1800) 32

theorem W15.inF {s : MachineState} (hpre : WalkPre s) {a : Word} (ha : W15 s a) : InF s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [W15, InF, Within] at ha ⊢
  rcases ha with ha | ha <;> constructor <;> addr_omega [ha, hb1]

theorem Inv.stepW {s v w : MachineState} (hpre : WalkPre s) (h : Inv s v) {W : Word → Prop}
    {T : Prop} (hW : ∀ a, W a → InF s a) (st : StepW s v w W T) : Inv s w := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hx
  rw [stackLo_eq] at hab
  have hh := st.heap.hi
  have m₀ := h.mono
  refine h.step hpre st.frame (fun a ha ↦ ?_) st.heap st.mono st.sp
  simp only [WalkW, Fresh, stackLo_eq, heapNext, heapEnd, InF] at ha hab hh m₀ hW ⊢
  rcases ha with ha | ha | ha | ⟨f1, f2⟩ | ⟨-, ha⟩
  · obtain ⟨i1, i2⟩ := hW a ha
    exact ⟨Or.inr (Or.inl (by addr_omega [i1, i2, hb1])), by addr_omega [i1, i2, hb1]⟩
  · exact ⟨Or.inr (Or.inl (by addr_omega [ha, hb1])), by addr_omega [ha, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inl ha)), by addr_omega [ha, hx, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr ⟨by omega, f2⟩)), by addr_omega [f1, f2, hh, hab, hb1]⟩
  · rw [tp] at ha
    exact ⟨Or.inr (Or.inl (by addr_omega [ha, hb1])), by addr_omega [ha, hb1]⟩

theorem StepT.stepW {s v w : MachineState} {lo : Word} {n : Nat} (st : StepT s v w lo n) :
    StepW s v w (fun a ↦ Within a lo n) True :=
  ⟨st.frame.mono fun a ha ↦ by
    rcases ha with (ha | ha | ha | ha) | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, ha⟩))), st.heap, st.mono, st.sp⟩

/-- A frame slot `S - k` R15 and R16 do not write keeps its value. -/
theorem StepW.slot15 {s v w : MachineState} (hpre : WalkPre s) {T : Prop}
    (st : StepW s v w (W15 s) T) {k : Nat} (hk : 104 + 8 ≤ k ∧ k ≤ 2656)
    (hn : (k ≤ 808 ∨ 928 + 8 ≤ k) ∧ (k ≤ 1768 ∨ 1800 + 8 ≤ k) ∧ (k ≤ 2088 ∨ 2440 + 8 ≤ k)) :
    w.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine st.getF hpre (by constructor <;> addr_omega [hb1, hk]) (fun i hi hw ↦ ?_) fun _ ↦ ?_
  · simp only [W15, Within] at hw
    rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, hk, hn]
  · rw [tp]; addr_omega [hb1, hk, hn]

/-- The registers `walk` keeps from `AtR15` through the call. -/
theorem keepsNS {u c w : MachineState} (h₁ : b800034c0.Holds u c) (hp : Preserves c w) :
    ∀ r ∈ ([.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
      w.getReg r = u.getReg r := by
  intro r hr
  rw [hp r (by revert r hr; decide), b800034c0_keeps h₁ r (by revert r hr; decide)]

/-- The scalars' call's result: what `next_scalars` returns at `S - 928`, read from `u₀`. -/
structure NS15 (s u₀ w : MachineState) : Prop where
  inv : Inv s w
  st : StepW s u₀ w (W15 s) True
  x27 : w.getReg .x27 = 6
  ok : VecResult u₀ w (s.getReg .x2 - 928)
  value : ∀ T, TranscriptAt u₀ (tp s) T →
    match (TM.nextScalars 2).run T with
    | some (xs, T') => vecCap w (s.getReg .x2 - 928) ≠ errNiche ∧
        NewVecE u₀ w (s.getReg .x2 - 928) xs ∧ TranscriptAt w (tp s) T'
    | none => vecCap w (s.getReg .x2 - 928) = errNiche

/-- `next_scalars(2)`'s call from `0x800034c0`, returning to `0x800034d4`. -/
theorem r15call (hNS : NextScalarsSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s)
    (hpc : u₀.pc = 0x800034c0) (h : AtR15 OI s u₀ A k R Q B lo lo2) :
    ∃ w, Reaches Image.code u₀ w ∧ ((w.pc = 0x800034d4 ∧ NS15 s u₀ w) ∨ Dead Image.code w) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have H := h.keep.at11.base
  have I := H.inv
  have sp : u₀.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  obtain ⟨c, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800034c0_spec hpc trivial
  have m₁ := b800034c0_mem_same h₁
  have I₁ := I.same m₁ (b800034c0_keeps h₁ .x2 (by decide))
  have x10 : c.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 928 := by
    rw [b800034c0_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11 : c.getReg .x11 = tp s := by
    rw [b800034c0_x11 h₁, sp, tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have ptr₁ : c.getMem (tp s) = s.getReg .x13 := by rw [m₁]; exact H.proofPtr
  have pre : NextScalarsPre c := tpre hpre I₁ ptr₁ (k := 928) (n := 24) (m := nextScalarsStack)
    (by omega) (by omega) (by omega) (by decide) (by decide) x10 x11
  obtain ⟨w, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hNS.call (Reaches.refl c) (b800034c0_pc h₁) pre
  swap
  · exact ⟨w, hr₁.trans hr₂, Or.inr hd⟩
  have stT := TFrame.stepT hpre I₁ (k := 928) (by decide) x10 x11 post.frame post.heap post.mono
    (hp₂ .x2 (by decide))
  have st₀ : StepW s u₀ c (fun _ ↦ False) False :=
    StepW.same I.heap m₁ (b800034c0_keeps h₁ .x2 (by decide)) _ _
  have st : StepW s u₀ w (W15 s) True := (st₀.trans stT.stepW).weaken
    (fun a ha ↦ by
      rcases ha with ha | ha
      · exact ha.elim
      · simp only [W15, Within] at ha ⊢; exact Or.inl (by addr_omega [ha, hb1]))
    fun _ ↦ trivial
  refine ⟨w, hr₁.trans hr₂, Or.inl ⟨by rw [hpc₂, returnAddress_eq, b800034c0_x1 h₁]; decide, {
    inv := I.stepW hpre (fun a ha ↦ W15.inF hpre ha) st
    st := st
    x27 := by rw [keepsNS h₁ hp₂ .x27 (by decide)]; exact h.x27
    ok := by
      have hk := post.ok
      rw [x10] at hk
      intro hc
      obtain ⟨hv, hb⟩ := hk hc
      refine ⟨hv, ?_⟩
      simp only [NewBuf, heapNext, m₁] at hb ⊢
      exact hb
    value := fun T hT ↦ by
      have hv := post.value T (by rw [x11]; exact TranscriptAt.same hpre I H.proofPtr m₁ hT)
      have e2 : (2 : Word).toNat = 2 := rfl
      rw [x10, x11, b800034c0_x12 h₁, e2] at hv
      generalize (TM.nextScalars 2).run T = o at hv ⊢
      rcases o with _ | ⟨xs, T'⟩
      · exact hv
      · obtain ⟨h1, ⟨hv', hb, he⟩, h3⟩ := hv
        refine ⟨h1, ⟨hv', ?_, he⟩, h3⟩
        simp only [NewBuf, heapNext, m₁] at hb ⊢
        exact hb }⟩⟩

/-- `S - 2080`'s `tables` `Vec`, as `drop_glue::<Layout>` reads it, kept from `AtR15`. -/
theorem tablesVec15 {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ y : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s)
    (h : AtR15 OI s u₀ A k R Q B lo lo2) {T : Prop} (st : StepW s u₀ y (W15 s) T) :
    vecPtr y (s.getReg .x2 - 2080) = B ∧ vecLen y (s.getReg .x2 - 2080) = 6 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have tv := h.layoutIn.tablesVec
  have sB := h.keep.at11.base.slots.2.2.2.2.2
  have e8 : s.getReg .x2 - 2080 + 8 = s.getReg .x2 - BitVec.ofNat 64 2072 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 2080 + 16 = s.getReg .x2 - BitVec.ofNat 64 2064 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  simp only [vecPtr, vecLen, e8, e16] at tv ⊢
  rw [st.slot15 hpre (by omega) (by omega), st.slot15 hpre (by omega) (by omega), tv.1, tv.2, sB]
  exact ⟨rfl, rfl⟩

/-- A byte of the stack. -/
theorem frameByte {s : MachineState} (hpre : WalkPre s) {x : Word}
    (h1 : (s.getReg .x2 - 11392).toNat ≤ x.toNat) (h2 : x.toNat < (s.getReg .x2).toNat) :
    Sym.validAccess 1 x = true := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hm := hpre.stack.mapped (by decide) (by decide)
  rw [stackLo_eq, stack_eq] at hm
  exact Proofs.Bytecode.valid_byte (a := s.getReg .x2 - 11392) (n := 11392)
    (by simp only [Mapped]; addr_omega [hm, hb1, hb3]) h1 (by addr_omega [h2, hb1])

theorem StepW.ext15 {s u₀ w v : MachineState} {T : Prop} (st : StepW s u₀ w (W15 s) T)
    (hh : HeapOk w) (hm : ∀ a, v.getMem a = w.getMem a) (sp : v.getReg .x2 = w.getReg .x2) :
    StepW s u₀ v (W15 s) T :=
  (st.trans (StepW.same hh hm sp (fun _ ↦ False) False)).weaken (fun _ ha ↦ ha.elim id False.elim)
    fun ht ↦ ht.elim id False.elim

/-- An `Err` written to the result's first 24 bytes, then `0x80004200`. -/
theorem errRes (hDL : DropLayoutSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ y y' : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat}
    (hpre : WalkPre s) (h : AtR15 OI s u₀ A k R Q B lo lo2) (I : Inv s y) {T : Prop}
    (st : StepW s u₀ y (W15 s) T) (fr : MemFrame y y' (s.getReg .x10) 24)
    (sp : y'.getReg .x2 = y.getReg .x2) (hpc : y'.pc = 0x80004200)
    (he : y'.getMem (s.getReg .x10) = errNiche) :
    ∃ t, Reaches Image.code y' t ∧ (Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hR := hpre.out
  have hO := hpre.outStack
  rw [stackLo_eq, stack_eq] at hO
  have fr' := DFrame.of_memFrame fr
  have hx := hpre.outFree.2
  have hn : heapNext y' = heapNext y := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr' nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi])
  have I' : Inv s y' := I.step hpre fr'
    (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hR]), by addr_omega [ha, hO, hb1]⟩)
    ⟨hn ▸ I.heap.lo, hn ▸ I.heap.hi⟩ hn.ge sp
  obtain ⟨eP, eL⟩ := tablesVec15 hpre h st
  have g (o : Nat) (ho : o + 8 ≤ 24) : y'.getMem (s.getReg .x2 - 2080 + BitVec.ofNat 64 o) =
      y.getMem (s.getReg .x2 - 2080 + BitVec.ofNat 64 o) :=
    fr _ (by simp only [Within]; addr_omega [hR, hO, hb1, ho])
  have H := h.keep.at11.base
  have hbB := H.bufB
  have hlo := hpre.heap.lo
  have hhi := H.inv.heap.hi
  have hl := H.loLe
  simp only [heapStart, heapEnd] at hlo hhi
  exact errTail0 (OI := OI) hDL hpre I' hpc hbB.2.1 (by omega) (by omega)
    (by rw [← eP]; exact g 8 (by decide)) (by rw [← eL]; exact g 16 (by decide)) he

/-- At `0x80003514`: the scalars' `Vec` at `S - 928` in `w`, `v` the same memory, both high limbs
zero. -/
structure Mid15 (s u₀ w v : MachineState) (P : Word) : Prop where
  ns : NS15 s u₀ w
  mem : ∀ a, v.getMem a = w.getMem a
  sp : v.getReg .x2 = w.getReg .x2
  x10 : v.getReg .x10 = P
  x21 : v.getReg .x21 = s.getReg .x10
  x22 : v.getReg .x22 = s.getReg .x2 - 512
  x23 : v.getReg .x23 = tp s + 8
  x27 : v.getReg .x27 = 6
  ptr : vecPtr w (s.getReg .x2 - 928) = P
  cap : vecCap w (s.getReg .x2 - 928) ≠ errNiche
  len : 2 ≤ (vecLen w (s.getReg .x2 - 928)).toNat
  buf : P.toNat % 8 = 0 ∧ heapNext u₀ ≤ P.toNat ∧ P.toNat + 48 ≤ heapNext w
  z0 : w.getMem (P + 16) = 0
  z1 : w.getMem (P + 40) = 0

theorem or_zero {a b : Word} (h : a ||| b = 0) : a = 0 ∧ b = 0 := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · have := congrArg (fun x : Word ↦ x.getLsbD i) h
    simp only [BitVec.getLsbD_or] at this
    simp_all
  · have := congrArg (fun x : Word ↦ x.getLsbD i) h
    simp only [BitVec.getLsbD_or] at this
    simp_all

set_option maxRecDepth 8192 in
/-- From `next_scalars`' return: its `Err`, the length's traps, the high limbs' `Err`, or
`0x80003514`. -/
theorem r15branch (hDL : DropLayoutSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ w : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat}
    (hpre : WalkPre s) (h : AtR15 OI s u₀ A k R Q B lo lo2) (hpc : w.pc = 0x800034d4)
    (N : NS15 s u₀ w) :
    ∃ t, Reaches Image.code w t ∧ (Done OI s t ∨ Dead Image.code t ∨
      (t.pc = 0x80003514 ∧ Mid15 s u₀ w t (vecPtr w (s.getReg .x2 - 928)))) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := N.inv
  have sp : w.getReg .x2 = s.getReg .x2 - 2656 := I.sp
  have hR := hpre.out
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800034d4_spec hpc (by
    rv_eval [sp]; and_intros <;> valid_access hval [hb1])
  have m₁ := b800034d4_mem_same h₁
  have k₁ := b800034d4_keeps h₁
  have e1728 : w.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x21 : v₁.getReg .x21 = s.getReg .x10 := by
    rw [b800034d4_x21 h₁, sp]
    have e : s.getReg .x2 - 2656 + 168 = s.getReg .x2 - BitVec.ofNat 64 2488 := by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [e, N.st.slot15 hpre (by omega) (by omega)]
    exact h.keep.at11.base.spills.2.2.2.2.2.2.2.2
  by_cases hc : w.getMem (w.getReg .x2 + 1728) = (0xffffffffffffffff : Word)
  · -- `Err`: copied to the result
    obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800039cc_spec (b800034d4_pc_taken h₁ hc) (by
      rv_eval [x21]
      and_intros <;> exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR])
        (by addr_omega [hR]))
    have fr := b800039cc_frame h₂ (by rw [x21]; addr_omega [hR])
    rw [x21] at fr
    obtain ⟨t, hr₃, ht⟩ := errRes hDL hpre h (I.same m₁ (k₁ .x2 (by decide)))
      (N.st.ext15 I.heap m₁ (k₁ .x2 (by decide))) fr
      (b800039cc_keeps h₂ .x2 (by decide)) (b800039cc_pc h₂)
      (by rw [← x21, b800039cc_m_x21_0 h₂, b800034d4_x12 h₁]; rfl)
    exact ⟨t, hr₁.trans (hr₂.trans hr₃), ht.imp_right Or.inl⟩
  have pc₁ := b800034d4_pc_not_taken h₁ hc
  have hcap : vecCap w (s.getReg .x2 - 928) ≠ errNiche := by rw [vecCap, ← e1728]; exact hc
  obtain ⟨hvo, hnb⟩ := N.ok hcap
  have x11 : v₁.getReg .x11 = vecLen w (s.getReg .x2 - 928) := by
    rw [b800034d4_x11 h₁, vecLen, ← e1728]; congr 1
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10 : v₁.getReg .x10 = vecPtr w (s.getReg .x2 - 928) := by
    rw [b800034d4_x10 h₁, vecPtr, ← e1728]; congr 1
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800034ec_spec pc₁ trivial
  by_cases h0 : v₁.getReg .x11 = (0 : Word)
  · exact ⟨v₂, hr₁.trans hr₂, Or.inr (Or.inl (trapAt (b800034ec_pc_taken h₂ h0)))⟩
  have k₂ := b800034ec_keeps h₂
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800034f0_spec (b800034ec_pc_not_taken h₂ h0) trivial
  have x11₂ : v₂.getReg .x11 = v₁.getReg .x11 := k₂ .x11 (by decide)
  by_cases h1 : v₂.getReg .x11 = (1 : Word)
  · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inl (trapAt (b800034f0_pc_taken h₃ h1)))⟩
  have k₃ := b800034f0_keeps h₃
  have hlen : 2 ≤ (vecLen w (s.getReg .x2 - 928)).toNat := by
    rw [← x11]
    rw [x11₂] at h1
    have a0 : (v₁.getReg .x11).toNat ≠ 0 := fun e ↦ h0 (BitVec.eq_of_toNat_eq e)
    have a1 : (v₁.getReg .x11).toNat ≠ 1 := fun e ↦ h1 (BitVec.eq_of_toNat_eq e)
    omega
  have hcl := hvo.len
  have hnb' := hnb
  simp only [NewBuf] at hnb'
  have hP8 := hnb'.1
  have hPb := hnb'.2.resolve_left (by omega)
  have hreg : Region (vecPtr w (s.getReg .x2 - 928)) ((vecCap w (s.getReg .x2 - 928)).toNat * 24) :=
    NewBuf.region hnb (h.keep.at11.base.inv.heap) N.inv.heap (by omega)
  have hwh := N.inv.heap.hi
  simp only [heapNext, heapEnd] at hwh
  have x10₃ : v₃.getReg .x10 = vecPtr w (s.getReg .x2 - 928) := by
    rw [k₃ .x10 (by decide), k₂ .x10 (by decide), x10]
  have m₁₃ (a : Word) : v₃.getMem a = w.getMem a := by
    rw [b800034f0_mem_same h₃, b800034ec_mem_same h₂, m₁]
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80003504_spec (b800034f0_pc_not_taken h₃ h1) (by
    rv_eval [x10₃]
    and_intros <;> exact Region.valid hreg (by addr_omega [hP8, hPb, hwh, hcl, hlen])
      (by addr_omega [hP8, hPb, hwh, hcl, hlen]) (by addr_omega [hP8, hPb, hwh, hcl, hlen]))
  have k₄ := b80003504_keeps h₄
  have m₁₄ (a : Word) : v₄.getMem a = w.getMem a := by rw [b80003504_mem_same h₄, m₁₃]
  have sp₄ : v₄.getReg .x2 = w.getReg .x2 := by
    rw [k₄ .x2 (by decide), k₃ .x2 (by decide), k₂ .x2 (by decide), k₁ .x2 (by decide)]
  have x21₄ : v₄.getReg .x21 = s.getReg .x10 := by
    rw [k₄ .x21 (by decide), k₃ .x21 (by decide), k₂ .x21 (by decide), x21]
  have k₁₃ (r : Reg) (hr : r ∈ ([.x2, .x27] : List Reg)) : v₃.getReg r = w.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  by_cases hz : v₃.getMem (v₃.getReg .x10 + (16 : Word)) ||| v₃.getMem (v₃.getReg .x10 + (40 : Word)) =
      (0 : Word)
  · have pc₄ := b80003504_pc_not_taken h₄ hz
    rw [x10₃, m₁₃, m₁₃] at hz
    obtain ⟨z0, z1⟩ := or_zero hz
    refine ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨pc₄, {
      ns := N
      mem := m₁₄
      sp := sp₄
      x10 := by rw [k₄ .x10 (by decide), x10₃]
      x21 := x21₄
      x22 := by
        rw [k₄ .x22 (by decide), b800034f0_x22 h₃, k₂ .x2 (by decide), k₁ .x2 (by decide), sp]
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      x23 := by
        rw [k₄ .x23 (by decide), b800034f0_x23 h₃, k₂ .x2 (by decide), k₁ .x2 (by decide), sp, tp]
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      x27 := by rw [k₄ .x27 (by decide), k₁₃ .x27 (by decide)]; exact N.x27
      ptr := rfl
      cap := hcap
      len := hlen
      buf := ⟨hP8, hPb.1, by omega⟩
      z0 := z0
      z1 := z1 }⟩)⟩
  · -- `Err`: a high limb
    obtain ⟨v₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800039dc_spec (b80003504_pc_taken h₄ hz) (by
      rv_eval [x21₄, sp₄, sp]
      and_intros <;> first
        | exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR]) (by addr_omega [hR])
        | exact frameByte hpre (by addr_omega [hb1]) (by addr_omega [hb1])
        | addr_omega [hb1, hb3])
    have fr := b800039dc_frame h₅ (by rw [x21₄]; addr_omega [hR])
    rw [x21₄] at fr
    obtain ⟨t, hr₆, ht⟩ := errRes hDL hpre h (I.same m₁₄ sp₄) (N.st.ext15 I.heap m₁₄ sp₄) fr
      (b800039dc_keeps h₅ .x2 (by decide)) (b800039dc_pc h₅)
      (by rw [← x21₄, b800039dc_m_x21_0 h₅]; rfl)
    exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))), ht.imp_right Or.inl⟩

end Rv64Verifier.Proofs.Walk
