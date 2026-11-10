import Rv64Verifier.Proofs.Bus.VbbTail21

/-!
# `verify_bus_balance` past the GKR loop: `vec![Form::default(); 3]` and the forms' buffer

From `alloc`'s entry (`Fps`): `alloc(8, 72)`, a `Vec<Form>` at `S - 608` of capacity `3`, `reserve(3)`
(`allocStep`); three default forms written into its buffer, then `try_allocate_in` of
`layout.tables.len()` `Vec<Form>`s, its buffer at `S - 1224`, its capacity at `S - 1328`
(`rowsStep`, `Rows0` at the clone loop's test). From here the count's limbs at `S - 1224` and
`S - 1232` are dead: `Kept2` is `Kept` without them.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## `Kept` without the count -/

/-- `Free` and the count's limbs. -/
def Free2 (s : MachineState) (a : Word) : Prop := Free s a ∨ Within a (s.getReg .x2 - 1232) 16

theorem Free2.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (Free2 s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha
  · exact Free.frameW hpre a ha
  · addr_omega [ha, hb1]

structure Kept2 (s u : MachineState) (k : Start) : Prop where
  out : u.getMem (s.getReg .x2 - 1312) = s.getReg .x10
  pushLen : u.getMem (s.getReg .x2 - 1264) = vecLen s (s.getReg .x11 + 24)
  countLen : u.getMem (s.getReg .x2 - 1248) = vecLen s (s.getReg .x11 + 72)
  layout : u.getMem (s.getReg .x2 - 1240) = s.getReg .x11
  beta1 : u.getMem (s.getReg .x2 - 1200) = k.beta1
  beta0 : u.getMem (s.getReg .x2 - 1192) = k.beta0
  beta2 : u.getMem (s.getReg .x2 - 1184) = k.beta2
  lm : u.getMem (s.getReg .x2 - 1136) = logMem s
  lb : u.getMem (s.getReg .x2 - 1152) = logBc s
  pullPtr : u.getMem (s.getReg .x2 - 1168) = vecPtr s (s.getReg .x11 + 48)
  pullLen : u.getMem (s.getReg .x2 - 1176) = vecLen s (s.getReg .x11 + 48)
  countPtr : u.getMem (s.getReg .x2 - 1160) = vecPtr s (s.getReg .x11 + 72)
  push : LayoutAt s u (s.getReg .x2 - 1080)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).push)
  pull : LayoutAt s u (s.getReg .x2 - 1024)
    (busLayoutRust [0, (logMem s).toNat, (logBc s).toNat] (busLayoutAt s (s.getReg .x11)).pull)
  count : LayoutAt s u (s.getReg .x2 - 968) (busLayoutRust [] (busLayoutAt s (s.getReg .x11)).count)
  weights : NewVecE s u (s.getReg .x2 - 888) (eqKernelRust k.alphas)

theorem Kept.toKept2 {s u : MachineState} {k : Start} (h : Kept s u k) : Kept2 s u k :=
  ⟨h.out, h.pushLen, h.countLen, h.layout, h.beta1, h.beta0, h.beta2, h.lm, h.lb, h.pullPtr,
    h.pullLen, h.countPtr, h.push, h.pull, h.count, h.weights⟩

/-- The words at `S - j`, `j` from `n` down, miss `Free2`. -/
theorem Free2.miss {s : MachineState} (hpre : BusBalancePre s) {j n : Nat} (hj : n ≤ j)
    (hj2 : j ≤ 1344)
    (h : ∀ i, j - n < i → i ≤ j → (1312 < i ∧ i ≤ 1344 → False) ∧ (1264 < i ∧ i ≤ 1304 → False) ∧
      (1248 < i ∧ i ≤ 1256 → False) ∧ (1200 < i ∧ i ≤ 1232 → False) ∧
      (1136 < i ∧ i ≤ 1144 → False) ∧ (1080 < i ∧ i ≤ 1128 → False) ∧ (104 < i ∧ i ≤ 864 → False)) :
    ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) n → ¬ Free2 s y := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro y hy hf
  have hyn : (s.getReg .x2).toNat - j ≤ y.toNat ∧ y.toNat < (s.getReg .x2).toNat - j + n := by
    addr_omega [hy, hb1, hj, hj2]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h ((s.getReg .x2).toNat - y.toNat) (by omega)
    (by omega)
  rcases hf with (hf | hf | hf | hf | hf | hf | hf) | hf
  · exact c1 (by addr_omega [hf, hb1, hyn])
  · exact c2 (by addr_omega [hf, hb1, hyn])
  · exact c3 (by addr_omega [hf, hb1, hyn])
  · exact c4 (by addr_omega [hf, hb1, hyn])
  · exact c5 (by addr_omega [hf, hb1, hyn])
  · exact c6 (by addr_omega [hf, hb1, hyn])
  · exact c7 (by addr_omega [hf, hb1, hyn])
  · exact c4 (by addr_omega [hf, hb1, hyn])

/-- A step writing only `Free2` keeps `Kept2`. -/
theorem Kept2.step {s v w : MachineState} {k : Start} (hpre : BusBalancePre s) (h : Kept2 s v k)
    (st : StepR s v w (Free2 s)) : Kept2 s w k := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hA := Free2.frameW hpre
  have wd (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hm : ∀ i, j - 8 < i → i ≤ j → (1312 < i ∧ i ≤ 1344 → False) ∧
        (1264 < i ∧ i ≤ 1304 → False) ∧ (1248 < i ∧ i ≤ 1256 → False) ∧
        (1200 < i ∧ i ≤ 1232 → False) ∧ (1136 < i ∧ i ≤ 1144 → False) ∧
        (1080 < i ∧ i ≤ 1128 → False) ∧ (104 < i ∧ i ≤ 864 → False)) :
      w.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    st.word hpre (Free2.miss hpre hj hj2 hm) (Or.inl (by addr_omega [hb1, hj, hj2]))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h.out]; exact wd 1312 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pushLen]; exact wd 1264 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.countLen]; exact wd 1248 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.layout]; exact wd 1240 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta1]; exact wd 1200 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta0]; exact wd 1192 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.beta2]; exact wd 1184 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.lm]; exact wd 1136 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.lb]; exact wd 1152 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pullPtr]; exact wd 1168 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.pullLen]; exact wd 1176 (by omega) (by omega) (by intro i h1 h2; omega)
  · rw [← h.countPtr]; exact wd 1160 (by omega) (by omega) (by intro i h1 h2; omega)
  · exact h.push.keepR hpre st hA (inFrame hpre (k := 1080) (n := 56) (by omega) (by omega))
      (Free2.miss hpre (j := 1080) (by omega) (by omega) (by intro i h1 h2; omega))
  · exact h.pull.keepR hpre st hA (inFrame hpre (k := 1024) (n := 56) (by omega) (by omega))
      (Free2.miss hpre (j := 1024) (by omega) (by omega) (by intro i h1 h2; omega))
  · exact h.count.keepR hpre st hA (inFrame hpre (k := 968) (n := 56) (by omega) (by omega))
      (Free2.miss hpre (j := 968) (by omega) (by omega) (by intro i h1 h2; omega))
  · exact h.weights.keepR hpre st hA (by addr_omega [hb1])
      (Free2.miss hpre (j := 888) (by omega) (by omega) (by intro i h1 h2; omega))

/-! ## `alloc` and `reserve` -/

/-- `alloc(8, 72)`, the `Vec<Form>` `(3, ptr, 0)` at `S - 608`, `reserve(3)`: at `0x80007298`, a
`Vec` of length `0` and capacity at least `3`, its buffer new since `alloc`'s entry. -/
theorem allocStep (hA : AllocSpec) (hR : ReserveFreshSpec 0x80004aec 24 8)
    {bev : MachineState → Word → List E → Option E} {s z : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (F : Fps bev s z k state mem mf bf bv) (hpc : z.pc = 0x80000284) :
    ∃ v, Reaches Image.code z v ∧ (Dead Image.code v ∨ (v.pc = 0x80007298 ∧ Inv s v ∧
      StepS s z v (Within · (s.getReg .x2 - 608) 24) ∧
      (∀ r ∈ calleeSaved, v.getReg r = z.getReg r) ∧ VecOk v (s.getReg .x2 - 608) 24 8 ∧
      3 ≤ (vecCap v (s.getReg .x2 - 608)).toNat ∧ vecLen v (s.getReg .x2 - 608) = 0 ∧
      NewBuf z v (vecPtr v (s.getReg .x2 - 608)) ((vecCap v (s.getReg .x2 - 608)).toNat * 24) 8))
    := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have I := F.inv
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  obtain ⟨t, hrt, ⟨hpct, hpt, post⟩ | hd⟩ :=
    hA.call (Reaches.refl z) hpc ⟨I.heap, by rw [F.x10]; decide⟩
  swap
  · exact ⟨t, hrt, Or.inl hd⟩
  have hal := post.aligned
  have hab := post.above
  have hnx := post.next
  have e3 : (3 : Word).toNat = 3 := rfl
  have e8 : (8 : Word).toNat = 8 := rfl
  have e72 : (72 : Word).toNat = 72 := rfl
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [F.x10, e8] at hal
  rw [F.x11, e72] at hnx
  have hlo := I.heap.lo
  have hhi := post.heap.hi
  simp only [heapNext, heapStart, heapEnd] at hab hnx hlo hhi
  have frt : DFrame z t (Within · nextAddr 8) := fun a ha ↦ post.mem a fun he ↦ ha 0 (by decide)
    (by rw [add_ofNat_zero, he]; exact ⟨Nat.le_refl _, by simp only [nextAddr]; decide⟩)
  have stt : StepS s z t (Within · (s.getReg .x2 - 608) 24) :=
    ⟨frt.mono fun _ ha ↦ Or.inr (Or.inr (Or.inl ha)), post.heap,
      by simp only [heapNext]; omega, hpt .x2 (by decide)⟩
  have It := I.afterR hpre (frameW_slot hpre (k := 608) (by omega) (by omega)) stt.toR
  have hpct' : t.pc = 0x80007274 := by rw [hpct, returnAddress_eq, F.x1]; decide
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007274_spec hpct' trivial
  have k₁ := b80007274_keeps h₁
  have pc₁ := b80007274_pc_not_taken h₁ (by intro h0; rw [h0, h00] at hab; omega)
  have m₁ := b80007274_mem_same h₁
  have I₁ := It.same m₁ (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007278_spec pc₁ (by
    rv_eval [sp₁]
    and_intros <;> valid_access hval [hb1])
  have k₂ := b80007278_keeps h₂
  have fr₂ : DFrame t₁ u₂ (Within · (s.getReg .x2 - 608) 24) :=
    (DFrame.of_memFrame (b80007278_frame h₂ (by rw [sp₁]; addr_omega [hb1]))).mono
      fun a ha ↦ by rw [sp₁] at ha; addr_omega [ha, hb1]
  have st₂ : StepS s t₁ u₂ (Within · (s.getReg .x2 - 608) 24) :=
    StepS.ofDFrame I₁.heap fr₂ (fun _ h ↦ h) (fun i hi hw ↦ by addr_omega [hw, hi, hb1])
      (k₂ .x2 (by decide))
  have I₂ := I₁.afterR hpre (frameW_slot hpre (k := 608) (by omega) (by omega)) st₂.toR
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  have hn₂ : heapNext u₂ = heapNext t := by
    simp only [heapNext]
    rw [fr₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb1], m₁]
  have c₂ : vecCap u₂ (s.getReg .x2 - 608) = 3 :=
    slotOf hpre sp₁ (j := 736) (by omega) (b80007278_m_x2_736 h₂)
  have p₂ : vecPtr u₂ (s.getReg .x2 - 608) = t.getReg .x10 := by
    rw [vecPtr, show s.getReg .x2 - 608 + 8 = s.getReg .x2 - BitVec.ofNat 64 (1344 - 744) by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], slotOf hpre sp₁ (j := 744) (by omega)
      (b80007278_m_x2_744 h₂), k₁ .x10 (by decide)]
  have l₂ : vecLen u₂ (s.getReg .x2 - 608) = 0 := by
    rw [vecLen, show s.getReg .x2 - 608 + 16 = s.getReg .x2 - BitVec.ofNat 64 (1344 - 752) by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact slotOf hpre sp₁ (j := 752) (by omega) (b80007278_m_x2_752 h₂)
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 608 := by
    rw [b80007278_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := reserveStack) hpre I₂ (n := 24) (k := 608)
    (by omega) (by omega) (by omega) (by decide)
  have pre : ReservePre 24 8 u₂ := {
    heap := I₂.heap
    self := by rw [x10₂]; exact regionRange o1 (Nat.le_refl _) (by addr_omega [hb1]) o1.2
    vec := by
      rw [x10₂]
      refine ⟨?_, by rw [l₂, c₂]; decide⟩
      simp only [RawVecOk, Buf]
      rw [p₂, c₂, hn₂, e3]
      simp only [heapNext, heapStart]
      exact ⟨hal, Or.inr ⟨by omega, by omega⟩⟩
    stack := hpre.stack.sub 1344 sp₂ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := x10₂ ▸ o2
    selfStack := x10₂ ▸ o3 }
  obtain ⟨v, hrv, ⟨hpcv, hpv, post₂, hfr⟩ | hd⟩ := hR.call (Reaches.refl u₂) (b80007278_pc h₂) pre
  swap
  · exact ⟨v, hrt.trans (hr₁.trans (hr₂.trans hrv)), Or.inl hd⟩
  have hsl : stackLo u₂ reserveStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 160) := by
    simp only [stackLo, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have frv := DFrame.of_byteFrame post₂.frame
  rw [x10₂, hsl] at frv
  have stv : StepS s u₂ v (Within · (s.getReg .x2 - 608) 24) :=
    ⟨frv.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr ha), post₂.heap, post₂.mono, hpv .x2 (by decide)⟩
  have st : StepS s z v (Within · (s.getReg .x2 - 608) 24) :=
    ((((stt.trans (StepS.same m₁ It.heap (k₁ .x2 (by decide)))).trans st₂).trans stv).weaken
      fun a ha ↦ by rcases ha with (((ha | ha) | ha) | ha) <;> exact ha)
  have hm := post₂.mono
  have hcap := post₂.cap
  have hvl := post₂.len
  rw [x10₂, l₂] at hcap hvl
  rw [x10₂] at hfr
  have hnz : heapNext z ≤ heapNext u₂ := by rw [hn₂]; simp only [heapNext]; omega
  refine ⟨v, hrt.trans (hr₁.trans (hr₂.trans hrv)), Or.inr ⟨by
    rw [hpcv, returnAddress_eq, b80007278_x1 h₂]; decide,
    I₂.afterR hpre (frameW_slot hpre (k := 608) (by omega) (by omega)) stv.toR, st,
    fun r hr ↦ by
      rw [hpv r hr, k₂ r (by unfold calleeSaved at hr; exact mem_of_mem hr _),
        k₁ r (mem_of_mem hr _), hpt r hr],
    by have := post₂.vec; rw [x10₂] at this; exact this,
    by rw [b80007278_x11 h₂, e3] at hcap; simpa using hcap, hvl, ?_⟩⟩
  rcases hfr with ⟨hp, hc⟩ | hfr
  · rw [hp, hc, p₂, c₂, e3]
    have hm' : heapNext t ≤ heapNext v := hn₂ ▸ hm
    simp only [NewBuf]
    refine ⟨hal, Or.inr ⟨hab, ?_⟩⟩
    simp only [heapNext] at hm' ⊢
    omega
  · simp only [NewBuf] at hfr ⊢
    exact ⟨hfr.1, hfr.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩

/-! ## The default forms and the forms' buffer -/

/-- What the steps from `alloc`'s entry to the clone loop write in the frame. -/
def RowsW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 608) 24 ∨ Within a (s.getReg .x2 - 1328) 8 ∨
    Within a (s.getReg .x2 - 1224) 8

theorem RowsW.frameW {s : MachineState} (hpre : BusBalancePre s) : FrameW s (RowsW s) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]

theorem RowsW.free2 {s : MachineState} (hpre : BusBalancePre s) {a : Word} (ha : RowsW s a) :
    Free2 s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases ha with ha | ha | ha
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
  · exact Or.inr (by addr_omega [ha, hb1])

/-- `Form::default()`'s three words at `p`. -/
def DefaultAt (u : MachineState) (p : Word) : Prop :=
  u.getMem p = 0 ∧ u.getMem (p + 8) = 8 ∧ u.getMem (p + 16) = 0

/-- Past `0x80007304`, at the clone loop's test: `vec![Form::default(); 3]` in `s1` (capacity),
`s2` (buffer), `s3` (length `3`), its buffer new since `z`; the forms' buffer of
`layout.tables.len()` (in `s9`) `Vec<Form>`s in `s7` and at `S - 1224`, its capacity at
`S - 1328`, new since the first. -/
structure Rows0 (s z w : MachineState) : Prop where
  inv : Inv s w
  step : StepS s z w (RowsW s)
  regs : ∀ r ∈ ([.x8, .x20, .x21, .x22, .x24, .x26, .x27] : List Reg), w.getReg r = z.getReg r
  icap : 3 ≤ (w.getReg .x9).toNat
  ibuf : NewBuf z w (w.getReg .x18) ((w.getReg .x9).toNat * 24) 8
  idef : ∀ i < 3, DefaultAt w (w.getReg .x18 + BitVec.ofNat 64 (24 * i))
  x19 : w.getReg .x19 = 3
  x25 : w.getReg .x25 = vecLen s (s.getReg .x11)
  x23 : w.getReg .x23 = w.getMem (s.getReg .x2 - 1224)
  ocap : w.getMem (s.getReg .x2 - 1328) = w.getReg .x25
  obuf : NewBuf z w (w.getReg .x23) ((w.getReg .x25).toNat * 24) 8
  apart : (w.getReg .x18).toNat + (w.getReg .x9).toNat * 24 ≤ (w.getReg .x23).toNat ∨
    (w.getReg .x25).toNat = 0
  pc : (w.pc = 0x80007320 ∧ 2 ≤ (w.getReg .x25).toNat) ∨
    (w.pc = 0x8000736c ∧ (w.getReg .x25).toNat < 2)

theorem rowsStep (hA : AllocSpec) (hR : ReserveFreshSpec 0x80004aec 24 8)
    (hT : TryAllocZeroedSpec) {bev : MachineState → Word → List E → Option E} {s z : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (F : Fps bev s z k state mem mf bf bv) (hpc : z.pc = 0x80000284) :
    ∃ w, Reaches Image.code z w ∧ (Dead Image.code w ∨ Rows0 s z w) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, hd | ⟨hpcv, Iv, stv, rgv, vv, capv, lenv, bufv⟩⟩ := allocStep hA hR hpre F hpc
  · exact ⟨v, hrv, Or.inl hd⟩
  have spv : v.getReg .x2 = s.getReg .x2 - 1344 := Iv.sp
  have Kv : Kept s v k := F.kept.step hpre (stv.toR.weaken fun a ha ↦
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  have av (j : Nat) (hj : j ≤ 1344) : v.getReg .x2 + BitVec.ofNat 64 j =
      s.getReg .x2 - BitVec.ofNat 64 (1344 - j) := by
    rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  have hp : v.getMem (v.getReg .x2 + 744) = vecPtr v (s.getReg .x2 - 608) := by
    rw [vecPtr]; exact congrArg v.getMem (by rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hl0 : v.getMem (v.getReg .x2 + 752) = 0 := by
    rw [← lenv, vecLen]
    exact congrArg v.getMem (by rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hc : v.getMem (v.getReg .x2 + 736) = vecCap v (s.getReg .x2 - 608) := by
    rw [vecCap]; exact congrArg v.getMem (by rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hlay : v.getMem (v.getReg .x2 + 104) = s.getReg .x11 := by
    rw [← Kv.layout]; exact congrArg v.getMem (by rw [spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hl := hpre.layout
  have hR' : Region (s.getReg .x11) 168 := by
    rcases hl.region with h0 | h0
    · exact absurd h0 (by decide)
    · exact h0
  have hRm := hR'
  simp only [Region, Mapped] at hRm
  have hlf := hl.free
  have htl : v.getMem (s.getReg .x11 + 16) = vecLen s (s.getReg .x11) := by
    rw [vecLen]; exact Iv.word hl (by addr_omega [hRm]) (by addr_omega [hRm])
  set P := vecPtr v (s.getReg .x2 - 608) with hP
  have hcap := capv
  obtain ⟨q0, q1, q2⟩ : P.toNat % 8 = 0 ∧ heapNext z ≤ P.toNat ∧
      P.toNat + (vecCap v (s.getReg .x2 - 608)).toNat * 24 ≤ heapNext v := by
    simp only [NewBuf] at bufv
    rcases bufv.2 with h0 | h0
    · omega
    · exact ⟨bufv.1, h0⟩
  have hlo := hpre.heap.lo
  have hmz := F.inv.mono
  have hhi := Iv.heap.hi
  simp only [heapNext, heapStart, heapEnd, Outside] at hlo hmz hhi q1 q2 hlf
  have hheap : ValidMemRange P 9 :=
    heapRange q0 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hp' : v.getMem (s.getReg .x2 - 600) = P := by
    rw [← hp, spv]; exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hl0' : v.getMem (s.getReg .x2 - 592) = 0 := by
    rw [← hl0, spv]; exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hlay' : v.getMem (s.getReg .x2 - 1240) = s.getReg .x11 := by
    rw [← hlay, spv]; exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  obtain ⟨u, hru, hu⟩ := Sym.BlockSpec.reaches b80007298_spec hpcv (by
    rv_eval [spv, hp', hl0', hlay']
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [q0, q1, q2, hcap, hhi]
      | exact Region.valid hR' (by addr_omega [hRm]) (by addr_omega [hRm]) (by addr_omega [hRm])
      | addr_omega [hRm, hlf, q1, q2, hcap, hmz, hhi, hb1])
  have k₁ := b80007298_keeps hu
  have fru : DFrame v u (Within · P 72) := fun a ha ↦ hu.frame a (by
    rv_eval [spv, hp', hl0', hlay']
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]; addr_omega [q0, q1, q2, hcap, hhi]))
  have hnu : heapNext u = heapNext v := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fru _ fun i hi hw ↦ by addr_omega [hw, hi, q1, q2, hcap, hhi])
  have stu : StepS s z u fun a ↦ Within a (s.getReg .x2 - 608) 24 ∨ False :=
    stv.extend (fru.mono fun a ha ↦ Or.inr ⟨by simp only [heapNext]; addr_omega [ha, q1], by
      simp only [heapNext]; addr_omega [ha, q1, q2, hcap]⟩) hnu (k₁ .x2 (by decide))
  have Iu : Inv s u := Iv.step hpre fru (fun a ha ↦ ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by
      simp only [heapNext]; addr_omega [ha, q1, hmz], by
      rw [hnu]; simp only [heapNext]; addr_omega [ha, q1, q2, hcap]⟩))),
      by addr_omega [ha, q2, hhi, hb1, hcap]⟩)
    ⟨hnu ▸ Iv.heap.lo, hnu ▸ Iv.heap.hi⟩ hnu.ge (k₁ .x2 (by decide))
  have spu : u.getReg .x2 = s.getReg .x2 - 1344 := Iu.sp
  have x9v : v.getReg .x9 = 8 := (rgv .x9 (by decide)).trans F.x9
  have mm (j : Nat) {c : Word} (h : u.getMem (v.getMem (v.getReg .x2 + 744) +
      (v.getMem (v.getReg .x2 + 752) * 16 + v.getMem (v.getReg .x2 + 752) * 8) +
      BitVec.ofNat 64 j) = c) : u.getMem (P + BitVec.ofNat 64 j) = c := by
    rw [hp, hl0] at h; simpa using h
  have m0 : u.getMem P = 0 := by
    have h := b80007298_m8 hu; rw [hp, hl0] at h; simpa using h
  have d0 : DefaultAt u P := ⟨m0, (mm 8 (b80007298_m7 hu)).trans x9v, mm 16 (b80007298_m6 hu)⟩
  have d1 : DefaultAt u (P + BitVec.ofNat 64 24) := by
    refine ⟨mm 24 (b80007298_m5 hu), ?_, ?_⟩
    · rw [BitVec.add_assoc]; exact (mm 32 (b80007298_m4 hu)).trans x9v
    · rw [BitVec.add_assoc]; exact mm 40 (b80007298_m3 hu)
  have d2 : DefaultAt u (P + BitVec.ofNat 64 48) := by
    refine ⟨mm 48 (b80007298_m2 hu), ?_, ?_⟩
    · rw [BitVec.add_assoc]; exact (mm 56 (b80007298_m1 hu)).trans x9v
    · rw [BitVec.add_assoc]; exact mm 64 (b80007298_m0 hu)
  have x10u : u.getReg .x10 = s.getReg .x2 - 608 := by
    rw [b80007298_x10 hu, spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := tryAllocStack) hpre Iu (n := 24) (k := 608)
    (by omega) (by omega) (by omega) (by decide)
  have pre : TryAllocPre .x13 .x14 u := {
    heap := Iu.heap
    out := by rw [x10u]; exact regionRange o1 (Nat.le_refl _) (by addr_omega [hb1]) o1.2
    align := by rw [b80007298_x13 hu]; decide
    size := by rw [b80007298_x14 hu]; decide
    stack := hpre.stack.sub 1344 spu (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := x10u ▸ o2
    outStack := x10u ▸ o3 }
  obtain ⟨t, hrt, ⟨hpct, hpt, post, -⟩ | hd⟩ := hT.call (Reaches.refl u) (b80007298_pc hu) pre
  swap
  · exact ⟨t, hrv.trans (hru.trans hrt), Or.inl hd⟩
  have hsl : stackLo u tryAllocStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 48) := by
    simp only [stackLo, spu]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have frt := DFrame.of_byteFrame post.frame
  rw [x10u, hsl] at frt
  have stt : StepS s u t (Within · (s.getReg .x2 - 608) 24) :=
    ⟨frt.mono fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr ha), post.heap, post.mono, hpt .x2 (by decide)⟩
  have It := Iu.afterR hpre (frameW_slot hpre (k := 608) (by omega) (by omega)) stt.toR
  have spt : t.getReg .x2 = s.getReg .x2 - 1344 := It.sp
  have hpct' : t.pc = 0x800072fc := by rw [hpct, returnAddress_eq, b80007298_x1 hu]; decide
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800072fc_spec hpct' (by
    rv_eval [spt]
    valid_access hval [hb1])
  have e736 : t.getReg .x2 + 736 = s.getReg .x2 - 608 := by
    rw [spt]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases htag : t.getMem (s.getReg .x2 - 608) = 0
  swap
  · have pc₁ := b800072fc_pc_taken h₁ (by rw [e736]; exact htag)
    exact ⟨t₁, hrv.trans (hru.trans (hrt.trans hr₁)), Or.inl (dead_of_fetch (by
      rw [pc₁]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have pc₁ := b800072fc_pc_not_taken h₁ (by rw [e736]; exact htag)
  have k₂ := b800072fc_keeps h₁
  have m₂ := b800072fc_mem_same h₁
  have I₁ := It.same m₂ (k₂ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  obtain ⟨w, hrw, h₃⟩ := Sym.BlockSpec.reaches b80007304_spec pc₁ (by
    rv_eval [sp₁]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80007304_keeps h₃
  have frw : DFrame t₁ w fun a ↦ Within a (s.getReg .x2 - 1328) 8 ∨
      Within a (s.getReg .x2 - 1224) 8 := fun a ha ↦ h₃.frame a (by
    rv_eval [sp₁]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]
      first | exact Or.inl (by addr_omega [hb1]) | exact Or.inr (by addr_omega [hb1])))
  have stw : StepS s t₁ w (RowsW s) :=
    StepS.ofDFrame I₁.heap frw (fun a ha ↦ Or.inr ha)
      (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1]) (k₃ .x2 (by decide))
  have Iw := I₁.afterR hpre (RowsW.frameW hpre) stw.toR
  have st : StepS s z w (RowsW s) :=
    ((((stu.trans stt).trans (StepS.same (A := fun _ ↦ False) m₂ It.heap
      (k₂ .x2 (by decide)))).trans stw).weaken fun a ha ↦ by
        rcases ha with ((((ha | ha) | ha) | ha) | ha)
        · exact Or.inl ha
        · exact ha.elim
        · exact Or.inl ha
        · exact ha.elim
        · exact ha)
  have ok := post.ok (by rw [x10u]; exact htag)
  rw [x10u] at ok
  obtain ⟨ok1, ok2⟩ := ok
  have a600 : s.getReg .x2 - 608 + 8 = s.getReg .x2 - 600 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a592 : s.getReg .x2 - 608 + 16 = s.getReg .x2 - 592 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [a600] at ok1
  rw [a592] at ok2
  have r₃ (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x24, .x25, .x26, .x27] :
      List Reg)) : w.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      hpt r (by unfold calleeSaved; exact mem_of_mem hr _)]
  have x25u : u.getReg .x25 = vecLen s (s.getReg .x11) := by
    rw [b80007298_x25 hu, hlay, htl]
  have x23w : w.getReg .x23 = t.getMem (s.getReg .x2 - 592) := by
    rw [b80007304_x23 h₃, sp₁, m₂]
    exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have w1224 : w.getMem (s.getReg .x2 - 1224) = t.getMem (s.getReg .x2 - 592) := by
    rw [show s.getReg .x2 - 1224 = t₁.getReg .x2 + 120 by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80007304_m_x2_120 h₃, sp₁, m₂]
    exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have w1328 : w.getMem (s.getReg .x2 - 1328) = t.getMem (s.getReg .x2 - 600) := by
    rw [show s.getReg .x2 - 1328 = t₁.getReg .x2 + 16 by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80007304_m_x2_16 h₃, sp₁, m₂]
    exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hnw : heapNext w = heapNext t := by
    simp only [heapNext]
    rw [frw _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1], m₂]
  have hmt := post.mono
  -- the default forms, kept from `u`
  have keepP (x : Word) (h1 : P.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ P.toNat + 72) :
      w.getMem x = u.getMem x := by
    rw [frw x fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, h1, h2, q2, hhi,
      hcap], m₂]
    refine frt x fun i hi hw ↦ ?_
    have hnu' : (u.getMem nextAddr).toNat = (v.getMem nextAddr).toNat := hnu
    simp only [Fresh, heapNext] at hw
    rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, hb1, h1, h2, q2, hhi, hcap, hnu']
  have dk (o : Nat) (ho : o ≤ 48) (hd : DefaultAt u (P + BitVec.ofNat 64 o)) :
      DefaultAt w (P + BitVec.ofNat 64 o) := by
    obtain ⟨d0, d1, d2⟩ := hd
    refine ⟨(keepP _ (by addr_omega [q2, hcap, hhi, ho]) (by addr_omega [q2, hcap, ho, hhi])).trans d0,
      (keepP _ (by addr_omega [q2, hcap, hhi, ho]) (by addr_omega [q2, hcap, ho, hhi])).trans d1,
      (keepP _ (by addr_omega [q2, hcap, hhi, ho]) (by addr_omega [q2, hcap, ho, hhi])).trans d2⟩
  refine ⟨w, hrv.trans (hru.trans (hrt.trans (hr₁.trans hrw))), Or.inr {
    inv := Iw
    step := st
    regs := fun r hr ↦ by
      rw [r₃ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _),
        rgv r (by unfold calleeSaved; exact mem_of_mem hr _)]
    icap := by rw [r₃ .x9 (by decide), b80007298_x9 hu, hc]; exact capv
    ibuf := by
      rw [r₃ .x18 (by decide), b80007298_x18 hu, hp, r₃ .x9 (by decide), b80007298_x9 hu, hc]
      simp only [NewBuf] at bufv ⊢
      refine ⟨bufv.1, bufv.2.imp_right fun h' ↦ ⟨h'.1, ?_⟩⟩
      rw [hnw]
      have hnu' : (u.getMem nextAddr).toNat = (v.getMem nextAddr).toNat := hnu
      simp only [heapNext] at h' hmt ⊢
      omega
    idef := by
      rw [r₃ .x18 (by decide), b80007298_x18 hu, hp]
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact dk 0 (by omega) (by simpa using d0)
      · exact dk 24 (by omega) d1
      · exact dk 48 (by omega) d2
    x19 := by rw [b80007304_x19 h₃, k₂ .x19 (by decide), hpt .x19 (by decide), b80007298_x19 hu, hl0]; rfl
    x25 := by rw [r₃ .x25 (by decide)]; exact x25u
    x23 := by rw [x23w, w1224]
    ocap := by rw [w1328, ok1, r₃ .x25 (by decide), b80007298_x11 hu, b80007298_x25 hu]
    obuf := by
      rw [x23w, r₃ .x25 (by decide), b80007298_x25 hu, ← b80007298_x11 hu,
        show (u.getReg .x11).toNat * 24 =
        (u.getReg .x11).toNat * (u.getReg .x14).toNat by rw [b80007298_x14 hu]; rfl]
      have := ok2
      rw [b80007298_x13 hu] at this
      simp only [NewBuf] at this ⊢
      refine ⟨this.1, this.2.imp_right fun h' ↦ ⟨?_, by rw [hnw]; exact h'.2⟩⟩
      have := h'.1
      rw [hnu] at this
      simp only [heapNext] at this ⊢
      omega
    apart := by
      rw [r₃ .x18 (by decide), b80007298_x18 hu, hp, r₃ .x9 (by decide), b80007298_x9 hu, hc,
        x23w, r₃ .x25 (by decide), b80007298_x25 hu, ← b80007298_x11 hu]
      have := ok2
      rw [b80007298_x13 hu, b80007298_x14 hu] at this
      simp only [NewBuf] at this
      rcases this.2 with h0 | h0
      · have e24 : (24 : Word).toNat = 24 := rfl
        exact Or.inr (by rw [e24] at h0; omega)
      · left
        have := h0.1
        rw [hnu] at this
        simp only [heapNext] at this
        omega
    pc := by
      rw [r₃ .x25 (by decide)]
      by_cases h2 : 2 ≤ (u.getReg .x25).toNat
      · exact Or.inl ⟨b80007304_pc_not_taken h₃ (by
          rw [k₂ .x25 (by decide), hpt .x25 (by decide)]; exact h2), h2⟩
      · exact Or.inr ⟨b80007304_pc_taken h₃ (by
          rw [k₂ .x25 (by decide), hpt .x25 (by decide)]; show _ < 2; omega), by omega⟩ }⟩

/-- From `0x80006ca0` to the clone loop's test: the rest's stages composed. -/
theorem restToRows (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) (hA : AllocSpec)
    (hG : GrowOneFreshSpec 0x8000c0a4 56 8) (hI : IndexMleSpec) (hC : SliceConcatSpec)
    {BcOk : MachineState → Nat → Word → Prop} {bev : MachineState → Word → List E → Option E}
    (hB : Vbb.BytecodeEvalSpec BcOk bev) (hBT : BcTransfer BcOk bev) (hP : PowSpec)
    (hF : FingerprintsSpec) (hR : ReserveFreshSpec 0x80004aec 24 8) {s q : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (hbc : BcOk s busBalanceStack (bytecodeOf s (s.getReg .x11)))
    (Sc : Scalars bev s q k state mem mf bf) (hpc : q.pc = 0x80006ca0) :
    ∃ w, Reaches Image.code q w ∧ (Done bev s w ∨ Dead Image.code w ∨
      ∃ z bv, Fps bev s z k state mem mf bf bv ∧ Rows0 s z w) := by
  obtain ⟨v, hrv, hd | ⟨hpcv, X⟩⟩ := restToConcat hT hM hA hG hI hpre Sc hpc
  · exact ⟨v, hrv, Or.inr (Or.inl hd)⟩
  obtain ⟨y, hry, hdone | hd | ⟨hpcy, bv, E⟩⟩ := evalStage hC hB hBT hpre hbc X hpcv
  · exact ⟨y, hrv.trans hry, Or.inl hdone⟩
  · exact ⟨y, hrv.trans hry, Or.inr (Or.inl hd)⟩
  obtain ⟨z, hrz, hd | ⟨hpcz, F⟩⟩ := fpsStage hP hF hpre E hpcy
  · exact ⟨z, hrv.trans (hry.trans hrz), Or.inr (Or.inl hd)⟩
  obtain ⟨w, hrw, hd | R⟩ := rowsStep hA hR hT hpre F hpcz
  · exact ⟨w, hrv.trans (hry.trans (hrz.trans hrw)), Or.inr (Or.inl hd)⟩
  exact ⟨w, hrv.trans (hry.trans (hrz.trans hrw)), Or.inr (Or.inr ⟨z, bv, F, R⟩)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
