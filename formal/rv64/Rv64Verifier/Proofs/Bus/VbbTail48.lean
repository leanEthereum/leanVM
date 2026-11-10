import Rv64Verifier.Proofs.Bus.VbbTail47

/-!
# `verify_bus_balance`'s side loop: the block's coordinates' loop

The loop at `0x800079bc` adds coordinate `j` of block `k`, read only in the `Layout`, times the
side's weight `j` (`weightAt`), to the block's form at `S - 296` (`CoI`, `coIter`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The side's weight `j`, at any state of the side's iteration. -/
theorem weightAt {s z h e t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} (hpre : BusBalancePre s) (En : Entry s z h e i sd point P n) (Ih : Inv s h)
    (C : Cur s z h t) (hzh : heapNext z ≤ heapNext h) {j : Nat}
    (hj : j < (e.getMem (s.getReg .x2 - 1248)).toNat) :
    eAt t (e.getMem (s.getReg .x2 - 1264) + BitVec.ofNat 64 (24 * j)) = sd.2.2.2.1.getD j 0 := by
  rcases En.wBuf with ⟨W8, Wb⟩ | ⟨hw1, hw2⟩
  · have hWl := Wb.resolve_left (by omega)
    have hz := Ih.heap.hi
    simp only [heapNext, heapEnd, heapStart] at hWl hz hzh
    have rd (q : Nat) (hq : q + 8 ≤ 24) :
        t.getMem (e.getMem (s.getReg .x2 - 1264) + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 q) =
          h.getMem (e.getMem (s.getReg .x2 - 1264) + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 q) :=
      C.low hpre Ih (by simp only [heapNext]; omega)
        (by simp only [heapStart]; addr_omega [hWl, hj, hq])
        (by simp only [heapNext]; addr_omega [hWl, hj, hq])
    rw [← En.wts, eListAt_getD _ _ hj]
    exact eAt_congr (by simpa using rd 0 (by omega)) (rd 8 (by omega)) (rd 16 (by omega))
  · have hw := En.wts
    rw [hw2] at hj
    rw [hw1, hw2, show (1 : Word).toNat = 1 from rfl] at hw
    rw [hw1]
    have hj0 : j = 0 := by
      have : (1 : Word).toNat = 1 := rfl
      omega
    subst hj0
    rw [← hw]
    simp only [eListAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, add_ofNat_zero,
      List.getD_cons_zero, oneAt (C.inv.rodata hpre), oneAt (Ih.rodata hpre)]

/-- In the coordinates' loop at `0x800079bc` from its entry `v₀`, `j` coordinates of block `k`
added, the block's form's buffer allocated from `t₀`'s `NEXT` on. -/
structure CoI (s z h t₀ v₀ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (k j : Nat) : Prop where
  cur : Cur s z h t
  fr : DFrame v₀ t (CoW s t₀ t)
  mono : heapNext v₀ ≤ heapNext t
  regs : ∀ r ∈ ([.x2, .x8, .x9, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg),
    t.getReg r = v₀.getReg r
  x18 : t.getReg .x18 = v₀.getReg .x18 - BitVec.ofNat 64 j
  x10 : t.getReg .x10 = v₀.getReg .x10 + BitVec.ofNat 64 (24 * j)
  x13 : t.getReg .x13 = v₀.getReg .x13 + BitVec.ofNat 64 (24 * j)
  ok : Layout.FormOk t (s.getReg .x2 - 296)
  fbuf : ∀ x, Layout.formBuf t (s.getReg .x2 - 296) x → heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext t
  form : (Layout.formOf t (s.getReg .x2 - 296)).toSpec =
    coFold sd.2.2.2.1 sd.2.2.2.2 (blockAt s (blkAddr s i k)).coordinates j
  len : 1 ≤ (vecLen t (s.getReg .x2 - 296)).toNat

/-- The weights lie below the frame. -/
theorem weightBuf {s z h e : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} (En : Entry s z h e i sd point P n) (hz : heapNext z ≤ heapEnd) :
    ValidMemRange (e.getMem (s.getReg .x2 - 1264)) (3 * (e.getMem (s.getReg .x2 - 1248)).toNat) ∧
      (0 < (e.getMem (s.getReg .x2 - 1248)).toNat →
        (e.getMem (s.getReg .x2 - 1264)).toNat + 24 * (e.getMem (s.getReg .x2 - 1248)).toNat ≤
          0xa0000f38) := by
  rcases En.wBuf with ⟨W8, Wb⟩ | ⟨hw1, hw2⟩
  · simp only [heapEnd] at hz
    rcases Wb with h0 | ⟨b1, b2⟩
    · exact ⟨fun q hq ↦ by omega, fun h ↦ by omega⟩
    · exact ⟨heapRange W8 b1 (by simp only [heapEnd]; omega), fun _ ↦ by omega⟩
  · rw [hw1, hw2]
    exact ⟨Layout.validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩), fun _ ↦ by decide⟩

set_option maxRecDepth 8192 in
/-- One coordinate. -/
theorem coIter (hAS : Layout.AddScaledSpec) {s z h e t₀ v₀ t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n k j : Nat} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (hzt : heapNext z ≤ heapNext t₀) (htv : heapNext t₀ ≤ heapNext v₀) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n)
    (hro : FormRowsRO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (blkAddr s i k) 1)
    (hv10 : v₀.getReg .x10 = vecPtr s (blkAddr s i k) + 16)
    (hv13 : v₀.getReg .x13 = e.getMem (s.getReg .x2 - 1264))
    (hv18 : v₀.getReg .x18 = e.getMem (s.getReg .x2 - 1248) + 1)
    (hv9 : v₀.getReg .x9 = coBound (e.getMem (s.getReg .x2 - 1248)) (vecLen s (blkAddr s i k)).toNat)
    (hc : (vecLen s (blkAddr s i k)).toNat < 2 ^ 60)
    (S : CoI s z h t₀ v₀ t i sd k j) (hjc : j < (vecLen s (blkAddr s i k)).toNat)
    (hjw : j ≤ (e.getMem (s.getReg .x2 - 1248)).toNat) (hpc : t.pc = 0x800079bc) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨ (CoI s z h t₀ v₀ t' i sd k (j + 1) ∧
      j + 1 ≤ (e.getMem (s.getReg .x2 - 1248)).toNat ∧
      ((j + 1 < (vecLen s (blkAddr s i k)).toNat ∧ t'.pc = 0x800079bc) ∨
        (j + 1 = (vecLen s (blkAddr s i k)).toNat ∧ t'.pc = 0x80007a08)))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have It := S.cur.inv
  have spt : t.getReg .x2 = s.getReg .x2 - 1344 := It.sp
  set wl := e.getMem (s.getReg .x2 - 1248) with hwl
  set wp := e.getMem (s.getReg .x2 - 1264) with hwp
  set c := (vecLen s (blkAddr s i k)).toNat with hcdef
  set cp := vecPtr s (blkAddr s i k) with hcp
  -- `0x800079bc`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800079bc_spec hpc trivial
  have m₁ := b800079bc_mem_same h₁
  have k₁ := b800079bc_keeps h₁
  have x18t : t.getReg .x18 = wl + 1 - BitVec.ofNat 64 j := by rw [S.x18, hv18]
  have hwl64 := wl.isLt
  by_cases hz : t.getReg .x18 - 1 = 0
  · exact ⟨t₁, hr₁, Or.inl (dead_of_fetch (by
      rw [b800079bc_pc_taken h₁ hz]
      exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have hjw' : j < wl.toNat := by
    rcases Nat.lt_or_ge j wl.toNat with h' | h'
    · exact h'
    · exfalso; apply hz; rw [x18t]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      have : (0 : Word).toNat = 0 := rfl
      have : (1 : Word).toNat = 1 := rfl
      omega
  have pc₁ := b800079bc_pc_not_taken h₁ hz
  have C₁ : Cur s z h t₁ := S.cur.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₁ It.heap (k₁ .x2 (by decide))) fun _ h ↦ h.elim
  -- the coordinates' headers, read only
  have hroF := hro.forms 0 (by omega)
  have hroT := hro.terms 0 (by omega)
  have htg := hro.tags 0 (by omega)
  simp only [Nat.mul_zero, add_ofNat_zero] at hroF hroT htg
  rw [← hcp, ← hcdef] at hroF
  rw [← hcp, ← hcdef] at hroT htg
  have hFb := hroF.bound
  have hFs := hroF.stack
  rw [stackLo_eq, stack_eq] at hFs
  have hvF : ValidMemRange cp (3 * c) :=
    Bus.RO.range (n := 3 * c) (by rw [show 8 * (3 * c) = 24 * c by omega]; exact hroF)
  have hF8 : cp.toNat % 8 = 0 := by
    rcases hroF.region with h0 | h0
    · omega
    · exact h0.2
  obtain ⟨hvW, hwE'⟩ := weightBuf En (le_trans hzh Ih.heap.hi)
  have hwE := hwE' (Nat.lt_of_le_of_lt (Nat.zero_le j) hjw')
  rw [← hwl, ← hwp] at hvW hwE
  have x10t : t₁.getReg .x10 = cp + BitVec.ofNat 64 (24 * j + 16) := by
    rw [k₁ .x10 (by decide), S.x10, hv10]; apply BitVec.eq_of_toNat_eq; addr_omega [hFb, hjc]
  have x13t : t₁.getReg .x13 = wp + BitVec.ofNat 64 (24 * j) := by
    rw [k₁ .x13 (by decide), S.x13, hv13]
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1344 := C₁.inv.sp
  -- `0x800079c4`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800079c4_spec pc₁ (by
    rv_eval [sp₁, x10t, x13t]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hvF [hFb, hjc]
      | valid_access hvW [hwE, hjw']
      | addr_omega [hb1, hFb, hFs, hjc, hwE, hjw'])
  have k₂ := b800079c4_keeps h₂
  have fr₂ : DFrame t₁ t₂ (Within · (s.getReg .x2 - 248) 24) := by
    have := DFrame.of_memFrame (b800079c4_frame h₂ (by rw [sp₁]; addr_omega [hb1]))
    rw [sp₁] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have hn₂ : heapNext t₂ = heapNext t₁ := by
    simp only [heapNext]; rw [fr₂ nextAddr fun q hq hw ↦ by addr_omega [hw, hq, hb1, hnx]]
  have st₂ : StepS s t₁ t₂ (Within · (s.getReg .x2 - 248) 24) :=
    StepS.ofDFrame C₁.inv.heap fr₂ (fun _ h ↦ h) (fun q hq hw ↦ by addr_omega [hw, hq, hb1, hnx])
      (k₂ .x2 (by decide))
  have C₂ : Cur s z h t₂ := C₁.next hpre hsz st₂ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  have rdF (q : Nat) (hq : q + 8 ≤ 24) :
      t₁.getMem (cp + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 q) =
        s.getMem (cp + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 q) := by
    rw [m₁]; exact It.word hroF (by addr_omega [hFb, hjc, hq]) (by addr_omega [hFb, hjc, hq])
  have x11₂ : t₂.getReg .x11 = vecPtr s (cp + BitVec.ofNat 64 (24 * j)) := by
    rw [b800079c4_x11 h₂, x10t]
    rw [show cp + BitVec.ofNat 64 (24 * j + 16) - 8 = cp + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 8
      by apply BitVec.eq_of_toNat_eq; addr_omega [hFb, hjc]]
    exact rdF 8 (by omega)
  have x12₂ : t₂.getReg .x12 = vecLen s (cp + BitVec.ofNat 64 (24 * j)) := by
    rw [b800079c4_x12 h₂, x10t]
    rw [show cp + BitVec.ofNat 64 (24 * j + 16) = cp + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 16
      by apply BitVec.eq_of_toNat_eq; addr_omega [hFb, hjc]]
    exact rdF 16 (by omega)
  have hroT' := hroT j hjc
  have htg' := htg j hjc
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1344 := C₂.inv.sp
  have hn₁ : heapNext t₁ = heapNext t := by simp only [heapNext, m₁]
  have hvt := S.mono
  have ht₂ : heapNext t₀ ≤ heapNext t₂ := by rw [hn₂, hn₁]; omega
  -- the block's form, kept from `t` to `t₂`
  have hdr (q : Nat) (hq : q < 3) : t₂.getMem (s.getReg .x2 - 296 + BitVec.ofNat 64 (8 * q)) =
      t.getMem (s.getReg .x2 - 296 + BitVec.ofNat 64 (8 * q)) := by
    rw [fr₂ _ fun x hx hw ↦ by addr_omega [hw, hx, hb1, hq], m₁]
  have hhE := It.heap.hi
  have fo₂ : Layout.formOf t₂ (s.getReg .x2 - 296) = Layout.formOf t (s.getReg .x2 - 296) ∧
      Layout.FormOk t₂ (s.getReg .x2 - 296) :=
    Layout.formOf_frame (toLayoutFrame ((DFrame.of_same m₁ (Within · (s.getReg .x2 - 248) 24)).trans
      fr₂ fun _ h ↦ h)) S.ok (fun x hx hw ↦ by addr_omega [hx, hw, hb1])
      (fun x hx hw ↦ by
        have := S.fbuf x hx
        simp only [heapNext, heapEnd] at this hhE
        addr_omega [hw, this, hb1, hhE])
      (by addr_omega [hb1]) It.heap (by rw [hn₂, hn₁])
  have fb₂ : ∀ x, Layout.formBuf t₂ (s.getReg .x2 - 296) x →
      heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext t₂ := by
    intro x hx
    have e8 := hdr 1 (by omega)
    have e0 := hdr 0 (by omega)
    simp only [Nat.mul_one, Nat.mul_zero, add_ofNat_zero] at e8 e0
    have hx' : Layout.formBuf t (s.getReg .x2 - 296) x := by
      simp only [Layout.formBuf, vecPtr, vecCap] at hx ⊢
      rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← e8, ← e0]; exact hx
    have := S.fbuf x hx'
    rw [hn₂, hn₁]; exact this
  -- `add_scaled`
  obtain ⟨v, hrv, ⟨hpcv, hp, Cv, frv, hmv, okv, fbv, hvv⟩ | hd⟩ := addScaledF hAS hpre hsz hzt ht₂ C₂
    (b800079c4_pc h₂) (by rw [b800079c4_x10 h₂, sp₁]; rv_eval [])
    (by rw [b800079c4_x13 h₂, sp₁]; rv_eval []) fo₂.2 fb₂ (by rw [x11₂, x12₂]; exact hroT')
    (by rw [x11₂, x12₂]; exact htg')
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans hrv), Or.inl hd⟩
  -- `0x800079fc`
  obtain ⟨t', hr₃, h₃⟩ := Sym.BlockSpec.reaches b800079fc_spec
    (by rw [hpcv, returnAddress_eq, b800079c4_x1 h₂]; decide) trivial
  have m₃ := b800079fc_mem_same h₃
  have k₃ := b800079fc_keeps h₃
  have hn₃ : heapNext t' = heapNext v := by simp only [heapNext, m₃]
  have x18v : v.getReg .x18 = wl + 1 - BitVec.ofNat 64 j - 1 := by
    rw [hp.reg .x18, k₂ .x18 (by decide), b800079bc_x18 h₁, x18t]
  have x9v : v.getReg .x9 = coBound wl c := by
    rw [hp.reg .x9, k₂ .x9 (by decide), k₁ .x9 (by decide), S.regs .x9 (by decide), hv9]
  have hex := exit_iff (wl := wl) hjc hjw' (by omega)
  -- the new element
  have hw₂ : eAt t₂ (s.getReg .x2 - 248) = sd.2.2.2.1.getD j 0 := by
    rw [← weightAt hpre En Ih S.cur hzh hjw']
    have e0 := b800079c4_m_x2_1096 h₂
    have e8 := b800079c4_m_x2_1104 h₂
    have e16 := b800079c4_m_x2_1112 h₂
    rw [sp₁, x13t, m₁] at e0 e8 e16
    rv_eval [] at e0 e8 e16
    refine eAt_congr e0 ((congrArg t₂.getMem ?_).trans e8) ((congrArg t₂.getMem ?_).trans e16) <;>
      (apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hcs : (blockAt s (blkAddr s i k)).coordinates.length = c := by
    simp [blockAt, formVecAt, hcdef]
  have hjc' : j < (blockAt s (blkAddr s i k)).coordinates.length := by rw [hcs]; exact hjc
  have hcj : (blockAt s (blkAddr s i k)).coordinates[j] =
      (Layout.formOf s (cp + BitVec.ofNat 64 (24 * j))).toSpec := by
    simp [blockAt, formVecAt, hcp]
  refine ⟨t', hr₁.trans (hr₂.trans (hrv.trans hr₃)), Or.inr ⟨⟨Cv.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₃ Cv.inv.heap (k₃ .x2 (by decide))) fun _ h ↦ h.elim, ?_, ?_, fun r hr ↦ ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, hjw', ?_⟩⟩
  · have htt' : heapNext t ≤ heapNext t' := by rw [hn₃]; rw [hn₂, hn₁] at hmv; exact hmv
    refine ((((S.fr.mono fun a ha ↦ CoW.mono htt' ha).trans (DFrame.of_same m₁ _) fun _ h ↦ h).trans
      (fr₂.mono fun a ha ↦ ?_) fun _ h ↦ h).trans (frv.mono fun a ha ↦ ?_) fun _ h ↦ h).trans
      (DFrame.of_same m₃ _) fun _ h ↦ h
    · exact Or.inr (Or.inl ha)
    · rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by rw [hn₃]; exact a2⟩)))
  · rw [hn₃]; rw [hn₂, hn₁] at hmv; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₃ _ (by decide), hp.reg _ (by decide), k₂ _ (by decide), k₁ _ (by decide),
        S.regs _ (by decide)]
  · rw [k₃ .x18 (by decide), x18v, hv18]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (1 : Word).toNat = 1 := rfl
    omega
  · rw [b800079fc_x10 h₃, hp.reg .x23, b800079c4_x23 h₂, x10t, hv10, BitVec.add_assoc,
      BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (24 : Word).toNat = 24 from rfl,
      show (16 : Word).toNat = 16 from rfl]
    omega
  · rw [b800079fc_x13 h₃, hp.reg .x19, b800079c4_x19 h₂, x13t, hv13]
    apply BitVec.eq_of_toNat_eq; addr_omega [hwE, hjw']
  · exact (Layout.formOf_frame (toLayoutFrame (DFrame.of_same m₃ (fun _ ↦ False))) okv
      (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) Cv.inv.heap (by rw [hn₃])).2
  · intro x hx
    have hx' : Layout.formBuf v (s.getReg .x2 - 296) x := by
      simp only [Layout.formBuf, vecPtr, vecCap, m₃] at hx ⊢; exact hx
    rw [hn₃]; exact fbv x hx'
  · have e : Layout.formOf t' (s.getReg .x2 - 296) = Layout.formOf v (s.getReg .x2 - 296) :=
      (Layout.formOf_frame (toLayoutFrame (DFrame.of_same m₃ (fun _ ↦ False))) okv
        (fun _ _ h ↦ h) (fun _ _ h ↦ h) (by addr_omega [hb1]) Cv.inv.heap (by rw [hn₃])).1
    rw [e, hvv, fo₂.1, LayoutMirror.FormRust.toSpec_addScaled, S.form, hw₂, x11₂, x12₂,
      coFold_succ hjc', hcj, addScaledRust_eq]
    rfl
  · have e : vecLen t' (s.getReg .x2 - 296) = vecLen v (s.getReg .x2 - 296) := by
      simp only [vecLen, m₃]
    have hl := addScaled_length (Layout.formOf t₂ (s.getReg .x2 - 296))
      ⟨Layout.termsOf s (t₂.getReg .x11) (t₂.getReg .x12).toNat⟩ (eAt t₂ (s.getReg .x2 - 248))
    rw [← hvv, fo₂.1] at hl
    simp only [Layout.formOf, Layout.termsOf_length] at hl
    have := S.len
    rw [e]; omega
  · rcases Nat.lt_or_ge (j + 1) c with hlt | hge
    · refine Or.inl ⟨hlt, b800079fc_pc_taken h₃ ?_⟩
      rw [x18v, x9v]; intro he; exact absurd (hex.mp he) (by omega)
    · refine Or.inr ⟨by omega, b800079fc_pc_not_taken h₃ ?_⟩
      rw [x18v, x9v]; exact hex.mpr (by omega)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
