import Rv64Verifier.Proofs.Bus.VbbTail39

/-!
# `verify_bus_balance`'s side loop: an iteration's selectors

From the side loop's head `h` to `0x800076c4` (`sideFront`): the tuple's read, the framework
selectors (`selFw`) and the tables' (`selTb`, from the state past the first as its head), with the
tuple's words in the registers and the frame (`Front`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts

/-- What an iteration writes from the head `h` to `u` before the block loop: the frame's slots but
the block loop's scratch and the totals, the stack below the frame, `NEXT` and the heap from `h`'s
`NEXT` on. -/
def FrW (s h u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1304) 24 ∨ Within a (s.getReg .x2 - 1272) 16 ∨
    Within a (s.getReg .x2 - 1248) 8 ∨ Within a (s.getReg .x2 - 1216) 72 ∨
    Within a (s.getReg .x2 - 320) 216 ∨ Within a (s.getReg .x2 - 4544) 3200 ∨
    Within a nextAddr 8 ∨ (heapNext h ≤ a.toNat ∧ a.toNat < heapNext u)

/-- At `0x800076c4` for side `i` (`sd`): its framework selectors from `s8`, its tables' from `s4`,
their counts at `S - 1288` and `S - 1296`, the tuple's words in the registers and the frame. -/
structure Front (s z h u : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) : Prop where
  cur : Cur s z h u
  x8 : u.getReg .x8 = sideWord s h i 32
  x18 : u.getReg .x18 = sideWord s h i 16
  x22 : u.getReg .x22 = sideWord s h i 8
  x26 : u.getReg .x26 = sideWord s h i 64
  x21 : u.getReg .x21 = h.getMem (s.getReg .x2 - 1144)
  x25 : u.getReg .x25 = h.getReg .x25
  x27 : u.getReg .x27 = h.getReg .x27
  m1168 : u.getMem (s.getReg .x2 - 1168) = sideWord s h i 80
  m1160 : u.getMem (s.getReg .x2 - 1160) = sideWord s h i 72
  m1248 : u.getMem (s.getReg .x2 - 1248) = sideWord s h i 56
  m1264 : u.getMem (s.getReg .x2 - 1264) = sideWord s h i 48
  m1192 : u.getMem (s.getReg .x2 - 1192) = sideWord s h i 24
  m1152 : u.getMem (s.getReg .x2 - 1152) = BitVec.ofNat 64 i
  m1288 : u.getMem (s.getReg .x2 - 1288) = BitVec.ofNat 64 sd.2.1.framework.length
  m1296 : u.getMem (s.getReg .x2 - 1296) = BitVec.ofNat 64 sd.2.1.tables.length
  fwBuf : NewBuf h u (u.getReg .x24) (24 * sd.2.1.framework.length) 8
  fw : eListAt u (u.getReg .x24) sd.2.1.framework.length = sd.2.1.framework.map (·.eqAbove point)
  tbBuf : NewBuf h u (u.getReg .x20) (24 * sd.2.1.tables.length) 8
  tb : eListAt u (u.getReg .x20) sd.2.1.tables.length = sd.2.1.tables.map (·.eqAbove point)
  fr : DFrame h u (FrW s h u)

theorem SelW.frW {s h h' u u' : MachineState} (hpre : BusBalancePre s)
    (hh : heapNext h ≤ heapNext h') (hu : heapNext u ≤ heapNext u') {a : Word}
    (ha : SelW s h' u a ∨ Within a (s.getReg .x2 - 1288) 8 ∨ Within a (s.getReg .x2 - 1296) 8) :
    FrW s h u' a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases ha with (hw | hw | hw | hw | ⟨a1, a2⟩) | hw | hw
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb1])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb1])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hw))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))
  · exact Or.inl (by addr_omega [hw, hb1])
  · exact Or.inl (by addr_omega [hw, hb1])

/-- A frame slot `S - j` outside `S - 248` and `S - 128` misses `SelW`. -/
theorem SelW.slot {s h u : MachineState} (hpre : BusBalancePre s) (hu : HeapOk u) {j : Nat}
    (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 224 ∨ 256 ≤ j) (h2 : j ≤ 104 ∨ 136 ≤ j) :
    ∀ i < 8, ¬ SelW s h u (s.getReg .x2 - BitVec.ofNat 64 j + BitVec.ofNat 64 i) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hh := hu.hi
  simp only [heapNext, heapEnd] at hh
  intro i hi hw
  rcases hw with hw | hw | hw | hw | ⟨-, hw⟩
  · addr_omega [hw, hi, hb1, hj, hj2, h1]
  · addr_omega [hw, hi, hb1, hj, hj2, h2]
  · addr_omega [hw, hi, hb1, hj, hj2]
  · addr_omega [hw, hi, hb1, hj, hj2, hnx]
  · simp only [heapNext] at hw; addr_omega [hw, hi, hb1, hj, hj2, hh]

/-- A heap address misses `SelW` below `h`'s `NEXT`. -/
theorem SelW.heap {s h u : MachineState} (hpre : BusBalancePre s) {a : Word}
    (h1 : heapStart ≤ a.toNat) (h2 : a.toNat < heapNext h) (hh : heapNext h ≤ heapEnd) :
    ¬ SelW s h u a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  rw [stackLo_eq] at hnx hab
  simp only [heapNext, heapEnd, heapStart] at h1 h2 hh hab
  rintro (hw | hw | hw | hw | ⟨hw, -⟩)
  · addr_omega [hw, h1, h2, hh, hb1]
  · addr_omega [hw, h1, h2, hh, hb1]
  · addr_omega [hw, h1, h2, hh, hb1]
  · simp only [nextAddr] at hw; addr_omega [hw, h1, h2, hh, hb1]
  · simp only [heapNext] at hw; omega

/-- The tables' `Vec<Placement>` of a layout of `z` at `S - c`, kept at the head. -/
theorem tbBufLow {s z v h₀ h : MachineState} (hpre : BusBalancePre s) (En : SideEnv s z v h₀ h)
    {i : Nat} (hi : i < 3) {l : BusLayoutRust} (L : LayoutAt s z (layAt s i) l) :
    LowBuf (h.getMem (layAt s i + 24 + 8)) (16 * (h.getMem (layAt s i + 24 + 16)).toNat)
      (heapNext z) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have e24 : layAt s i + 24 = s.getReg .x2 - BitVec.ofNat 64 (1056 - 56 * i) := by
    simp only [layAt]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi]
  have hv : VecOk z (layAt s i + 24) 16 8 := L.tables
  have hn : NewBuf s z (vecPtr z (layAt s i + 24)) (16 * (vecCap z (layAt s i + 24)).toNat) 8 :=
    L.tablesNew
  rw [e24] at hv hn ⊢
  exact layoutBuf hpre En (by omega) (by omega) hv hn

set_option maxRecDepth 8192 in
/-- From the head to `0x800076c4`. -/
theorem sideFront (hT : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    (hEA : EqAboveSpec) {s z v h₀ h : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (En : SideEnv s z v h₀ h) (SO : SideOk s z h i sd)
    (PA : PointAt z h (h.getReg .x27) (h.getMem (s.getReg .x2 - 1144)) point) (hi : i < 3)
    (hx22 : h.getReg .x22 = BitVec.ofNat 64 i) (hpc : h.pc = 0x800074e0) :
    ∃ u, Reaches Image.code h u ∧ (Dead Image.code u ∨ (u.pc = 0x800076c4 ∧ Front s z h u i sd point)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  -- `0x800074e0`
  obtain ⟨u₁, hr₁, hpc₁, A⟩ := block74e0 hpre Ih hi hx22 SO.lay hpc
  have st₁ : StepS s h u₁ fun a ↦ Within a (s.getReg .x2 - 1264) 8 ∨
      Within a (s.getReg .x2 - 1248) 8 ∨ Within a (s.getReg .x2 - 1192) 48 :=
    StepS.ofDFrame Ih.heap A.frame (fun _ h ↦ h) (fun j hj hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hb1, hnx]) (A.keeps .x2 (by decide))
  have C₁ : Cur s z h u₁ := (Cur.start Ih).next hpre hsz st₁ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    rcases ha with ha | ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))
  have L := SO.layoutZ
  have hF : LowBuf (h.getMem (layAt s i + 8)) (16 * (h.getMem (layAt s i + 16)).toNat)
      (heapNext z) :=
    layoutBuf hpre En (c := 1080 - 56 * i) (by omega) (by omega) L.framework L.frameworkNew
  -- the framework's selectors
  obtain ⟨u₂, hr₂, hd | ⟨Pf, S1, hpc₂⟩⟩ := selFw hT hR hEA hpre hsz Ih hzh PA rfl hF A C₁ hpc₁
  · exact ⟨u₂, hr₁.trans hr₂, Or.inl hd⟩
  have C₂ := S1.cur
  have I₂ := C₂.inv
  have hzu₂ : heapNext z ≤ heapNext u₂ := le_trans hzh C₂.step.mono
  have slot₂ (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344)
      (hx : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 → ¬ SlotW s y) :
      u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    C₂.slot hpre hj hj2 hx
  have m1144 : u₂.getMem (s.getReg .x2 - 1144) = h.getMem (s.getReg .x2 - 1144) :=
    slot₂ 1144 (by omega) (by omega) fun y hy hy' ↦ by
      simp only [SlotW] at hy'
      rcases hy' with hy' | hy' | hy' | hy' | hy' | hy' | hy' <;> addr_omega [hy, hy', hb1]
  have lay (k : Nat) (hk : k < 56) (hk8 : k % 8 = 0) :
      u₂.getMem (layAt s i + BitVec.ofNat 64 k) = h.getMem (layAt s i + BitVec.ofNat 64 k) := by
    have e : layAt s i + BitVec.ofNat 64 k = s.getReg .x2 - BitVec.ofNat 64 (1080 - 56 * i - k) := by
      simp only [layAt]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hi, hk]
    rw [e]
    exact slot₂ _ (by omega) (by omega) fun y hy hy' ↦ by
      simp only [SlotW] at hy'
      rcases hy' with hy' | hy' | hy' | hy' | hy' | hy' | hy' <;> addr_omega [hy, hy', hb1, hi, hk]
  have l32 : u₂.getMem (layAt s i + 24 + 8) = h.getMem (layAt s i + 24 + 8) := by
    rw [BitVec.add_assoc]; exact lay 32 (by omega) rfl
  have l40 : u₂.getMem (layAt s i + 24 + 16) = h.getMem (layAt s i + 24 + 16) := by
    rw [BitVec.add_assoc]; exact lay 40 (by omega) rfl
  have PA₂ : PointAt z u₂ (h.getReg .x27) (u₂.getMem (s.getReg .x2 - 1144)) point := by
    rw [m1144]; exact ⟨PA.p8, PA.lo, PA.hi, PA.at hpre C₂ Ih hzh⟩
  have hF₂ : LowBuf (u₂.getMem (layAt s i + 24 + 8)) (16 * (u₂.getMem (layAt s i + 24 + 16)).toNat)
      (heapNext z) := by
    rw [l32, l40]; exact tbBufLow hpre En hi L
  have x20₂ : u₂.getReg .x20 = layAt s i := (S1.regs .x20 (by decide)).trans A.x20
  have x21₂ : u₂.getReg .x21 = u₂.getMem (s.getReg .x2 - 1144) := S1.x21.trans m1144.symm
  have hl32 : u₂.getMem (layAt s i + 32) = u₂.getMem (layAt s i + 24 + 8) := by
    rw [BitVec.add_assoc]; rfl
  have hl40 : u₂.getMem (layAt s i + 40) = u₂.getMem (layAt s i + 24 + 16) := by
    rw [BitVec.add_assoc]; rfl
  -- the tables' selectors
  obtain ⟨u₃, hr₃, hd | ⟨Pt, S2, hpc₃⟩⟩ := selTb hT hR hEA hpre hsz I₂ hzu₂ PA₂ hF₂ (Cur.start I₂)
    x20₂ x21₂ S1.x27 hl32 hl40 hi hpc₂
  · exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inl hd⟩
  refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨hpc₃, ?_⟩⟩
  have C₃ : Cur s z h u₃ := C₂.next hpre hsz S2.cur.step fun _ ha ↦ ha
  have hn₂₃ := S2.cur.step.mono
  have hn₁₂ := C₂.step.mono
  have hu₃ := C₃.inv.heap
  -- frame slots from `u₁` to `u₃`
  have keep (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 224 ∨ 256 ≤ j)
      (h2 : j ≤ 104 ∨ 136 ≤ j) (h3 : j ≠ 1288) (h4 : j ≠ 1296) (h8 : j % 8 = 0) :
      u₃.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = u₁.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    (S2.fr _ fun k hk hw ↦ by
      rcases hw with hw | hw
      · exact SelW.slot hpre hu₃ hj hj2 h1 h2 k hk hw
      · addr_omega [hw, hk, hb1, hj, hj2, h3, h4, h8]).trans
    (S1.fr _ fun k hk hw ↦ by
      rcases hw with hw | hw
      · exact SelW.slot hpre C₂.inv.heap hj hj2 h1 h2 k hk hw
      · addr_omega [hw, hk, hb1, hj, hj2, h3, h4, h8])
  have hlenF : sd.2.1.framework.length = (h.getMem (layAt s i + 16)).toNat := by
    rw [← SO.layout]; simp [busLayoutOf, placementsAt, vecLen, layAt]
  have hlenT : sd.2.1.tables.length = (u₂.getMem (layAt s i + 24 + 16)).toNat := by
    rw [l40, ← SO.layout]; simp [busLayoutOf, placementsAt, vecLen, layAt]
  have hfw : sd.2.1.framework = placementsAt h (layAt s i) := by rw [← SO.layout]; rfl
  have htb : sd.2.1.tables = placementsAt u₂ (layAt s i + 24) := by
    rw [← SO.layout]
    show placementsAt h (layAt s i + 24) = _
    obtain ⟨F8, hFb⟩ := tbBufLow hpre En hi L
    have hlo := I₂.heap.lo
    refine (placementsAt_congr l32 l40 fun j hj k hk ↦ ?_).symm
    rcases hFb with h0 | ⟨b1, b2⟩
    · simp only [vecLen] at hj; omega
    have hz := Ih.heap.hi
    simp only [vecPtr, vecLen] at hj ⊢
    simp only [heapStart, heapNext, heapEnd] at b1 b2 hz hzh
    exact C₂.low hpre Ih hzh (by simp only [heapStart]; addr_omega [b1, b2, hj, hk, hz])
      (by simp only [heapNext]; addr_omega [b1, b2, hj, hk, hz])
  have x24₃ : u₃.getReg .x24 = Pf := (S2.regs .x24 (by decide)).trans S1.x24
  refine ⟨C₃, ?_, ?_, ?_, ?_, ?_, ?_, S2.x27, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S2.regs .x8 (by decide), S1.regs .x8 (by decide), A.x8]
  · rw [S2.regs .x18 (by decide), S1.regs .x18 (by decide), A.x18]
  · rw [S2.regs .x22 (by decide), S1.regs .x22 (by decide), A.x22]
  · rw [S2.regs .x26 (by decide), S1.regs .x26 (by decide), A.x26]
  · rw [S2.x21, m1144]
  · rw [S2.regs .x25 (by decide), S1.regs .x25 (by decide), A.keeps .x25 (by decide)]
  · exact (keep 1168 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans A.m176
  · exact (keep 1160 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans A.m184
  · exact (keep 1248 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans A.m96
  · exact (keep 1264 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans A.m80
  · exact (keep 1192 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans A.m152
  · exact (keep 1152 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl).trans A.m192
  · rw [hlenF, ← S1.m56]
    exact S2.fr _ fun k hk hw ↦ by
      rcases hw with hw | hw
      · exact SelW.slot hpre hu₃ (j := 1288) (by omega) (by omega) (by omega) (by omega) k hk hw
      · addr_omega [hw, hk, hb1]
  · rw [hlenT]; exact S2.m48
  · rw [x24₃]
    obtain ⟨b8, bb⟩ := S1.buf
    refine ⟨b8, ?_⟩
    rcases bb with h0 | ⟨b1, b2⟩
    · exact Or.inl (by rw [hlenF, h0])
    · exact Or.inr ⟨b1, by rw [hlenF]; omega⟩
  · rw [x24₃, hlenF, hfw, ← S1.vals]
    refine S2.fr.eListAt fun k hk hw ↦ ?_
    obtain ⟨-, bb⟩ := S1.buf
    rcases bb with h0 | ⟨b1, b2⟩
    · omega
    have hh := I₂.heap.hi
    have hlo := Ih.heap.lo
    simp only [heapNext, heapEnd, heapStart] at b1 b2 hh hlo
    rcases hw with hw | hw
    · exact SelW.heap hpre (h := u₂) (u := u₃) (by simp only [heapStart]; addr_omega [b1, b2, hk, hlo, hh])
        (by simp only [heapNext]; addr_omega [b1, b2, hk, hlo, hh]) I₂.heap.hi hw
    · addr_omega [hw, hk, hb1, b1, b2, hh]
  · rw [S2.x20]
    obtain ⟨b8, bb⟩ := S2.buf
    refine ⟨b8, ?_⟩
    rcases bb with h0 | ⟨b1, b2⟩
    · exact Or.inl (by rw [← hlenT] at h0; rw [h0])
    · exact Or.inr ⟨by omega, by rw [hlenT]; exact b2⟩
  · rw [S2.x20, hlenT, S2.vals, htb]
  · refine ((A.frame.mono fun a ha ↦ ?_).trans S1.fr fun a ha ↦ ?_).trans S2.fr fun a ha ↦ ?_
    · rcases ha with ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))
    · rcases ha with ha | ha
      · exact SelW.frW hpre (le_refl _) hn₂₃ (Or.inl ha)
      · exact SelW.frW hpre (le_refl _) hn₂₃ (Or.inr (Or.inl ha))
    · rcases ha with ha | ha
      · exact SelW.frW hpre hn₁₂ (le_refl _) (Or.inl ha)
      · exact SelW.frW hpre hn₁₂ (le_refl _) (Or.inr (Or.inr ha))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
