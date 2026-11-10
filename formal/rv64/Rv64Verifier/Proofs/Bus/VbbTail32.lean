import Rv64Verifier.Proofs.Bus.VbbTail31

/-!
# `verify_bus_balance`'s side loop: a side's tuple

At the loop's head `h` for side `i`, the tuple at `S - 592 + 88 i` (`sideWord`) holds `sidesOf`'s
side `i` (`SideOk`): the framework fingerprints and the weights, each in the heap below `z`'s `NEXT`
(the count side's weights the `ONE` in `.rodata`), the blocks' `Vec` of the layout, the
`BusLayout`'s address in the frame, `beta`'s limbs (`sideOk`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- Word `k` of side `i`'s tuple. -/
def sideWord (s t : MachineState) (i k : Nat) : Word :=
  t.getMem (s.getReg .x2 - BitVec.ofNat 64 (592 - 88 * i - k))

/-- The default side, `accAt_succ`'s. -/
def noSide : List BusBlock × BusLayoutRust × List E × List E × E := ([], ⟨0, [], []⟩, [], [], 0)

/-- `n` bytes from `p` in the heap below `B`, or none. -/
def LowBuf (p : Word) (n B : Nat) : Prop :=
  p.toNat % 8 = 0 ∧ (n = 0 ∨ heapStart ≤ p.toNat ∧ p.toNat + n ≤ B)

/-- Side `i`'s tuple at `h` holds `sd`. -/
structure SideOk (s z h : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) : Prop where
  fps : eListAt h (sideWord s h i 8) (sideWord s h i 16).toNat = sd.2.2.1
  fpsBuf : LowBuf (sideWord s h i 8) (24 * (sideWord s h i 16).toNat) (heapNext z)
  bptr : sideWord s h i 24 = vecPtr s (s.getReg .x11 + BitVec.ofNat 64 (24 * (i + 1)))
  blen : sideWord s h i 32 = vecLen s (s.getReg .x11 + BitVec.ofNat 64 (24 * (i + 1)))
  blocks : blocksAt s (s.getReg .x11 + BitVec.ofNat 64 (24 * (i + 1))) = sd.1
  lay : sideWord s h i 40 = s.getReg .x2 - BitVec.ofNat 64 (1080 - 56 * i)
  layout : busLayoutOf h (s.getReg .x2 - BitVec.ofNat 64 (1080 - 56 * i)) = sd.2.1
  layoutZ : LayoutAt s z (s.getReg .x2 - BitVec.ofNat 64 (1080 - 56 * i)) sd.2.1
  weights : eListAt h (sideWord s h i 48) (sideWord s h i 56).toNat = sd.2.2.2.1
  wBuf : LowBuf (sideWord s h i 48) (24 * (sideWord s h i 56).toNat) (heapNext z) ∨
    (sideWord s h i 48 = 0xa00000b0 ∧ sideWord s h i 56 = 1)
  beta : eOf3 (sideWord s h i 64) (sideWord s h i 72) (sideWord s h i 80) = sd.2.2.2.2

theorem oneAt {u : MachineState} (h : RodataOk u) : eAt u 0xa00000b0 = 1 :=
  eAt_eq_of_limbs (by
    rw [limbs_one, h.word (a := 0xa00000b0) (v := 1), h.word (a := 0xa00000b0 + 8) (v := 0),
      h.word (a := 0xa00000b0 + 16) (v := 0)])

theorem eOf3_zero : eOf3 0 0 0 = 0 := by
  apply eq_of_limbs
  decide +kernel

theorem _root_.Rv64Verifier.Transcript.NewVecE.low {s z : MachineState} {a : Word} {xs : List E}
    (h : NewVecE s z a xs) (hs : HeapOk s) :
    LowBuf (vecPtr z a) (24 * (vecLen z a).toNat) (heapNext z) := by
  have hb := h.buf
  have hl := h.vec.len
  have := hs.lo
  simp only [NewBuf] at hb
  refine ⟨hb.1, ?_⟩
  rcases hb.2 with h0 | h0
  · exact Or.inl (by rw [Nat.mul_eq_zero] at h0; omega)
  · exact Or.inr ⟨by omega, by omega⟩

theorem slot_add {S : Word} {j k : Nat} (hS : j ≤ S.toNat) (hk : k ≤ j) :
    S - BitVec.ofNat 64 j + BitVec.ofNat 64 k = S - BitVec.ofNat 64 (j - k) := by
  apply BitVec.eq_of_toNat_eq
  addr_omega [hS, hk]

theorem placementsAt_congr {t t' : MachineState} {a : Word}
    (h8 : t'.getMem (a + 8) = t.getMem (a + 8)) (h16 : t'.getMem (a + 16) = t.getMem (a + 16))
    (hb : ∀ i < (vecLen t a).toNat, ∀ k < 2,
      t'.getMem (vecPtr t a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * k)) =
        t.getMem (vecPtr t a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * k))) :
    placementsAt t' a = placementsAt t a := by
  have ep : vecPtr t' a = vecPtr t a := h8
  have el : vecLen t' a = vecLen t a := h16
  simp only [placementsAt, ep, el]
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  have e0 := hb i hi' 0 (by omega)
  have e1 := hb i hi' 1 (by omega)
  simp only [Nat.mul_zero, add_ofNat_zero, Nat.mul_one] at e0 e1
  rw [e0, show (8 : Word) = BitVec.ofNat 64 8 from rfl, e1]

/-- A `BusLayout` whose header and placements' buffers are kept. -/
theorem busLayoutOf_congr {t t' : MachineState} {a : Word}
    (hh : ∀ k < 7, k ≠ 0 → k ≠ 3 →
      t'.getMem (a + BitVec.ofNat 64 (8 * k)) = t.getMem (a + BitVec.ofNat 64 (8 * k)))
    (hb : ∀ i < (vecLen t a).toNat, ∀ k < 2,
      t'.getMem (vecPtr t a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * k)) =
        t.getMem (vecPtr t a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * k)))
    (hb' : ∀ i < (vecLen t (a + 24)).toNat, ∀ k < 2,
      t'.getMem (vecPtr t (a + 24) + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * k)) =
        t.getMem (vecPtr t (a + 24) + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * k))) :
    busLayoutOf t' a = busLayoutOf t a := by
  have e (k : Nat) (hk : k < 7) (h0 : k ≠ 0) (h3 : k ≠ 3) (b : Word)
      (hbk : b = BitVec.ofNat 64 (8 * k)) : t'.getMem (a + b) = t.getMem (a + b) := by
    rw [hbk]; exact hh k hk h0 h3
  have e24 (c : Word) (hc : c.toNat = 8 ∨ c.toNat = 16) :
      t'.getMem (a + 24 + c) = t.getMem (a + 24 + c) := by
    rw [BitVec.add_assoc]
    rcases hc with hc | hc
    · exact e 4 (by omega) (by omega) (by omega) _ (by apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hc]; rfl)
    · exact e 5 (by omega) (by omega) (by omega) _ (by apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, hc]; rfl)
  simp only [busLayoutOf]
  rw [e 6 (by omega) (by omega) (by omega) 48 rfl,
    placementsAt_congr (e 1 (by omega) (by omega) (by omega) 8 rfl)
      (e 2 (by omega) (by omega) (by omega) 16 rfl) hb,
    placementsAt_congr (e24 8 (Or.inl rfl)) (e24 16 (Or.inr rfl)) hb']

/-- The heap below `z`'s `NEXT`, from `z` to the loop's head. -/
theorem heapKeptZ {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} {P : Word} {n : Nat}
    {acc : List (List Form) × List E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (Sd : Sides s z h₀ h P n acc) :
    HeapKept s z h (heapNext z) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have stZH := (C.rows1.step.trans C.setup.step).trans Sd.step
  have hzh := stZH.mono
  have hht := Sd.inv.heap.hi
  intro x h1 h2
  refine stZH.frame x fun i hi hw ↦ ?_
  simp only [heapNext, heapEnd] at h1 h2 hht hzh
  rcases hw with hw | hw | hw | hw
  · simp only [RowsW, SetupW, LoopW] at hw
    rcases hw with ((hw | hw | hw) | (hw | hw)) | (hw | hw | hw | hw | hw | hw | hw | hw) <;>
      addr_omega [hw, hi, h1, h2, hht, hzh, hb1]
  · addr_omega [hw, hi, h1, h2, hht, hzh, hb1]
  · addr_omega [hw, hi, h1, h2, hht, hzh, hb1]
  · simp only [Fresh, heapNext] at hw
    addr_omega [hw, hi, h1, h2, hht, hzh, hb1]

/-- What the loop's head `h` keeps: the sides' array of the entry `h₀`, `v`'s frame of `z`'s but
`RowsW`, the layouts' headers and the heap below `NEXT` of `z`. -/
structure SideEnv (s z v h₀ h : MachineState) : Prop where
  hh : ∀ j, 328 ≤ j → j ≤ 608 →
    h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = h₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j)
  vz : ∀ j, 8 ≤ j → j ≤ 1344 → (j ≤ 584 ∨ 616 ≤ j) → (j ≤ 1320 ∨ 1336 ≤ j) →
    (j ≤ 1216 ∨ 1232 ≤ j) →
    v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = z.getMem (s.getReg .x2 - BitVec.ofNat 64 j)
  hz : ∀ j, 920 ≤ j → j ≤ 1080 →
    h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = z.getMem (s.getReg .x2 - BitVec.ofNat 64 j)
  hk : HeapKept s z h (heapNext z)

theorem sideEnv {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} {P : Word} {n : Nat}
    {acc : List (List Form) × List E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (Sd : Sides s z h₀ h P n acc) :
    SideEnv s z v h₀ h := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have stZH := (C.rows1.step.trans C.setup.step).trans Sd.step
  refine ⟨fun j hj hj2 ↦ Sd.step.slot' hpre (by omega) (by omega) fun y hy hy' ↦ ?_,
    fun j hj hj2 c1 c2 c3 ↦ C.rows1.step.slot' hpre hj hj2 fun y hy hy' ↦ ?_,
    fun j hj hj2 ↦ stZH.slot' hpre (by omega) (by omega) fun y hy hy' ↦ ?_, heapKeptZ hpre C Sd⟩
  · simp only [LoopW] at hy'
    rcases hy' with hy' | hy' | hy' | hy' | hy' | hy' | hy' | hy' <;>
      addr_omega [hy, hy', hb1, hj, hj2]
  · simp only [RowsW] at hy'
    rcases hy' with hy' | hy' | hy' <;> addr_omega [hy, hy', hb1, hj, hj2, c1, c2, c3]
  · simp only [RowsW, SetupW, LoopW] at hy'
    rcases hy' with ((hy' | hy' | hy') | (hy' | hy')) | (hy' | hy' | hy' | hy' | hy' | hy' | hy' |
      hy') <;> addr_omega [hy, hy', hb1, hj, hj2]

/-- A layout of `z` in the frame, kept at `h`. -/
theorem SideEnv.layout {s z v h₀ h : MachineState} (hpre : BusBalancePre s)
    (E : SideEnv s z v h₀ h) (hz : HeapOk z) {j : Nat} (hj : 968 ≤ j) (hj2 : j ≤ 1080)
    {l : BusLayoutRust} (L : LayoutAt s z (s.getReg .x2 - BitVec.ofNat 64 j) l) :
    busLayoutOf h (s.getReg .x2 - BitVec.ofNat 64 j) = l := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hzs := hpre.heap.lo
  have hzh := hz.hi
  rw [← L.value]
  refine busLayoutOf_congr (fun k hk _ _ ↦ ?_) (fun i hi k hk ↦ ?_) (fun i hi k hk ↦ ?_)
  · rw [slot_add (by addr_omega [hb1, hj2]) (by omega)]
    exact E.hz _ (by omega) (by omega)
  · have nb := L.frameworkNew
    have vl := L.framework.len
    simp only [NewBuf] at nb
    rcases nb.2 with h0 | ⟨b1, b2⟩
    · omega
    · simp only [heapNext, heapEnd, heapStart] at b1 b2 hzs hzh
      exact E.hk _ (by simp only [heapNext]; addr_omega [b1, b2, hzs, hzh, hi, hk, vl])
        (by simp only [heapNext]; addr_omega [b1, b2, hzs, hzh, hi, hk, vl])
  · have nb := L.tablesNew
    have vl := L.tables.len
    simp only [NewBuf] at nb
    rcases nb.2 with h0 | ⟨b1, b2⟩
    · omega
    · simp only [heapNext, heapEnd, heapStart] at b1 b2 hzs hzh
      exact E.hk _ (by simp only [heapNext]; addr_omega [b1, b2, hzs, hzh, hi, hk, vl])
        (by simp only [heapNext]; addr_omega [b1, b2, hzs, hzh, hi, hk, vl])

/-- A `Vec<E>` of `z`, its elements kept at `h`. -/
theorem SideEnv.elems {s z v h₀ h : MachineState} (En : SideEnv s z v h₀ h) (hz : HeapOk z)
    {a : Word} {xs : List E} (N : NewVecE s z a xs) :
    eListAt h (vecPtr z a) (vecLen z a).toNat = xs := by
  rw [eListAt_heapKept En.hk hz.hi (le_refl _) N.buf (by have := N.vec.len; omega)]
  exact N.elems

theorem sideOk0 {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (En : SideEnv s z v h₀ h) :
    SideOk s z h 0 ((sidesOf s k state mem mf bf bv).getD 0 noSide) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have F := C.fps
  have K := F.kept
  have K2 := C.kept
  have sw (j : Nat) (x : Word) (hx : (j, x) ∈ setupWords s v) (h1 : 328 ≤ j) (h2 : j ≤ 608) :
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = x := (En.hh j h1 h2).trans (C.setup.words _ hx)
  have p8 : sideWord s h 0 8 = vecPtr z (s.getReg .x2 - BitVec.ofNat 64 656) :=
    (sw 584 (v.getMem (s.getReg .x2 - 648)) (by simp [setupWords]) (by omega) (by omega)).trans
      ((En.vz 648 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (congrArg z.getMem (slot_add (S := s.getReg .x2) (j := 656) (k := 8) (by addr_omega [hb1]) (by omega)).symm))
  have p16 : sideWord s h 0 16 = vecLen z (s.getReg .x2 - BitVec.ofNat 64 656) :=
    (sw 576 (v.getMem (s.getReg .x2 - 640)) (by simp [setupWords]) (by omega) (by omega)).trans
      ((En.vz 640 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (congrArg z.getMem (slot_add (S := s.getReg .x2) (j := 656) (k := 16) (by addr_omega [hb1]) (by omega)).symm))
  have p48 : sideWord s h 0 48 = vecPtr z (s.getReg .x2 - BitVec.ofNat 64 888) :=
    (sw 544 (v.getReg .x20) (by simp [setupWords]) (by omega) (by omega)).trans
      ((C.rows1.regs .x20 (by decide)).trans ((C.rows0.regs .x20 (by decide)).trans
        F.x20))
  have p56 : sideWord s h 0 56 = vecLen z (s.getReg .x2 - BitVec.ofNat 64 888) :=
    (sw 536 (v.getReg .x21) (by simp [setupWords]) (by omega) (by omega)).trans
      ((C.rows1.regs .x21 (by decide)).trans ((C.rows0.regs .x21 (by decide)).trans
        F.x21))
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, K.push, ?_, ?_, ?_⟩
  · rw [p8, p16]; exact En.elems F.inv.heap F.pushF
  · rw [p8, p16]; exact F.pushF.low hpre.heap
  · exact (sw 568 (v.getMem (s.getReg .x2 - 1272)) (by simp [setupWords]) (by omega) (by omega)).trans
      ((En.vz 1272 (by omega) (by omega) (by omega) (by omega) (by omega)).trans F.pushPtr)
  · exact (sw 560 (v.getMem (s.getReg .x2 - 1264)) (by simp [setupWords]) (by omega) (by omega)).trans
      K2.pushLen
  · exact sw 552 (s.getReg .x2 - 1080) (by simp [setupWords]) (by omega) (by omega)
  · exact En.layout hpre F.inv.heap (by omega) (by omega) K.push
  · rw [p48, p56]; exact En.elems F.inv.heap K.weights
  · rw [p48, p56]; exact Or.inl (K.weights.low hpre.heap)
  · have b0 : sideWord s h 0 64 = k.beta0 :=
      (sw 528 (v.getMem (s.getReg .x2 - 1192)) (by simp [setupWords]) (by omega) (by omega)).trans
        K2.beta0
    have b1 : sideWord s h 0 72 = k.beta1 :=
      (sw 520 (v.getMem (s.getReg .x2 - 1200)) (by simp [setupWords]) (by omega) (by omega)).trans
        K2.beta1
    have b2 : sideWord s h 0 80 = k.beta2 :=
      (sw 512 (v.getMem (s.getReg .x2 - 1184)) (by simp [setupWords]) (by omega) (by omega)).trans
        K2.beta2
    rw [b0, b1, b2]
    rfl

theorem sideOk1 {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (En : SideEnv s z v h₀ h) :
    SideOk s z h 1 ((sidesOf s k state mem mf bf bv).getD 1 noSide) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have F := C.fps
  have K := F.kept
  have K2 := C.kept
  have sw (j : Nat) (x : Word) (hx : (j, x) ∈ setupWords s v) (h1 : 328 ≤ j) (h2 : j ≤ 608) :
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = x := (En.hh j h1 h2).trans (C.setup.words _ hx)
  have p8 : sideWord s h 1 8 = vecPtr z (s.getReg .x2 - BitVec.ofNat 64 680) :=
    (sw 496 (v.getMem (s.getReg .x2 - 672)) (by simp [setupWords]) (by omega) (by omega)).trans
      ((En.vz 672 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (congrArg z.getMem (slot_add (S := s.getReg .x2) (j := 680) (k := 8) (by addr_omega [hb1])
          (by omega)).symm))
  have p16 : sideWord s h 1 16 = vecLen z (s.getReg .x2 - BitVec.ofNat 64 680) :=
    (sw 488 (v.getMem (s.getReg .x2 - 664)) (by simp [setupWords]) (by omega) (by omega)).trans
      ((En.vz 664 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (congrArg z.getMem (slot_add (S := s.getReg .x2) (j := 680) (k := 16) (by addr_omega [hb1])
          (by omega)).symm))
  have p48 : sideWord s h 1 48 = vecPtr z (s.getReg .x2 - BitVec.ofNat 64 888) :=
    (sw 456 (v.getReg .x8) (by simp [setupWords]) (by omega) (by omega)).trans
      ((C.rows1.regs .x8 (by decide)).trans ((C.rows0.regs .x8 (by decide)).trans F.x8))
  have p56 : sideWord s h 1 56 = vecLen z (s.getReg .x2 - BitVec.ofNat 64 888) :=
    (sw 448 (v.getReg .x22) (by simp [setupWords]) (by omega) (by omega)).trans
      ((C.rows1.regs .x22 (by decide)).trans ((C.rows0.regs .x22 (by decide)).trans F.x22))
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, K.pull, ?_, ?_, ?_⟩
  · rw [p8, p16]; exact En.elems F.inv.heap F.pullF
  · rw [p8, p16]; exact F.pullF.low hpre.heap
  · exact (sw 480 (v.getMem (s.getReg .x2 - 1168)) (by simp [setupWords]) (by omega) (by omega)).trans
      K2.pullPtr
  · exact (sw 472 (v.getMem (s.getReg .x2 - 1176)) (by simp [setupWords]) (by omega) (by omega)).trans
      K2.pullLen
  · exact sw 464 (s.getReg .x2 - 1024) (by simp [setupWords]) (by omega) (by omega)
  · exact En.layout hpre F.inv.heap (by omega) (by omega) K.pull
  · rw [p48, p56]; exact En.elems F.inv.heap K.weights
  · rw [p48, p56]; exact Or.inl (K.weights.low hpre.heap)
  · have b0 : sideWord s h 1 64 = k.beta0 :=
      (sw 440 (v.getMem (s.getReg .x2 - 1192)) (by simp [setupWords]) (by omega) (by omega)).trans
        K2.beta0
    have b1 : sideWord s h 1 72 = k.beta1 :=
      (sw 432 (v.getMem (s.getReg .x2 - 1200)) (by simp [setupWords]) (by omega) (by omega)).trans
        K2.beta1
    have b2 : sideWord s h 1 80 = k.beta2 :=
      (sw 424 (v.getMem (s.getReg .x2 - 1184)) (by simp [setupWords]) (by omega) (by omega)).trans
        K2.beta2
    rw [b0, b1, b2]
    rfl

theorem sideOk2 {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (En : SideEnv s z v h₀ h) (Ih : Inv s h) :
    SideOk s z h 2 ((sidesOf s k state mem mf bf bv).getD 2 noSide) := by
  have F := C.fps
  have K := F.kept
  have K2 := C.kept
  have sw (j : Nat) (x : Word) (hx : (j, x) ∈ setupWords s v) (h1 : 328 ≤ j) (h2 : j ≤ 608) :
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = x := (En.hh j h1 h2).trans (C.setup.words _ hx)
  have p8 : sideWord s h 2 8 = 8 := sw 408 8 (by simp [setupWords]) (by omega) (by omega)
  have p16 : sideWord s h 2 16 = 0 := sw 400 0 (by simp [setupWords]) (by omega) (by omega)
  have p48 : sideWord s h 2 48 = 0xa00000b0 :=
    sw 368 0xa00000b0 (by simp [setupWords]) (by omega) (by omega)
  have p56 : sideWord s h 2 56 = 1 := sw 360 1 (by simp [setupWords]) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, K.count, ?_, Or.inr ⟨p48, p56⟩, ?_⟩
  · rw [p8, p16]; rfl
  · rw [p8, p16]; exact ⟨rfl, Or.inl rfl⟩
  · exact (sw 392 (v.getMem (s.getReg .x2 - 1160)) (by simp [setupWords]) (by omega) (by omega)).trans
      K2.countPtr
  · exact (sw 384 (v.getMem (s.getReg .x2 - 1248)) (by simp [setupWords]) (by omega) (by omega)).trans
      K2.countLen
  · exact sw 376 (s.getReg .x2 - 968) (by simp [setupWords]) (by omega) (by omega)
  · exact En.layout hpre F.inv.heap (by omega) (by omega) K.count
  · rw [p48, p56]
    show eListAt h 0xa00000b0 1 = [1]
    simp only [eListAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, add_ofNat_zero,
      oneAt (Ih.rodata hpre)]
  · have b0 : sideWord s h 2 64 = 0 := sw 352 0 (by simp [setupWords]) (by omega) (by omega)
    have b1 : sideWord s h 2 72 = 0 := sw 344 0 (by simp [setupWords]) (by omega) (by omega)
    have b2 : sideWord s h 2 80 = 0 := sw 336 0 (by simp [setupWords]) (by omega) (by omega)
    rw [b0, b1, b2, eOf3_zero]
    rfl

theorem sideOk {bev : MachineState → Word → List E → Option E} {s z w v h₀ h : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E} {P : Word} {n : Nat}
    {acc : List (List Form) × List E} {i : Nat} (hpre : BusBalancePre s)
    (C : SCtx bev s z w v h₀ k state mem mf bf bv) (Sd : Sides s z h₀ h P n acc) (hi : i < 3) :
    SideOk s z h i ((sidesOf s k state mem mf bf bv).getD i noSide) := by
  have En := sideEnv hpre C Sd
  interval_cases i
  · exact sideOk0 hpre C En
  · exact sideOk1 hpre C En
  · exact sideOk2 hpre C En Sd.inv

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
