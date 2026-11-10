import Rv64Verifier.Proofs.Walk.R20A

/-!
# `walk` R20, `verify_keccak`'s arguments

`r20pre`: from `AtR20` the evaluations' count and the KECCAK table's values' count are checked
(`0x80003eb0`, `0x80003ebc`: a trap otherwise), and `0x80003ed4` jumps to `verify_keccak` with the
table's point and its 25 output lanes (`AtKC`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Gkr Rv64Verifier.Model.Gkr Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- An aligned heap buffer allocated by `walk` is a region. -/
theorem regionH {s u : MachineState} (hs : HeapOk s) (hu : HeapOk u) {p : Word} {n : Nat}
    (h1 : heapNext s ≤ p.toNat) (h2 : p.toNat + n ≤ heapNext u) (h3 : p.toNat % 8 = 0) :
    Region p n := by
  have := hs.lo
  have := hu.hi
  simp only [Region, Mapped, heapStart, heapEnd] at *
  omega

/-- `n` elements from the `c`-th of a list in memory. -/
theorem eListAt_slice (u : MachineState) (p : Word) {L c n : Nat} (h : c + n ≤ L) :
    ((eListAt u p L).drop c).take n = eListAt u (p + BitVec.ofNat 64 (24 * c)) n := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, eListAt_length]; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, eListAt_getElem]
    congr 1
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    ring

/-- A heap buffer allocated by `walk`, or empty, misses what lies above the heap. -/
theorem heapApart {c : MachineState} (hc : HeapOk c) {p : Word} {n : Nat}
    (hp : n = 0 ∨ p.toNat + n ≤ heapNext c) {lo : Word} {m : Nat} (hlo : heapEnd ≤ lo.toNat) :
    Apart p n lo m := by
  rcases hp with h | h
  · exact Or.inl h
  · have := hc.hi; simp only [Apart, heapNext, heapEnd] at *; omega

/-- At `verify_keccak`'s entry: the table phase's claims and the public input's, `cl`. -/
structure AtKC (OI : MachineState → Word → List (List Opening) → Prop)
    (s u₀ w t c : MachineState) (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64))
    (lir : BitVec 64) (bus : BusResultRust) (evs : List (List E × List E)) (P C L : Word)
    (cl : List ColumnClaim) : Prop where
  core : CoreT OI s u₀ w t c layout lir evs P C L.toNat cl
    (keccakPhaseRust layout evs >>= afterKeccak layout rows lir bus cl)
  pc : c.pc = 0x80008e34
  x1 : c.getReg .x1 = 0x80003f00
  x10 : c.getReg .x10 = s.getReg .x2 - 928
  x11 : c.getReg .x11 = tp s
  x22 : c.getReg .x22 = lir
  x23 : c.getReg .x23 = s.getReg .x10
  x24 : c.getReg .x24 = s.getReg .x2 - 512
  x25 : c.getReg .x25 = L
  x26 : c.getReg .x26 + 1 = L
  h5 : 5 < evs.length
  h65 : 65 ≤ evs[5].2.length
  pre : VerifyKeccakPreE c
  inst : eListAt c (kInst c) (kInstLen c) = evs[5].1
  output : eListAt c (kOutput c) 25 = (evs[5].2.drop 40).take 25
  shape : shapeOf c = ⟨layout.keccakLogSteps, 12⟩

section Pre
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {pub : List ColumnClaim}

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- To `verify_keccak`'s entry, or a trap. -/
theorem r20pre (hpre : WalkPre s) (h : AtR17 OI s u₀ layout rows lir bus)
    (A : AtR20 OI s u₀ w t u layout rows lir bus evs P C L pub) :
    ∃ c, Reaches Image.code u c ∧ (AtKC OI s u₀ w t c layout rows lir bus evs P C L
      (bus.claims ++ tableClaimsRust evs ++ pub) ∨ Dead Image.code c) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have H := A.toCoreT
  have I := H.rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hs0 := hpre.heap.lo
  have htm := H.tmono
  have hwm := H.wmono
  have hsm := H.smono
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd, heapStart] at hh hs0 hab
  have ea (c d : Word) (hc : c.toNat + d.toNat = 2656) : u.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  obtain ⟨Pa, Pl, Pf⟩ := rowsAt_facts H.rowsAt
  -- `0x80003eb0`: six tables
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80003eb0_spec A.pc (by
    rv_eval [sp]; valid_access hval [hb1])
  have m₁ := b80003eb0_mem_same h₁
  have k₁ := b80003eb0_keeps h₁
  have e48 : u.getMem (u.getReg .x2 + 48) = vecLen t (s.getReg .x2 - 928) := by
    rw [ea 48 2608 rfl]; exact H.evLen
  by_cases h6 : evs.length < 6
  · exact ⟨u₁, hr₁, Or.inr (trapAt (b80003eb0_pc_taken h₁ (by
      rw [e48, Pl]; exact h6)))⟩
  have pc₁ := b80003eb0_pc_not_taken h₁ (by rw [e48, Pl]; show 6 ≤ _; omega)
  have h5 : 5 < evs.length := by omega
  rcases Pf with h0 | ⟨p1, p2⟩
  · omega
  set Pe := vecPtr t (s.getReg .x2 - 928) with hPe
  have pk := H.rowsAt.pairs 5 h5
  obtain ⟨Ia, Il, If⟩ := newVecE_facts pk.1
  obtain ⟨Va, Vl, Vf⟩ := newVecE_facts pk.2
  have hpe (c : Nat) (hc : c ≤ 40) : u.getMem (Pe + BitVec.ofNat 64 (240 + c)) =
      t.getMem (Pe + BitVec.ofNat 64 (240 + c)) :=
    H.evKept _ (by addr_omega [p1, p2, h5, hc, htm, hh]) (by addr_omega [p1, p2, h5, hc, htm, hh])
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide), sp]
  have e40 : u₁.getMem (u₁.getReg .x2 + 40) = Pe := by
    rw [m₁, k₁ .x2 (by decide), ea 40 2616 rfl]; exact H.evPtr
  have eVl : u₁.getMem (Pe + 280) = BitVec.ofNat 64 evs[5].2.length := by
    rw [m₁, show (280 : Word) = BitVec.ofNat 64 (240 + 40) from rfl, hpe 40 (by omega),
      show Pe + BitVec.ofNat 64 (240 + 40) = Pe + BitVec.ofNat 64 (48 * 5 + 24) + 16 by bv_omega]
    apply BitVec.eq_of_toNat_eq
    show (vecLen t (Pe + BitVec.ofNat 64 (48 * 5 + 24))).toNat = _
    rw [Vl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := (vecLen t (Pe + BitVec.ofNat 64 (48 * 5 + 24))).isLt; rw [Vl] at this; exact this)]
  have e40' : u₁.getMem (s.getReg .x2 - 2616) = Pe := by
    rw [m₁]; exact H.evPtr
  -- `0x80003ebc`: the KECCAK table's values
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003ebc_spec pc₁ (by
    rv_eval [sp₁, e40']
    and_intros <;> first
      | valid_access hval [hb1]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [p1, p2, Pa, h5, htm, hh, hwm, hsm, hs0]))
  have m₂ := b80003ebc_mem_same h₂
  have k₂ := b80003ebc_keeps h₂
  by_cases h64 : evs[5].2.length ≤ 64
  · exact ⟨u₂, hr₁.trans hr₂, Or.inr (trapAt (b80003ebc_pc_taken h₂ (by
      rw [e40, eVl, BitVec.toNat_ofNat]; show _ ≤ 64; omega)))⟩
  have hn64 : evs[5].2.length < 2 ^ 64 := by
    have := (vecLen t (Pe + BitVec.ofNat 64 (48 * 5 + 24))).isLt; rw [Vl] at this; exact this
  have pc₂ := b80003ebc_pc_not_taken h₂ (by
    rw [e40, eVl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]; show 64 < _; omega)
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₂ .x2 (by decide), sp₁]
  have x12₂ : u₂.getReg .x12 = Pe := by rw [b80003ebc_x12 h₂, e40]
  rcases Vf with v0 | ⟨v1, v2⟩
  · omega
  -- `0x80003ed4`: the arguments
  obtain ⟨c, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003ed4_spec pc₂ (by
    rv_eval [sp₂, x12₂]
    and_intros <;> first
      | valid_access hval [hb1]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [p1, p2, Pa, h5, htm, hh, hwm, hsm, hs0]))
  have m₃ := b80003ed4_mem_same h₃
  have k₃ := b80003ed4_keeps h₃
  have mm (a : Word) : c.getMem a = u.getMem a := by rw [m₃, m₂, m₁]
  have R (r : Reg) (h3 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x9, .x17, .x18, .x19, .x20, .x21,
      .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h2 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x13, .x14, .x15, .x16, .x17, .x18,
        .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x28, .x29, .x30, .x31] : List Reg))
      (h1 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17,
        .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
        List Reg)) : c.getReg r = u.getReg r := by
    rw [k₃ r h3, k₂ r h2, k₁ r h1]
  have spc : c.getReg .x2 = u.getReg .x2 := R .x2 (by decide) (by decide) (by decide)
  have Hc := H.same hpre mm spc
  have Ic := Hc.rest.inv
  have ptrc := Hc.proofPtr
  have hhc := Ic.heap.hi
  have hnc : heapNext c = heapNext u := by simp only [heapNext, mm]
  have hsl := stackLo_callee Ic verifyKeccakStack
  have eS (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2656) : u₂.getReg .x2 + BitVec.ofNat 64 (2656 - k) =
      s.getReg .x2 - BitVec.ofNat 64 k := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hk]
  have gk (k : Nat) (hk : (1872 + 8 ≤ k ∧ k ≤ 2080) ∨ (2544 + 8 ≤ k ∧ k ≤ 2584) ∨ k = 2088) :
      u₂.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    rw [m₂, m₁]
    refine H.rest.get (keep_slot hpre ?_)
    rcases hk with hk | hk | hk <;> omega
  have LI := h.layoutIn
  set P5 := Pe + BitVec.ofNat 64 (48 * 5) with hP5
  set V5 := Pe + BitVec.ofNat 64 (48 * 5 + 24) with hV5
  have g5 (c' : Nat) (hc : c' ≤ 40) (y : Word) (hy : y = Pe + BitVec.ofNat 64 (240 + c')) :
      u₂.getMem y = t.getMem y := by
    subst hy; rw [m₂, m₁]; exact hpe c' hc
  have x14 : c.getReg .x14 = vecPtr t P5 := by
    rw [b80003ed4_x14 h₃, x12₂, g5 8 (by omega) (Pe + 248) rfl]; simp only [vecPtr, hP5]; congr 1; bv_omega
  have x15 : c.getReg .x15 = vecLen t P5 := by
    rw [b80003ed4_x15 h₃, x12₂, g5 16 (by omega) (Pe + 256) rfl]; simp only [vecLen, hP5]; congr 1; bv_omega
  have x16 : c.getReg .x16 = vecPtr t V5 + 960 := by
    rw [b80003ed4_x16 h₃, x12₂, g5 32 (by omega) (Pe + 272) rfl]; simp only [vecPtr, hV5]; congr 2; bv_omega
  have x10 : c.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 928 := by
    rw [b80003ed4_x10 h₃, ← eS 928 (by omega)]; rfl
  have x11 : c.getReg .x11 = tp s := by rw [b80003ed4_x11 h₃, sp₂, tp]; bv_omega
  have x12 : (c.getReg .x12).toNat = layout.keccakLogSteps := by
    rw [b80003ed4_x12 h₃, ← LI.keccakLogSteps, show (768 : Word) = BitVec.ofNat 64 (2656 - 1888)
      from rfl, eS 1888 (by omega), gk 1888 (by omega)]; rfl
  have x13 : c.getReg .x13 = 12 := by
    rw [b80003ed4_x13 h₃, ← LI.keccakDepth, show (776 : Word) = BitVec.ofNat 64 (2656 - 1880)
      from rfl, eS 1880 (by omega), gk 1880 (by omega)]; rfl
  have hEnd (k : Nat) (hk : k ≤ 2656) : heapEnd ≤ (s.getReg .x2 - BitVec.ofNat 64 k).toNat := by
    simp only [heapEnd]; addr_omega [hab, hb1, hk]
  have hEnd' : heapEnd ≤ (stackLo c verifyKeccakStack).toNat := by
    rw [hsl]; simp only [heapEnd, verifyKeccakStack]; addr_omega [hab, hb1]
  have hiv : 24 * evs[5].1.length = 0 ∨ heapNext s ≤ (vecPtr t P5).toNat ∧
      (vecPtr t P5).toNat + 24 * evs[5].1.length ≤ heapNext c := by
    rw [← Il]; rcases If with h0 | ⟨q1, q2⟩
    · left; omega
    · right; constructor <;> omega
  have iv : 24 * (kInstLen c) = 0 ∨ heapNext s ≤ (kInst c).toNat ∧
      (kInst c).toNat + 24 * kInstLen c ≤ heapNext c := by
    simp only [kInst, kInstLen, x14, x15, Il]; exact hiv
  have ov : heapNext s ≤ (kOutput c).toNat ∧ (kOutput c).toNat + 24 * 25 ≤ heapNext c ∧
      (kOutput c).toNat % 8 = 0 := by
    simp only [kOutput, x16]; rw [Vl] at v2
    refine ⟨?_, ?_, ?_⟩ <;> addr_omega [v1, v2, Va, h64, hsm, hwm, htm, hhc, hnc]
  have ivA (lo : Word) (m : Nat) (hlo : heapEnd ≤ lo.toNat) : Apart (kInst c) (24 * kInstLen c) lo m :=
    heapApart Ic.heap (iv.imp_right fun h ↦ h.2) hlo
  have ovA (lo : Word) (m : Nat) (hlo : heapEnd ≤ lo.toNat) : Apart (kOutput c) (24 * 25) lo m :=
    heapApart Ic.heap (Or.inr ov.2.1) hlo
  have hS := hpre.heap
  have ek : ∀ y : Word, heapNext w ≤ y.toNat → y.toNat + 8 ≤ heapNext t → c.getMem y = t.getMem y :=
    fun y h1 h2 ↦ (mm y).trans (H.evKept y h1 h2)
  have hrng (k : Nat) (hk : k < 24 * 25) : (vecPtr t V5 + 960 + BitVec.ofNat 64 k).toNat + 8 ≤
      heapNext t + 8 := by rw [Vl] at v2; addr_omega [v1, v2, h64, hk, hhc, htm]
  refine ⟨c, hr₁.trans (hr₂.trans hr₃), Or.inl {
    core := Hc
    pc := b80003ed4_pc h₃
    x1 := b80003ed4_x1 h₃
    x10 := x10
    x11 := x11
    x22 := by
      rw [k₃ .x22 (by decide), b80003ebc_x22 h₂, sp₁,
        show s.getReg .x2 - 2656 + 72 = s.getReg .x2 - BitVec.ofNat 64 2584 by bv_omega, m₁,
        H.rest.get (keep_slot hpre (by omega))]
      exact h.rate
    x23 := by rw [R .x23 (by decide) (by decide) (by decide), A.x23]
    x24 := by rw [R .x24 (by decide) (by decide) (by decide), A.x24]
    x25 := by rw [R .x25 (by decide) (by decide) (by decide), A.x25]
    x26 := by rw [R .x26 (by decide) (by decide) (by decide), A.x26]
    h5 := h5
    h65 := by omega
    pre := {
      toTPre := tpre hpre Ic ptrc (k := 928) (n := 96) (by omega) (by omega) (by omega)
        (by decide) (by decide) x10 x11
      depth := x13
      checked := by
        simp only [Checked]
        rw [x11, byteAt_congr (u := u₀) (by rw [tp]; addr_omega [hb1, hb3]) (by
          rw [mm, show tp s + 360 = s.getReg .x2 - BitVec.ofNat 64 2088 by rw [tp]; bv_omega]
          exact H.rest.get (keep_slot hpre (by omega))), h.checked]
        decide
      inst := by
        rcases iv with h0 | h0
        · left; omega
        · right; exact regionH hS Ic.heap h0.1 h0.2 (by simp only [kInst, x14]; exact Ia)
      output := regionH hS Ic.heap ov.1 ov.2.1 ov.2.2
      instFree := by
        rcases iv with h0 | h0
        · left; omega
        · right; exact (heap_ok Ic.heap h0.2).1
      outputFree := (heap_ok Ic.heap ov.2.1).1
      instStack := ivA _ _ hEnd'
      outputStack := ovA _ _ hEnd'
      instOut := ivA _ _ (by rw [x10]; exact hEnd 928 (by omega))
      outputOut := ovA _ _ (by rw [x10]; exact hEnd 928 (by omega))
      instSelf := ivA _ _ (by rw [x11, tp]; simp only [heapEnd]; addr_omega [hab, hb1])
      outputSelf := ovA _ _ (by rw [x11, tp]; simp only [heapEnd]; addr_omega [hab, hb1]) }
    inst := by
      simp only [kInst, kInstLen, x14, x15]
      rw [← pk.1.elems]
      simp only [vecEs]
      refine Bus.eListAt_congr fun i hi ↦ ?_
      rw [Il] at hi
      rcases If with h0 | ⟨q1, q2⟩
      · rw [Il] at h0; omega
      rw [Il] at q2
      exact eAt_congr (ek _ (by addr_omega [q1, q2, hi]) (by addr_omega [q1, q2, hi]))
        (ek _ (by addr_omega [q1, q2, hi]) (by addr_omega [q1, q2, hi]))
        (ek _ (by addr_omega [q1, q2, hi]) (by addr_omega [q1, q2, hi]))
    output := by
      simp only [kOutput, x16]
      rw [← pk.2.elems]
      simp only [vecEs]
      rw [eListAt_slice t _ (by rw [Vl]; omega)]
      rw [Vl] at v2
      refine Bus.eListAt_congr fun i hi ↦ ?_
      exact eAt_congr (ek _ (by addr_omega [v1, v2, hi, h64]) (by addr_omega [v1, v2, hi, h64]))
        (ek _ (by addr_omega [v1, v2, hi, h64]) (by addr_omega [v1, v2, hi, h64]))
        (ek _ (by addr_omega [v1, v2, hi, h64]) (by addr_omega [v1, v2, hi, h64]))
    shape := by simp only [shapeOf, x12, x13]; rfl }⟩

end Pre

end Rv64Verifier.Proofs.Walk
