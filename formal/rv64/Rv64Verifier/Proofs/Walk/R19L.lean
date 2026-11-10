import Rv64Verifier.Proofs.Walk.R19K

/-!
# `walk` R19, the public input's claims: the claim's store

`r19pC2`: from `0x80003b14` (`AtC`): claim `L + i` (column `i`, the point's clone, the value)
stored, the length and the buffer at `S - 1616`, `S - 2472`; then the next limb's head, or, the
three claims pushed, `0x80003eb0` (`AtR20`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem pubClaims_eq {s : MachineState} (hpre : WalkPre s) (layout : LayoutMirror.LayoutRust)
    (c : E) : pubClaims layout (bytesAt s (s.getReg .x12) 32) c =
      (List.range 3).map fun j ↦ (⟨j, c :: List.replicate (layout.logMemory - 1) 0, pubVal s j c⟩ :
        ColumnClaim) := by
  have h0 := pub_limbs hpre 0
  have h1 := pub_limbs hpre 1
  have h2 := pub_limbs hpre 2
  simp only [pubClaims, pubVal, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
  rfl

theorem pubClaims_take_succ {s : MachineState} (hpre : WalkPre s)
    (layout : LayoutMirror.LayoutRust) (c : E) {i : Nat} (hi : i < 3) :
    (pubClaims layout (bytesAt s (s.getReg .x12) 32) c).take (i + 1) =
      (pubClaims layout (bytesAt s (s.getReg .x12) 32) c).take i ++
        [⟨i, c :: List.replicate (layout.logMemory - 1) 0, pubVal s i c⟩] := by
  rw [List.take_add_one, pubClaims_eq hpre]
  congr 1
  simp [hi]

section Iter
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t u : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word} {i : Nat} {c : E}
  {pt : Word}

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- From `0x80003b14`: the claim stored, then the next head or `AtR20`. -/
theorem r19pC2 (hpre : WalkPre s) (h : AtR17 OI s u₀ layout rows lir bus)
    (Hd : HeadR19 OI s u₀ w t u layout rows lir bus evs P C L i c pt)
    {y : MachineState} {P₁ C₁ cp : Word}
    (A : AtC OI s u₀ w t u y layout rows lir bus evs L i c pt P₁ C₁ cp) :
    ∃ v, Reaches Image.code y v ∧ ((i + 1 < 3 ∧
      HeadR19 OI s u₀ w t v layout rows lir bus evs P₁ C₁ L (i + 1) c pt) ∨
      (i + 1 = 3 ∧ AtR20 OI s u₀ w t v layout rows lir bus evs P₁ C₁ (L + 3)
        (pubClaims layout (bytesAt s (s.getReg .x12) 32) c))) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have Cy := A.core
  have I := Cy.rest.inv
  have sp := I.sp
  have hh := I.heap.hi
  have hl := Hd.rest.inv.heap.lo
  simp only [heapEnd, heapStart] at hh hl
  have hi := Hd.hi
  have hn := Hd.hn
  have room := A.room
  have hC := Cy.n_lt
  have bP := Cy.buf
  obtain ⟨ba, bhi, blo, -⟩ := bP
  have hs0 := hpre.heap.lo
  simp only [heapStart] at hs0
  have bP0 : heapNext s ≤ P₁.toNat := by rcases blo with h0 | h0 <;> omega
  have hLi : (L + BitVec.ofNat 64 i).toNat = L.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have eX0 : (L + BitVec.ofNat 64 i) * 64 - (L + BitVec.ofNat 64 i) * 8 =
      BitVec.ofNat 64 (56 * (L.toNat + i)) := by
    have := hLi; bv_omega
  have hX : (P₁ + BitVec.ofNat 64 (56 * (L.toNat + i))).toNat = P₁.toNat + 56 * (L.toNat + i) := by
    addr_omega [bhi, room, hh]
  obtain ⟨y', hr, h'⟩ := Sym.BlockSpec.reaches b80003b14_spec A.pc (by
    rv_eval [sp, A.x14, A.x26, eX0]
    and_intros <;> first
      | valid_access hval [hb1, hb3]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [hX, ba, bhi, room, hh, bP0, hs0])
      | addr_omega [hX, bhi, room, hh, hb1])
  have k' := b80003b14_keeps h'
  have sp' : y'.getReg .x2 = y.getReg .x2 := k' .x2 (by decide)
  have Wok : ∀ a, (Within a (s.getReg .x2 - 1616) 8 ∨ Within a (s.getReg .x2 - 2472) 8) →
      InF s a ∧ ¬ KeepR s u₀ a ∧ ¬ Within a (tp s) 368 ∧ ¬ Within a (s.getReg .x2 - 1632) 16 ∧
        ¬ Within a (s.getReg .x2 - 2616) 16 := fun a ha ↦ ha.elim
    (fun h ↦ range_okT hpre Cy.rest (c := 1616) (k := 1616) (n := 8) rfl (by omega) (by omega)
      (by omega) (by omega) (by omega) h)
    (fun h ↦ range_okT hpre Cy.rest (c := 2472) (k := 2472) (n := 8) rfl (by omega) (by omega)
      (by omega) (by omega) (by omega) h)
  have fr : DFrame y y' fun a ↦ Within a (P₁ + BitVec.ofNat 64 (56 * (L.toNat + i))) 56 ∨
      (Within a (s.getReg .x2 - 1616) 8 ∨ Within a (s.getReg .x2 - 2472) 8) := h'.dframe (by
    rv_eval [sp, A.x14, A.x26, eX0]
    and_intros <;> first
      | (left; simp only [Within]; constructor <;> addr_omega [hX, bhi, room, hh])
      | (right; simp only [Within]; addr_omega [hb1]))
  have m3 := b80003b14_m3 h'
  have m6 := b80003b14_m6 h'
  have m7 := b80003b14_m7 h'
  have m2 := b80003b14_m2 h'
  have m1 := b80003b14_m1 h'
  have m5 := b80003b14_m5 h'
  rw [A.x14, A.x26, eX0] at m3 m6 m7 m2 m1 m5
  rw [spAdd hpre sp 152 2504 rfl, A.s152] at m3
  rw [spAdd hpre sp 1320 1336 rfl, A.h1320] at m6
  rw [spAdd hpre sp 1328 1328 rfl, A.h1328] at m7
  have hn64 : layout.logMemory < 2 ^ 64 := by
    have := Hd.nSlot; have := (u.getMem (s.getReg .x2 - 2512)).isLt; omega
  have hcp := A.cpApart
  have hcp2 := A.cp2
  have gH (a : Word) (a1 : a.toNat + 8 ≤ heapNext y)
      (a2 : a.toNat + 8 ≤ P₁.toNat + 56 * (L.toNat + i) ∨ P₁.toNat + 56 * (L.toNat + i) + 56 ≤ a.toNat) :
      y'.getMem a = y.getMem a :=
    fr a fun j hj h ↦ by
      rcases h with h | h | h <;> simp only [Within] at h
      · rw [hX] at h; addr_omega [h, hj, a1, a2, hh]
      · addr_omega [h, hj, a1, hh, hb1]
      · addr_omega [h, hj, a1, hh, hb1]
  have cpe' : eListAt y' cp layout.logMemory = c :: List.replicate (layout.logMemory - 1) 0 := by
    rw [← A.cpe]
    refine Bus.eListAt_congr fun j hj ↦ eAt_congr ?_ ?_ ?_ <;>
      (refine gH _ (by addr_omega [hcp2, hj]) ?_; simp only [Apart] at hcp
       rcases hcp with q | q | q | q <;> first | omega | addr_omega [hcp2, hj, q, room])
  set X := P₁ + BitVec.ofNat 64 (56 * (L.toNat + i)) with hXd
  have hc : claimAt y' X = ⟨i, c :: List.replicate (layout.logMemory - 1) 0, pubVal s i c⟩ := by
    simp only [claimAt, vecEs, vecPtr, vecLen]
    rw [m3, m6, m7, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hn64, cpe']
    congr 1
    refine eAt_eq_of_limbs ?_
    rw [show X + 32 + 8 = X + 40 by bv_omega, show X + 32 + 16 = X + 48 by bv_omega, m2, m1, m5]
    exact A.val
  have smono := Hd.smono
  have rmono := Hd.rest.mono
  have hy' : heapNext y' = heapNext y := by
    simp only [heapNext]
    rw [fr nextAddr fun j hj h ↦ by
      rcases h with h | h | h <;> simp only [Within, nextAddr] at h
      · rw [hX] at h; addr_omega [h, hj, bhi, room, hh]
      · addr_omega [h, hj, hb1]
      · addr_omega [h, hj, hb1]]
  have C' := Cy.storeW hpre room Wok fr sp' hc ⟨by
      simp only [vecLen, vecPtr]
      rw [m6, m7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
      exact Or.inr ⟨A.cpa, by rw [hy']; exact hcp2, Or.inr (by have := A.cp1; omega)⟩, by
      simp only [vecLen, vecPtr]
      rw [m6, m7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
      exact hcp⟩
  rw [List.append_assoc, ← pubClaims_take_succ hpre layout c hi] at C'
  have gU (k : Nat) (hk : 112 ≤ k ∧ k ≤ 2648) (hk1 : (520 ≤ k ∧ k ≤ 1312) ∨ 2512 ≤ k) :
      y'.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 k) := by
    have k1 := hk.1
    have k2 := hk.2
    rw [fr _ fun j hj h ↦ by
        rcases h with h | h | h <;> simp only [Within] at h
        · rw [hX] at h; addr_omega [h, hj, bhi, room, hh, hb1, k1, k2]
        · rcases hk1 with ⟨q, q'⟩ | q <;>
            first | addr_omega [h, hj, hb1, k1, k2, q] | addr_omega [h, hj, hb1, k1, k2, q, q']
        · rcases hk1 with ⟨q, q'⟩ | q <;>
            first | addr_omega [h, hj, hb1, k1, k2, q] | addr_omega [h, hj, hb1, k1, k2, q, q'],
      A.st.getF hpre (by addr_omega [hb1, k1, k2]) (fun j hj h ↦ by
        rcases h with h | h
        · simp only [IW, Within] at h
          rcases h with h | h | h | h | h | h | h <;> rcases hk1 with ⟨q, q'⟩ | q <;>
            first | addr_omega [h, hj, hb1, k1, k2, q] | addr_omega [h, hj, hb1, k1, k2, q, q']
        · simp only [Within] at h; rcases hk1 with ⟨q, q'⟩ | q <;>
            first | addr_omega [h, hj, hb1, k1, k2, q] | addr_omega [h, hj, hb1, k1, k2, q, q'])
        (fun h ↦ h.elim)]
  have e192 : y.getMem (y.getReg .x2 + 192) = BitVec.ofNat 64 i + 1 := by
    rw [spAdd hpre sp 192 2464 rfl, A.s192]
  have hy'u : heapNext u ≤ heapNext y' := by rw [hy']; exact A.st.mono
  have ptv : eListAt y' pt layout.logMemory = c :: List.replicate (layout.logMemory - 1) 0 := by
    have pa := A.ptApart
    have po := Hd.ptOld.1
    have hm := A.st.mono
    simp only [Old] at po
    rw [← Hd.ptVal, ← A.st.eListH hpre (fun a ha ↦ ha.elim (fun h ↦ (IW_ok hpre Hd.rest h).1)
      fun h ↦ (range_ok hpre Hd.rest (c := 1632) (k := 1632) (n := 16) rfl (by omega) (by omega)
        h).1) (by omega)]
    refine Bus.eListAt_congr fun j hj ↦ eAt_congr ?_ ?_ ?_ <;>
      (refine gH _ (by addr_omega [po.2.1, hj, hm]) ?_; simp only [Apart] at pa
       rcases pa with q | q | q | q <;> first | omega | addr_omega [po.2.1, hj, q, room])
  rcases Nat.lt_or_ge (i + 1) 3 with hlt | hge
  · have pc' := b80003b14_pc_not_taken h' (by
      rw [e192]; intro he; have := congrArg BitVec.toNat he
      rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this; simp at this; omega)
    refine ⟨y', hr, Or.inl ⟨hlt, {
      toCoreT := C'
      pc := pc'
      hi := hlt
      x12 := by rw [b80003b14_x12 h', e192]; bv_omega
      x20 := by
        rw [b80003b14_x20 h', spAdd hpre sp 128 2528 rfl, show (2528 : Word) = BitVec.ofNat 64 2528
          from rfl, ← fr _ fun j hj h ↦ by
            rcases h with h | h | h <;> simp only [Within] at h
            · rw [hX] at h; addr_omega [h, hj, bhi, room, hh, hb1]
            · addr_omega [h, hj, hb1]
            · addr_omega [h, hj, hb1], gU 2528 (by omega) (by omega)]
        exact Hd.c0
      x21 := by
        rw [b80003b14_x21 h', spAdd hpre sp 120 2536 rfl, show (2536 : Word) = BitVec.ofNat 64 2536
          from rfl, ← fr _ fun j hj h ↦ by
            rcases h with h | h | h <;> simp only [Within] at h
            · rw [hX] at h; addr_omega [h, hj, bhi, room, hh, hb1]
            · addr_omega [h, hj, hb1]
            · addr_omega [h, hj, hb1], gU 2536 (by omega) (by omega)]
        exact Hd.c1
      x27 := by
        rw [b80003b14_x27 h', spAdd hpre sp 112 2544 rfl, show (2544 : Word) = BitVec.ofNat 64 2544
          from rfl, ← fr _ fun j hj h ↦ by
            rcases h with h | h | h <;> simp only [Within] at h
            · rw [hX] at h; addr_omega [h, hj, bhi, room, hh, hb1]
            · addr_omega [h, hj, hb1]
            · addr_omega [h, hj, hb1], gU 2544 (by omega) (by omega)]
        exact Hd.c2
      x24 := by rw [b80003b14_x24 h', spAdd hpre sp 2144 512 rfl]
      x25 := by rw [b80003b14_x25 h', A.x26]; bv_omega
      lenSlot := by
        rw [← spAdd hpre sp 1040 1616 rfl, b80003b14_m_x2_1040 h', A.x26]; bv_omega
      ptr184 := by rw [← spAdd hpre sp 184 2472 rfl, b80003b14_m_x2_184 h', A.x14]
      c0 := by rw [show (2528 : Word) = BitVec.ofNat 64 2528 from rfl, gU 2528 (by omega) (by omega)]; exact Hd.c0
      c1 := by rw [show (2536 : Word) = BitVec.ofNat 64 2536 from rfl, gU 2536 (by omega) (by omega)]; exact Hd.c1
      c2 := by rw [show (2544 : Word) = BitVec.ofNat 64 2544 from rfl, gU 2544 (by omega) (by omega)]; exact Hd.c2
      ptSlot := by
        rw [show (2520 : Word) = BitVec.ofNat 64 2520 from rfl, gU 2520 (by omega) (by omega)]
        exact Hd.ptSlot
      nSlot := by
        rw [show (2512 : Word) = BitVec.ofNat 64 2512 from rfl, gU 2512 (by omega) (by omega)]
        exact Hd.nSlot
      hn := hn
      ptOld := ⟨Hd.ptOld.1.mono hy'u, Hd.ptOld.2⟩
      ptVal := ptv
      ptApart := A.ptApart
      pairs := fun j hj ↦ by
        have e1 : s.getReg .x2 - 912 + BitVec.ofNat 64 (16 * j) =
            s.getReg .x2 - BitVec.ofNat 64 (912 - 16 * j) := by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
        have e2 : s.getReg .x2 - 904 + BitVec.ofNat 64 (16 * j) =
            s.getReg .x2 - BitVec.ofNat 64 (904 - 16 * j) := by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
        rw [e1, e2, gU _ (by omega) (by omega), gU _ (by omega) (by omega), ← e1, ← e2]
        exact Hd.pairs j hj
      cols := fun j hj ↦ by
        have e1 : s.getReg .x2 - 848 + BitVec.ofNat 64 (8 * j) =
            s.getReg .x2 - BitVec.ofNat 64 (848 - 8 * j) := by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
        rw [e1, gU _ (by omega) (by omega), ← e1]
        exact Hd.cols j hj }⟩⟩
  · have hi2 : i = 2 := by omega
    subst hi2
    have pc' := b80003b14_pc_taken h' (by rw [e192]; rfl)
    have e3 : (L + 3).toNat = L.toNat + 2 + 1 := by
      rw [BitVec.toNat_add]; have : (3 : Word).toNat = 3 := rfl; omega
    rw [← e3, List.take_of_length_le (by simp [pubClaims])] at C'
    refine ⟨y', hr, Or.inr ⟨rfl, {
      toCoreT := C'
      pc := pc'
      x23 := by
        rw [b80003b14_x23 h', spAdd hpre sp 168 2488 rfl, show (2488 : Word) = BitVec.ofNat 64 2488
          from rfl, Cy.rest.get (keep_slot hpre (by omega))]
        exact h.sret
      x24 := by rw [b80003b14_x24 h', spAdd hpre sp 2144 512 rfl]
      x25 := by rw [b80003b14_x25 h', A.x26]; bv_omega
      x26 := by rw [k' .x26 (by decide), A.x26]; bv_omega }⟩⟩

end Iter

end Rv64Verifier.Proofs.Walk
