import Rv64Verifier.Proofs.Walk.R20G

/-!
# `walk` R20, the outputs' claim stored

`r20store`: `0x80003f84` writes the outputs' claim (column `QKECCAK`, the outputs' point and word)
past the claims, and goes on to `ring_switch`'s call (`AtR21m`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus Rv64Verifier.Model.Gkr Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem sub_add_lit (x a b c : Word) (h : b.toNat + c.toNat = a.toNat) :
    x - a + b = x - c := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := a.isLt; have := b.isLt; have := c.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub]
  omega

theorem add_add_lit (X a b c : Word) (h : a.toNat + b.toNat = c.toNat) : X + a + b = X + c := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  rw [BitVec.toNat_add]
  omega

section Store
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w t c y : MachineState}
  {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
  {bus : BusResultRust} {evs : List (List E × List E)} {P C L : Word}
  {cl : List ColumnClaim} {o : KeccakOpenings} {ks ke : Nat} {p : List E} {wd : E} {N : Nat}

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- The outputs' claim stored: on to `ring_switch`'s call. -/
theorem r20store (hpre : WalkPre s)
    (A : AtStore OI s u₀ w t c y layout rows lir bus evs P C L cl o ks ke p wd N) :
    ∃ y', Reaches Image.code y y' ∧ AtR21m OI s u₀ w t y' layout rows lir bus evs P C
      (L.toNat + 1) (cl ++ [⟨LayoutMirror.qkeccakRust, p, wd⟩]) o ks ke := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have H := A.core
  have sp := H.rest.inv.sp
  have hh := H.rest.inv.heap.hi
  have hs0 := hpre.heap.lo
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd, heapStart] at hh hs0 hab
  obtain ⟨bal, bhi, blo, -⟩ := H.buf
  have room := A.room
  have hC := H.n_lt
  have hPs : heapNext s ≤ P.toNat := by rcases blo with h0 | h0 <;> omega
  have eP : y.getMem (y.getReg .x2 + 1032) = P := by
    rw [sp, show s.getReg .x2 - 2656 + 1032 = s.getReg .x2 - 1624 by bv_omega]; exact H.ptrSlot
  have eP' : y.getMem (s.getReg .x2 - 1624) = P := H.ptrSlot
  have hmul : L * 64 - L * 8 = BitVec.ofNat 64 (56 * L.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat]
    simp only [show (64 : Word).toNat = 64 from rfl, show (8 : Word).toNat = 8 from rfl]
    omega
  have hXn : (P + BitVec.ofNat 64 (56 * L.toNat)).toNat = P.toNat + 56 * L.toNat := by
    addr_omega [bhi, room, hh, hC]
  obtain ⟨y', hr, h₁⟩ := Sym.BlockSpec.reaches b80003f84_spec A.pc (by
    rv_eval [sp, eP', A.x25, A.x20, hmul]
    and_intros <;> first
      | valid_access hval [hb1]
      | (refine heapValid ?_ ?_ ?_ <;> addr_omega [bhi, room, hh, hs0, bal, hPs]))
  have k₁ := b80003f84_keeps h₁
  have sp' : y'.getReg .x2 = y.getReg .x2 := k₁ .x2 (by decide)
  have fr : DFrame y y' (Within · (P + BitVec.ofNat 64 (56 * L.toNat)) 56) :=
    h₁.dframe (by
      rv_eval [sp, eP', A.x25, A.x20, hmul]
      simp only [Within]
      and_intros <;> addr_omega [hXn, bhi, room, hh, hC])
  have kp : ∀ z : Word, z.toNat + 8 ≤ P.toNat + 56 * L.toNat ∨ P.toNat + 56 * L.toNat + 56 ≤ z.toNat →
      z.toNat + 8 ≤ 2 ^ 64 → y'.getMem z = y.getMem z := fun z hz hw ↦
    fr z fun i hi h' ↦ by simp only [Within] at h'; rw [hXn] at h'; addr_omega [hz, hw, hi, h']
  have kS (a : Word) (k : Nat) (ha : a = s.getReg .x2 - BitVec.ofNat 64 k) (hk : 8 ≤ k ∧ k ≤ 11392) :
      y'.getMem a = y.getMem a := by
    subst ha
    exact kp _ (Or.inr (by addr_omega [hb1, hk, hab, bhi, room, hh])) (by addr_omega [hb1, hk])
  have hn' : heapNext y' = heapNext y := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (kp nextAddr (Or.inr (by
      have : nextAddr.toNat = 2684358448 := rfl
      omega)) (by decide))
  have hmc : heapNext s ≤ heapNext c := by
    have := H.smono; have := H.umono; have := H.wmono; have := A.before; omega
  have bufN := A.bufN
  have heapN := A.heapN
  -- a buffer `verify_keccak` allocated misses the claim
  have keepV (a : Word) {xs : List E} (hv : NewVecE c y a xs) (hN : VecBy y c a N) :
      ∀ z : Word, (vecPtr y a).toNat ≤ z.toNat →
        z.toNat + 8 ≤ (vecPtr y a).toNat + 24 * xs.length → y'.getMem z = y.getMem z := by
    intro z h1 h2
    obtain ⟨-, Il, -⟩ := newVecE_facts hv
    simp only [VecBy] at hN
    rw [Il] at hN
    rcases hN with h0 | ⟨q1, q2⟩
    · rw [h0] at h2; omega
    refine kp z ?_ (by omega)
    rcases bufN with b | b <;> omega
  have mvV (a : Word) (k : Nat) (ha : a = s.getReg .x2 - BitVec.ofNat 64 k) (hk : 24 ≤ k ∧ k ≤ 2656)
      {xs : List E} (hv : NewVecE c y a xs) (hN : VecBy y c a N) : NewVecE t y' a xs :=
    NewVecE.move (NewVecE.widen' hv A.before) (kS a k ha (by omega))
      (kS (a + 8) (k - 8) (by rw [ha]; apply BitVec.eq_of_toNat_eq; bv_omega) (by omega))
      (kS (a + 16) (k - 16) (by rw [ha]; apply BitVec.eq_of_toNat_eq; bv_omega) (by omega))
      (by omega) (keepV a hv hN)
  -- the claim written
  have w0 := b80003f84_m0 h₁
  have w1 := b80003f84_m1 h₁
  have w2 := b80003f84_m2 h₁
  have w3 := b80003f84_m3 h₁
  have w4 := b80003f84_m4 h₁
  have w5 := b80003f84_m5 h₁
  rw [eP, A.x25, hmul] at w0 w1 w2 w3 w4 w5
  rw [A.x20] at w0 w1 w2
  rw [sp] at w4 w5
  obtain ⟨X, hXd⟩ : ∃ X, P + BitVec.ofNat 64 (56 * L.toNat) = X := ⟨_, rfl⟩
  rw [hXd] at w0 w1 w2 w3 w4 w5 fr hXn
  obtain ⟨c1, c2, c3, c4, c5⟩ := A.copy
  have ePt : vecPtr y' X = vecPtr y (s.getReg .x2 - 880) := by
    simp only [vecPtr]
    rw [sub_add_lit _ 880 8 872 rfl, w5,
      sub_add_lit _ 2656 888 1768 rfl, c1]
  have eLn : vecLen y' X = vecLen y (s.getReg .x2 - 880) := by
    simp only [vecLen]
    rw [sub_add_lit _ 880 16 864 rfl, w4,
      sub_add_lit _ 2656 896 1760 rfl, c2]
  obtain ⟨Oa, Ol, -⟩ := newVecE_facts A.outv
  have oN := A.outN
  simp only [VecBy] at oN
  have hc : claimAt y' X =
      ⟨LayoutMirror.qkeccakRust, p, wd⟩ := by
    simp only [claimAt]
    rw [w3]
    congr 1
    · rw [← A.outv.elems]
      simp only [vecEs]
      rw [ePt, eLn]
      refine Bus.eListAt_congr fun i hi ↦ ?_
      rw [Ol] at hi
      have := keepV _ A.outv A.outN
      rw [Ol] at oN
      rcases oN with h0 | ⟨q1, q2⟩
      · omega
      exact eAt_congr (this _ (by addr_omega [hi, q2, heapN, hh]) (by addr_omega [hi, q2, heapN, hh]))
        (this _ (by addr_omega [hi, q2, heapN, hh]) (by addr_omega [hi, q2, heapN, hh]))
        (this _ (by addr_omega [hi, q2, heapN, hh]) (by addr_omega [hi, q2, heapN, hh]))
    · rw [← A.outw]
      refine eAt_congr ?_ ?_ ?_
      · rw [w2, c3]
      · rw [sub_add_lit _ 856 8 848 rfl,
          add_add_lit X 32 8 40 rfl, w1,
          sub_add_lit _ 1752 8 1744 rfl, c4]
      · rw [sub_add_lit _ 856 16 840 rfl,
          add_add_lit X 32 16 48 rfl, w0,
          sub_add_lit _ 1752 16 1736 rfl, c5]
  have hpt : ((vecLen y' X).toNat = 0 ∨
        Old s y' (vecPtr y' X)
          (24 * (vecLen y' X).toNat)) ∧
      Apart (vecPtr y' X)
        (24 * (vecLen y' X).toNat) P (56 * C.toNat) := by
    rw [ePt, eLn]
    rcases oN with h0 | ⟨q1, q2⟩
    · exact ⟨Or.inl h0, Or.inl (by omega)⟩
    · refine ⟨Or.inr ⟨Oa, by omega, Or.inr (by omega)⟩, ?_⟩
      simp only [Apart]
      rcases bufN with b | b <;> omega
  subst hXd
  have H' := H.store hpre room fr sp' hc hpt
  refine ⟨y', hr, {
    core := H'.congr rfl (by
      simp only [afterKeccak, A.some, Option.toList, List.map_cons, List.map_nil])
    pc := b80003f84_pc h₁
    x12 := by
      rw [k₁ .x12 (by decide), A.x12]; simp only [vecPtr]
      rw [kS _ 896 (sub_add_lit _ 904 8 896 rfl) (by omega)]
    x13 := by
      rw [k₁ .x13 (by decide), A.x13]; simp only [vecLen]
      rw [kS _ 888 (sub_add_lit _ 904 16 888 rfl) (by omega)]
    x18 := by rw [b80003f84_x18 h₁, eP]
    x22 := by rw [k₁ .x22 (by decide), A.x22]
    x23 := by rw [k₁ .x23 (by decide), A.x23]
    x24 := by rw [k₁ .x24 (by decide), A.x24]
    x25 := by
      rw [b80003f84_x25 h₁, show y.getReg .x26 + 2 = L + 1 by rw [← A.x26]; exact (add_add_lit _ 1 1 2 rfl).symm]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
    in1 := mvV _ 1728 rfl (by omega) A.in1 A.in1N
    in2 := mvV _ 904 rfl (by omega) A.in2 A.in2N }⟩

end Store

end Rv64Verifier.Proofs.Walk
