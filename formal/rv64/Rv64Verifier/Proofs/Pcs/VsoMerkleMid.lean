import Rv64Verifier.Proofs.Pcs.VsoMerkleFront

/-!
# `verify_stacked_opening`'s Merkle checks: between the scans, and around the path loop

`0x8000aaa0` compares the phase's path count with the query count (the `Err` at `0x8000b83c`),
`0x8000aaa4` starts the leaf index scan (`scans`). `0x8000aad8` spills `a6`, `s3`, `s2`, `s9`, `s8`
at `S - 1008` and reads the transcript's checked byte (a replay goes to `0x8000b0c0`); `0x8000aaf4`
sends an empty phase to `0x8000b0c8`; `0x8000aaf8` keeps the phase header at `S - 832` and enters
the path loop (`enterPaths`). After the loop, `0x8000b0d0` reloads the paths and their count from the
header (`reload`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem mul8 (x : Word) : x * 8 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
  rw [Nat.mul_comm]

/-- The leaf indices and shapes the scans checked, of the `n` paths from `P` in `t`'s memory. -/
def Scanned (t : MachineState) (P Q : Word) (n : ℕ) (lw sc : Word) : Prop :=
  ∀ i < n, t.getMem (P + BitVec.ofNat 64 (56 * i) + 16) = lw ∧
    t.getMem (P + BitVec.ofNat 64 (56 * i) + 40) = sc ∧
    t.getMem (P + BitVec.ofNat 64 (56 * i) + 48) = t.getMem (Q + BitVec.ofNat 64 (8 * i))

/-- **Both scans**, from the front's end `t`: the paths' shape and leaf indices, or an `Err`. -/
theorem scans {s t : MachineState} {P N Q : Word} (hpre : VsoPre s) (hpc : t.pc = 0x8000aa80)
    (hsp : t.getReg .x2 = s.getReg .x2 - 1040) (hQ : t.getMem (s.getReg .x2 - 824) = Q)
    (hPn : P.toNat + 56 * N.toNat < 2 ^ 64)
    (hv : ∀ j < N.toNat, Region (P + BitVec.ofNat 64 (56 * j)) 56)
    (hq : (t.getReg .x26).toNat = 0 ∨ Region Q (8 * (t.getReg .x26).toNat))
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (56 * N.toNat)) (h11 : t.getReg .x11 = N)
    (h13 : t.getReg .x13 = BitVec.ofNat 64 (56 * N.toNat)) (h14 : t.getReg .x14 = P)
    (h22 : t.getReg .x22 = P) :
    ∃ v, Reaches Image.code t v ∧ (∀ a, v.getMem a = t.getMem a) ∧
      (∀ r ∈ KS2, v.getReg r = t.getReg r) ∧
      (v.pc = 0x8000b830 ∨ v.pc = 0x8000b83c ∨ (v.pc = 0x8000aad8 ∧ N = t.getReg .x26 ∧
        Scanned t P Q N.toNat (t.getReg .x12) (t.getReg .x8))) := by
  have hb := bounds hpre
  obtain ⟨v, r1, m1, k1, hv1⟩ := scan1 (u := t) hPn hv N.toNat 0 t (Nat.sub_zero _) (Nat.zero_le _)
    hpc (by rw [h13, Nat.sub_zero]) (by rw [h14, Nat.mul_zero, add_ofNat_zero]) fun _ ↦ rfl
  rcases hv1 with hpc1 | ⟨hpc1, hall1⟩
  · exact ⟨v, r1, m1, keepsOf k1 (by decide), Or.inl hpc1⟩
  obtain ⟨v2, r2, h2⟩ := Sym.BlockSpec.reaches b8000aaa0_spec hpc1 trivial
  have k2 := b8000aaa0_keeps h2
  have k12 : ∀ r ∈ KS1, v2.getReg r = t.getReg r := keepsTrans k1 (keepsOf k2 (by decide))
  have m2 : ∀ a, v2.getMem a = t.getMem a := fun a ↦ by rw [b8000aaa0_mem_same h2, m1]
  by_cases hN : N = t.getReg .x26
  swap
  · exact ⟨v2, r1.trans r2, m2, keepsOf k12 (by decide), Or.inr (Or.inl (b8000aaa0_pc_taken h2 (by
      rw [k1 .x11 (by decide), k1 .x26 (by decide), h11]; exact hN)))⟩
  have sp2 : v2.getReg .x2 = s.getReg .x2 - 1040 := by rw [k12 .x2 (by decide), hsp]
  have hq' : N.toNat = 0 ∨ Region Q (8 * N.toNat) := by rw [hN]; exact hq
  obtain ⟨v3, r3, h3⟩ := Sym.BlockSpec.reaches b8000aaa4_spec (b8000aaa0_pc_not_taken h2 (by
      rw [k1 .x11 (by decide), k1 .x26 (by decide), h11]; exact hN)) (by
    rv_eval [sp2]; valid_access hpre.stack.valid [hb])
  have k3 := b8000aaa4_keeps h3
  have m3 : ∀ a, v3.getMem a = t.getMem a := fun a ↦ by rw [b8000aaa4_mem_same h3, m2]
  have k23 : ∀ r ∈ KS2, v3.getReg r = t.getReg r :=
    keepsTrans (keepsOf k12 (by decide)) (keepsOf k3 (by decide))
  obtain ⟨v4, r4, m4, k4, hv4⟩ := scan2 (u := t) (Q := Q) hPn hv hq' N.toNat 0 v3 (Nat.sub_zero _)
    (Nat.zero_le _) (b8000aaa4_pc h3)
    (by rw [k3 .x10 (by decide), k12 .x10 (by decide), h10, Nat.sub_zero])
    (by rw [b8000aaa4_x11 h3, k2 .x26 (by decide), k1 .x26 (by decide), ← hN, mul8, Nat.sub_zero])
    (by rw [b8000aaa4_x12 h3, k12 .x22 (by decide), h22, Nat.mul_zero, add_ofNat_zero])
    (by
      rw [b8000aaa4_x13 h3, sp2, m2, show s.getReg .x2 - 1040 + 216 = s.getReg .x2 - 824 by rv_eval [],
        hQ, Nat.mul_zero, add_ofNat_zero])
    m3
  refine ⟨v4, r1.trans (r2.trans (r3.trans r4)), m4, keepsTrans k23 k4, ?_⟩
  rcases hv4 with hpc4 | ⟨hpc4, hall2⟩
  · exact Or.inr (Or.inl hpc4)
  refine Or.inr (Or.inr ⟨hpc4, hN, fun i hi ↦ ?_⟩)
  obtain ⟨e1, e2⟩ := hall1 i (Nat.zero_le _) hi
  exact ⟨e1, e2, hall2 i (Nat.zero_le _) hi⟩

/-- The registers `enterPaths` keeps. -/
def KE : List Reg := [.x2, .x5, .x9, .x17, .x22, .x26]

/-- `0x8000aad8`'s spills at `S - 1008`, from the scans' end `v`. -/
structure Spills (s v w : MachineState) : Prop where
  x16 : w.getMem (s.getReg .x2 - 1008) = v.getReg .x16
  x19 : w.getMem (s.getReg .x2 - 1000) = v.getReg .x19
  x18 : w.getMem (s.getReg .x2 - 992) = v.getReg .x18
  x25 : w.getMem (s.getReg .x2 - 984) = v.getReg .x25
  x24 : w.getMem (s.getReg .x2 - 976) = v.getReg .x24

/-- **Into the path loop**, from the scans' end `v` on a checked transcript: an empty phase to
`0x8000b0dc`, else the path loop's start, the phase header `H` (`a7`) kept at `S - 832`. -/
theorem enterPaths {s v : MachineState} (hpre : VsoPre s) (hpc : v.pc = 0x8000aad8)
    (hsp : v.getReg .x2 = s.getReg .x2 - 1040) (hx20 : v.getReg .x20 = s.getReg .x10)
    (hck : extractByte (v.getMem (s.getReg .x10 + 360)) 0 ≠ 0) :
    ∃ w, Reaches Image.code v w ∧ (∀ r ∈ KE, w.getReg r = v.getReg r) ∧
      DFrame v w (fun a ↦ Within a (s.getReg .x2 - 1008) 40 ∨ Within a (s.getReg .x2 - 832) 8) ∧
      Spills s v w ∧
      ((w.pc = 0x8000b0dc ∧ w.getReg .x20 = 0 ∧ v.getReg .x26 = 0) ∨
        (w.pc = 0x8000ab38 ∧ v.getReg .x26 ≠ 0 ∧ w.getMem (s.getReg .x2 - 832) = v.getReg .x17)) := by
  have hb := bounds hpre
  have hT := Region.bounds hpre.self.ok.self
  obtain ⟨w1, r1, h1⟩ := Sym.BlockSpec.reaches b8000aad8_spec hpc (by
    rv_eval [hsp, hx20]
    refine ⟨by valid_access hpre.stack.valid [hb], by valid_access hpre.stack.valid [hb],
      by valid_access hpre.stack.valid [hb], by valid_access hpre.stack.valid [hb],
      by valid_access hpre.stack.valid [hb], by addr_omega [hT],
      Mapped.valid hpre.self.ok.self.1 (i := 360) (by decide)⟩)
  have k1 := b8000aad8_keeps h1
  have f1 := DFrame.of_memFrame (b8000aad8_frame h1 (by rw [hsp]; addr_omega [hb]))
  rw [hsp, show s.getReg .x2 - 1040 + 32 = s.getReg .x2 - 1008 by rv_eval []] at f1
  have pc1 : w1.pc = 0x8000aaf4 := Sym.Expect.Holds.pc_eq h1 (by
    rv_eval [hx20]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  have sl1 : Spills s v w1 := by
    have e1 := b8000aad8_m_x2_32 h1
    have e2 := b8000aad8_m_x2_40 h1
    have e3 := b8000aad8_m_x2_48 h1
    have e4 := b8000aad8_m_x2_56 h1
    have e5 := b8000aad8_m_x2_64 h1
    rw [hsp] at e1 e2 e3 e4 e5
    rv_eval [] at e1 e2 e3 e4 e5
    exact ⟨e1, e2, e3, e4, e5⟩
  obtain ⟨w2, r2, h2⟩ := Sym.BlockSpec.reaches b8000aaf4_spec pc1 trivial
  have k2 := b8000aaf4_keeps h2
  have m2 := b8000aaf4_mem_same h2
  have k12 : ∀ r ∈ KE, w2.getReg r = v.getReg r :=
    keepsTrans (keepsOf k1 (by decide)) (keepsOf k2 (by decide))
  have f12 : DFrame v w2 (fun a ↦ Within a (s.getReg .x2 - 1008) 40 ∨
      Within a (s.getReg .x2 - 832) 8) :=
    (f1.trans (DFrame.of_same m2 _) fun _ h ↦ h).mono fun _ h ↦ Or.inl h
  have sl2 : Spills s v w2 := ⟨by rw [m2]; exact sl1.x16, by rw [m2]; exact sl1.x19,
    by rw [m2]; exact sl1.x18, by rw [m2]; exact sl1.x25, by rw [m2]; exact sl1.x24⟩
  have x26₁ : w1.getReg .x26 = v.getReg .x26 := k1 .x26 (by decide)
  by_cases h0 : v.getReg .x26 = 0
  · obtain ⟨w3, r3, h3⟩ := Sym.BlockSpec.reaches b8000b0c8_spec
      (b8000aaf4_pc_taken h2 (by rw [x26₁]; exact h0)) trivial
    have m3 := b8000b0c8_mem_same h3
    exact ⟨w3, r1.trans (r2.trans r3),
      keepsTrans k12 (keepsOf (b8000b0c8_keeps h3) (by decide)),
      f12.trans (DFrame.of_same m3 _) (fun _ h ↦ h),
      ⟨by rw [m3]; exact sl2.x16, by rw [m3]; exact sl2.x19, by rw [m3]; exact sl2.x18,
        by rw [m3]; exact sl2.x25, by rw [m3]; exact sl2.x24⟩,
      Or.inl ⟨b8000b0c8_pc h3, b8000b0c8_x20 h3, h0⟩⟩
  have sp2 : w2.getReg .x2 = s.getReg .x2 - 1040 := by rw [k12 .x2 (by decide), hsp]
  obtain ⟨w3, r3, h3⟩ := Sym.BlockSpec.reaches b8000aaf8_spec
    (b8000aaf4_pc_not_taken h2 (by rw [x26₁]; exact h0)) (by
      rv_eval [sp2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have f3 := DFrame.of_memFrame (b8000aaf8_frame h3 (by rw [sp2]; addr_omega [hb]))
  rw [sp2, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval []] at f3
  have e3 := b8000aaf8_m_x2_208 h3
  rw [sp2, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval []] at e3
  have kp (y : Word) (hy : Within y (s.getReg .x2 - 1008) 40) : w3.getMem y = w2.getMem y :=
    f3 y fun i hi hw ↦ by addr_omega [hy, hw, hi, hb]
  exact ⟨w3, r1.trans (r2.trans r3), keepsTrans k12 (keepsOf (b8000aaf8_keeps h3) (by decide)),
    f12.trans f3 (fun _ h ↦ Or.inr h),
    ⟨by rw [kp _ (by addr_omega [hb])]; exact sl2.x16, by rw [kp _ (by addr_omega [hb])]; exact sl2.x19,
      by rw [kp _ (by addr_omega [hb])]; exact sl2.x18, by rw [kp _ (by addr_omega [hb])]; exact sl2.x25,
      by rw [kp _ (by addr_omega [hb])]; exact sl2.x24⟩,
    Or.inr ⟨b8000aaf8_pc h3, h0, by rw [e3, k2 .x17 (by decide), k1 .x17 (by decide)]⟩⟩

/-- **After the path loop**: the paths and their count reloaded from the header at `S - 832`. -/
theorem reload {s w : MachineState} {H : Word} (hpre : VsoPre s) (hpc : w.pc = 0x8000b0d0)
    (hsp : w.getReg .x2 = s.getReg .x2 - 1040) (hH : w.getMem (s.getReg .x2 - 832) = H)
    (hr : Region H 24) :
    ∃ v, Reaches Image.code w v ∧ v.pc = 0x8000b0dc ∧ v.getReg .x20 = w.getMem (H + 16) ∧
      v.getReg .x22 = w.getMem (H + 8) ∧ (∀ a, v.getMem a = w.getMem a) ∧
      ∀ r ∈ [Reg.x2, .x9, .x26], v.getReg r = w.getReg r := by
  have hb := bounds hpre
  have hHb := Region.bounds hr
  have e : w.getMem (w.getReg .x2 + 208) = H := by
    rw [hsp, show s.getReg .x2 - 1040 + 208 = s.getReg .x2 - 832 by rv_eval []]; exact hH
  obtain ⟨v, r, h⟩ := Sym.BlockSpec.reaches b8000b0d0_spec hpc (by
    rv_eval [hsp, hH]
    refine ⟨Region.valid hr (by addr_omega [hHb]) (by addr_omega [hHb]) (by addr_omega [hHb]),
      Region.valid hr (by addr_omega [hHb]) (by addr_omega [hHb]) (by addr_omega [hHb]),
      by valid_access hpre.stack.valid [hb]⟩)
  exact ⟨v, r, b8000b0d0_pc h, by rw [b8000b0d0_x20 h, e], by rw [b8000b0d0_x22 h, e],
    b8000b0d0_mem_same h, keepsOf (b8000b0d0_keeps h) (by decide)⟩

end Rv64Verifier.Proofs.Pcs.Vso
