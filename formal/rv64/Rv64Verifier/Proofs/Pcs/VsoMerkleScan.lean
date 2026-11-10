import Rv64Verifier.Proofs.Pcs.VsoPaths

/-!
# `verify_stacked_opening`'s Merkle checks: the shape scans

Before any path is hashed, two scans over the phase's `n` paths from `P`: at `0x8000aa80` every
leaf's length (`+16`) is `a2` and every siblings' count (`+40`) is `s0`, else the `Err` at
`0x8000b830` (`scan1`); at `0x8000aab0` every leaf index (`+48`) is the query at `Q`, else the
`Err` at `0x8000b83c` (`scan2`). Neither writes memory.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem keepsOf {t v : MachineState} {L K : List Reg} (k : ∀ r ∈ L, v.getReg r = t.getReg r)
    (hsub : ∀ r ∈ K, r ∈ L) : ∀ r ∈ K, v.getReg r = t.getReg r := fun r hr ↦ k r (hsub r hr)

theorem keepsTrans {t v w : MachineState} {K : List Reg} (h1 : ∀ r ∈ K, v.getReg r = t.getReg r)
    (h2 : ∀ r ∈ K, w.getReg r = v.getReg r) : ∀ r ∈ K, w.getReg r = t.getReg r :=
  fun r hr ↦ (h2 r hr).trans (h1 r hr)

theorem ofNat_ne_zero {m : ℕ} (h0 : 0 < m) (h : m < 2 ^ 64) : BitVec.ofNat 64 m ≠ 0 := by
  intro h'
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
  exact absurd this (by simp; omega)

theorem ofNat_sub_mul {c m : ℕ} (hm : 1 ≤ m) (h : c * m < 2 ^ 64) :
    BitVec.ofNat 64 (c * m) - BitVec.ofNat 64 c = BitVec.ofNat 64 (c * (m - 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : c ≤ c * m := Nat.le_mul_of_pos_right c hm
  rw [Nat.mul_sub_one]
  obtain ⟨x, hx⟩ : ∃ x, x = c * m := ⟨_, rfl⟩
  rw [← hx] at h1 h ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem addr8 (Q : Word) (j : ℕ) :
    Q + BitVec.ofNat 64 (8 * j) + 8 = Q + BitVec.ofNat 64 (8 * (j + 1)) := by
  rw [BitVec.add_assoc, show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
    show 8 * j + 8 = 8 * (j + 1) by ring]

/-- The registers the first scan keeps. -/
def KS1 : List Reg :=
  [.x2, .x5, .x8, .x9, .x10, .x11, .x12, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
    .x26, .x27]

/-- **The leaves' and the siblings' shape**, from path `j` on. -/
theorem scan1 {u : MachineState} {P : Word} {n : ℕ} (hPn : P.toNat + 56 * n < 2 ^ 64)
    (hv : ∀ j < n, Region (P + BitVec.ofNat 64 (56 * j)) 56) :
    ∀ k j t, n - j = k → j ≤ n → t.pc = 0x8000aa80 →
      t.getReg .x13 = BitVec.ofNat 64 (56 * (n - j)) →
      t.getReg .x14 = P + BitVec.ofNat 64 (56 * j) → (∀ a, t.getMem a = u.getMem a) →
      ∃ v, Reaches Image.code t v ∧ (∀ a, v.getMem a = u.getMem a) ∧
        (∀ r ∈ KS1, v.getReg r = t.getReg r) ∧
        (v.pc = 0x8000b830 ∨ (v.pc = 0x8000aaa0 ∧ ∀ i, j ≤ i → i < n →
          u.getMem (P + BitVec.ofNat 64 (56 * i) + 16) = t.getReg .x12 ∧
          u.getMem (P + BitVec.ofNat 64 (56 * i) + 40) = t.getReg .x8))
  | 0, j, t, hk, hj, hpc, h13, _, hm => by
    have hjn : j = n := by omega
    obtain ⟨v, r, h⟩ := Sym.BlockSpec.reaches b8000aa80_spec hpc trivial
    refine ⟨v, r, fun a ↦ by rw [b8000aa80_mem_same h, hm], keepsOf (b8000aa80_keeps h) (by decide),
      Or.inr ⟨b8000aa80_pc_taken h (by rw [h13, hjn, Nat.sub_self]; rfl),
        fun i h1 h2 ↦ absurd h2 (by omega)⟩⟩
  | k + 1, j, t, hk, hj, hpc, h13, h14, hm => by
    have hjn : j < n := by omega
    have hP := Region.bounds (hv j hjn)
    obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000aa80_spec hpc trivial
    have k1 := keepsOf (K := KS1 ++ [.x13, .x14]) (b8000aa80_keeps h1) (by decide)
    have pc1 := b8000aa80_pc_not_taken h1 (by rw [h13]; exact ofNat_ne_zero (by omega) (by omega))
    have x14₁ : t1.getReg .x14 = P + BitVec.ofNat 64 (56 * j) := by
      rw [k1 .x14 (by decide), h14]
    obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000aa84_spec pc1 (by
      rv_eval [x14₁]
      exact Region.valid (hv j hjn) (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP]))
    have m12 : ∀ a, t1.getMem a = u.getMem a := fun a ↦ by rw [b8000aa80_mem_same h1, hm]
    rcases eq_or_ne (t1.getMem (t1.getReg .x14 + 16)) (t1.getReg .x12) with he | he
    swap
    · refine ⟨t2, r1.trans r2, fun a ↦ by rw [b8000aa84_mem_same h2, m12],
        keepsTrans (fun r hr ↦ k1 r (List.mem_append_left _ hr))
          (keepsOf (b8000aa84_keeps h2) (by decide)), Or.inl (b8000aa84_pc_taken h2 he)⟩
    have k2 := keepsOf (K := KS1 ++ [.x13, .x14]) (b8000aa84_keeps h2) (by decide)
    have m2 : ∀ a, t2.getMem a = u.getMem a := fun a ↦ by rw [b8000aa84_mem_same h2, m12]
    have x14₂ : t2.getReg .x14 = P + BitVec.ofNat 64 (56 * j) := by
      rw [k2 .x14 (by decide), x14₁]
    obtain ⟨t3, r3, h3⟩ := Sym.BlockSpec.reaches b8000aa8c_spec (b8000aa84_pc_not_taken h2 he) (by
      rv_eval [x14₂]
      exact Region.valid (hv j hjn) (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP]))
    have k3 := keepsOf (K := KS1) (b8000aa8c_keeps h3) (by decide)
    have m3 : ∀ a, t3.getMem a = u.getMem a := fun a ↦ by rw [b8000aa8c_mem_same h3, m2]
    have k123 : ∀ r ∈ KS1, t3.getReg r = t.getReg r :=
      keepsTrans (keepsTrans (fun r hr ↦ k1 r (List.mem_append_left _ hr))
        (fun r hr ↦ k2 r (List.mem_append_left _ hr))) k3
    rcases eq_or_ne (t2.getMem (t2.getReg .x14 + 40)) (t2.getReg .x8) with he' | he'
    swap
    · obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000aa9c_spec (b8000aa8c_pc_not_taken h3 he')
        trivial
      exact ⟨t4, r1.trans (r2.trans (r3.trans r4)), fun a ↦ by rw [b8000aa9c_mem_same h4, m3],
        keepsTrans k123 (keepsOf (b8000aa9c_keeps h4) (by decide)), Or.inl (b8000aa9c_pc h4)⟩
    obtain ⟨v, r4, mv, kv, hv'⟩ := scan1 hPn hv k (j + 1) t3 (by omega) (by omega)
      (b8000aa8c_pc_taken h3 he')
      (by
        rw [b8000aa8c_x13 h3, k2 .x13 (by decide), k1 .x13 (by decide), h13,
          show (56 : Word) = BitVec.ofNat 64 56 from rfl, ofNat_sub_mul (by omega) (by omega), Nat.sub_sub])
      (by rw [b8000aa8c_x14 h3, x14₂, addr56]) m3
    have x12₃ : t3.getReg .x12 = t.getReg .x12 := k123 .x12 (by decide)
    have x8₃ : t3.getReg .x8 = t.getReg .x8 := k123 .x8 (by decide)
    refine ⟨v, r1.trans (r2.trans (r3.trans r4)), mv, keepsTrans k123 kv, ?_⟩
    rcases hv' with hpc' | ⟨hpc', hall⟩
    · exact Or.inl hpc'
    refine Or.inr ⟨hpc', fun i h1 h2 ↦ ?_⟩
    rcases Nat.lt_or_ge j i with hlt | hle
    · rw [← x12₃, ← x8₃]; exact hall i hlt h2
    · rw [show i = j by omega]
      refine ⟨?_, ?_⟩
      · rw [← m12, ← x14₁, he, k1 .x12 (by decide)]
      · rw [← m2, ← x14₂, he', k2 .x8 (by decide), k1 .x8 (by decide)]

/-- The registers the second scan keeps. -/
def KS2 : List Reg :=
  [.x2, .x5, .x9, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- **The leaf indices are the queries**, from path `j` on. -/
theorem scan2 {u : MachineState} {P Q : Word} {n : ℕ} (hPn : P.toNat + 56 * n < 2 ^ 64)
    (hv : ∀ j < n, Region (P + BitVec.ofNat 64 (56 * j)) 56) (hq : n = 0 ∨ Region Q (8 * n)) :
    ∀ k j t, n - j = k → j ≤ n → t.pc = 0x8000aab0 →
      t.getReg .x10 = BitVec.ofNat 64 (56 * (n - j)) →
      t.getReg .x11 = BitVec.ofNat 64 (8 * (n - j)) →
      t.getReg .x12 = P + BitVec.ofNat 64 (56 * j) → t.getReg .x13 = Q + BitVec.ofNat 64 (8 * j) →
      (∀ a, t.getMem a = u.getMem a) →
      ∃ v, Reaches Image.code t v ∧ (∀ a, v.getMem a = u.getMem a) ∧
        (∀ r ∈ KS2, v.getReg r = t.getReg r) ∧
        (v.pc = 0x8000b83c ∨ (v.pc = 0x8000aad8 ∧ ∀ i, j ≤ i → i < n →
          u.getMem (P + BitVec.ofNat 64 (56 * i) + 48) = u.getMem (Q + BitVec.ofNat 64 (8 * i))))
  | 0, j, t, hk, hj, hpc, h10, _, _, _, hm => by
    have hjn : j = n := by omega
    obtain ⟨v, r, h⟩ := Sym.BlockSpec.reaches b8000aab0_spec hpc trivial
    refine ⟨v, r, fun a ↦ by rw [b8000aab0_mem_same h, hm], keepsOf (b8000aab0_keeps h) (by decide),
      Or.inr ⟨b8000aab0_pc_taken h (by rw [h10, hjn, Nat.sub_self]; rfl),
        fun i h1 h2 ↦ absurd h2 (by omega)⟩⟩
  | k + 1, j, t, hk, hj, hpc, h10, h11, h12, h13, hm => by
    have hjn : j < n := by omega
    have hP := Region.bounds (hv j hjn)
    have hQ : Q.toNat + 8 * n ≤ 0xc0000000 ∧ Q.toNat % 8 = 0 ∧ 0x20 ≤ Q.toNat := by
      rcases hq with h0 | h0
      · omega
      · have := Region.bounds h0; omega
    obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000aab0_spec hpc trivial
    have k1 := b8000aab0_keeps h1
    have pc1 := b8000aab0_pc_not_taken h1 (by rw [h10]; exact ofNat_ne_zero (by omega) (by omega))
    obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000aab4_spec pc1 trivial
    have k2 := b8000aab4_keeps h2
    have pc2 := b8000aab4_pc_not_taken h2 (by
      rw [k1 .x11 (by decide), h11]; exact ofNat_ne_zero (by omega) (by omega))
    have x12₂ : t2.getReg .x12 = P + BitVec.ofNat 64 (56 * j) := by
      rw [k2 .x12 (by decide), k1 .x12 (by decide), h12]
    have x13₂ : t2.getReg .x13 = Q + BitVec.ofNat 64 (8 * j) := by
      rw [k2 .x13 (by decide), k1 .x13 (by decide), h13]
    obtain ⟨t3, r3, h3⟩ := Sym.BlockSpec.reaches b8000aab8_spec pc2 (by
      rv_eval [x12₂, x13₂]
      have hQr : Region Q (8 * n) := by
        rcases hq with h0 | h0
        · omega
        · exact h0
      exact ⟨Region.valid hQr (by addr_omega [hQ, hjn]) (by addr_omega [hQ, hjn])
          (by addr_omega [hQ, hjn]),
        Region.valid (hv j hjn) (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])⟩)
    have m2 : ∀ a, t2.getMem a = u.getMem a := fun a ↦ by
      rw [b8000aab4_mem_same h2, b8000aab0_mem_same h1, hm]
    have m3 : ∀ a, t3.getMem a = u.getMem a := fun a ↦ by rw [b8000aab8_mem_same h3, m2]
    have k123 : ∀ r ∈ KS2, t3.getReg r = t.getReg r :=
      keepsTrans (keepsTrans (keepsOf k1 (by decide)) (keepsOf k2 (by decide)))
        (keepsOf (b8000aab8_keeps h3) (by decide))
    rcases eq_or_ne (t2.getMem (t2.getReg .x12 + 48)) (t2.getMem (t2.getReg .x13)) with he | he
    swap
    · obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000aad4_spec (b8000aab8_pc_not_taken h3 he)
        trivial
      exact ⟨t4, r1.trans (r2.trans (r3.trans r4)), fun a ↦ by rw [b8000aad4_mem_same h4, m3],
        keepsTrans k123 (keepsOf (b8000aad4_keeps h4) (by decide)), Or.inl (b8000aad4_pc h4)⟩
    obtain ⟨v, r4, mv, kv, hv'⟩ := scan2 hPn hv hq k (j + 1) t3 (by omega) (by omega)
      (b8000aab8_pc_taken h3 he)
      (by
        rw [b8000aab8_x10 h3, k2 .x10 (by decide), k1 .x10 (by decide), h10,
          show (56 : Word) = BitVec.ofNat 64 56 from rfl, ofNat_sub_mul (by omega) (by omega), Nat.sub_sub])
      (by
        rw [b8000aab8_x11 h3, k2 .x11 (by decide), k1 .x11 (by decide), h11,
          show (8 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_sub_mul (by omega) (by omega), Nat.sub_sub])
      (by rw [b8000aab8_x12 h3, x12₂, addr56]) (by rw [b8000aab8_x13 h3, x13₂, addr8]) m3
    refine ⟨v, r1.trans (r2.trans (r3.trans r4)), mv, keepsTrans k123 kv, ?_⟩
    rcases hv' with hpc' | ⟨hpc', hall⟩
    · exact Or.inl hpc'
    refine Or.inr ⟨hpc', fun i h1 h2 ↦ ?_⟩
    rcases Nat.lt_or_ge j i with hlt | hle
    · exact hall i hlt h2
    · rw [show i = j by omega, ← m2, ← m2, ← x12₂, ← x13₂]
      exact he

end Rv64Verifier.Proofs.Pcs.Vso
