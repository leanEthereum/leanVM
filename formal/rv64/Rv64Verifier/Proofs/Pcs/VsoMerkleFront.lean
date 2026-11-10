import Rv64Verifier.Proofs.Pcs.VsoMerkleScan

/-!
# `verify_stacked_opening`'s Merkle checks: the front, and the `Err`s

`0x8000aa14` picks the leaf's width factor (`1` at level `0`, else `3`); `0x8000aa28` takes the
next phase of openings, `Err(5)` at `0x8000b860` if none is left; `0x8000aa38` counts it read
(`[x20 + 352]`), loads its header `H` (`x17`): the paths `P` (`x22`, `x14`), their number `n`
(`x11`), `56 n` (`x10`, `x13`), `E = P + 56 n` (`x5`), and the leaf's width `a2` shifted by the
level's fold count at `S - 784`. The `Err`s at `0x8000b830`, `0x8000b83c`, `0x8000b860`,
`0x8000b8d4` return their discriminant through `0x8000b844`, `0x8000b84c` (`errTail`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **An `Err` of the Merkle checks**, to the exit with a discriminant that is no `Ok`. -/
theorem errTail {s v : MachineState} (hpre : VsoPre s) (hsp : v.getReg .x2 = s.getReg .x2 - 1040)
    (hpc : v.pc = 0x8000b830 ∨ v.pc = 0x8000b83c ∨ v.pc = 0x8000b860 ∨ v.pc = 0x8000b8d4) :
    ∃ w, Reaches Image.code v w ∧ w.pc = 0x8000a0bc ∧ w.getReg .x10 ≠ okTag ∧
      w.getReg .x2 = v.getReg .x2 ∧ ∀ a, w.getMem a = v.getMem a := by
  have hb := bounds hpre
  have tail : ∀ t : MachineState, t.pc = 0x8000b844 → t.getReg .x1 ≠ okTag →
      ∃ w, Reaches Image.code t w ∧ w.pc = 0x8000a0bc ∧ w.getReg .x10 ≠ okTag ∧
        w.getReg .x2 = t.getReg .x2 ∧ ∀ a, w.getMem a = t.getMem a := by
    intro t hpc hne
    obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000b844_spec hpc trivial
    obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000b84c_spec (b8000b844_pc h1) trivial
    refine ⟨t2, r1.trans r2, b8000b84c_pc h2, by rw [b8000b84c_x10 h2, b8000b844_x22 h1]; exact hne,
      by rw [b8000b84c_keeps h2 .x2 (by decide), b8000b844_keeps h1 .x2 (by decide)],
      fun a ↦ by rw [b8000b84c_mem_same h2, b8000b844_mem_same h1]⟩
  have fin : ∀ t : MachineState, Reaches Image.code v t → t.pc = 0x8000b844 →
      t.getReg .x1 ≠ okTag → t.getReg .x2 = v.getReg .x2 → (∀ a, t.getMem a = v.getMem a) →
      ∃ w, Reaches Image.code v w ∧ w.pc = 0x8000a0bc ∧ w.getReg .x10 ≠ okTag ∧
        w.getReg .x2 = v.getReg .x2 ∧ ∀ a, w.getMem a = v.getMem a := by
    intro t r hpc hne hsp' hm
    obtain ⟨w, r', hpc', hne', hsp'', hm'⟩ := tail t hpc hne
    exact ⟨w, r.trans r', hpc', hne', hsp''.trans hsp', fun a ↦ (hm' a).trans (hm a)⟩
  rcases hpc with hpc | hpc | hpc | hpc
  · obtain ⟨t, r, h⟩ := Sym.BlockSpec.reaches b8000b830_spec hpc (by
      rv_eval [hsp]; valid_access hpre.stack.valid [hb])
    exact fin t r (b8000b830_pc h) (by rw [b8000b830_x1 h]; decide)
      (b8000b830_keeps h .x2 (by decide)) (b8000b830_mem_same h)
  · obtain ⟨t, r, h⟩ := Sym.BlockSpec.reaches b8000b83c_spec hpc (by
      rv_eval [hsp]; valid_access hpre.stack.valid [hb])
    exact fin t r (b8000b83c_pc h) (by rw [b8000b83c_x1 h]; decide)
      (b8000b83c_keeps h .x2 (by decide)) (b8000b83c_mem_same h)
  · obtain ⟨t, r, h⟩ := Sym.BlockSpec.reaches b8000b860_spec hpc (by
      rv_eval [hsp]; valid_access hpre.stack.valid [hb])
    exact fin t r (b8000b860_pc h) (by rw [b8000b860_x1 h]; decide)
      (b8000b860_keeps h .x2 (by decide)) (b8000b860_mem_same h)
  · obtain ⟨t, r, h⟩ := Sym.BlockSpec.reaches b8000b8d4_spec hpc trivial
    exact fin t r (b8000b8d4_pc h) (by rw [b8000b8d4_x1 h]; decide)
      (b8000b8d4_keeps h .x2 (by decide)) (b8000b8d4_mem_same h)

/-- At `0x8000aa14`: the transcript in `s4`, the level and its fold count in their slots, the
proof's header and the openings' outer header mapped, the phase to read, if any, mapped and apart
from the opening offset. -/
structure FrontIn (s u : MachineState) (ℓ fc : ℕ) : Prop where
  pc : u.pc = 0x8000aa14
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  x20 : u.getReg .x20 = s.getReg .x10
  lvl : u.getMem (s.getReg .x2 - 856) = BitVec.ofNat 64 ℓ
  fold : u.getMem (s.getReg .x2 - 784) = BitVec.ofNat 64 fc
  self : Region (s.getReg .x10) 368
  proof : Region (u.getMem (s.getReg .x10)) 48
  hdr : (u.getMem (s.getReg .x10 + 352)).toNat < (u.getMem (u.getMem (s.getReg .x10) + 40)).toNat →
    Region (u.getMem (u.getMem (s.getReg .x10) + 32) +
      BitVec.ofNat 64 (24 * (u.getMem (s.getReg .x10 + 352)).toNat)) 24 ∧
    Apart (u.getMem (u.getMem (s.getReg .x10) + 32) +
      BitVec.ofNat 64 (24 * (u.getMem (s.getReg .x10 + 352)).toNat)) 24 (s.getReg .x10 + 352) 8

/-- The opening offset `off` and the phase header `H` the front read. -/
def phaseH (s u : MachineState) : Word :=
  u.getMem (u.getMem (s.getReg .x10) + 32) +
    BitVec.ofNat 64 (24 * (u.getMem (s.getReg .x10 + 352)).toNat)

/-- The registers the front keeps. -/
def FR : List Reg := [.x8, .x9, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27]

/-- At `0x8000aa80`, the shape scan's start. -/
structure Front (s u t : MachineState) (ℓ fc : ℕ) : Prop where
  pc : t.pc = 0x8000aa80
  sp : t.getReg .x2 = s.getReg .x2 - 1040
  x5 : t.getReg .x5 = u.getMem (phaseH s u + 8) +
    BitVec.ofNat 64 (56 * (u.getMem (phaseH s u + 16)).toNat)
  x10 : t.getReg .x10 = BitVec.ofNat 64 (56 * (u.getMem (phaseH s u + 16)).toNat)
  x11 : t.getReg .x11 = u.getMem (phaseH s u + 16)
  x12 : t.getReg .x12 = (if ℓ = 0 then 1 else 3 : Word) <<< (fc % 64)
  x13 : t.getReg .x13 = BitVec.ofNat 64 (56 * (u.getMem (phaseH s u + 16)).toNat)
  x14 : t.getReg .x14 = u.getMem (phaseH s u + 8)
  x16 : t.getReg .x16 = BitVec.ofNat 64 ℓ + 1
  x17 : t.getReg .x17 = phaseH s u
  x22 : t.getReg .x22 = u.getMem (phaseH s u + 8)
  regs : ∀ r ∈ FR, t.getReg r = u.getReg r
  off : t.getMem (s.getReg .x10 + 352) = u.getMem (s.getReg .x10 + 352) + 1
  fr : DFrame u t (Within · (s.getReg .x10 + 352) 8)
  hdr : (u.getMem (s.getReg .x10 + 352)).toNat < (u.getMem (u.getMem (s.getReg .x10) + 40)).toNat

theorem mul56 (x : Word) :
    x * 64 - x * 8 = BitVec.ofNat 64 (56 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (64 : Word).toNat = 64 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

/-- **The front**: the `Err` for no phase left, or the scan's start. -/
theorem front {s u : MachineState} {ℓ fc : ℕ} (hpre : VsoPre s) (hf : FrontIn s u ℓ fc)
    (hℓ : ℓ < 2 ^ 64) (hfc : fc < 2 ^ 64) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x8000b860 ∧ t.getReg .x2 = s.getReg .x2 - 1040 ∧
      ∀ a, t.getMem a = u.getMem a) ∨ Front s u t ℓ fc) := by
  have hb := bounds hpre
  have hsp := hf.sp
  have hT := Region.bounds hf.self
  have hPr := Region.bounds hf.proof
  obtain ⟨t1, r1, h1⟩ := Sym.BlockSpec.reaches b8000aa14_spec hf.pc (by
    rv_eval [hsp]; valid_access hpre.stack.valid [hb])
  have k1 := b8000aa14_keeps h1
  have m1 := b8000aa14_mem_same h1
  have e184 : u.getMem (u.getReg .x2 + 184) = BitVec.ofNat 64 ℓ := by
    rw [hsp, show s.getReg .x2 - 1040 + 184 = s.getReg .x2 - 856 by rv_eval []]; exact hf.lvl
  -- the width factor
  obtain ⟨t2, r2, x10₂, k2, m2, pc2⟩ : ∃ t2, Reaches Image.code t1 t2 ∧
      t2.getReg .x10 = (if ℓ = 0 then 1 else 3 : Word) ∧
      (∀ r ∈ [Reg.x2, .x8, .x9, .x15, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
        t2.getReg r = t1.getReg r) ∧
      (∀ a, t2.getMem a = t1.getMem a) ∧ t2.pc = 0x8000aa28 := by
    by_cases h0 : ℓ = 0
    · obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000aa24_spec
        (b8000aa14_pc_taken h1 (by rw [e184, h0]; rfl)) trivial
      exact ⟨t2, r2, by rw [b8000aa24_x10 h2]; simp [h0], keepsOf (b8000aa24_keeps h2) (by decide),
        b8000aa24_mem_same h2, b8000aa24_pc h2⟩
    · obtain ⟨t2, r2, h2⟩ := Sym.BlockSpec.reaches b8000aa1c_spec
        (b8000aa14_pc_not_taken h1 (by rw [e184]; exact ofNat_ne_zero (by omega) hℓ)) trivial
      exact ⟨t2, r2, by rw [b8000aa1c_x10 h2]; simp [h0], keepsOf (b8000aa1c_keeps h2) (by decide),
        b8000aa1c_mem_same h2, b8000aa1c_pc h2⟩
  have m12 : ∀ a, t2.getMem a = u.getMem a := fun a ↦ by rw [m2, m1]
  have x20₂ : t2.getReg .x20 = s.getReg .x10 := by
    rw [k2 .x20 (by simp), k1 .x20 (by decide), hf.x20]
  have sp2 : t2.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [k2 .x2 (by simp), k1 .x2 (by decide), hsp]
  -- the phase
  obtain ⟨t3, r3, h3⟩ := Sym.BlockSpec.reaches b8000aa28_spec pc2 (by
    rv_eval [x20₂, m12]
    exact ⟨Region.valid hf.self (by addr_omega [hT]) (by addr_omega [hT]) (by addr_omega [hT]),
      Region.valid hf.proof (by addr_omega [hPr]) (by addr_omega [hPr]) (by addr_omega [hPr]),
      Region.valid hf.self (by addr_omega [hT]) (by addr_omega [hT]) (by addr_omega [hT])⟩)
  have k3 := b8000aa28_keeps h3
  have m3 : ∀ a, t3.getMem a = u.getMem a := fun a ↦ by rw [b8000aa28_mem_same h3, m12]
  rcases Nat.lt_or_ge (u.getMem (s.getReg .x10 + 352)).toNat
    (u.getMem (u.getMem (s.getReg .x10) + 40)).toNat with hlt | hge
  swap
  · exact ⟨t3, r1.trans (r2.trans r3), Or.inl ⟨b8000aa28_pc_taken h3 (by rw [x20₂, m12, m12, m12]; exact hge),
      by rw [k3 .x2 (by decide), sp2], m3⟩⟩
  obtain ⟨hH0, hHa0⟩ := hf.hdr hlt
  have hH : Region (phaseH s u) 24 := hH0
  have hHa : Apart (phaseH s u) 24 (s.getReg .x10 + 352) 8 := hHa0
  have hHb := Region.bounds hH
  have x11₃ : t3.getReg .x11 = u.getMem (s.getReg .x10 + 352) := by
    rw [b8000aa28_x11 h3, x20₂, m12]
  have x12₃ : t3.getReg .x12 = u.getMem (s.getReg .x10) := by rw [b8000aa28_x12 h3, x20₂, m12]
  have x20₃ : t3.getReg .x20 = s.getReg .x10 := by rw [k3 .x20 (by decide), x20₂]
  have sp3 : t3.getReg .x2 = s.getReg .x2 - 1040 := by rw [k3 .x2 (by decide), sp2]
  have eH : u.getMem (u.getMem (s.getReg .x10) + 32) +
      (u.getMem (s.getReg .x10 + 352) * 16 + u.getMem (s.getReg .x10 + 352) * 8) = phaseH s u := by
    simp only [phaseH]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := (u.getMem (s.getReg .x10 + 352)).isLt
    have hc := (u.getMem (u.getMem (s.getReg .x10) + 40)).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
    omega
  obtain ⟨t4, r4, h4⟩ := Sym.BlockSpec.reaches b8000aa38_spec (b8000aa28_pc_not_taken h3 (by
      rw [x20₂, m12, m12, m12]; exact hlt)) (by
    rv_eval [x11₃, x12₃, x20₃, sp3, m3, eH]
    have hIs := hpre.self.stack
    rw [stackLo_vso, vso_stack] at hIs
    have hw1 : Within (s.getReg .x10 + 352) (s.getReg .x10) 368 := by addr_omega [hT]
    refine ⟨fun h ↦ ?_, by valid_access hpre.stack.valid [hb], fun h ↦ ?_,
      Region.valid hH (by addr_omega [hHb]) (by addr_omega [hHb]) (by addr_omega [hHb]), fun h ↦ ?_,
      Region.valid hH (by addr_omega [hHb]) (by addr_omega [hHb]) (by addr_omega [hHb]),
      Region.valid hf.self (by addr_omega [hT]) (by addr_omega [hT]) (by addr_omega [hT]),
      Region.valid hf.proof (by addr_omega [hPr]) (by addr_omega [hPr]) (by addr_omega [hPr])⟩
    · rw [← h] at hw1; addr_omega [hw1, hIs, hb]
    · have h1 : Within (phaseH s u + 8) (phaseH s u) 24 := by addr_omega [hHb]
      rw [h] at h1; addr_omega [h1, hHa]
    · have h1 : Within (phaseH s u + 16) (phaseH s u) 24 := by addr_omega [hHb]
      rw [h] at h1; addr_omega [h1, hHa])
  have k4 := b8000aa38_keeps h4
  have fr4 := DFrame.of_memFrame (b8000aa38_frame h4 (by rw [x20₃]; addr_omega [hT]))
  rw [x20₃] at fr4
  have off4 := b8000aa38_m_x20_352 h4
  rw [x20₃, x11₃] at off4
  have x5₄ : t4.getReg .x5 = t3.getMem ((t3.getMem (t3.getReg .x12 + 32) +
      (t3.getReg .x11 * 16 + t3.getReg .x11 * 8)) + 8) +
      (t3.getMem ((t3.getMem (t3.getReg .x12 + 32) + (t3.getReg .x11 * 16 + t3.getReg .x11 * 8)) + 16) * 64 -
        t3.getMem ((t3.getMem (t3.getReg .x12 + 32) + (t3.getReg .x11 * 16 + t3.getReg .x11 * 8)) + 16) * 8) :=
    h4.reg_eq .x5 rfl (by rv_eval [])
  have x12₄ : t4.getReg .x12 = t3.getReg .x10 <<< ((t3.getMem (t3.getReg .x2 + 256)).toNat % 64) :=
    h4.reg_eq .x12 rfl (by rv_eval [])
  have e256 : t3.getMem (t3.getReg .x2 + 256) = BitVec.ofNat 64 fc := by
    rw [sp3, m3, show s.getReg .x2 - 1040 + 256 = s.getReg .x2 - 784 by rv_eval []]; exact hf.fold
  simp only [x11₃, x12₃, m3, eH] at x5₄
  refine ⟨t4, r1.trans (r2.trans (r3.trans r4)), Or.inr {
    pc := b8000aa38_pc h4
    sp := by rw [k4 .x2 (by decide), sp3]
    x5 := by rw [x5₄, mul56 _]
    x10 := by rw [b8000aa38_x10 h4]; simp only [x11₃, x12₃, m3, eH]; exact mul56 _
    x11 := by rw [b8000aa38_x11 h4]; simp only [x11₃, x12₃, m3, eH]
    x12 := by
      rw [x12₄, e256, k3 .x10 (by decide), x10₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfc]
    x13 := by rw [b8000aa38_x13 h4]; simp only [x11₃, x12₃, m3, eH]; exact mul56 _
    x14 := by rw [b8000aa38_x14 h4]; simp only [x11₃, x12₃, m3, eH]
    x16 := by
      rw [b8000aa38_x16 h4, k3 .x15 (by decide), k2 .x15 (by simp), b8000aa14_x15 h1, e184]
    x17 := by rw [b8000aa38_x17 h4]; simp only [x11₃, x12₃, m3, eH]
    x22 := by rw [b8000aa38_x22 h4]; simp only [x11₃, x12₃, m3, eH]
    regs := fun r hr ↦ by
      rw [k4 r (mem_of_mem hr _), k3 r (mem_of_mem hr _), k2 r (mem_of_mem hr _),
        k1 r (mem_of_mem hr _)]
    off := by rw [off4]
    fr := (DFrame.of_same m3 _).trans fr4 fun _ h ↦ h
    hdr := hlt }⟩

end Rv64Verifier.Proofs.Pcs.Vso
