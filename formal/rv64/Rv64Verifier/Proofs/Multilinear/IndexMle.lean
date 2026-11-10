import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F83

/-!
# `verifier::multilinear::index_mle`

```rust
pub fn index_mle(point: &[E]) -> E {
    let mut result = ONE;
    let mut generator_power = GEN;
    for &challenge in point {
        result *= ONE + challenge * (ONE + generator_power);
        generator_power = generator_power.square();
    }
    result
}
```

compiled at `0x80010cd4` (`Blocks/F83.lean`), with `S` the entry's `sp`: `result` at `S - 152`,
`generator_power` at `S - 128`. `0x80010cd4` makes a 160-byte frame and sets both; `0x80010d10`
puts the point's end in `s1`; the loop, at the challenge `a1`: `ONE + g` at `S - 56` and
`mul` into `S - 80` (`0x80010d4c`), `ONE +` that at `S - 104` and `mul(result, ..)` into `S - 56`
(`0x80010d7c`), the product to `result` and `E::square(g)` into `S - 56` (`0x80010dac`), the
square to `g` and the next challenge (`0x80010dd4`); `0x80010df4` copies `result` out and
returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.IndexMle
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.FieldContracts Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F83
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

@[rv_addr] def len (s : MachineState) : Nat := (s.getReg .x12).toNat

def point (s : MachineState) : List E := eListAt s (s.getReg .x11) (len s)

/-- One iteration on `(result, generator_power)`. -/
def step (acc : E × E) (c : E) : E × E := (acc.1 * (1 + c * (1 + acc.2)), acc.2 ^ 2)

/-- The state after `k` challenges. -/
def st (s : MachineState) (k : Nat) : E × E := ((point s).take k).foldl step (1, gen)

def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem mem_of_kept {r : Reg} (h : r ∈ kept) (l : List Reg)
    (hl : ∀ r ∈ kept, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- The stack below the saved registers. -/
@[rv_addr] def locals (s : MachineState) : Word := stackLo s indexMleStack
@[rv_addr] def localsSize : Nat := indexMleStack - 32

structure FrameInv (s t : MachineState) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 160
  ret : t.getReg .x8 = s.getReg .x10
  kept : ∀ r ∈ kept, t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  mem : MemFrame s t (stackLo s indexMleStack) indexMleStack

structure LoopInv (s t : MachineState) (k : Nat) : Prop extends FrameInv s t where
  res : eAt t (s.getReg .x2 - 152) = (st s k).1
  gp : eAt t (s.getReg .x2 - 128) = (st s k).2
  lt : k < len s
  pc : t.pc = 0x80010d4c
  x11 : t.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (24 * k)
  x9 : t.getReg .x9 = s.getReg .x11 + BitVec.ofNat 64 (24 * len s)

structure ExitInv (s t : MachineState) : Prop extends FrameInv s t where
  pc : t.pc = 0x80010df4
  res : eAt t (s.getReg .x2 - 152) = Model.indexMleRust (point s)

theorem sp_bounds {s : MachineState} (h : IndexMlePre s) :
    1216 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  simp only [indexMleStack, mulStack] at this
  omega

theorem limbs_gen : Model.limbs gen = (2, 0, 0) := by decide +kernel

theorem st_zero (s : MachineState) : st s 0 = (1, gen) := by simp [st]

theorem st_succ {s : MachineState} {k : Nat} (hk : k < len s) :
    st s (k + 1) = step (st s k) (eAt s (s.getReg .x11 + BitVec.ofNat 64 (24 * k))) := by
  unfold st
  rw [List.take_succ_eq_append_getElem (by rw [point, eListAt_length]; exact hk),
    List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, point, eListAt_getElem]

theorem st_len (s : MachineState) : (st s (len s)).1 = Model.indexMleRust (point s) := by
  rw [st, List.take_of_length_le (by simp [point, eListAt_length])]
  rfl

/-- `eAt` across `mul`, apart from what it writes. -/
theorem mul_eAt {u v : MachineState} (h : MulPost u v) {p : Word}
    (h₁ : Apart p 24 (u.getReg .x10) 24) (h₂ : Apart p 24 (stackLo u mulStack) mulStack)
    (hw : p.toNat + 24 ≤ 2 ^ 64) : eAt v p = eAt u p := by
  unfold eAt
  rw [h.frame p (by addr_omega [h₁, hw]) (by addr_omega [h₂, hw]),
    h.frame (p + 8) (by addr_omega [h₁, hw]) (by addr_omega [h₂, hw]),
    h.frame (p + 16) (by addr_omega [h₁, hw]) (by addr_omega [h₂, hw])]

/-- `1 + x` from `x`'s limbs, `c0` flipped. -/
theorem one_add_eAt {t u : MachineState} {a b : Word} (h₀ : t.getMem a = u.getMem b ^^^ 1)
    (h₁ : t.getMem (a + 8) = u.getMem (b + 8)) (h₂ : t.getMem (a + 16) = u.getMem (b + 16)) :
    eAt t a = 1 + eAt u b := by
  apply eAt_eq_of_limbs
  rw [limbs_add, limbs_one, limbs_eAt, h₀, h₁, h₂]
  simp only [Prod.mk.injEq]
  refine ⟨BitVec.xor_comm _ _, ?_, ?_⟩ <;> exact (BitVec.zero_xor).symm

/-- A frame invariant carries over a block that writes nothing. -/
theorem FrameInv.of_same {s t u : MachineState} (h : FrameInv s t)
    (hm : ∀ a, u.getMem a = t.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
      u.getReg r = t.getReg r) : FrameInv s u where
  sp := (hr _ (by decide)).trans h.sp
  ret := (hr _ (by decide)).trans h.ret
  kept r hr' := (hr r (mem_of_kept hr' _)).trans (h.kept r hr')
  ra := (hm _).trans h.ra
  s0 := (hm _).trans h.s0
  s1 := (hm _).trans h.s1
  s2 := (hm _).trans h.s2
  mem a ha := (hm a).trans (h.mem a ha)

/-! ## Entry -/

theorem setup {s : MachineState} (hpc : s.pc = 0x80010cd4) (hpre : IndexMlePre s) :
    ∃ t, Reaches Image.code s t ∧ (ExitInv s t ∨ LoopInv s t 0) := by
  have hsp := sp_bounds hpre
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010cd4_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsp])
  have k₁ := b80010cd4_keeps h₁
  have hm₁ := b80010cd4_frame h₁ (by addr_omega [hsp])
  have r₀ := b80010cd4_m_x2_n152 h₁
  have r₁ := b80010cd4_m_x2_n144 h₁
  have r₂ := b80010cd4_m_x2_n136 h₁
  have g₀ := b80010cd4_m_x2_n128 h₁
  have g₁ := b80010cd4_m_x2_n120 h₁
  have g₂ := b80010cd4_m_x2_n112 h₁
  have hf : FrameInv s t₁ := {
    sp := b80010cd4_x2 h₁
    ret := b80010cd4_x8 h₁
    kept := fun r hr ↦ k₁ r (mem_of_kept hr _)
    ra := b80010cd4_m_x2_n8 h₁
    s0 := b80010cd4_m_x2_n16 h₁
    s1 := b80010cd4_m_x2_n24 h₁
    s2 := b80010cd4_m_x2_n32 h₁
    mem := hm₁.mono fun a ha ↦ by addr_omega [ha, hsp] }
  have hres : eAt t₁ (s.getReg .x2 - 152) = 1 := by
    apply eAt_eq_of_limbs
    rv_eval [r₀, r₁, r₂, limbs_one]
  have hgp : eAt t₁ (s.getReg .x2 - 128) = gen := by
    apply eAt_eq_of_limbs
    rv_eval [g₀, g₁, g₂, limbs_gen]
  by_cases h0 : s.getReg .x12 = 0
  · refine ⟨t₁, hr₁, Or.inl { toFrameInv := hf, pc := b80010cd4_pc_taken h₁ h0, res := ?_ }⟩
    rw [hres, show point s = [] by simp [point, len, h0, eListAt]]
    rfl
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010d10_spec
      (b80010cd4_pc_not_taken h₁ h0) trivial
    have hP := ValidMemRange.bounds hpre.point (by bv_omega)
    have hx9 : t₂.getReg .x9 = s.getReg .x11 + BitVec.ofNat 64 (24 * len s) := by
      rw [h₂.reg .x9 rfl]
      rv_eval [k₁ .x11 (by decide), k₁ .x12 (by decide)]
      exact end_ptr _ _ (by bv_omega) (by omega)
    have hm₂ := b80010d10_mem_same h₂
    have k₂ := b80010d10_keeps h₂
    refine ⟨t₂, hr₁.trans hr₂, Or.inr {
      toFrameInv := hf.of_same hm₂ (h₂.keeps rfl)
      res := by rw [st_zero, ← hres]; unfold eAt; rw [hm₂, hm₂, hm₂]
      gp := by rw [st_zero, ← hgp]; unfold eAt; rw [hm₂, hm₂, hm₂]
      lt := by addr_omega [h0]
      pc := b80010d10_pc h₂
      x11 := by rw [k₂ .x11 (by decide), k₁ .x11 (by decide)]; simp
      x9 := hx9 }⟩

/-! ## The loop -/

def measure (t : MachineState) : Nat := (t.getReg .x9).toNat - (t.getReg .x11).toNat

def Done (s t : MachineState) : Prop := ExitInv s t ∨ Dead Image.code t

set_option maxHeartbeats 4000000 in
theorem body (hMul : MulSpec) (hSq : ESquareSpec) {s : MachineState} (hpre : IndexMlePre s)
    (t : MachineState) (hinv : ∃ k, LoopInv s t k) :
    (∃ u, Reaches Image.code t u ∧ Done s u) ∨
      (∃ u, Reaches Image.code t u ∧ (∃ k, LoopInv s u k) ∧ measure u < measure t) := by
  obtain ⟨k, ht⟩ := hinv
  have hsp := sp_bounds hpre
  have hk := ht.lt
  have hP := ValidMemRange.bounds hpre.point (by simp only [len] at hk; omega)
  have hps := hpre.pointStack
  have hval := hpre.stack.valid
  obtain ⟨pC, hpC⟩ : ∃ p, p = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := ⟨_, rfl⟩
  have hx11 : t.getReg .x11 = pC := by rw [ht.x11, hpC]
  have hS (a : Word) (h : Apart a 24 (stackLo s indexMleStack) indexMleStack)
      (hw : a.toNat + 24 ≤ 2 ^ 64) :
      eAt t a = eAt s a := ht.mem.eAt h hw
  have ec : eAt t pC = eAt s pC :=
    hS pC (by addr_omega [hpC, hk, hP, hps, hsp]) (by addr_omega [hpC, hk, hP])
  -- `ONE + g`, then `mul(challenge, ..)` into `S - 80`
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80010d4c_spec ht.pc (by
    rv_eval [ht.sp]
    and_intros <;> valid_access hval [hsp])
  have k₁ := b80010d4c_keeps h₁
  have hu2 : u.getReg .x2 = s.getReg .x2 - 160 := (k₁ .x2 (by decide)).trans ht.sp
  have hu10 := b80010d4c_x10 h₁
  have hu12 := b80010d4c_x12 h₁
  have hu11 : u.getReg .x11 = pC := (k₁ .x11 (by decide)).trans hx11
  have hu18 := b80010d4c_x18 h₁
  have a₀ := b80010d4c_m_x2_104 h₁
  have a₁ := b80010d4c_m_x2_112 h₁
  have a₂ := b80010d4c_m_x2_120 h₁
  have hm₁ := b80010d4c_frame h₁ (by rw [ht.sp]; addr_omega [hsp])
  rv_eval [ht.sp, hx11] at hu10 hu12 hu18 a₀ a₁ a₂ hm₁
  have e₁ : eAt u (s.getReg .x2 - 56) = 1 + (st s k).2 := by
    rw [← ht.gp]; exact one_add_eAt (by rw [a₀]) (by rv_eval [a₁]) (by rv_eval [a₂])
  have hu (a : Word) (h : Apart a 24 (s.getReg .x2 - 56) 24) (hw : a.toNat + 24 ≤ 2 ^ 64) :
      eAt u a = eAt t a := hm₁.eAt h hw
  have hpre₁ : MulPre u := {
    out := by rw [hu10]; valid_sub hval [hsp]
    lhs := by rw [hu11]; valid_sub hpre.point [hpC, hk, hP]
    rhs := by rw [hu12]; valid_sub hval [hsp]
    stack := ⟨by valid_sub hval [hsp, hu2], by addr_omega [hsp, hu2]⟩
    outLhs := by rw [hu10, hu11]; addr_omega [hsp, hpC, hk, hP, hps]
    outRhs := by rw [hu10, hu12]; addr_omega [hsp]
    outStack := by addr_omega [hsp, hu10, hu2]
    lhsStack := by rw [hu11]; addr_omega [hsp, hu2, hpC, hk, hP, hps]
    rhsStack := by rw [hu12]; addr_omega [hsp, hu2]
    rodata := hpre.rodata.frame (ht.mem.trans hm₁ fun a ha ↦ by addr_omega [ha, hsp])
      (by addr_omega [hsp, hpre.stackRodata])
    stackRodata := by addr_omega [hsp, hu2, hpre.stackRodata] }
  obtain ⟨v, hr₂, ⟨hvpc, hpres₁, hpost₁⟩ | hdead⟩ := hMul.call hr₁ (b80010d4c_pc h₁) hpre₁
  swap
  · exact Or.inl ⟨v, hr₂, Or.inr hdead⟩
  have hv2 : v.getReg .x2 = s.getReg .x2 - 160 := (hpres₁.reg .x2).trans hu2
  have hprod₁ := hpost₁.value
  rw [hu10, hu11, hu12, e₁, hu pC (by addr_omega [hpC, hk, hP, hps, hsp])
    (by addr_omega [hpC, hk, hP]), ec] at hprod₁
  have hv (a : Word) (h₁ : Apart a 24 (s.getReg .x2 - 80) 24)
      (h₂ : Apart a 24 (s.getReg .x2 - 1184) 1024) (hw : a.toNat + 24 ≤ 2 ^ 64) :
      eAt v a = eAt u a :=
    mul_eAt hpost₁ (by rw [hu10]; exact h₁) (by addr_omega [h₂, hu2, hsp]) hw
  -- `ONE +` the product, then `mul(result, ..)` into `S - 56`
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010d7c_spec
    (by rw [hvpc, returnAddress_eq, b80010d4c_x1 h₁]; decide +kernel) (by
      rv_eval [hv2]
      and_intros <;> valid_access hval [hsp])
  have k₃ := b80010d7c_keeps h₃
  have hw2 : w.getReg .x2 = s.getReg .x2 - 160 := (k₃ .x2 (by decide)).trans hv2
  have hw10 := b80010d7c_x10 h₃
  have hw11 := b80010d7c_x11 h₃
  have hw12 := b80010d7c_x12 h₃
  have b₀ := b80010d7c_m_x2_56 h₃
  have b₁ := b80010d7c_m_x2_64 h₃
  have b₂ := b80010d7c_m_x2_72 h₃
  have hm₃ := b80010d7c_frame h₃ (by rw [hv2]; addr_omega [hsp])
  rv_eval [hv2] at hw10 hw11 hw12 b₀ b₁ b₂ hm₃
  have e₃ : eAt w (s.getReg .x2 - 104) = 1 + eAt s pC * (1 + (st s k).2) := by
    rw [← hprod₁]; exact one_add_eAt (by rw [b₀]) (by rv_eval [b₁]) (by rv_eval [b₂])
  have eres : eAt w (s.getReg .x2 - 152) = (st s k).1 := by
    rw [hm₃.eAt (by addr_omega [hsp]) (by addr_omega [hsp]),
      hv _ (by addr_omega [hsp]) (by addr_omega [hsp]) (by addr_omega [hsp]),
      hu _ (by addr_omega [hsp]) (by addr_omega [hsp]), ht.res]
  have egp : eAt w (s.getReg .x2 - 128) = (st s k).2 := by
    rw [hm₃.eAt (by addr_omega [hsp]) (by addr_omega [hsp]),
      hv _ (by addr_omega [hsp]) (by addr_omega [hsp]) (by addr_omega [hsp]),
      hu _ (by addr_omega [hsp]) (by addr_omega [hsp]), ht.gp]
  have hrod₂ : RodataOk w := hpre.rodata.frame
    (((ht.mem.trans hm₁ fun a ha ↦ by addr_omega [ha, hsp]).trans
      (MemFrame.of_two hpost₁.frame (fun a ha ↦ by rw [hu10] at ha; addr_omega [ha, hsp])
        (fun a ha ↦ by addr_omega [ha, hsp, hu2])) fun _ h ↦ h).trans hm₃
      fun a ha ↦ by addr_omega [ha, hsp])
    (by addr_omega [hsp, hpre.stackRodata])
  have hpre₂ : MulPre w := {
    out := by rw [hw10]; valid_sub hval [hsp]
    lhs := by rw [hw11]; valid_sub hval [hsp]
    rhs := by rw [hw12]; valid_sub hval [hsp]
    stack := ⟨by valid_sub hval [hsp, hw2], by addr_omega [hsp, hw2]⟩
    outLhs := by rw [hw10, hw11]; addr_omega [hsp]
    outRhs := by rw [hw10, hw12]; addr_omega [hsp]
    outStack := by addr_omega [hsp, hw10, hw2]
    lhsStack := by rw [hw11]; addr_omega [hsp, hw2]
    rhsStack := by rw [hw12]; addr_omega [hsp, hw2]
    rodata := hrod₂
    stackRodata := by addr_omega [hsp, hw2, hpre.stackRodata] }
  obtain ⟨x, hr₄, ⟨hxpc, hpres₂, hpost₂⟩ | hdead⟩ := hMul.call hr₃ (b80010d7c_pc h₃) hpre₂
  swap
  · exact Or.inl ⟨x, hr₂.trans hr₄, Or.inr hdead⟩
  have hx2 : x.getReg .x2 = s.getReg .x2 - 160 := (hpres₂.reg .x2).trans hw2
  have hprod₂ := hpost₂.value
  rw [hw10, hw11, hw12, e₃, eres] at hprod₂
  -- the product to `result`, then `E::square(g)` into `S - 56`
  obtain ⟨y, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80010dac_spec
    (by rw [hxpc, returnAddress_eq, b80010d7c_x1 h₃]; decide +kernel) (by
      rv_eval [hx2]
      and_intros <;> valid_access hval [hsp])
  have k₅ := b80010dac_keeps h₅
  have hy2 : y.getReg .x2 = s.getReg .x2 - 160 := (k₅ .x2 (by decide)).trans hx2
  have hy10 := b80010dac_x10 h₅
  have hy11 := b80010dac_x11 h₅
  have c₀ := b80010dac_m_x2_8 h₅
  have c₁ := b80010dac_m_x2_16 h₅
  have c₂ := b80010dac_m_x2_24 h₅
  have hm₅ := b80010dac_frame h₅ (by rw [hx2]; addr_omega [hsp])
  rv_eval [hx2] at hy10 hy11 c₀ c₁ c₂ hm₅
  have eres' : eAt y (s.getReg .x2 - 152) = (st s k).1 * (1 + eAt s pC * (1 + (st s k).2)) := by
    rw [← hprod₂]; unfold eAt; rw [c₀]; rv_eval [c₁, c₂]
  have egp' : eAt y (s.getReg .x2 - 128) = (st s k).2 := by
    rw [hm₅.eAt (by addr_omega [hsp]) (by addr_omega [hsp]),
      mul_eAt hpost₂ (by rw [hw10]; addr_omega [hsp]) (by addr_omega [hsp, hw2])
        (by addr_omega [hsp]), egp]
  obtain ⟨z, hr₆, ⟨hzpc, hpres₃, hpost₃⟩ | hdead⟩ := hSq.call hr₅ (b80010dac_pc h₅)
    ⟨by rw [hy10]; valid_sub hval [hsp], by rw [hy11]; valid_sub hval [hsp]⟩
  swap
  · exact Or.inl ⟨z, hr₂.trans (hr₄.trans hr₆), Or.inr hdead⟩
  have hz2 : z.getReg .x2 = s.getReg .x2 - 160 := (hpres₃.reg .x2).trans hy2
  have hsq := hpost₃.value
  rw [hy10, hy11, egp'] at hsq
  have hm₆ := hpost₃.frame
  rw [hy10] at hm₆
  -- the square to `g`, the next challenge
  obtain ⟨z', hr₇, h₇⟩ := Sym.BlockSpec.reaches b80010dd4_spec
    (by rw [hzpc, returnAddress_eq, b80010dac_x1 h₅]; decide +kernel) (by
      rv_eval [hz2]
      and_intros <;> valid_access hval [hsp])
  have k₇ := b80010dd4_keeps h₇
  have d₀ := b80010dd4_m_x2_32 h₇
  have d₁ := b80010dd4_m_x2_40 h₇
  have d₂ := b80010dd4_m_x2_48 h₇
  have hm₇ := b80010dd4_frame h₇ (by rw [hz2]; addr_omega [hsp])
  rv_eval [hz2] at d₀ d₁ d₂ hm₇
  have hnext : st s (k + 1) = ((st s k).1 * (1 + eAt s pC * (1 + (st s k).2)),
      (st s k).2 * (st s k).2) := by
    rw [st_succ hk, ← hpC, step, sq]
  -- memory: everything since `t` within the locals
  have hall : MemFrame t z' (locals s) localsSize :=
    ((((((hm₁.mono fun a ha ↦ by addr_omega [ha, hsp]).trans
      (MemFrame.of_two hpost₁.frame (fun a ha ↦ by rw [hu10] at ha; addr_omega [ha, hsp])
        (fun a ha ↦ by addr_omega [ha, hsp, hu2])) fun _ h ↦ h).trans hm₃
      fun a ha ↦ by addr_omega [ha, hsp]).trans
      (MemFrame.of_two hpost₂.frame (fun a ha ↦ by rw [hw10] at ha; addr_omega [ha, hsp])
        (fun a ha ↦ by addr_omega [ha, hsp, hw2])) fun _ h ↦ h).trans hm₅
      fun a ha ↦ by addr_omega [ha, hsp]).trans hm₆ fun a ha ↦ by addr_omega [ha, hsp]).trans hm₇
      fun a ha ↦ by addr_omega [ha, hsp]
  have hold (a : Word) (ha₁ : (s.getReg .x2).toNat - 32 ≤ a.toNat)
      (ha₂ : a.toNat < (s.getReg .x2).toNat) : z'.getMem a = t.getMem a :=
    hall a (by addr_omega [ha₁, ha₂, hsp])
  have regs (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27]) : z'.getReg r = u.getReg r := by
    have hc : r ∈ calleeSaved := by unfold calleeSaved; exact Runtime.mem_of_mem hr _
    rw [k₇ r (Runtime.mem_of_mem hr _), hpres₃ r hc, k₅ r (Runtime.mem_of_mem hr _), hpres₂ r hc,
      k₃ r (Runtime.mem_of_mem hr _), hpres₁ r hc]
  have hf : FrameInv s z' := {
    sp := by rw [regs .x2 (by decide), hu2]
    ret := by rw [regs .x8 (by decide), k₁ .x8 (by decide), ht.ret]
    kept := fun r hr ↦ by rw [regs r (mem_of_kept hr _), k₁ r (mem_of_kept hr _), ht.kept r hr]
    ra := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.ra
    s0 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s0
    s1 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s1
    s2 := (hold _ (by addr_omega [hsp]) (by addr_omega [hsp])).trans ht.s2
    mem := ht.mem.trans hall fun a h ↦ by addr_omega [h, hsp] }
  have hres : eAt z' (s.getReg .x2 - 152) = (st s (k + 1)).1 := by
    rw [hnext, hm₇.eAt (by addr_omega [hsp]) (by addr_omega [hsp]),
      hm₆.eAt (by addr_omega [hsp]) (by addr_omega [hsp]), eres']
  have hgp : eAt z' (s.getReg .x2 - 128) = (st s (k + 1)).2 := by
    rw [hnext, ← hsq]; unfold eAt; rw [d₀]; rv_eval [d₁, d₂]
  have hz18 : z'.getReg .x18 = pC + 24 := by rw [regs .x18 (by decide), hu18]
  have hz9 : z'.getReg .x9 = s.getReg .x11 + BitVec.ofNat 64 (24 * len s) := by
    rw [regs .x9 (by decide), k₁ .x9 (by decide), ht.x9]
  have hz11 : z'.getReg .x11 = pC + 24 := by
    rw [b80010dd4_x11 h₇, hpres₃.reg .x18, k₅ .x18 (by decide), hpres₂.reg .x18,
      k₃ .x18 (by decide), hpres₁.reg .x18, hu18]
  have hreach := hr₂.trans (hr₄.trans (hr₆.trans hr₇))
  by_cases hlast : k + 1 = len s
  · refine Or.inl ⟨z', hreach, Or.inl {
      toFrameInv := hf
      pc := b80010dd4_pc_not_taken h₇ (by
        rw [hpres₃.reg .x18, k₅ .x18 (by decide), hpres₂.reg .x18, k₃ .x18 (by decide),
          hpres₁.reg .x18, hu18, hpres₃.reg .x9, k₅ .x9 (by decide), hpres₂.reg .x9,
          k₃ .x9 (by decide), hpres₁.reg .x9, k₁ .x9 (by decide), ht.x9]
        addr_omega [hpC, hlast, hP])
      res := by rw [hres, hlast, st_len] }⟩
  · have hk1 : k + 1 < len s := by omega
    refine Or.inr ⟨z', hreach, ⟨k + 1, {
      toFrameInv := hf
      res := hres
      gp := hgp
      lt := hk1
      pc := b80010dd4_pc_taken h₇ (by
        rw [hpres₃.reg .x18, k₅ .x18 (by decide), hpres₂.reg .x18, k₃ .x18 (by decide),
          hpres₁.reg .x18, hu18, hpres₃.reg .x9, k₅ .x9 (by decide), hpres₂.reg .x9,
          k₃ .x9 (by decide), hpres₁.reg .x9, k₁ .x9 (by decide), ht.x9]
        addr_omega [hpC, hk1, hP])
      x11 := by rw [hz11]; addr_omega [hpC, hk1, hP]
      x9 := hz9 }⟩, ?_⟩
    simp only [measure]
    rw [hz9, hz11, ht.x9, hx11]
    addr_omega [hpC, hk1, hP]

/-! ## The epilogue -/

theorem exit {s t : MachineState} (hpre : IndexMlePre s) (ht : ExitInv s t) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧
      eAt u (s.getReg .x10) = Model.indexMleRust (point s) ∧
      ∀ a, ¬ Within a (s.getReg .x10) 24 → ¬ Within a (stackLo s indexMleStack) indexMleStack →
        u.getMem a = s.getMem a := by
  have hsp := sp_bounds hpre
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hrs := hpre.retStack
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80010df4_spec ht.pc (by
    rv_eval [ht.sp, ht.ret]
    and_intros <;> first
      | addr_omega [hsp, hret, hrs]
      | valid_access hpre.stack.valid [hsp]
      | valid_access hpre.ret [hret])
  have k := b80010df4_keeps h
  have pc := b80010df4_pc h
  have x2 := b80010df4_x2 h
  have x8 := b80010df4_x8 h
  have x9 := b80010df4_x9 h
  have x18 := b80010df4_x18 h
  have m₀ := b80010df4_m_x8_0 h
  have m₁ := b80010df4_m_x8_8 h
  have m₂ := b80010df4_m_x8_16 h
  have hm := b80010df4_frame h (by rw [ht.ret]; addr_omega [hret])
  rv_eval [ht.sp, ht.ret, ht.ra, ht.s0, ht.s1, ht.s2] at pc x2 x8 x9 x18 m₀ m₁ m₂ hm
  refine ⟨u, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 ((k _ (by decide)).trans (ht.kept _ (by decide))) fun r hr ↦ ?_,
    ?_, fun a h₁ h₂ ↦ (hm a h₁).trans (ht.mem a h₂)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k _ (by decide)).trans (ht.kept _ (by decide))
  · rw [← ht.res]; unfold eAt; rv_eval [m₀, m₁, m₂]

/-! ## `index_mle` -/

/-- **`index_mle` meets its contract**, given `mul`'s and `E::square`'s. -/
theorem index_mle_spec (hMul : MulSpec) (hSq : ESquareSpec) : IndexMleSpec := by
  intro s hpc hpre
  obtain ⟨t, hst, ht⟩ := setup hpc hpre
  obtain ⟨u, hsu, hu⟩ : ∃ u, Reaches Image.code s u ∧ Done s u := by
    rcases ht with ht | ht
    · exact ⟨t, hst, Or.inl ht⟩
    · obtain ⟨u, htu, hu⟩ := Reaches.loop (fun t ↦ ∃ k, LoopInv s t k) measure (Done s)
        (body hMul hSq hpre) t ⟨0, ht⟩
      exact ⟨u, hst.trans htu, hu⟩
  rcases hu with hu | hdead
  · obtain ⟨v, huv, hvpc, hpres, hval, hframe⟩ := exit hpre hu
    exact ⟨v, hsu.trans huv, Or.inl ⟨hvpc, hpres, hval, hframe⟩⟩
  · exact ⟨u, hsu, Or.inr hdead⟩

end Rv64Verifier.Proofs.Multilinear.IndexMle
