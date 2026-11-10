import Rv64Verifier.Proofs.Runtime.Step
import Rv64Verifier.Blocks.F95

/-!
# `memset`, at `0x800121f4`

`compiler_builtins::mem::memset` (`Blocks/F95.lean`): fewer than 16 bytes are stored one at a time
(`0x8001226c`, then the byte loop at `0x80012278`); otherwise the bytes up to the next multiple of
8 (`0x800121fc`, the byte loop at `0x80012214`), then whole doublewords holding the byte eight
times (`0x80012224`, `0x80012234`, the loop at `0x80012250`), then the rest (`0x8001225c`, the loop
at `0x80012278`). `0x80012288` returns.

The byte loops store at addresses of any alignment, which the generated blocks cannot (`Step.lean`):
`fill_loop` runs one by `step_sb` and an expectation for the three instructions after the store
(`tailE`).
-/

namespace Rv64Verifier.Runtime.Memset
open RiscvZkvm.Rv64 Rv64Verifier.Sym
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def allRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- After a byte store at `L`: the count `rc` down by one, the pointer `rp` up by one, back to `L`
unless the count reached zero. -/
def tailE (L : Word) (rc rp : Reg) : Expect where
  steps := 3
  pc := .ite .ne (.bin .add (.reg rc) (.c 0xffffffffffffffff)) (.c 0) (.c L) (.c (L + 16))
  regs := (rc, .bin .add (.reg rc) (.c 0xffffffffffffffff)) :: (rp, .bin .add (.reg rp) (.c 1)) ::
    (allRegs.filter fun r ↦ decide (r ≠ rc) && decide (r ≠ rp)).map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := []

theorem tail_head : Spec (0x80012214 + 4) (tailE 0x80012214 .x15 .x16) :=
  spec_of 18566 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem tail_tail : Spec (0x80012278 + 4) (tailE 0x80012278 .x12 .x13) :=
  spec_of 18591 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem sb_head : Image.code.fetch 0x80012214 = some (.base (.SB .x16 .x11 0)) :=
  fetch_of (by decide +kernel)
theorem sb_tail : Image.code.fetch 0x80012278 = some (.base (.SB .x13 .x11 0)) :=
  fetch_of (by decide +kernel)

theorem tail_reg {L : Word} {rc rp : Reg} {s t : MachineState} (h : (tailE L rc rp).Holds s t)
    {r : Reg} (h1 : r ≠ rc) (h2 : r ≠ rp) : t.getReg r = s.getReg r := by
  by_cases h0 : r = .x0
  · subst h0; rfl
  refine h.2.1 (r, .reg r) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr
    ⟨r, List.mem_filter.mpr ⟨?_, by simp [h1, h2]⟩, rfl⟩)))
  cases r <;> first | exact absurd rfl h0 | decide

theorem tail_rc {L : Word} {rc rp : Reg} {s t : MachineState} (h : (tailE L rc rp).Holds s t) :
    t.getReg rc = s.getReg rc + 0xffffffffffffffff :=
  h.2.1 _ (List.mem_cons_self ..)

theorem tail_rp {L : Word} {rc rp : Reg} {s t : MachineState} (h : (tailE L rc rp).Holds s t) :
    t.getReg rp = s.getReg rp + 1 :=
  h.2.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

/-- `n` bytes from `dst` being set to `c8`, the first `k` done; nothing else written. -/
structure Filled (s u : MachineState) (dst : Word) (n : Nat) (c8 : BitVec 8) (k : Nat) : Prop where
  bytes : ∀ i < k, byteAt u (dst + BitVec.ofNat 64 i) = c8
  frame : ByteFrame s u (Within · dst n)

/-- A byte loop: `m` more bytes from `dst + k` set to `a1`'s low byte. -/
theorem fill_loop {L : Word} {rc rp : Reg} (hsb : Image.code.fetch L = some (.base (.SB rp .x11 0)))
    (htail : Spec (L + 4) (tailE L rc rp))
    (hr : rc ≠ .x11 ∧ rp ≠ .x11 ∧ rc ≠ rp)
    {s : MachineState} {dst : Word} {n : Nat} (hmap : Mapped dst n) :
    ∀ m u k, u.pc = L → (u.getReg rc).toNat = m → 0 < m → u.getReg rp = dst + BitVec.ofNat 64 k →
      k + m ≤ n → Filled s u dst n ((u.getReg .x11).truncate 8) k →
      ∃ v, Reaches Image.code u v ∧ v.pc = L + 16 ∧ v.getReg rp = dst + BitVec.ofNat 64 (k + m) ∧
        Filled s v dst n ((u.getReg .x11).truncate 8) (k + m) ∧
        ∀ r, r ≠ rc → r ≠ rp → v.getReg r = u.getReg r := by
  have hn := hmap
  simp only [Mapped] at hn
  intro m
  induction m with
  | zero => intro _ _ _ _ h0; omega
  | succ m ih =>
    intro u k hpc hc _ hp hk hf
    have haddr : u.getReg rp + signExtend12 0 = dst + BitVec.ofNat 64 k := by
      rw [show signExtend12 (0 : BitVec 12) = 0 from rfl, Sym.add_zero_lit, hp]
    obtain ⟨u₁, hs₁, hpc₁, hr₁, hb₁, hu₁⟩ := step_sb (hpc ▸ hsb)
      (by rw [haddr]; exact hmap.valid (by omega))
    rw [haddr] at hb₁
    obtain ⟨u₂, hr₂, h₂⟩ := htail.reaches (by rw [hpc₁, hpc]) trivial
    have hm₂ (a : Word) : u₂.getMem a = u₁.getMem a := h₂.frame a (by simp [tailE])
    have hreg (r : Reg) (h1 : r ≠ rc) (h2 : r ≠ rp) : u₂.getReg r = u.getReg r :=
      (tail_reg h₂ h1 h2).trans (hr₁ r)
    have hx11 : u₂.getReg .x11 = u.getReg .x11 := hreg .x11 (Ne.symm hr.1) (Ne.symm hr.2.1)
    have hrp : u₂.getReg rp = dst + BitVec.ofNat 64 (k + 1) := by
      rw [tail_rp h₂, hr₁, hp, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    have hf' : Filled s u₂ dst n ((u.getReg .x11).truncate 8) (k + 1) := by
      refine ⟨fun i hi ↦ ?_, hf.frame.trans ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩ fun _ h ↦ h⟩
      · have hb : byteAt u₂ (dst + BitVec.ofNat 64 i) = byteAt u₁ (dst + BitVec.ofNat 64 i) := by
          simp only [byteAt_eq, hm₂]
        rw [hb, hb₁]
        by_cases hik : i = k
        · subst hik; simp only [↓reduceIte]
        · have hne : dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 k := by
            intro h; apply hik
            have := congrArg BitVec.toNat h
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
            omega
          simp only [hne, ↓reduceIte]
          exact hf.bytes i (by omega)
      · have hb : byteAt u₂ a = byteAt u₁ a := by simp only [byteAt_eq, hm₂]
        rw [hb, hb₁]
        have hne : a ≠ dst + BitVec.ofNat 64 k := fun h ↦ ha (by rw [h]; addr_omega [hn, hk])
        simp only [hne, ↓reduceIte]
      · rw [hm₂, hu₁ a ha]
    have pc₂ := h₂.pc
    rv_eval [hr₁] at pc₂
    have hdec' : (u.getReg rc + 0xffffffffffffffff).toNat = m := by
      rw [BitVec.toNat_add, hc, show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl]
      omega
    have hdec : (u.getReg rc - 1).toNat = m := by
      rw [BitVec.toNat_sub, hc, show (1 : Word).toNat = 1 from rfl]
      omega
    have hu₂ : Reaches Image.code u u₂ := (show Reaches Image.code u u₁ from ⟨1, hs₁⟩).trans hr₂
    rcases eq_ite_cases pc₂ with ⟨hne, hpc₂⟩ | ⟨hne, hpc₂⟩
    · have hm0 : m ≠ 0 := by
        intro h0
        simp only [bne_iff_ne, ne_eq] at hne
        exact hne (BitVec.eq_of_toNat_eq (by rw [hdec, h0]; rfl))
      have hc₂ : (u₂.getReg rc).toNat = m := by rw [tail_rc h₂, hr₁, hdec']
      obtain ⟨v, hrv, hpcv, hrpv, hfv, hregv⟩ := ih u₂ (k + 1) hpc₂ hc₂ (by omega) hrp
        (by omega) (by rw [hx11]; exact hf')
      refine ⟨v, hu₂.trans hrv, hpcv, by rw [hrpv, show k + 1 + m = k + (m + 1) by omega],
        by rw [← hx11, show k + (m + 1) = k + 1 + m by omega]; exact hfv,
        fun r h1 h2 ↦ (hregv r h1 h2).trans (hreg r h1 h2)⟩
    · have hm0 : m = 0 := by
        simp only [bne_iff_ne, ne_eq, Classical.not_not] at hne
        rw [← hdec, hne]; rfl
      subst hm0
      exact ⟨u₂, hu₂, hpc₂, hrp, hf', fun r h1 h2 ↦ hreg r h1 h2⟩

/-! ## The doubleword loop -/

/-- The byte eight times, as `0x80012234` builds it. -/
def rep (c : Word) : Word :=
  ((((c &&& 255#64) <<< 8 ||| c &&& 255#64) <<< 16 |||
      ((c &&& 255#64) <<< 8 ||| c &&& 255#64)) <<< 32) |||
    (((c &&& 255#64) <<< 8 ||| c &&& 255#64) <<< 16 ||| ((c &&& 255#64) <<< 8 ||| c &&& 255#64))

theorem rep_eq {s t : MachineState} (h : Blocks.F95.b80012234.Holds s t) :
    t.getReg .x15 = rep (s.getReg .x11) := by
  have := h.reg .x15 rfl
  simp only [reduceReg, E.eval, BinOp.eval] at this
  rw [this]; rfl

theorem extractByte_rep (c : Word) {i : Nat} (hi : i < 8) : extractByte (rep c) i = c.truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [extractByte, rep, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hk,
    decide_true, Bool.true_and, getLsbD_255]
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The registers `memset` never writes. -/
def keepRegs : List Reg :=
  [.x1, .x2, .x8, .x9, .x10, .x11, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The doubleword loop at `0x80012250`, `j` doublewords done, `x14` the next. -/
structure WordInv (s u : MachineState) (dst : Word) (n h : Nat) (j : Nat) : Prop where
  pc : u.pc = 0x80012250
  x14 : u.getReg .x14 = dst + BitVec.ofNat 64 (h + 8 * j)
  x13 : (u.getReg .x13).toNat = dst.toNat + h + 8 * ((n - h) / 8)
  x15 : u.getReg .x15 = rep (s.getReg .x11)
  x12 : (u.getReg .x12).toNat = n - h
  lt : h + 8 * j + 8 ≤ n
  al : (dst.toNat + h) % 8 = 0
  keep : ∀ r ∈ keepRegs, u.getReg r = s.getReg r
  filled : Filled s u dst n ((s.getReg .x11).truncate 8) (h + 8 * j)

/-- The doubleword loop is over. -/
def WordDone (s u : MachineState) (dst : Word) (n h : Nat) : Prop :=
  u.pc = 0x8001225c ∧ (u.getReg .x13).toNat = dst.toNat + h + 8 * ((n - h) / 8) ∧
    (u.getReg .x12).toNat = n - h ∧ (∀ r ∈ keepRegs, u.getReg r = s.getReg r) ∧
    Filled s u dst n ((s.getReg .x11).truncate 8) (h + 8 * ((n - h) / 8))

theorem word_body {s : MachineState} {dst : Word} {n h : Nat} (hmap : Mapped dst n)
    (u : MachineState) (hu : ∃ j, WordInv s u dst n h j) :
    (∃ v, Reaches Image.code u v ∧ WordDone s v dst n h) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ j, WordInv s v dst n h j) ∧
        (v.getReg .x13).toNat - (v.getReg .x14).toNat <
          (u.getReg .x13).toNat - (u.getReg .x14).toNat) := by
  obtain ⟨j, hj⟩ := hu
  have hm := hmap
  simp only [Mapped] at hm
  have hlt := hj.lt
  have hal := hj.al
  have hx14 := hj.x14
  have hx13 := hj.x13
  obtain ⟨v, hr, hv⟩ := Sym.BlockSpec.reaches Blocks.F95.b80012250_spec hj.pc (by
    rv_eval [hx14]
    exact hmap.valid8 (by addr_omega [hlt, hm]) (by addr_omega [hlt, hm]) (by addr_omega [hlt, hm, hal]))
  have kv := Blocks.F95.b80012250_keeps hv
  have hw := Blocks.F95.b80012250_m_x14_0 hv
  have hfr := Blocks.F95.b80012250_frame hv (by rw [hx14]; addr_omega [hlt, hm])
  rw [hx14, hj.x15] at hw
  rw [hx14] at hfr
  have hun := hv.unaligned (by rv_eval [hx14]; addr_omega [hlt, hm, hal])
  have hfill : Filled s v dst n ((s.getReg .x11).truncate 8) (h + 8 * (j + 1)) := by
    refine ⟨fun i hi ↦ ?_, hj.filled.frame.trans ((ByteFrame.of_memFrame hfr
      (by addr_omega [hlt, hm, hal]) (by decide) hun).mono fun a ha ↦ by addr_omega [ha, hlt, hm])
      fun _ h ↦ h⟩
    by_cases hi' : i < h + 8 * j
    · rw [← hj.filled.bytes i hi', byteAt_eq, byteAt_eq, hfr]
      simp only [Within, toNat_alignDown]
      addr_omega [hi', hlt, hm]
    · rw [byteAt_of_within (b := dst + BitVec.ofNat 64 (h + 8 * j)) (by addr_omega [hlt, hm, hal])
        (by addr_omega [hi, hi', hlt, hm]) (by addr_omega [hi, hlt, hm]), hw, extractByte_rep]
      addr_omega [hi, hi', hlt, hm]
  have hkeep : ∀ r ∈ keepRegs, v.getReg r = s.getReg r :=
    fun r hr' ↦ (kv r (mem_of_mem hr' _)).trans (hj.keep r hr')
  have hx14v : v.getReg .x14 = dst + BitVec.ofNat 64 (h + 8 * (j + 1)) := by
    rw [Blocks.F95.b80012250_x14 hv, hx14]; addr_omega [hlt, hm]
  have hx13v := kv .x13 (by decide)
  have hx12v := kv .x12 (by decide)
  by_cases hlast : h + 8 * (j + 1) + 8 ≤ n
  · refine Or.inr ⟨v, hr, ⟨j + 1, Blocks.F95.b80012250_pc_taken hv ?_, hx14v,
      by rw [hx13v]; exact hx13, by rw [kv .x15 (by decide)]; exact hj.x15,
      by rw [hx12v]; exact hj.x12, hlast, hal, hkeep, hfill⟩, ?_⟩
    · rw [hx14]; addr_omega [hlast, hlt, hm, hx13]
    · rw [hx14v, hx13v, hx14]; addr_omega [hlast, hlt, hm, hx13]
  · have hW : h + 8 * (j + 1) = h + 8 * ((n - h) / 8) := by omega
    refine Or.inl ⟨v, hr, Blocks.F95.b80012250_pc_not_taken hv ?_, by rw [hx13v]; exact hx13,
      by rw [hx12v]; exact hj.x12, hkeep, hW ▸ hfill⟩
    rw [hx14]; addr_omega [hlast, hlt, hm, hx13]

/-! ## `memset` -/

open Rv64Verifier.Blocks.F95

/-- `0x80012288`: return, every byte set. -/
theorem ret {s u : MachineState} (hpc : u.pc = 0x80012288)
    (hk : ∀ r ∈ keepRegs, u.getReg r = s.getReg r)
    (hf : Filled s u (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8)
      (s.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧ MemsetPost s t) ∨
      Dead Image.code t) := by
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b80012288_spec hpc trivial
  have k := b80012288_keeps h
  have hm := b80012288_mem_same h
  refine ⟨t, hr, Or.inl ⟨by rw [b80012288_pc h, hk .x1 (by decide)]; rfl,
    fun r hr' ↦ (k r (mem_of_mem hr' _)).trans (hk r (mem_of_mem hr' _)),
    (k .x10 (by decide)).trans (hk .x10 (by decide)), ?_,
    hf.frame.trans (ByteFrame.of_same hm _) fun _ h ↦ h⟩⟩
  apply List.ext_getElem (by simp [bytesAt_length])
  intro i h1 _
  rw [bytesAt_getElem, List.getElem_replicate]
  rw [bytesAt_length] at h1
  rw [← hf.bytes i h1]
  simp only [byteAt_eq, hm]

/-- From `0x8001225c`: the bytes past the last doubleword. -/
theorem tail {s u : MachineState} {h : Nat} (hmap : Mapped (s.getReg .x10) (s.getReg .x12).toNat)
    (hd : WordDone s u (s.getReg .x10) (s.getReg .x12).toNat h) (hh : h ≤ (s.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧ MemsetPost s t) ∨
      Dead Image.code t) := by
  obtain ⟨hpc, hx13, hx12, hk, hf⟩ := hd
  have hm := hmap
  simp only [Mapped] at hm
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8001225c_spec hpc trivial
  have k₁ := b8001225c_keeps h₁
  have hk₁ : ∀ r ∈ keepRegs, u₁.getReg r = s.getReg r :=
    fun r hr ↦ (k₁ r (mem_of_mem hr _)).trans (hk r hr)
  have hf₁ : Filled s u₁ (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8)
      (h + 8 * (((s.getReg .x12).toNat - h) / 8)) :=
    ⟨fun i hi ↦ by rw [← hf.bytes i hi]; simp only [byteAt_eq, b8001225c_mem_same h₁],
      hf.frame.trans (ByteFrame.of_same (b8001225c_mem_same h₁) _) fun _ h ↦ h⟩
  have hr7 : (u.getReg .x12 &&& 7).toNat = ((s.getReg .x12).toNat - h) % 8 := by
    rw [show u.getReg .x12 &&& 7 = u.getReg .x12 &&& 7#64 from rfl, toNat_and7, hx12]
  by_cases h0 : ((s.getReg .x12).toNat - h) % 8 = 0
  · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80012268_spec
      (b8001225c_pc_not_taken h₁ (by rw [BitVec.toNat_add, hr7, h0]; omega)) trivial
    obtain ⟨t, hr, ht⟩ := ret (b80012268_pc h₂)
      (fun r hr ↦ (b80012268_keeps h₂ r (mem_of_mem hr _)).trans (hk₁ r hr))
      ⟨fun i hi ↦ by
        rw [← hf₁.bytes i (by omega)]; simp only [byteAt_eq, b80012268_mem_same h₂],
        hf₁.frame.trans (ByteFrame.of_same (b80012268_mem_same h₂) _) fun _ h ↦ h⟩
    exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩
  · have hx13w : u₁.getReg .x13 =
        s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (((s.getReg .x12).toNat - h) / 8)) := by
      rw [k₁ .x13 (by decide)]
      apply BitVec.eq_of_toNat_eq
      rw [hx13, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    obtain ⟨v, hrv, hpcv, -, hfv, hregv⟩ := fill_loop sb_tail tail_tail
      (by decide) hmap (((s.getReg .x12).toNat - h) % 8) u₁ _
      (b8001225c_pc_taken h₁ (by rw [BitVec.toNat_add, hr7]; omega))
      (by rw [b8001225c_x12 h₁, hr7]) (by omega) hx13w (by omega)
      (by rw [hk₁ .x11 (by decide)]; exact hf₁)
    rw [hk₁ .x11 (by decide), show h + 8 * (((s.getReg .x12).toNat - h) / 8) +
      ((s.getReg .x12).toNat - h) % 8 = (s.getReg .x12).toNat by omega] at hfv
    obtain ⟨t, hr, ht⟩ := ret hpcv (fun r hr ↦ (hregv r (ne_of_mem_of_not_mem hr (by decide))
      (ne_of_mem_of_not_mem hr (by decide))).trans (hk₁ r hr)) hfv
    exact ⟨t, hr₁.trans (hrv.trans hr), ht⟩

theorem and_not7 (x : Word) : (x &&& (0xfffffffffffffff8 : Word)).toNat = x.toNat - x.toNat % 8 := by
  rw [show (0xfffffffffffffff8 : Word) = ~~~7#64 by decide]
  exact toNat_alignDown x

/-- From `0x80012224`, the first `h` bytes set, `dst + h` aligned, at least 16 bytes: the
doublewords, then the rest. -/
theorem mid {s u : MachineState} {h : Nat} (hmap : Mapped (s.getReg .x10) (s.getReg .x12).toNat)
    (hpc : u.pc = 0x80012224) (hn : 16 ≤ (s.getReg .x12).toNat) (hh : h < 8)
    (hal : ((s.getReg .x10).toNat + h) % 8 = 0)
    (hx13 : (u.getReg .x13).toNat = h) (hx14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 h)
    (hx12 : u.getReg .x12 = s.getReg .x12) (hk : ∀ r ∈ keepRegs, u.getReg r = s.getReg r)
    (hf : Filled s u (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8) h) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧ MemsetPost s t) ∨
      Dead Image.code t) := by
  have hm := hmap
  simp only [Mapped] at hm
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80012224_spec hpc trivial
  have k₁ := b80012224_keeps h₁
  have hsub : (u.getReg .x12 - u.getReg .x13).toNat = (s.getReg .x12).toNat - h := by
    rw [BitVec.toNat_sub, hx12, hx13]; omega
  have hW := and_not7 (u.getReg .x12 - u.getReg .x13)
  rw [hsub] at hW
  have hend : (u.getReg .x14 + ((u.getReg .x12 - u.getReg .x13) &&& (0xfffffffffffffff8 : Word))).toNat =
      (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8) := by
    rw [BitVec.toNat_add, hW, hx14, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80012234_spec
    (b80012224_pc_not_taken h₁ (by
      rw [hend, hx14, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) trivial
  have k₂ := b80012234_keeps h₂
  have hm₂ (a : Word) : u₂.getMem a = u.getMem a :=
    (b80012234_mem_same h₂ a).trans (b80012224_mem_same h₁ a)
  have hinv : WordInv s u₂ (s.getReg .x10) (s.getReg .x12).toNat h 0 := {
    pc := b80012234_pc h₂
    x14 := by rw [k₂ .x14 (by decide), k₁ .x14 (by decide), hx14, Nat.mul_zero, Nat.add_zero]
    x13 := by rw [k₂ .x13 (by decide), b80012224_x13 h₁, hend]
    x15 := by rw [rep_eq h₂, k₁ .x11 (by decide), hk .x11 (by decide)]
    x12 := by rw [k₂ .x12 (by decide), b80012224_x12 h₁, hsub]
    lt := by omega
    al := hal
    keep := fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans ((k₁ r (mem_of_mem hr _)).trans (hk r hr))
    filled := ⟨fun i hi ↦ by rw [← hf.bytes i hi]; simp only [byteAt_eq, hm₂],
      hf.frame.trans (ByteFrame.of_same hm₂ _) fun _ h ↦ h⟩ }
  obtain ⟨v, hrv, hdv⟩ := Reaches.loop (fun u ↦ ∃ j, WordInv s u (s.getReg .x10)
    (s.getReg .x12).toNat h j) (fun u ↦ (u.getReg .x13).toNat - (u.getReg .x14).toNat)
    (WordDone s · (s.getReg .x10) (s.getReg .x12).toNat h) (word_body hmap) u₂ ⟨0, hinv⟩
  obtain ⟨t, hr, ht⟩ := tail hmap hdv (by omega)
  exact ⟨t, hr₁.trans (hr₂.trans (hrv.trans hr)), ht⟩

/-- **`memset` meets its contract.** -/
theorem memset_spec : MemsetSpec 0x800121f4 := by
  intro s hpc hpre
  have hmap : Mapped (s.getReg .x10) (s.getReg .x12).toNat := hpre
  have hm := hmap
  simp only [Mapped] at hm
  have hf0 : Filled s s (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8) 0 :=
    ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), ByteFrame.refl _ _⟩
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800121f4_spec hpc trivial
  have k₁ := b800121f4_keeps h₁
  have hf₁ : ∀ k, Filled s s (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8) k →
      Filled s u₁ (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8) k :=
    fun k hf ↦ ⟨fun i hi ↦ by rw [← hf.bytes i hi]; simp only [byteAt_eq, b800121f4_mem_same h₁],
      hf.frame.trans (ByteFrame.of_same (b800121f4_mem_same h₁) _) fun _ h ↦ h⟩
  by_cases hsmall : (s.getReg .x12).toNat < 16
  · -- one byte at a time
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8001226c_spec
      (b800121f4_pc_taken h₁ hsmall) trivial
    have k₂ := b8001226c_keeps h₂
    have hf₂ : Filled s u₂ (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8) 0 :=
      ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), (hf₁ 0 hf0).frame.trans
        (ByteFrame.of_same (b8001226c_mem_same h₂) _) fun _ h ↦ h⟩
    have hk₂ : ∀ r ∈ keepRegs, u₂.getReg r = s.getReg r :=
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    have hx12 : u₁.getReg .x12 = s.getReg .x12 := k₁ .x12 (by decide)
    have hx10 : u₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
    by_cases h0 : (s.getReg .x12).toNat = 0
    · obtain ⟨t, hr, ht⟩ := ret (b8001226c_pc_taken h₂ (by
        rw [hx12, hx10, BitVec.toNat_add, h0]; omega)) hk₂ (by rw [h0]; rw [h0] at hf₂; exact hf₂)
      exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩
    · obtain ⟨v, hrv, hpcv, -, hfv, hregv⟩ := fill_loop sb_tail tail_tail (by decide) hmap
        (s.getReg .x12).toNat u₂ 0
        (b8001226c_pc_not_taken h₂ (by rw [hx12, hx10, BitVec.toNat_add]; omega))
        (by rw [k₂ .x12 (by decide), hx12]) (by omega)
        (by rw [b8001226c_x13 h₂, hx10]; simp) (by omega)
        (by rw [hk₂ .x11 (by decide)]; exact hf₂)
      rw [hk₂ .x11 (by decide), Nat.zero_add] at hfv
      obtain ⟨t, hr, ht⟩ := ret hpcv (fun r hr ↦ (hregv r (ne_of_mem_of_not_mem hr (by decide))
        (ne_of_mem_of_not_mem hr (by decide))).trans (hk₂ r hr)) hfv
      exact ⟨t, hr₁.trans (hr₂.trans (hrv.trans hr)), ht⟩
  · -- up to a multiple of 8, the doublewords, the rest
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800121fc_spec
      (b800121f4_pc_not_taken h₁ (Nat.le_of_not_lt hsmall)) trivial
    have k₂ := b800121fc_keeps h₂
    have hx10 : u₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
    have hx13 := b800121fc_x13 h₂
    have hx14 := b800121fc_x14 h₂
    rw [hx10] at hx13 hx14
    have hH : (((0 : Word) - s.getReg .x10) &&& (7 : Word)).toNat =
        (2 ^ 64 - (s.getReg .x10).toNat) % 8 := by
      rw [show ((0 : Word) - s.getReg .x10) &&& (7 : Word) = ((0 : Word) - s.getReg .x10) &&& 7#64
        from rfl, toNat_and7, BitVec.toNat_sub]
      have : (0 : Word).toNat = 0 := rfl
      omega
    have hh8 : (2 ^ 64 - (s.getReg .x10).toNat) % 8 < 8 := Nat.mod_lt _ (by decide)
    have hal : ((s.getReg .x10).toNat + (2 ^ 64 - (s.getReg .x10).toNat) % 8) % 8 = 0 := by omega
    have hx14' : u₂.getReg .x14 =
        s.getReg .x10 + BitVec.ofNat 64 ((2 ^ 64 - (s.getReg .x10).toNat) % 8) := by
      rw [hx14]; congr 1; apply BitVec.eq_of_toNat_eq; rw [hH, BitVec.toNat_ofNat]; omega
    have hk₂ : ∀ r ∈ keepRegs, u₂.getReg r = s.getReg r :=
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    have hf₂ : Filled s u₂ (s.getReg .x10) (s.getReg .x12).toNat ((s.getReg .x11).truncate 8) 0 :=
      ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), (hf₁ 0 hf0).frame.trans
        (ByteFrame.of_same (b800121fc_mem_same h₂) _) fun _ h ↦ h⟩
    have hx12 : u₂.getReg .x12 = s.getReg .x12 := (k₂ .x12 (by decide)).trans (k₁ .x12 (by decide))
    by_cases h0 : (2 ^ 64 - (s.getReg .x10).toNat) % 8 = 0
    · obtain ⟨t, hr, ht⟩ := mid hmap (b800121fc_pc_taken h₂ (by
          rw [hx10, BitVec.toNat_add, hH, h0]; omega)) (Nat.le_of_not_lt hsmall) (by decide)
        (by rw [Nat.add_zero]; omega) (by rw [hx13, hH, h0]) (by rw [hx14', h0]) hx12 hk₂ hf₂
      exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩
    · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8001220c_spec
        (b800121fc_pc_not_taken h₂ (by rw [hx10, BitVec.toNat_add, hH]; omega)) trivial
      have k₃ := b8001220c_keeps h₃
      have hk₃ : ∀ r ∈ keepRegs, u₃.getReg r = s.getReg r :=
        fun r hr ↦ (k₃ r (mem_of_mem hr _)).trans (hk₂ r hr)
      obtain ⟨v, hrv, hpcv, -, hfv, hregv⟩ := fill_loop sb_head tail_head (by decide) hmap
        ((2 ^ 64 - (s.getReg .x10).toNat) % 8) u₃ 0 (b8001220c_pc h₃)
        (by rw [b8001220c_x15 h₃, hx13, hH]) (by omega)
        (by rw [b8001220c_x16 h₃, k₂ .x10 (by decide), hx10]; simp) (by omega)
        (by rw [hk₃ .x11 (by decide)]
            exact ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), hf₂.frame.trans
              (ByteFrame.of_same (b8001220c_mem_same h₃) _) fun _ h ↦ h⟩)
      rw [hk₃ .x11 (by decide), Nat.zero_add] at hfv
      have hreg (r : Reg) (hr : r ∈ [Reg.x12, .x13, .x14] ++ keepRegs) : v.getReg r = u₃.getReg r :=
        hregv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
      obtain ⟨t, hr, ht⟩ := mid hmap hpcv (Nat.le_of_not_lt hsmall) hh8 hal
        (by rw [hreg .x13 (by decide), k₃ .x13 (by decide), hx13, hH])
        (by rw [hreg .x14 (by decide), k₃ .x14 (by decide), hx14'])
        (by rw [hreg .x12 (by decide), k₃ .x12 (by decide), hx12])
        (fun r hr ↦ (hreg r (List.mem_append_right _ hr)).trans (hk₃ r hr)) hfv
      exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hrv.trans hr))), ht⟩

end Rv64Verifier.Runtime.Memset
