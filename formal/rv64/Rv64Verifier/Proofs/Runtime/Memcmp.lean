import Rv64Verifier.Proofs.Runtime.Step
import Rv64Verifier.Blocks.F97

/-!
# `memcmp`, at `0x800126b4`

`compiler_builtins`' byte loop (`Blocks/F97.lean`): `0x800126b4` returns `0` for no bytes; at
`0x800126b8` two `LBU`s (`step_lbu`: the addresses have any alignment) and a branch on their
difference (`bneE`), to `0x800126dc` (return the difference) or `0x800126c4` (advance, and return
`0` at the end through `0x800126d4`).
-/

namespace Rv64Verifier.Runtime.Memcmp
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Blocks.F97
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def allRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- `0x800126c0`: `bne a3, a4`. -/
def bneE : Expect where
  steps := 1
  pc := .ite .ne (.reg .x13) (.reg .x14) (.c 0x800126dc) (.c 0x800126c4)
  regs := allRegs.map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := []

theorem bne_spec : Spec 0x800126c0 bneE :=
  spec_of 18864 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)

theorem lbu_a : Image.code.fetch 0x800126b8 = some (.base (.LBU .x13 .x10 0)) :=
  fetch_of (by decide +kernel)
theorem lbu_b : Image.code.fetch 0x800126bc = some (.base (.LBU .x14 .x11 0)) :=
  fetch_of (by decide +kernel)

theorem bytesAt_succ (s : MachineState) (p : Word) (n : Nat) :
    bytesAt s p (n + 1) = byteAt s p :: bytesAt s (p + 1) n := by
  apply List.ext_getElem (by simp [bytesAt_length])
  intro i h1 h2
  cases i with
  | zero => simp [bytesAt_getElem]
  | succ i =>
    simp only [bytesAt_getElem, List.getElem_cons_succ, BitVec.add_assoc]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (1 : Word).toNat = 1 := rfl
    omega

/-- What `memcmp` returns from `s`. -/
def result (s : MachineState) : Word :=
  cmpBytes (bytesAt s (s.getReg .x10) (s.getReg .x12).toNat)
    (bytesAt s (s.getReg .x11) (s.getReg .x12).toNat)

/-- At `0x800126b8`, `k` bytes equal. -/
structure Inv (s u : MachineState) (k : Nat) : Prop where
  pc : u.pc = 0x800126b8
  x10 : u.getReg .x10 = s.getReg .x10 + BitVec.ofNat 64 k
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 k
  x12 : (u.getReg .x12).toNat = (s.getReg .x12).toNat - k
  lt : k < (s.getReg .x12).toNat
  keep : ∀ r ∈ calleeSaved ++ [.x1], u.getReg r = s.getReg r
  mem : ∀ a, u.getMem a = s.getMem a
  res : result s = cmpBytes (bytesAt s (s.getReg .x10 + BitVec.ofNat 64 k) ((s.getReg .x12).toNat - k))
    (bytesAt s (s.getReg .x11 + BitVec.ofNat 64 k) ((s.getReg .x12).toNat - k))

def Done (s t : MachineState) : Prop :=
  (t.pc = returnAddress s ∧ Preserves s t ∧ MemcmpPost s t) ∨ Dead Image.code t

theorem ret {s u : MachineState} (h : (u.pc = 0x800126d4 ∨ u.pc = 0x800126dc))
    (hk : ∀ r ∈ calleeSaved ++ [.x1], u.getReg r = s.getReg r) (hm : ∀ a, u.getMem a = s.getMem a)
    (hres : (u.pc = 0x800126d4 → result s = 0) ∧
      (u.pc = 0x800126dc → result s = u.getReg .x13 - u.getReg .x14)) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  rcases h with h | h
  · obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b800126d4_spec h trivial
    have k := b800126d4_keeps ht
    exact ⟨t, hr, Or.inl ⟨by rw [b800126d4_pc ht, hk .x1 (by decide)]; rfl,
      fun r hr' ↦ (k r (mem_of_mem hr' _)).trans (hk r (List.mem_append_left _ hr')),
      by rw [b800126d4_x10 ht]; exact (hres.1 h).symm, fun a ↦ (b800126d4_mem_same ht a).trans (hm a)⟩⟩
  · obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b800126dc_spec h trivial
    have k := b800126dc_keeps ht
    exact ⟨t, hr, Or.inl ⟨by rw [b800126dc_pc ht, hk .x1 (by decide)]; rfl,
      fun r hr' ↦ (k r (mem_of_mem hr' _)).trans (hk r (List.mem_append_left _ hr')),
      by rw [b800126dc_x10 ht]; exact (hres.2 h).symm, fun a ↦ (b800126dc_mem_same ht a).trans (hm a)⟩⟩

theorem lbu_other {s t : MachineState} {rd : Reg} {v : Word}
    (h : ∀ r, t.getReg r = if r = rd ∧ rd ≠ .x0 then v else s.getReg r) {r : Reg} (hr : r ≠ rd) :
    t.getReg r = s.getReg r := by
  rw [h r]; simp [hr]

theorem lbu_rd {s t : MachineState} {rd : Reg} {v : Word}
    (h : ∀ r, t.getReg r = if r = rd ∧ rd ≠ .x0 then v else s.getReg r) (h0 : rd ≠ .x0) :
    t.getReg rd = v := by
  rw [h rd]; simp [h0]

theorem zeroExtend_inj {a b : BitVec 8} (h : a.zeroExtend 64 = b.zeroExtend 64) : a = b := by
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth] at this
  have ha := a.isLt
  have hb := b.isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- One byte of each: return their difference, or `0` at the end, or the next byte. -/
theorem body {s : MachineState} (hpre : MemcmpPre s) (u : MachineState) (hu : ∃ k, Inv s u k) :
    (∃ t, Reaches Image.code u t ∧ Done s t) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ k, Inv s v k) ∧
        (v.getReg .x12).toNat < (u.getReg .x12).toNat) := by
  obtain ⟨k, hk⟩ := hu
  have hlt := hk.lt
  have h0 : signExtend12 (0 : BitVec 12) = 0 := rfl
  obtain ⟨u₁, hs₁, hpc₁, hr₁, hm₁⟩ := step_lbu (hk.pc ▸ lbu_a)
    (by rw [h0, Sym.add_zero_lit, hk.x10]; exact hpre.lhs.valid hlt)
  obtain ⟨u₂, hs₂, hpc₂, hr₂, hm₂⟩ := step_lbu (by rw [hpc₁, hk.pc]; exact lbu_b)
    (by rw [h0, Sym.add_zero_lit, lbu_other hr₁ (by decide), hk.x11]; exact hpre.rhs.valid hlt)
  obtain ⟨u₃, hr₃, h₃⟩ := bne_spec.reaches (by rw [hpc₂, hpc₁, hk.pc]; rfl) trivial
  have hreg (r : Reg) (h1 : r ≠ .x13) (h2 : r ≠ .x14) : u₃.getReg r = u.getReg r := by
    by_cases hz : r = .x0
    · subst hz; rfl
    rw [h₃.2.1 (r, .reg r) (List.mem_map.mpr ⟨r, by cases r <;> simp_all [allRegs], rfl⟩)]
    show u₂.getReg r = _
    rw [lbu_other hr₂ h2, lbu_other hr₁ h1]
  have hm₃ (a : Word) : u₃.getMem a = s.getMem a :=
    (h₃.frame a (by simp [bneE])).trans ((hm₂ a).trans ((hm₁ a).trans (hk.mem a)))
  have hb1 : u₂.getReg .x13 = (byteAt s (s.getReg .x10 + BitVec.ofNat 64 k)).zeroExtend 64 := by
    rw [lbu_other hr₂ (by decide), lbu_rd hr₁ (by decide), h0, Sym.add_zero_lit, hk.x10]
    simp only [byteAt_eq, hk.mem]
  have hb2 : u₂.getReg .x14 = (byteAt s (s.getReg .x11 + BitVec.ofNat 64 k)).zeroExtend 64 := by
    rw [lbu_rd hr₂ (by decide), h0, Sym.add_zero_lit, lbu_other hr₁ (by decide), hk.x11]
    simp only [byteAt_eq, hm₁, hk.mem]
  have hkeep (r : Reg) (hr : r ∈ calleeSaved ++ [.x1]) : u₃.getReg r = s.getReg r :=
    (hreg r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))).trans
      (hk.keep r hr)
  have hres := hk.res
  rw [show (s.getReg .x12).toNat - k = ((s.getReg .x12).toNat - k - 1) + 1 by omega,
    bytesAt_succ, bytesAt_succ] at hres
  have hreach : Reaches Image.code u u₃ :=
    (show Reaches Image.code u u₂ from ⟨2, Steps.trans hs₁ hs₂⟩).trans hr₃
  have pc₃ := h₃.pc
  rv_eval [] at pc₃
  rcases eq_ite_cases pc₃ with ⟨hne, pc₃⟩ | ⟨heq, pc₃⟩
  · simp only [bne_iff_ne, ne_eq] at hne
    rw [hb1, hb2] at hne
    have hne' : byteAt s (s.getReg .x10 + BitVec.ofNat 64 k) ≠
        byteAt s (s.getReg .x11 + BitVec.ofNat 64 k) := fun h ↦ hne (by rw [h])
    have hd : u₃.pc = 0x800126d4 → result s = 0 := fun h ↦ by rw [pc₃] at h; cases h
    have h13 : u₃.getReg .x13 = u₂.getReg .x13 := h₃.2.1 _ (List.mem_map.mpr ⟨.x13, by decide, rfl⟩)
    have h14 : u₃.getReg .x14 = u₂.getReg .x14 := h₃.2.1 _ (List.mem_map.mpr ⟨.x14, by decide, rfl⟩)
    have hdiff : u₃.pc = 0x800126dc → result s = u₃.getReg .x13 - u₃.getReg .x14 := fun _ ↦ by
      rw [hres, cmpBytes, h13, h14, hb1, hb2, ite_eq_right_of_eq_false _ _ (eq_false hne')]
    obtain ⟨t, hr, ht⟩ := ret (Or.inr pc₃) hkeep hm₃ ⟨hd, hdiff⟩
    exact Or.inl ⟨t, hreach.trans hr, ht⟩
  · simp only [bne_iff_ne, ne_eq, Classical.not_not] at heq
    rw [hb1, hb2] at heq
    have heq' := zeroExtend_inj heq
    rw [cmpBytes, ite_eq_left_of_eq_true _ _ (eq_true heq')] at hres
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800126c4_spec pc₃ trivial
    have k₄ := b800126c4_keeps h₄
    have hm₄ (a : Word) : u₄.getMem a = s.getMem a := (b800126c4_mem_same h₄ a).trans (hm₃ a)
    have hkeep₄ (r : Reg) (hr : r ∈ calleeSaved ++ [.x1]) : u₄.getReg r = s.getReg r :=
      (k₄ r (mem_of_mem hr _)).trans (hkeep r hr)
    have hx12 : (u₃.getReg .x12 - 1).toNat = (s.getReg .x12).toNat - (k + 1) := by
      rw [hreg .x12 (by decide) (by decide), BitVec.toNat_sub, hk.x12,
        show (1 : Word).toNat = 1 from rfl]
      omega
    have hreach₄ := hreach.trans hr₄
    by_cases hlast : k + 1 = (s.getReg .x12).toNat
    · obtain ⟨t, hr, ht⟩ := ret (Or.inl (b800126c4_pc_not_taken h₄ (BitVec.eq_of_toNat_eq (by
        rw [hx12]; simp only [hlast, Nat.sub_self]; rfl)))) hkeep₄ hm₄
        ⟨fun _ ↦ by rw [hres, show (s.getReg .x12).toNat - k - 1 = 0 by omega]; rfl,
          fun h ↦ by rw [b800126c4_pc_not_taken h₄ (BitVec.eq_of_toNat_eq (by
            rw [hx12]; simp only [hlast, Nat.sub_self]; rfl))] at h; cases h⟩
      exact Or.inl ⟨t, hreach₄.trans hr, ht⟩
    · refine Or.inr ⟨u₄, hreach₄, ⟨k + 1, {
        pc := b800126c4_pc_taken h₄ fun h ↦ by
          have := congrArg BitVec.toNat h; rw [hx12] at this; exact hlast (by simp at this; omega)
        x10 := by
          rw [b800126c4_x10 h₄, hreg .x10 (by decide) (by decide), hk.x10, BitVec.add_assoc,
            BitVec.ofNat_add]; rfl
        x11 := by
          rw [b800126c4_x11 h₄, hreg .x11 (by decide) (by decide), hk.x11, BitVec.add_assoc,
            BitVec.ofNat_add]; rfl
        x12 := by rw [b800126c4_x12 h₄, hx12]
        lt := by omega
        keep := hkeep₄
        mem := hm₄
        res := by
          rw [hres, BitVec.add_assoc, BitVec.add_assoc, BitVec.ofNat_add,
            show (s.getReg .x12).toNat - k - 1 = (s.getReg .x12).toNat - (k + 1) by omega]; rfl }⟩, ?_⟩
      rw [b800126c4_x12 h₄, hx12, hk.x12]
      omega

/-- **`memcmp` meets its contract.** -/
theorem memcmp_spec : MemcmpSpec := by
  intro s hpc hpre
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800126b4_spec hpc trivial
  have k₁ := b800126b4_keeps h₁
  have hm₁ := b800126b4_mem_same h₁
  have hkeep (r : Reg) (hr : r ∈ calleeSaved ++ [.x1]) : u₁.getReg r = s.getReg r :=
    k₁ r (mem_of_mem hr _)
  by_cases hz : s.getReg .x12 = 0
  · obtain ⟨t, hr, ht⟩ := ret (Or.inl (b800126b4_pc_taken h₁ hz)) hkeep hm₁
      ⟨fun _ ↦ by simp only [result, hz]; rfl, fun h ↦ by rw [b800126b4_pc_taken h₁ hz] at h; cases h⟩
    exact ⟨t, hr₁.trans hr, ht⟩
  have hn : 0 < (s.getReg .x12).toNat :=
    Nat.pos_of_ne_zero fun h ↦ hz (BitVec.eq_of_toNat_eq h)
  have hinv : Inv s u₁ 0 := {
    pc := b800126b4_pc_not_taken h₁ hz
    x10 := by rw [k₁ .x10 (by decide)]; simp
    x11 := by rw [k₁ .x11 (by decide)]; simp
    x12 := by rw [k₁ .x12 (by decide)]; simp
    lt := hn
    keep := hkeep
    mem := hm₁
    res := by simp [result] }
  obtain ⟨t, hr, ht⟩ := Reaches.loop (fun u ↦ ∃ k, Inv s u k) (fun u ↦ (u.getReg .x12).toNat)
    (Done s) (body hpre) u₁ ⟨0, hinv⟩
  exact ⟨t, hr₁.trans hr, ht⟩

end Rv64Verifier.Runtime.Memcmp
