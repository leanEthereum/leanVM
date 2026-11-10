import Rv64Verifier.Proofs.Runtime.Memset
import Rv64Verifier.Proofs.Runtime.Memcmp
import Rv64Verifier.Blocks.F94

/-!
# `memcpy`, at `0x80011ff8`, when the source and destination agree modulo 8

`compiler_builtins::mem::memcpy` (`Blocks/F94.lean`) copies fewer than 16 bytes one at a time
(`0x8001212c`, the byte loop at `0x80012168`); otherwise the bytes up to the destination's next
multiple of 8 (`0x80012004`, the loop at `0x80012020`), then whole doublewords: loaded and stored
as they are when the source is then aligned too (`0x8001213c`, the loop at `0x80012144`), else
shifted together from aligned loads (`0x80012050`..`0x8001210c`, through a stack buffer); then the
rest (`0x80012158`, the loop at `0x80012168`). `0x80012180` returns.

`memcpy_coaligned` proves the contract for fewer than 16 bytes, or for a source and destination
equal modulo 8, which never take the shifting path. The byte loops (`copy_loop`) run `step_lbu`,
`step_sb` and expectations for the instructions between (`decE`, `tailCE`).
-/

namespace Rv64Verifier.Runtime.Memcpy
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime.Memset
open Rv64Verifier.Runtime.Memcmp (lbu_rd lbu_other)
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The registers but those of `l`, unchanged. -/
def keepE (l : List Reg) : List (Reg × E) :=
  (allRegs.filter fun r ↦ decide (r ∉ l)).map fun r ↦ (r, .reg r)

theorem keepE_reg {x : Expect} {s t : MachineState} (h : x.Holds s t) {l : List Reg}
    (hl : ∀ p ∈ keepE l, p ∈ x.regs) {r : Reg} (hr : r ∉ l) : t.getReg r = s.getReg r := by
  by_cases h0 : r = .x0
  · subst h0; rfl
  exact h.2.1 (r, .reg r) (hl _ (List.mem_map.mpr ⟨r, List.mem_filter.mpr
    ⟨by cases r <;> simp_all [allRegs], by simp [hr]⟩, rfl⟩))

/-- At `L + 4`, between the load and the store: the count `rc` down by one. -/
def decE (L : Word) (rc : Reg) : Expect where
  steps := 1
  pc := .c (L + 8)
  regs := (rc, .bin .add (.reg rc) (.c 0xffffffffffffffff)) :: keepE [rc]
  mem := []
  writes := []
  obl := []

/-- At `L + 12`, after the store: both pointers up by one, back to `L` unless the count is
zero. -/
def tailCE (L : Word) (rc rd rs : Reg) : Expect where
  steps := 3
  pc := .ite .ne (.reg rc) (.c 0) (.c L) (.c (L + 24))
  regs := (rd, .bin .add (.reg rd) (.c 1)) :: (rs, .bin .add (.reg rs) (.c 1)) :: keepE [rd, rs]
  mem := []
  writes := []
  obl := []

theorem dec_head : Spec (0x80012020 + 4) (decE 0x80012020 .x15) :=
  spec_of 18441 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)
theorem tail_head : Spec (0x80012020 + 12) (tailCE 0x80012020 .x15 .x16 .x17) :=
  spec_of 18443 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)
theorem lbu_head : Image.code.fetch 0x80012020 = some (.base (.LBU .x5 .x17 0)) :=
  fetch_of (by decide +kernel)
theorem sb_head : Image.code.fetch (0x80012020 + 8) = some (.base (.SB .x16 .x5 0)) :=
  fetch_of (by decide +kernel)

theorem dec_tail : Spec (0x80012168 + 4) (decE 0x80012168 .x12) :=
  spec_of 18523 1 (by decide +kernel) (by decide +kernel) (by decide) (by decide)
theorem tail_tail : Spec (0x80012168 + 12) (tailCE 0x80012168 .x12 .x13 .x11) :=
  spec_of 18525 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide)
theorem lbu_tail : Image.code.fetch 0x80012168 = some (.base (.LBU .x14 .x11 0)) :=
  fetch_of (by decide +kernel)
theorem sb_tail : Image.code.fetch (0x80012168 + 8) = some (.base (.SB .x13 .x14 0)) :=
  fetch_of (by decide +kernel)

/-- The first `k` of `n` bytes copied from `src` to `dst`; nothing else written. -/
structure Copied (s u : MachineState) (dst src : Word) (n k : Nat) : Prop where
  bytes : ∀ i < k, byteAt u (dst + BitVec.ofNat 64 i) = byteAt s (src + BitVec.ofNat 64 i)
  frame : ByteFrame s u (Within · dst n)

theorem truncate_zeroExtend (b : BitVec 8) : (b.zeroExtend 64).truncate 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem Copied.src {s u : MachineState} {dst src : Word} {n k : Nat} (h : Copied s u dst src n k)
    (hd : Mapped dst n) (hs : Mapped src n) (hap : Apart dst n src n) {i : Nat} (hi : i < n) :
    byteAt u (src + BitVec.ofNat 64 i) = byteAt s (src + BitVec.ofNat 64 i) :=
  h.frame.byte _ fun hw ↦ by addr_omega [hw, hd, hs, hap, hi]

/-- A byte loop: `m` more bytes from `src + k` to `dst + k`. -/
theorem copy_loop {L : Word} {rt rc rd rs : Reg}
    (hlbu : Image.code.fetch L = some (.base (.LBU rt rs 0))) (hdec : Spec (L + 4) (decE L rc))
    (hsb : Image.code.fetch (L + 8) = some (.base (.SB rd rt 0)))
    (htail : Spec (L + 12) (tailCE L rc rd rs))
    (hr : rt ≠ rc ∧ rt ≠ rd ∧ rt ≠ rs ∧ rc ≠ rd ∧ rc ≠ rs ∧ rd ≠ rs ∧ rt ≠ .x0)
    {s : MachineState} {dst src : Word} {n : Nat} (hd : Mapped dst n) (hs : Mapped src n)
    (hap : Apart dst n src n) :
    ∀ m u k, u.pc = L → (u.getReg rc).toNat = m → 0 < m → u.getReg rd = dst + BitVec.ofNat 64 k →
      u.getReg rs = src + BitVec.ofNat 64 k → k + m ≤ n → Copied s u dst src n k →
      ∃ v, Reaches Image.code u v ∧ v.pc = L + 24 ∧ v.getReg rd = dst + BitVec.ofNat 64 (k + m) ∧
        v.getReg rs = src + BitVec.ofNat 64 (k + m) ∧ Copied s v dst src n (k + m) ∧
        ∀ r, r ≠ rt → r ≠ rc → r ≠ rd → r ≠ rs → v.getReg r = u.getReg r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  have hdm := hd
  have hsm := hs
  simp only [Mapped] at hdm hsm
  have h0 : signExtend12 (0 : BitVec 12) = 0 := rfl
  intro m
  induction m with
  | zero => intro _ _ _ _ h _; omega
  | succ m ih =>
    intro u k hpc hc _ hrd hrs hk hcp
    obtain ⟨u₁, hs₁, hpc₁, hr₁, hm₁⟩ := step_lbu (hpc ▸ hlbu)
      (by rw [h0, Sym.add_zero_lit, hrs]; exact hs.valid (by omega))
    obtain ⟨u₂, hr₂, h₂⟩ := hdec.reaches (by rw [hpc₁, hpc]) trivial
    have k₂ (r : Reg) (hr : r ≠ rc) : u₂.getReg r = u₁.getReg r :=
      keepE_reg h₂ (fun p hp ↦ List.mem_cons_of_mem _ hp) (by simp [hr])
    obtain ⟨u₃, hs₃, hpc₃, hr₃, hb₃, hu₃⟩ := step_sb (code := Image.code) (s := u₂)
      (by rw [h₂.pc]; exact hsb) (by
        rw [h0, Sym.add_zero_lit, k₂ rd (Ne.symm h4), lbu_other hr₁ (Ne.symm h2), hrd]
        exact hd.valid (by omega))
    obtain ⟨u₄, hr₄, h₄⟩ := htail.reaches (by rw [hpc₃, h₂.pc]; show L + 8 + 4 = L + 12; rw [BitVec.add_assoc]; rfl) trivial
    have k₄ (r : Reg) (hr1 : r ≠ rd) (hr2 : r ≠ rs) : u₄.getReg r = u₃.getReg r :=
      keepE_reg h₄ (fun p hp ↦ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)) (by simp [hr1, hr2])
    have hm₄ (a : Word) : u₄.getMem a = u₃.getMem a := h₄.frame a (by simp [tailCE])
    have hm₂ (a : Word) : u₂.getMem a = u₁.getMem a := h₂.frame a (by simp [decE])
    have hrt : (u₂.getReg rt).truncate 8 = byteAt s (src + BitVec.ofNat 64 k) := by
      rw [k₂ rt h1, lbu_rd hr₁ h7, h0, Sym.add_zero_lit, hrs, truncate_zeroExtend,
        hcp.src hd hs hap (by omega)]
    have hrd₂ : u₂.getReg rd = dst + BitVec.ofNat 64 k := by
      rw [k₂ rd (Ne.symm h4), lbu_other hr₁ (Ne.symm h2), hrd]
    rw [h0, Sym.add_zero_lit, hrd₂, hrt] at hb₃
    have hreg (r : Reg) (a1 : r ≠ rt) (a2 : r ≠ rc) (a3 : r ≠ rd) (a4 : r ≠ rs) :
        u₄.getReg r = u.getReg r := by
      rw [k₄ r a3 a4, hr₃, k₂ r a2, lbu_other hr₁ a1]
    have hrd₄ : u₄.getReg rd = dst + BitVec.ofNat 64 (k + 1) := by
      rw [h₄.2.1 _ (List.mem_cons_self ..)]
      show u₃.getReg rd + 1 = _
      rw [hr₃, hrd₂, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    have hrs₄ : u₄.getReg rs = src + BitVec.ofNat 64 (k + 1) := by
      rw [h₄.2.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]
      show u₃.getReg rs + 1 = _
      rw [hr₃, k₂ rs (Ne.symm h5), lbu_other hr₁ (Ne.symm h3), hrs, BitVec.add_assoc,
        BitVec.ofNat_add]; rfl
    have hrc₃ : u₃.getReg rc = u.getReg rc + 0xffffffffffffffff := by
      rw [hr₃, h₂.2.1 _ (List.mem_cons_self ..)]
      show u₁.getReg rc + _ = _
      rw [lbu_other hr₁ (Ne.symm h1)]
      rfl
    have hcp' : Copied s u₄ dst src n (k + 1) := by
      refine ⟨fun i hi ↦ ?_, hcp.frame.trans ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩ fun _ h ↦ h⟩
      · have hb : byteAt u₄ (dst + BitVec.ofNat 64 i) = byteAt u₃ (dst + BitVec.ofNat 64 i) := by
          simp only [byteAt_eq, hm₄]
        rw [hb, hb₃]
        by_cases hik : i = k
        · subst hik; simp only [↓reduceIte]
        · have hne : dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 k := by
            intro h; apply hik
            have := congrArg BitVec.toNat h
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
            omega
          simp only [hne, ↓reduceIte]
          rw [← hcp.bytes i (by omega)]
          simp only [byteAt_eq, hm₂, hm₁]
      · have hb : byteAt u₄ a = byteAt u₃ a := by simp only [byteAt_eq, hm₄]
        rw [hb, hb₃]
        have hne : a ≠ dst + BitVec.ofNat 64 k := fun h ↦ ha (by rw [h]; addr_omega [hdm, hk])
        simp only [hne, ↓reduceIte]
        simp only [byteAt_eq, hm₂, hm₁]
      · rw [hm₄, hu₃ a ha, hm₂, hm₁]
    have hreach : Reaches Image.code u u₄ := by
      obtain ⟨n₂, hn₂⟩ := hr₂
      obtain ⟨n₄, hn₄⟩ := hr₄
      exact ⟨1 + n₂ + 1 + n₄, ((hs₁.trans hn₂).trans hs₃).trans hn₄⟩
    have pc₄ := h₄.pc
    rv_eval [hrc₃] at pc₄
    have hdec' : (u.getReg rc - 1).toNat = m := by
      rw [BitVec.toNat_sub, hc, show (1 : Word).toNat = 1 from rfl]
      omega
    rcases eq_ite_cases pc₄ with ⟨hne, hpc₄⟩ | ⟨hne, hpc₄⟩
    · have hm0 : m ≠ 0 := by
        intro hz
        simp only [bne_iff_ne, ne_eq] at hne
        exact hne (BitVec.eq_of_toNat_eq (by rw [hdec', hz]; rfl))
      have hc₄ : (u₄.getReg rc).toNat = m := by
        rw [k₄ rc h4 h5, hrc₃, BitVec.toNat_add, hc,
          show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl]
        omega
      obtain ⟨v, hrv, hpcv, hrdv, hrsv, hcpv, hregv⟩ := ih u₄ (k + 1) hpc₄ hc₄ (by omega) hrd₄
        hrs₄ (by omega) hcp'
      refine ⟨v, hreach.trans hrv, hpcv, by rw [hrdv, show k + 1 + m = k + (m + 1) by omega],
        by rw [hrsv, show k + 1 + m = k + (m + 1) by omega],
        by rw [show k + (m + 1) = k + 1 + m by omega]; exact hcpv,
        fun r a1 a2 a3 a4 ↦ (hregv r a1 a2 a3 a4).trans (hreg r a1 a2 a3 a4)⟩
    · have hm0 : m = 0 := by
        simp only [bne_iff_ne, ne_eq, Classical.not_not] at hne
        rw [← hdec', hne]; rfl
      subst hm0
      exact ⟨u₄, hreach, hpc₄, hrd₄, hrs₄, hcp', hreg⟩

/-! ## The doubleword loop, source and destination aligned -/

open Rv64Verifier.Blocks.F94

/-- The registers `memcpy` never writes but `sp`. -/
def keepC : List Reg :=
  [.x1, .x3, .x4, .x8, .x9, .x10, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- At `0x80012144`, `j` doublewords done after `h` bytes. -/
structure DwInv (s u : MachineState) (h j : Nat) : Prop where
  pc : u.pc = 0x80012144
  x14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j)
  x16 : u.getReg .x16 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * j)
  x13 : (u.getReg .x13).toNat = (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8)
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h
  x12 : (u.getReg .x12).toNat = (s.getReg .x12).toNat - h
  x15 : (u.getReg .x15).toNat = 8 * (((s.getReg .x12).toNat - h) / 8)
  x2 : u.getReg .x2 = s.getReg .x2 - 16
  lt : h + 8 * j + 8 ≤ (s.getReg .x12).toNat
  ald : ((s.getReg .x10).toNat + h) % 8 = 0
  als : ((s.getReg .x11).toNat + h) % 8 = 0
  keep : ∀ r ∈ keepC, u.getReg r = s.getReg r
  copied : Copied s u (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat (h + 8 * j)

/-- The doubleword loop is over: at `0x80012158`. -/
structure DwDone (s u : MachineState) (h : Nat) : Prop where
  pc : u.pc = 0x80012158
  x13 : (u.getReg .x13).toNat = (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8)
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h
  x12 : (u.getReg .x12).toNat = (s.getReg .x12).toNat - h
  x15 : (u.getReg .x15).toNat = 8 * (((s.getReg .x12).toNat - h) / 8)
  x2 : u.getReg .x2 = s.getReg .x2 - 16
  keep : ∀ r ∈ keepC, u.getReg r = s.getReg r
  copied : Copied s u (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat
    (h + 8 * (((s.getReg .x12).toNat - h) / 8))

theorem dw_body {s : MachineState} {h : Nat} (hpre : MemcpyPre s) (u : MachineState)
    (hu : ∃ j, DwInv s u h j) :
    (∃ v, Reaches Image.code u v ∧ DwDone s v h) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ j, DwInv s v h j) ∧
        (v.getReg .x13).toNat - (v.getReg .x14).toNat <
          (u.getReg .x13).toNat - (u.getReg .x14).toNat) := by
  obtain ⟨j, hj⟩ := hu
  have hd := hpre.dst
  have hs := hpre.src
  have hap := hpre.apart
  have hdm := hd
  have hsm := hs
  simp only [Mapped] at hdm hsm
  have hlt := hj.lt
  have hald := hj.ald
  have hals := hj.als
  have hx14 := hj.x14
  have hx16 := hj.x16
  have hx13 := hj.x13
  obtain ⟨v, hr, hv⟩ := Sym.BlockSpec.reaches b80012144_spec hj.pc (by
    rv_eval [hx14, hx16]
    exact ⟨hd.valid8 (by addr_omega [hlt, hdm]) (by addr_omega [hlt, hdm])
      (by addr_omega [hlt, hdm, hald]), hs.valid8 (by addr_omega [hlt, hsm])
      (by addr_omega [hlt, hsm]) (by addr_omega [hlt, hsm, hals])⟩)
  have kv := b80012144_keeps hv
  have hw := b80012144_m_x14_0 hv
  have hfr := b80012144_frame hv (by rw [hx14]; addr_omega [hlt, hdm])
  rw [hx14, hx16] at hw
  rw [hx14] at hfr
  have hun := hv.unaligned (by rv_eval [hx14]; addr_omega [hlt, hdm, hald])
  have hcp : Copied s v (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat (h + 8 * (j + 1)) := by
    refine ⟨fun i hi ↦ ?_, hj.copied.frame.trans ((ByteFrame.of_memFrame hfr
      (by addr_omega [hlt, hdm, hald]) (by decide) hun).mono fun a ha ↦ by addr_omega [ha, hlt, hdm])
      fun _ h ↦ h⟩
    by_cases hi' : i < h + 8 * j
    · rw [← hj.copied.bytes i hi', byteAt_eq, byteAt_eq, hfr]
      simp only [Within, toNat_alignDown]
      addr_omega [hi', hlt, hdm]
    · rw [byteAt_of_within (b := s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j))
        (by addr_omega [hlt, hdm, hald]) (by addr_omega [hi, hi', hlt, hdm])
        (by addr_omega [hi, hlt, hdm]), hw,
        ← hj.copied.src hd hs hap (i := i) (by omega),
        byteAt_of_within (b := s.getReg .x11 + BitVec.ofNat 64 (h + 8 * j))
        (by addr_omega [hlt, hsm, hals]) (by addr_omega [hi, hi', hlt, hsm])
        (by addr_omega [hi, hlt, hsm])]
      congr 1
      addr_omega [hi, hi', hlt, hdm, hsm]
  have hkeep : ∀ r ∈ keepC, v.getReg r = s.getReg r :=
    fun r hr' ↦ (kv r (mem_of_mem hr' _)).trans (hj.keep r hr')
  have hx14v : v.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (j + 1)) := by
    rw [b80012144_x14 hv, hx14]; addr_omega [hlt, hdm]
  have hx16v : v.getReg .x16 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (j + 1)) := by
    rw [b80012144_x16 hv, hx16]; addr_omega [hlt, hsm]
  have hx13v := kv .x13 (by decide)
  have hx2v := kv .x2 (by decide)
  have hx11v := kv .x11 (by decide)
  have hx12v := kv .x12 (by decide)
  have hx15v := kv .x15 (by decide)
  by_cases hlast : h + 8 * (j + 1) + 8 ≤ (s.getReg .x12).toNat
  · refine Or.inr ⟨v, hr, ⟨j + 1, b80012144_pc_taken hv ?_, hx14v, hx16v,
      by rw [hx13v]; exact hx13, by rw [hx11v]; exact hj.x11, by rw [hx12v]; exact hj.x12,
      by rw [hx15v]; exact hj.x15, by rw [hx2v]; exact hj.x2, hlast, hald, hals, hkeep, hcp⟩, ?_⟩
    · rw [hx14]; addr_omega [hlast, hlt, hdm, hx13]
    · rw [hx14v, hx13v, hx14]; addr_omega [hlast, hlt, hdm, hx13]
  · have hW : h + 8 * (j + 1) = h + 8 * (((s.getReg .x12).toNat - h) / 8) := by omega
    refine Or.inl ⟨v, hr, ⟨b80012144_pc_not_taken hv ?_, by rw [hx13v]; exact hx13,
      by rw [hx11v]; exact hj.x11, by rw [hx12v]; exact hj.x12, by rw [hx15v]; exact hj.x15,
      by rw [hx2v]; exact hj.x2, hkeep, hW ▸ hcp⟩⟩
    rw [hx14]; addr_omega [hlast, hlt, hdm, hx13]

/-! ## `memcpy` -/

/-- `0x80012180`: pop the frame, return, every byte copied. -/
theorem ret {s u : MachineState} (hpc : u.pc = 0x80012180) (hx2 : u.getReg .x2 = s.getReg .x2 - 16)
    (hk : ∀ r ∈ keepC, u.getReg r = s.getReg r)
    (hc : Copied s u (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat (s.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t) ∨
      Dead Image.code t) := by
  obtain ⟨t, hr, h⟩ := Sym.BlockSpec.reaches b80012180_spec hpc trivial
  have k := b80012180_keeps h
  have hm := b80012180_mem_same h
  refine ⟨t, hr, Or.inl ⟨by rw [b80012180_pc h, hk .x1 (by decide)]; rfl,
    fun r hr' ↦ ?_, (k .x10 (by decide)).trans (hk .x10 (by decide)), ?_,
    (hc.frame.trans (ByteFrame.of_same hm _) fun _ h ↦ h).mono fun _ h ↦ Or.inl h⟩⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | hr'
    · rw [b80012180_x2 h, hx2]; exact BitVec.sub_add_cancel _ _
    · have : r ∈ keepC := by simp only [keepC, List.mem_cons, List.not_mem_nil, or_false]; tauto
      rw [k r (mem_of_mem this _), hk r this]
  · refine bytesAt_eq_iff.mpr fun i hi ↦ ?_
    rw [← hc.bytes i hi]
    simp only [byteAt_eq, hm]

/-- From `0x80012158`, after the doublewords: the rest. -/
theorem tail {s u : MachineState} {h : Nat} (hpre : MemcpyPre s) (hd : DwDone s u h)
    (hh : h ≤ (s.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t) ∨
      Dead Image.code t) := by
  have hdm := hpre.dst
  have hsm := hpre.src
  simp only [Mapped] at hdm hsm
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80012158_spec hd.pc trivial
  have k₁ := b80012158_keeps h₁
  have hm₁ := b80012158_mem_same h₁
  have hk₁ : ∀ r ∈ keepC, u₁.getReg r = s.getReg r :=
    fun r hr ↦ (k₁ r (mem_of_mem hr _)).trans (hd.keep r hr)
  have hc₁ : Copied s u₁ (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat
      (h + 8 * (((s.getReg .x12).toNat - h) / 8)) :=
    ⟨fun i hi ↦ by rw [← hd.copied.bytes i hi]; simp only [byteAt_eq, hm₁],
      hd.copied.frame.trans (ByteFrame.of_same hm₁ _) fun _ h ↦ h⟩
  have hr7 : (u.getReg .x12 &&& 7).toNat = ((s.getReg .x12).toNat - h) % 8 := by
    rw [show u.getReg .x12 &&& 7 = u.getReg .x12 &&& 7#64 from rfl, toNat_and7, hd.x12]
  have hx2₁ : u₁.getReg .x2 = s.getReg .x2 - 16 := (k₁ .x2 (by decide)).trans hd.x2
  have hx13 := hd.x13
  by_cases h0 : ((s.getReg .x12).toNat - h) % 8 = 0
  · rw [show h + 8 * (((s.getReg .x12).toNat - h) / 8) = (s.getReg .x12).toNat by omega] at hc₁
    obtain ⟨t, hr, ht⟩ := ret (b80012158_pc_taken h₁ (by rw [BitVec.toNat_add, hr7, h0]; omega))
      hx2₁ hk₁ hc₁
    exact ⟨t, hr₁.trans hr, ht⟩
  · have hx13w : u₁.getReg .x13 =
        s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (((s.getReg .x12).toNat - h) / 8)) := by
      rw [k₁ .x13 (by decide)]
      apply BitVec.eq_of_toNat_eq
      rw [hx13, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hx11w : u₁.getReg .x11 =
        s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (((s.getReg .x12).toNat - h) / 8)) := by
      rw [b80012158_x11 h₁, hd.x11]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hd.x15, BitVec.toNat_add,
        BitVec.toNat_ofNat]
      omega
    obtain ⟨v, hrv, hpcv, -, -, hcv, hregv⟩ := copy_loop lbu_tail dec_tail sb_tail tail_tail
      (by decide) hpre.dst hpre.src hpre.apart (((s.getReg .x12).toNat - h) % 8) u₁ _
      (b80012158_pc_not_taken h₁ (by rw [BitVec.toNat_add, hr7]; omega))
      (by rw [b80012158_x12 h₁, hr7]) (by omega) hx13w hx11w (by omega) hc₁
    rw [show h + 8 * (((s.getReg .x12).toNat - h) / 8) + ((s.getReg .x12).toNat - h) % 8 =
      (s.getReg .x12).toNat by omega] at hcv
    have hreg (r : Reg) (hr : r ∈ Reg.x2 :: keepC) : v.getReg r = u₁.getReg r :=
      hregv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
        (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
    obtain ⟨t, hr, ht⟩ := ret hpcv ((hreg .x2 (by decide)).trans hx2₁)
      (fun r hr ↦ (hreg r (List.mem_cons_of_mem _ hr)).trans (hk₁ r hr)) hcv
    exact ⟨t, hr₁.trans (hrv.trans hr), ht⟩

/-- From `0x80012038`, `h` bytes copied up to an aligned destination, the source aligned too: the
doublewords, then the rest. -/
theorem rest {s u : MachineState} {h : Nat} (hpre : MemcpyPre s) (hpc : u.pc = 0x80012038)
    (hn : 16 ≤ (s.getReg .x12).toNat) (hh : h < 8)
    (hald : ((s.getReg .x10).toNat + h) % 8 = 0) (hals : ((s.getReg .x11).toNat + h) % 8 = 0)
    (hx11 : u.getReg .x11 = s.getReg .x11) (hx12 : u.getReg .x12 = s.getReg .x12)
    (hx13 : (u.getReg .x13).toNat = h) (hx14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 h)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 16) (hk : ∀ r ∈ keepC, u.getReg r = s.getReg r)
    (hc : Copied s u (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat h) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t) ∨
      Dead Image.code t) := by
  have hdm := hpre.dst
  have hsm := hpre.src
  simp only [Mapped] at hdm hsm
  have h13 : u.getReg .x13 = BitVec.ofNat 64 h := BitVec.eq_of_toNat_eq (by
    rw [hx13, BitVec.toNat_ofNat]; omega)
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80012038_spec hpc trivial
  have k₁ := b80012038_keeps h₁
  have hsub : (u.getReg .x12 - u.getReg .x13).toNat = (s.getReg .x12).toNat - h := by
    rw [BitVec.toNat_sub, hx12, hx13]; omega
  have hW := and_not7 (u.getReg .x12 - u.getReg .x13)
  rw [hsub] at hW
  have hend : (u.getReg .x14 + ((u.getReg .x12 - u.getReg .x13) &&& (0xfffffffffffffff8 : Word))).toNat =
      (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8) := by
    rw [BitVec.toNat_add, hW, hx14, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hsrc : u.getReg .x11 + u.getReg .x13 = s.getReg .x11 + BitVec.ofNat 64 h := by
    rw [hx11, h13]
  have hal0 : (u.getReg .x11 + u.getReg .x13) &&& (7 : Word) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [show (u.getReg .x11 + u.getReg .x13) &&& (7 : Word) =
      (u.getReg .x11 + u.getReg .x13) &&& 7#64 from rfl, toNat_and7, hsrc, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    show _ = 0
    omega
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8001213c_spec (b80012038_pc_taken h₁ hal0) trivial
  have k₂ := b8001213c_keeps h₂
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80012140_spec
    (b8001213c_pc_not_taken h₂ (by
      rw [b80012038_x13 h₁, hend, k₁ .x14 (by decide), hx14, BitVec.toNat_add,
        BitVec.toNat_ofNat]
      omega)) trivial
  have k₃ := b80012140_keeps h₃
  have hm (a : Word) : u₃.getMem a = u.getMem a :=
    (b80012140_mem_same h₃ a).trans ((b8001213c_mem_same h₂ a).trans (b80012038_mem_same h₁ a))
  have hinv : DwInv s u₃ h 0 := {
    pc := b80012140_pc h₃
    x14 := by rw [k₃ .x14 (by decide), k₂ .x14 (by decide), k₁ .x14 (by decide), hx14, Nat.mul_zero,
      Nat.add_zero]
    x16 := by rw [b80012140_x16 h₃, k₂ .x11 (by decide), b80012038_x11 h₁, hsrc, Nat.mul_zero,
      Nat.add_zero]
    x13 := by rw [k₃ .x13 (by decide), k₂ .x13 (by decide), b80012038_x13 h₁, hend]
    x11 := by rw [k₃ .x11 (by decide), k₂ .x11 (by decide), b80012038_x11 h₁, hsrc]
    x12 := by rw [k₃ .x12 (by decide), k₂ .x12 (by decide), b80012038_x12 h₁, hsub]
    x15 := by rw [k₃ .x15 (by decide), k₂ .x15 (by decide), b80012038_x15 h₁, hW]; omega
    x2 := by rw [k₃ .x2 (by decide), k₂ .x2 (by decide), k₁ .x2 (by decide), hx2]
    lt := by omega
    ald := hald
    als := hals
    keep := fun r hr ↦ (k₃ r (mem_of_mem hr _)).trans ((k₂ r (mem_of_mem hr _)).trans
      ((k₁ r (mem_of_mem hr _)).trans (hk r hr)))
    copied := ⟨fun i hi ↦ by rw [← hc.bytes i (by omega)]; simp only [byteAt_eq, hm],
      hc.frame.trans (ByteFrame.of_same hm _) fun _ h ↦ h⟩ }
  obtain ⟨v, hrv, hdv⟩ := Reaches.loop (fun u ↦ ∃ j, DwInv s u h j)
    (fun u ↦ (u.getReg .x13).toNat - (u.getReg .x14).toNat) (DwDone s · h) (dw_body hpre) u₃
    ⟨0, hinv⟩
  obtain ⟨t, hr, ht⟩ := tail hpre hdv (by omega)
  exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hrv.trans hr))), ht⟩

/-- `memcpy`'s precondition, with fewer than 16 bytes or the source and destination equal
modulo 8. -/
def CoPre (s : MachineState) : Prop :=
  MemcpyPre s ∧ ((s.getReg .x12).toNat < 16 ∨ (s.getReg .x10).toNat % 8 = (s.getReg .x11).toNat % 8)

/-- **`memcpy` meets its contract** for fewer than 16 bytes or a source and destination equal
modulo 8 (`Vec` buffers of 8-aligned elements, as `finish_grow` copies them). -/
theorem memcpy_coaligned : FunSpec Image.code 0x80011ff8 CoPre MemcpyPost := by
  intro s hpc ⟨hpre, hco⟩
  have hdm := hpre.dst
  have hsm := hpre.src
  simp only [Mapped] at hdm hsm
  have hc0 : Copied s s (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat 0 :=
    ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), ByteFrame.refl _ _⟩
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011ff8_spec hpc trivial
  have k₁ := b80011ff8_keeps h₁
  have hm₁ := b80011ff8_mem_same h₁
  have hx2₁ := b80011ff8_x2 h₁
  have hcopy (u : MachineState) (hm : ∀ a, u.getMem a = s.getMem a) :
      Copied s u (s.getReg .x10) (s.getReg .x11) (s.getReg .x12).toNat 0 :=
    ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), (ByteFrame.of_same hm _)⟩
  by_cases hsmall : (s.getReg .x12).toNat < 16
  · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8001212c_spec (b80011ff8_pc_taken h₁ hsmall)
      trivial
    have k₂ := b8001212c_keeps h₂
    have hm₂ (a : Word) : u₂.getMem a = s.getMem a := (b8001212c_mem_same h₂ a).trans (hm₁ a)
    have hx10 : u₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
    have hx12 : u₁.getReg .x12 = s.getReg .x12 := k₁ .x12 (by decide)
    have hk₂ : ∀ r ∈ keepC, u₂.getReg r = s.getReg r :=
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    have hx2₂ : u₂.getReg .x2 = s.getReg .x2 - 16 := (k₂ .x2 (by decide)).trans hx2₁
    by_cases h0 : (s.getReg .x12).toNat = 0
    · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80012138_spec
        (b8001212c_pc_not_taken h₂ (by rw [hx10, hx12, BitVec.toNat_add, h0]; omega)) trivial
      have k₃ := b80012138_keeps h₃
      obtain ⟨t, hr, ht⟩ := ret (b80012138_pc h₃) ((k₃ .x2 (by decide)).trans hx2₂)
        (fun r hr ↦ (k₃ r (mem_of_mem hr _)).trans (hk₂ r hr))
        ⟨fun i hi ↦ absurd (h0 ▸ hi) (Nat.not_lt_zero _),
          ByteFrame.of_same (fun a ↦ (b80012138_mem_same h₃ a).trans (hm₂ a)) _⟩
      exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), ht⟩
    · obtain ⟨v, hrv, hpcv, -, -, hcv, hregv⟩ := copy_loop lbu_tail dec_tail sb_tail tail_tail
        (by decide) hpre.dst hpre.src hpre.apart (s.getReg .x12).toNat u₂ 0
        (b8001212c_pc_taken h₂ (by rw [hx10, hx12, BitVec.toNat_add]; omega))
        (by rw [k₂ .x12 (by decide), hx12]) (by omega)
        (by rw [b8001212c_x13 h₂, hx10]; simp)
        (by rw [k₂ .x11 (by decide), k₁ .x11 (by decide)]; simp) (by omega) (hcopy u₂ hm₂)
      rw [Nat.zero_add] at hcv
      have hreg (r : Reg) (hr : r ∈ Reg.x2 :: keepC) : v.getReg r = u₂.getReg r :=
        hregv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
          (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
      obtain ⟨t, hr, ht⟩ := ret hpcv ((hreg .x2 (by decide)).trans hx2₂)
        (fun r hr ↦ (hreg r (List.mem_cons_of_mem _ hr)).trans (hk₂ r hr)) hcv
      exact ⟨t, hr₁.trans (hr₂.trans (hrv.trans hr)), ht⟩
  · have hco' : (s.getReg .x10).toNat % 8 = (s.getReg .x11).toNat % 8 := by omega
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80012004_spec
      (b80011ff8_pc_not_taken h₁ (Nat.le_of_not_lt hsmall)) trivial
    have k₂ := b80012004_keeps h₂
    have hx10 : u₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
    have hx13 := b80012004_x13 h₂
    have hx14 := b80012004_x14 h₂
    rw [hx10] at hx13 hx14
    have hH : (((0 : Word) - s.getReg .x10) &&& (7 : Word)).toNat =
        (2 ^ 64 - (s.getReg .x10).toNat) % 8 := by
      rw [show ((0 : Word) - s.getReg .x10) &&& (7 : Word) = ((0 : Word) - s.getReg .x10) &&& 7#64
        from rfl, toNat_and7, BitVec.toNat_sub]
      have : (0 : Word).toNat = 0 := rfl
      omega
    have hh8 : (2 ^ 64 - (s.getReg .x10).toNat) % 8 < 8 := Nat.mod_lt _ (by decide)
    have hald : ((s.getReg .x10).toNat + (2 ^ 64 - (s.getReg .x10).toNat) % 8) % 8 = 0 := by omega
    have hals : ((s.getReg .x11).toNat + (2 ^ 64 - (s.getReg .x10).toNat) % 8) % 8 = 0 := by omega
    have hx14' : u₂.getReg .x14 =
        s.getReg .x10 + BitVec.ofNat 64 ((2 ^ 64 - (s.getReg .x10).toNat) % 8) := by
      rw [hx14]; congr 1; apply BitVec.eq_of_toNat_eq; rw [hH, BitVec.toNat_ofNat]; omega
    have hm₂ (a : Word) : u₂.getMem a = s.getMem a := (b80012004_mem_same h₂ a).trans (hm₁ a)
    have hk₂ : ∀ r ∈ keepC, u₂.getReg r = s.getReg r :=
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    have hx2₂ : u₂.getReg .x2 = s.getReg .x2 - 16 := (k₂ .x2 (by decide)).trans hx2₁
    have hx11 : u₂.getReg .x11 = s.getReg .x11 := (k₂ .x11 (by decide)).trans (k₁ .x11 (by decide))
    have hx12 : u₂.getReg .x12 = s.getReg .x12 := (k₂ .x12 (by decide)).trans (k₁ .x12 (by decide))
    by_cases h0 : (2 ^ 64 - (s.getReg .x10).toNat) % 8 = 0
    · obtain ⟨t, hr, ht⟩ := rest (h := 0) hpre (b80012004_pc_taken h₂ (by
          rw [hx10, BitVec.toNat_add, hH, h0]; omega)) (Nat.le_of_not_lt hsmall) (by decide)
        (by rw [Nat.add_zero]; omega) (by rw [Nat.add_zero]; omega) hx11 hx12
        (by rw [hx13, hH, h0]) (by rw [hx14', h0]) hx2₂ hk₂ (hcopy u₂ hm₂)
      exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩
    · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80012014_spec
        (b80012004_pc_not_taken h₂ (by rw [hx10, BitVec.toNat_add, hH]; omega)) trivial
      have k₃ := b80012014_keeps h₃
      have hm₃ (a : Word) : u₃.getMem a = s.getMem a := (b80012014_mem_same h₃ a).trans (hm₂ a)
      obtain ⟨v, hrv, hpcv, -, -, hcv, hregv⟩ := copy_loop lbu_head dec_head sb_head tail_head
        (by decide) hpre.dst hpre.src hpre.apart ((2 ^ 64 - (s.getReg .x10).toNat) % 8) u₃ 0
        (b80012014_pc h₃) (by rw [b80012014_x15 h₃, hx13, hH]) (by omega)
        (by rw [b80012014_x16 h₃, k₂ .x10 (by decide), hx10]; simp)
        (by rw [b80012014_x17 h₃, hx11]; simp) (by omega) (hcopy u₃ hm₃)
      rw [Nat.zero_add] at hcv
      have hreg (r : Reg) (hr : r ∈ [Reg.x2, .x11, .x12, .x13, .x14] ++ keepC) :
          v.getReg r = u₃.getReg r :=
        hregv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
          (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
      obtain ⟨t, hr, ht⟩ := rest hpre hpcv (Nat.le_of_not_lt hsmall) hh8 hald hals
        (by rw [hreg .x11 (by decide), k₃ .x11 (by decide), hx11])
        (by rw [hreg .x12 (by decide), k₃ .x12 (by decide), hx12])
        (by rw [hreg .x13 (by decide), k₃ .x13 (by decide), hx13, hH])
        (by rw [hreg .x14 (by decide), k₃ .x14 (by decide), hx14'])
        (by rw [hreg .x2 (by decide), k₃ .x2 (by decide), hx2₂])
        (fun r hr ↦ (hreg r (List.mem_append_right _ hr)).trans
          ((k₃ r (mem_of_mem hr _)).trans (hk₂ r hr))) hcv
      exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hrv.trans hr))), ht⟩

end Rv64Verifier.Runtime.Memcpy
