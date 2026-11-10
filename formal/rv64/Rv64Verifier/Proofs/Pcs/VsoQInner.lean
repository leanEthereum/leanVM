import Rv64Verifier.Proofs.Pcs.VsoQSetup

/-!
# `verify_stacked_opening`'s level loop: `sample_queries`' chunks

One sample's chunks, from `0x8000a970`: the chunk's bit offset `j d` bounded (`< 256`, `< 192`, panics
past either), the two lanes it straddles loaded from `S - 384` (the sample's three, then `0`), and
`0x8000a934` stores `(lo >> sh | (hi << 1) << (sh ^ 63)) & (2^d - 1)`, which is `queryWindow`'s
128-bit window (`window_eq`), at the positions' end. `len < cap` throughout, so `grow_one` is not
called. After the sample's last chunk the loop goes back to `0x8000a8cc`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem window_eq (lo hi : Word) (sh : ℕ) (h : sh < 64) :
    (lo >>> sh ||| (hi <<< 1) <<< (63 - sh)) =
      ((lo.setWidth 128 ||| hi.setWidth 128 <<< 64) >>> sh).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi64
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  by_cases h1 : i + sh < 64
  · have e1 : sh + i < 128 := by omega
    have e2 : sh + i < 64 := by omega
    by_cases h2 : i < 63 - sh
    · simp [e1, e2, h2, hi64]
    · have e3 : i - (63 - sh) = 0 := by omega
      simp [e1, e2, h2, e3, hi64]
  · have hl : lo.getLsbD (sh + i) = false := BitVec.getLsbD_of_ge lo _ (by omega)
    have e1 : sh + i < 128 := by omega
    have e2 : ¬ sh + i < 64 := by omega
    have e3 : ¬ i < 63 - sh := by omega
    have e4 : i - (63 - sh) < 64 := by omega
    have e5 : ¬ i - (63 - sh) < 1 := by omega
    have e6 : sh + i - 64 < 128 := by omega
    have e7 : i - (63 - sh) - 1 = sh + i - 64 := by omega
    simp [hl, e1, e2, e3, e4, e5, e6, e7, hi64]

theorem neg_add_cancel_w (a b : Word) : 0 - a + (b + a) = b := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  have := b.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, show (0 : Word).toNat = 0 from rfl]
  omega

theorem xor63 {a : Word} (h : a.toNat < 64) : (a ^^^ 63).toNat = 63 - a.toNat := by
  rw [BitVec.toNat_xor, show (63 : Word).toNat = 63 from rfl]
  have key : ∀ n, n < 64 → n ^^^ 63 = 63 - n := by decide
  exact key _ h

theorem and63_toNat (a : Word) : (a &&& 63).toNat = a.toNat % 64 := by
  rw [BitVec.toNat_and, show (63 : Word).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- `0x8000a934`'s window, as the executor writes it. -/
theorem chunk_eq (lo hi : Word) {k : ℕ} (hk : k < 192) :
    (lo >>> ((BitVec.ofNat 64 k &&& 63).toNat % 64) |||
        hi * (2 : Word) * BitVec.ofNat 64 (2 ^ ((BitVec.ofNat 64 k &&& 63 ^^^ 63).toNat % 64))) =
      ((lo.setWidth 128 ||| hi.setWidth 128 <<< 64) >>> (k % 64)).setWidth 64 := by
  have ha : (BitVec.ofNat 64 k &&& 63).toNat = k % 64 := by
    rw [and63_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  have hx : (BitVec.ofNat 64 k &&& 63 ^^^ 63).toNat = 63 - k % 64 := by
    rw [xor63 (by rw [ha]; omega), ha]
  have e1 : k % 64 % 64 = k % 64 := by omega
  have e2 : (63 - k % 64) % 64 = 63 - k % 64 := by omega
  rw [ha, hx, e1, e2, ← window_eq lo hi (k % 64) (by omega), Sym.shiftLeft_eq_mul,
    Sym.shiftLeft_eq_mul]
  rfl

/-- A sample's three limbs and a zero, as `sample_queries` reads them. -/
def bitsOf (smp : E) : List Word :=
  [(smp.limb 0).toBitVec, (smp.limb 1).toBitVec, (smp.limb 2).toBitVec, 0#64]

/-- The block length at depth `d`. -/
def blOf (d : ℕ) : BitVec 64 := 1#64 <<< (d % 64)

/-- The first `j` chunks of a sample. -/
def chunksOf (smp : E) (d j : ℕ) : List Word :=
  (List.range j).map (Model.Pcs.queryWindow (bitsOf smp) (blOf d) d)

theorem blOf_sub {d : ℕ} (hd : d < 64) : blOf d - 1 = BitVec.ofNat 64 (2 ^ d - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [blOf, BitVec.toNat_sub, Model.Pcs.one_shiftLeft_toNat hd, BitVec.toNat_ofNat]
  have : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hd
  have : 0 < 2 ^ d := Nat.two_pow_pos d
  show (2 ^ 64 - 1 % 2 ^ 64 + 2 ^ d) % 2 ^ 64 = (2 ^ d - 1) % 2 ^ 64
  omega

/-- At `0x8000a970`, chunk `j` of the sample `smp` next, `r` drawn before it. -/
structure QInner (s w u : MachineState) (d cnt : ℕ) (r : List Word) (smp : E) (j : ℕ) : Prop where
  pc : u.pc = 0x8000a970
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s u (u.getMem nextAddr)
  fr : DFrame w u (QW s w u)
  mono : heapNext w ≤ heapNext u
  x1 : u.getReg .x1 = vecPtr u (s.getReg .x2 - 464)
  x8 : u.getReg .x8 = BitVec.ofNat 64 d
  x9 : u.getReg .x9 = w.getReg .x9
  x18 : u.getReg .x18 = 0 - BitVec.ofNat 64 d
  x19 : u.getReg .x19 = BitVec.ofNat 64 (2 ^ d - 1)
  x21 : u.getReg .x21 = BitVec.ofNat 64 (min (192 / d) (cnt - r.length))
  x22 : u.getReg .x22 = BitVec.ofNat 64 j
  x23 : u.getReg .x23 = BitVec.ofNat 64 (j * d)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (8 * (r.length + j))
  x26 : u.getReg .x26 = BitVec.ofNat 64 (r.length + j)
  s832 : u.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 cnt
  s824 : u.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 (192 / d)
  l0 : u.getMem (s.getReg .x2 - 384) = (smp.limb 0).toBitVec
  l1 : u.getMem (s.getReg .x2 - 376) = (smp.limb 1).toBitVec
  l2 : u.getMem (s.getReg .x2 - 368) = (smp.limb 2).toBitVec
  l3 : u.getMem (s.getReg .x2 - 360) = 0
  vec : QVec s w u cnt (r ++ chunksOf smp d j)
  jlt : j < min (192 / d) (cnt - r.length)
  d0 : 0 < d
  d64 : d < 64

/-- At `0x8000a8cc`, back from a sample: `r` drawn. -/
structure QBack (s w u : MachineState) (d cnt : ℕ) (r : List Word) : Prop where
  pc : u.pc = 0x8000a8cc
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s u (u.getMem nextAddr)
  fr : DFrame w u (QW s w u)
  mono : heapNext w ≤ heapNext u
  x1 : u.getReg .x1 = vecPtr u (s.getReg .x2 - 464)
  x8 : u.getReg .x8 = BitVec.ofNat 64 d
  x9 : u.getReg .x9 = w.getReg .x9
  x18 : u.getReg .x18 = 0 - BitVec.ofNat 64 d
  x19 : u.getReg .x19 = BitVec.ofNat 64 (2 ^ d - 1)
  x26 : u.getReg .x26 = BitVec.ofNat 64 r.length
  s832 : u.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 cnt
  s824 : u.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 (192 / d)
  vec : QVec s w u cnt r
  d0 : 0 < d
  d64 : d < 64

/-- **A chunk**, from `0x8000a970`: the next chunk, or back to `0x8000a8cc` after the sample's
last. -/
theorem chunk {s w u : MachineState} {d cnt : ℕ} {r : List Word} {smp : E} {j : ℕ}
    (hpre : VsoPre s) (h : QInner s w u d cnt r smp j) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨
      ((∀ T, TranscriptAt u (s.getReg .x10) T → TranscriptAt v (s.getReg .x10) T) ∧
        ((j + 1 < min (192 / d) (cnt - r.length) ∧ QInner s w v d cnt r smp (j + 1)) ∨
        (j + 1 = min (192 / d) (cnt - r.length) ∧
          QBack s w v d cnt (r ++ chunksOf smp d (j + 1)))))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hjm := h.jlt
  have hd0 := h.d0
  have hd64 := h.d64
  have hjd : j * d < 192 := by
    have h1 : j < 192 / d := lt_of_lt_of_le hjm (Nat.min_le_left _ _)
    have h2 : j * d < 192 / d * d := Nat.mul_lt_mul_of_pos_right h1 hd0
    exact lt_of_lt_of_le h2 (Nat.div_mul_le_self _ _)
  have hjr : r.length + j < cnt := by
    have := Nat.min_le_right (192 / d) (cnt - r.length); omega
  have x23n : (BitVec.ofNat 64 (j * d)).toNat = j * d := by rw [BitVec.toNat_ofNat]; omega
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a970_spec h.pc trivial
  have hpc₁ := b8000a970_pc_taken h₁ (by rw [h.x23, x23n]; show _ ≤ 255; omega)
  have hm₁ := b8000a970_mem_same h₁
  have k₁ := b8000a970_keeps h₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a97c_spec hpc₁ trivial
  have hpc₂ := b8000a97c_pc_taken h₂ (by
    rw [k₁ .x18 (by decide), k₁ .x23 (by decide), k₁ .x8 (by decide), h.x18, h.x23, h.x8,
      neg_add_cancel_w, x23n]
    exact hjd)
  have hm₂ := b8000a97c_mem_same h₂
  have k₂ := b8000a97c_keeps h₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₂ .x2 (by decide), k₁ .x2 (by decide), h.sp]
  have x23₂ : t₂.getReg .x23 = BitVec.ofNat 64 (j * d) := by
    rw [k₂ .x23 (by decide), k₁ .x23 (by decide), h.x23]
  have hidx : (BitVec.ofNat 64 (j * d) >>> 6) * 8 = BitVec.ofNat 64 (8 * (j * d / 64)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, x23n, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    show j * d / 2 ^ 6 * 8 % 2 ^ 64 = 8 * (j * d / 64) % 2 ^ 64
    omega
  have hcap : vecCap u (s.getReg .x2 - 464) = BitVec.ofNat 64 cnt := h.vec.cap
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a990_spec (b8000a97c_pc_taken h₂ (by
      rw [k₁ .x18 (by decide), k₁ .x23 (by decide), k₁ .x8 (by decide), h.x18, h.x23, h.x8,
        neg_add_cancel_w, x23n]
      exact hjd)) (by
    rv_eval [sp₂, x23₂, hidx]
    and_intros <;> valid_access hst.valid [hb, hjd])
  have hm₃ := b8000a990_mem_same h₃
  have k₃ := b8000a990_keeps h₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₃ .x2 (by decide), sp₂]
  have hfit := h.inv.fits
  have hhu := h.inv.heap hpre.heap
  have hbuf := h.vec.buf
  have hlen := h.vec.le
  simp only [List.length_append, chunksOf, List.length_map, List.length_range] at hlen
  have hcb : cnt * 8 ≤ heapEnd := by
    rcases hbuf.2 with h0 | h0
    · omega
    · simp only [heapNext] at h0 hfit; omega
  have hcap64 : cnt < 2 ^ 64 := by simp only [heapEnd] at hcb; omega
  have hpc₃ := b8000a990_pc_taken h₃ (by
    rw [k₂ .x26 (by decide), k₁ .x26 (by decide), h.x26, sp₂, hm₂, hm₁]
    rv_eval []
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp only [vecCap] at hcap
    rw [hcap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64] at this
    omega)
  have x1₃ : t₃.getReg .x1 = vecPtr u (s.getReg .x2 - 464) := by
    rw [k₃ .x1 (by decide), k₂ .x1 (by decide), k₁ .x1 (by decide), h.x1]
  have x24₃ : t₃.getReg .x24 = BitVec.ofNat 64 (8 * (r.length + j)) := by
    rw [k₃ .x24 (by decide), k₂ .x24 (by decide), k₁ .x24 (by decide), h.x24]
  have hP := hbuf.2
  have hP8 := hbuf.1
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a934_spec hpc₃ (by
    rv_eval [sp₃, x1₃, x24₃]
    have hPe : 0x20 ≤ (vecPtr u (s.getReg .x2 - 464)).toNat ∧
        (vecPtr u (s.getReg .x2 - 464)).toNat + cnt * 8 ≤ heapEnd := by
      rcases hP with h0 | h0
      · omega
      · have := h.vec.hw; simp only [heapNext] at h0 hfit this; simp only [heapStart] at this; omega
    have hR : Region (vecPtr u (s.getReg .x2 - 464)) (cnt * 8) := heap_region hPe.1 hPe.2 hP8
    have hRb := Region.bounds hR
    refine ⟨by valid_access hst.valid [hb],
      Region.valid hR (by addr_omega [hRb, hjr]) (by addr_omega [hRb, hjr]) (by addr_omega [hRb, hjr]),
      by addr_omega [hPe, hjr, hb]⟩)
  have e₄ := h₄.mem_eq 1 (by decide) rfl rfl
  rv_eval [] at e₄
  have lane : ∀ i, i ≤ 3 →
      u.getMem (s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * i)) = (bitsOf smp).getD i 0 := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 0) = s.getReg .x2 - 384 by addr_omega [hb],
        h.l0]; rfl
    · rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 1) = s.getReg .x2 - 376 by addr_omega [hb],
        h.l1]; rfl
    · rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 2) = s.getReg .x2 - 368 by addr_omega [hb],
        h.l2]; rfl
    · rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 3) = s.getReg .x2 - 360 by addr_omega [hb],
        h.l3]; rfl
  have x25₃ : t₃.getReg .x25 = (bitsOf smp).getD (j * d / 64) 0 := by
    rw [b8000a990_x25 h₃, sp₂, x23₂, hidx, hm₂, hm₁, ← lane (j * d / 64) (by omega)]
    exact congrArg u.getMem (by addr_omega [hb, hjd])
  have x20₃ : t₃.getReg .x20 = (bitsOf smp).getD (j * d / 64 + 1) 0 := by
    rw [b8000a990_x20 h₃, sp₂, x23₂, hidx, hm₂, hm₁, ← lane (j * d / 64 + 1) (by omega)]
    exact congrArg u.getMem (by addr_omega [hb, hjd])
  have x23₃ : t₃.getReg .x23 = BitVec.ofNat 64 (j * d) := by rw [k₃ .x23 (by decide), x23₂]
  have x19₃ : t₃.getReg .x19 = BitVec.ofNat 64 (2 ^ d - 1) := by
    rw [k₃ .x19 (by decide), k₂ .x19 (by decide), k₁ .x19 (by decide), h.x19]
  have hval : t₄.getMem (vecPtr u (s.getReg .x2 - 464) + BitVec.ofNat 64 (8 * (r.length + j))) =
      Model.Pcs.queryWindow (bitsOf smp) (blOf d) d j := by
    rw [x1₃, x24₃, x23₃, x19₃, x25₃, x20₃, chunk_eq _ _ hjd] at e₄
    rw [e₄, Model.Pcs.queryWindow, blOf_sub hd64]
  -- what the chunk wrote
  have hPe : (vecPtr u (s.getReg .x2 - 464)).toNat + cnt * 8 ≤ heapNext u ∧
      heapNext w ≤ (vecPtr u (s.getReg .x2 - 464)).toNat := by
    rcases hP with h0 | h0
    · omega
    · exact ⟨h0.2, h0.1⟩
  have hhs := h.vec.hs
  have hmw := h.mono
  set P := vecPtr u (s.getReg .x2 - 464) with hPdef
  have X₄ : DFrame u t₄ fun a ↦ Within a (s.getReg .x2 - 448) 8 ∨
      Within a (P + BitVec.ofNat 64 (8 * (r.length + j))) 8 := by
    refine (DFrame.of_same (fun a ↦ by rw [hm₃, hm₂, hm₁]) _).trans
      ((holds_dframe h₄).mono fun a ⟨k, hk, hw⟩ ↦ ?_) fun _ h ↦ h
    simp only [b8000a934, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> rv_eval [sp₃, x1₃, x24₃] at hw
    · exact Or.inl (by addr_omega [hw, hb])
    · exact Or.inr hw
  have miss (y : Word) (hy : Within y (s.getReg .x2 - 448) 8 ∨
      Within y (P + BitVec.ofNat 64 (8 * (r.length + j))) 8) :
      y.toNat < heapNext u ∧ heapNext w ≤ y.toNat ∨ Within y (s.getReg .x2 - 448) 8 := by
    rcases hy with hy | hy
    · exact Or.inr hy
    · exact Or.inl ⟨by addr_omega [hy, hPe, hjr], by addr_omega [hy, hPe, hjr]⟩
  have hhi := hhu.hi
  have nx₄ : t₄.getMem nextAddr = u.getMem nextAddr := X₄ _ fun i hi hw ↦ by
    rcases miss _ hw with ⟨h1, -⟩ | h1
    · simp only [heapNext, heapEnd] at h1 hhi; addr_omega [hi, h1, hhi]
    · addr_omega [hi, h1, hb, hnx]
  have hn₄ : heapNext t₄ = heapNext u := by simp only [heapNext, nx₄]
  have inv₄ : InvR s t₄ (t₄.getMem nextAddr) := by
    rw [nx₄]
    refine Inv.step' hpre h.inv X₄ (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx₄ (le_refl _) h.inv.fits
      (by rw [b8000a934_keeps h₄ .x2 (by decide), sp₃, h.sp])
    · rcases miss _ ha with ⟨h1, h2⟩ | h1
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext] at h1; exact h1⟩))
      · exact frame_wr hpre (by addr_omega [h1, hb])
    · rcases miss _ ha with ⟨h1, -⟩ | h1
      · simp only [heapNext, heapEnd] at h1 hhi; addr_omega [h1, hhi, hb]
      · addr_omega [h1, hb]
  have keepS (y : Word) (h1 : (s.getReg .x2 - 1040).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) (h3 : ¬ ((s.getReg .x2 - 448).toNat ≤ y.toNat ∧
        y.toNat < (s.getReg .x2 - 440).toNat)) (h5 : y.toNat % 8 = 0) : t₄.getMem y = u.getMem y :=
    X₄ y fun i hi hw ↦ by
      rcases miss _ hw with ⟨h4, -⟩ | h4
      · simp only [heapNext, heapEnd] at h4 hhi; addr_omega [hi, h1, h2, h4, hhi, hb]
      · addr_omega [hi, h1, h2, h3, h4, h5, hb]
  have k₄ := b8000a934_keeps h₄
  have hl1 : (r ++ chunksOf smp d (j + 1)).length = r.length + j + 1 := by
    simp [chunksOf]; omega
  have hchunks : chunksOf smp d (j + 1) = chunksOf smp d j ++
      [Model.Pcs.queryWindow (bitsOf smp) (blOf d) d j] := by
    simp only [chunksOf, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  have hvec : QVec s w t₄ cnt (r ++ chunksOf smp d (j + 1)) := {
    cap := by
      rw [← h.vec.cap]; exact keepS _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
    len := by
      have := b8000a934_m_x2_592 h₄
      rw [sp₃, k₃ .x26 (by decide), k₂ .x26 (by decide), k₁ .x26 (by decide), h.x26] at this
      rv_eval [] at this
      simp only [vecLen]
      rw [show s.getReg .x2 - 464 + 16 = s.getReg .x2 - 448 by rv_eval [], this, hl1]
      addr_omega [hjr, hcap64]
    buf := by
      have e : vecPtr t₄ (s.getReg .x2 - 464) = P :=
        keepS _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      rw [e]; simp only [NewBuf] at hbuf ⊢; rw [hn₄]; exact hbuf
    elems := by
      have e : vecPtr t₄ (s.getReg .x2 - 464) = P :=
        keepS _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      rw [e, hl1, readWords_snoc, hchunks, ← List.append_assoc]
      have e1 := h.vec.elems
      rw [show (r ++ chunksOf smp d j).length = r.length + j by simp [chunksOf]] at e1
      rw [DFrame.readWords' X₄ (fun a ha hw ↦ by
        rcases ha with ha | ha
        · simp only [heapNext, heapEnd] at hhi; addr_omega [ha, hw, hPe, hjr, hb, hhi]
        · addr_omega [ha, hw, hPe, hjr]) (by addr_omega [hPe, hjr, hhi]), e1, hval]
    le := by rw [hl1]; omega
    hw := h.vec.hw
    hs := h.vec.hs }
  have hm192 : min (192 / d) (cnt - r.length) ≤ 192 :=
    le_trans (Nat.min_le_left _ _) (Nat.div_le_self _ _)
  have x21₃ : t₃.getReg .x21 = BitVec.ofNat 64 (min (192 / d) (cnt - r.length)) := by
    rw [k₃ .x21 (by decide), k₂ .x21 (by decide), k₁ .x21 (by decide), h.x21]
  have x22₃ : t₃.getReg .x22 = BitVec.ofNat 64 j := by
    rw [k₃ .x22 (by decide), k₂ .x22 (by decide), k₁ .x22 (by decide), h.x22]
  have x26₃ : t₃.getReg .x26 = BitVec.ofNat 64 (r.length + j) := by
    rw [k₃ .x26 (by decide), k₂ .x26 (by decide), k₁ .x26 (by decide), h.x26]
  have x22₄ : t₄.getReg .x22 = BitVec.ofNat 64 (j + 1) := by
    rw [b8000a934_x22 h₄, x22₃]; addr_omega [hjm, hm192]
  have x26₄ : t₄.getReg .x26 = BitVec.ofNat 64 (r.length + (j + 1)) := by
    rw [b8000a934_x26 h₄, x26₃]; addr_omega [hjr, hcap64]
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₄ .x2 (by decide), sp₃]
  have kk (r' : Reg) (h1 : r' ∈ [Reg.x8, .x9, .x18, .x19]) : t₄.getReg r' = u.getReg r' := by
    rw [k₄ r' (mem_of_mem h1 _), k₃ r' (mem_of_mem h1 _), k₂ r' (mem_of_mem h1 _),
      k₁ r' (mem_of_mem h1 _)]
  have lanes (o : ℕ) (ho : o = 384 ∨ o = 376 ∨ o = 368 ∨ o = 360) :
      t₄.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
    keepS _ (by rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hb])
      (by rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hb])
      (by rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hb])
      (by rcases ho with rfl | rfl | rfl | rfl <;> addr_omega [hb])
  have hP4 : vecPtr t₄ (s.getReg .x2 - 464) = P :=
    keepS _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  have hr₁₄ := hr₁.trans (hr₂.trans (hr₃.trans hr₄))
  have s832₄ : t₄.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 cnt := by
    rw [← h.s832]
    exact keepS _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  have s824₄ : t₄.getMem (s.getReg .x2 - 824) = BitVec.ofNat 64 (192 / d) := by
    rw [← h.s824]
    exact keepS _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  have fr₄ : DFrame w t₄ (QW s w t₄) := (h.fr.mono fun a ha ↦ QW.of_heap (by rw [hn₄]) ha).trans X₄
    fun a ha ↦ by
      rcases miss _ ha with ⟨h1, h2⟩ | h1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, by rw [hn₄]; exact h1⟩)))))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h1, hb])))
  have htr : ∀ T, TranscriptAt u (s.getReg .x10) T → TranscriptAt t₄ (s.getReg .x10) T :=
    fun T hT ↦ tr_keep hpre h.inv hT X₄ fun a ha ↦ by
      rcases miss _ ha with ⟨h1, h2⟩ | h1
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by simp only [heapNext] at h1 hhi; omega⟩))
      · exact Or.inl (by addr_omega [h1, hb])
  by_cases hlast : j + 1 = min (192 / d) (cnt - r.length)
  · refine ⟨t₄, hr₁₄, Or.inr ⟨htr, Or.inr ⟨hlast, {
      pc := b8000a934_pc_taken h₄ (by rw [x21₃, x22₃]; addr_omega [hlast, hm192])
      sp := sp₄
      inv := inv₄
      fr := fr₄
      mono := by rw [hn₄]; exact h.mono
      x1 := by rw [k₄ .x1 (by decide), x1₃, hP4]
      x8 := by rw [kk .x8 (by decide), h.x8]
      x9 := by rw [kk .x9 (by decide), h.x9]
      x18 := by rw [kk .x18 (by decide), h.x18]
      x19 := by rw [kk .x19 (by decide), h.x19]
      x26 := by rw [x26₄, hl1]; rfl
      s832 := s832₄
      s824 := s824₄
      vec := hvec
      d0 := hd0
      d64 := hd64 }⟩⟩⟩
  have hlt1 : j + 1 < min (192 / d) (cnt - r.length) := by omega
  refine ⟨t₄, hr₁₄, Or.inr ⟨htr, Or.inl ⟨hlt1, {
    pc := b8000a934_pc_not_taken h₄ (by rw [x21₃, x22₃]; addr_omega [hlt1, hm192])
    sp := sp₄
    inv := inv₄
    fr := fr₄
    mono := by rw [hn₄]; exact h.mono
    x1 := by rw [k₄ .x1 (by decide), x1₃, hP4]
    x8 := by rw [kk .x8 (by decide), h.x8]
    x9 := by rw [kk .x9 (by decide), h.x9]
    x18 := by rw [kk .x18 (by decide), h.x18]
    x19 := by rw [kk .x19 (by decide), h.x19]
    x21 := by rw [k₄ .x21 (by decide), x21₃]
    x22 := x22₄
    x23 := by
      rw [b8000a934_x23 h₄, k₃ .x27 (by decide), b8000a97c_x27 h₂, k₁ .x23 (by decide),
        k₁ .x8 (by decide), h.x23, h.x8]
      have e : (j + 1) * d = j * d + d := Nat.succ_mul j d
      rw [e]
      addr_omega [hjd, hd64]
    x24 := by
      rw [b8000a934_x24 h₄, x24₃]
      simp only [heapEnd] at hcb
      addr_omega [hjr, hcb]
    x26 := x26₄
    s832 := s832₄
    s824 := s824₄
    l0 := by rw [← h.l0]; exact lanes 384 (by decide)
    l1 := by rw [← h.l1]; exact lanes 376 (by decide)
    l2 := by rw [← h.l2]; exact lanes 368 (by decide)
    l3 := by rw [← h.l3]; exact lanes 360 (by decide)
    vec := hvec
    jlt := hlt1
    d0 := hd0
    d64 := hd64 }⟩⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
