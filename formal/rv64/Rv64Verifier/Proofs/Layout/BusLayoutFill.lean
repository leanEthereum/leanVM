import Rv64Verifier.Proofs.Layout.BusLayoutBase

/-!
# `bus_layout`: the sizes

From the entry to `0x80010bb8`: the buffer `P` of `try_allocate_in(m + n, 8, 8)` holds the rows
and the blocks' `log_rows` (`srcWord`).
-/

namespace Rv64Verifier.Layout.BusLayout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Bus Rv64Verifier.Blocks.F82
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The sizes' first `k` words written to `P`, a new buffer for `n + m` of them. -/
structure Fill (s u : MachineState) (nx P : Word) (k : Nat) : Prop where
  inv : Inv s u nx
  x8 : u.getReg .x8 = s.getReg .x12
  x9 : u.getReg .x9 = s.getReg .x10
  x18 : u.getReg .x18 = P
  align : P.toNat % 8 = 0
  buf : (s.getReg .x12).toNat + (s.getReg .x14).toNat = 0 ∨ heapNext s ≤ P.toNat ∧
    P.toNat + 8 * ((s.getReg .x12).toNat + (s.getReg .x14).toNat) ≤ nx.toNat
  words : ∀ i < k, u.getMem (P + BitVec.ofNat 64 (8 * i)) = srcWord s i
  le : k ≤ (s.getReg .x12).toNat + (s.getReg .x14).toNat

/-- The facts every step uses. -/
theorem facts {s : MachineState} (h : BusLayoutPre s) :
    (s.getReg .x10).toNat % 8 = 0 ∧ (s.getReg .x10).toNat + 56 ≤ 0xc0000000 ∧
      8 * (s.getReg .x12).toNat ≤ 0xc0000000 ∧ 48 * (s.getReg .x14).toNat ≤ 0xc0000000 ∧
      ((s.getReg .x12).toNat = 0 ∨ (s.getReg .x11).toNat % 8 = 0 ∧
        (s.getReg .x11).toNat + 8 * (s.getReg .x12).toNat ≤ 0xc0000000) ∧
      ((s.getReg .x14).toNat = 0 ∨ (s.getReg .x13).toNat % 8 = 0 ∧
        (s.getReg .x13).toNat + 48 * (s.getReg .x14).toNat ≤ 0xc0000000) := by
  have ho := h.out
  have hr := h.rows.region
  have hk := h.blocks.region
  simp only [Transcript.Region, Mapped] at ho hr hk
  omega

theorem Fill.mono {s u v : MachineState} {nx P : Word} {k : Nat} (h : Fill s u nx P k)
    (hpre : BusLayoutPre s) (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x9, .x18, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Fill s v nx P k where
  inv := h.inv.same hpre hm hr
  x8 := (hr _ (by decide)).trans h.x8
  x9 := (hr _ (by decide)).trans h.x9
  x18 := (hr _ (by decide)).trans h.x18
  align := h.align
  buf := h.buf
  words := fun i hi ↦ (hm _).trans (h.words i hi)
  le := h.le

/-- From the entry through `reserve` to `0x80010b54`'s branch: an empty buffer `P`. -/
theorem start (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x8000d628) {s : MachineState}
    (hpc : s.pc = 0x80010acc) (hpre : BusLayoutPre s) :
    ∃ u, Reaches Image.code s u ∧ ((∃ nx P, Fill s u nx P 0 ∧
      u.pc = (if s.getReg .x12 = 0 then 0x80010b80 else 0x80010b64) ∧
      u.getReg .x19 = 0 ∧ u.getReg .x20 = s.getReg .x14 ∧ u.getReg .x21 = s.getReg .x13 ∧
      u.getReg .x22 = s.getReg .x11 ∧ u.getReg .x23 = 0) ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hheap := hpre.heap
  obtain ⟨ho8, ho56, hn8, hm48, -, -⟩ := facts hpre
  obtain ⟨t₁, hr₁, h₁⟩ := BlockSpec.reaches b80010acc_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80010acc_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack112 hpre)
    (by rw [b80010acc_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b80010acc_m_x2_n8 h₁, b80010acc_m_x2_n16 h₁, b80010acc_m_x2_n24 h₁,
        b80010acc_m_x2_n32 h₁, b80010acc_m_x2_n40 h₁, b80010acc_m_x2_n48 h₁, b80010acc_m_x2_n56 h₁,
        b80010acc_m_x2_n64 h₁, b80010acc_m_x2_n72 h₁⟩)
    (fun r hr ↦ k₁ r (by revert hr; revert r; decide))
    ((b80010acc_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 112 := b80010acc_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 104 := b80010acc_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = s.getReg .x2 - 160 := by
    simp only [stackLo, tryAllocStack, hsp₁]; rv_eval []
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b80010acc_x13 h₁]; decide
    size := by rw [b80010acc_x14 h₁]; decide
    stack := hst.sub 112 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b80010acc_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := inv₁.step hpre hfr₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr ha))
    rfl (by rw [← heapNext, ← heapNext, ← hn₁]; exact hpost₂.mono) hpost₂.heap.hi
    fun r hr ↦ hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 112 := (hpres₂.reg .x2).trans hsp₁
  obtain ⟨t₃, hr₃, h₃⟩ := BlockSpec.reaches b80010b28_spec
    (by rw [hpc₂, returnAddress_eq, b80010acc_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  rcases eq_or_ne (t₂.getMem (s.getReg .x2 - 104)) 0 with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b80010b28_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b80010b28_keeps h₃
  have inv₃ := inv₂.same hpre (b80010b28_mem_same h₃) k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, b80010acc_x11 h₁] at hcap hbuf
  rw [b80010acc_x14 h₁, b80010acc_x13 h₁] at hbuf
  rv_eval [] at hcap hbuf
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 88) := ⟨_, rfl⟩
  rw [← hP] at hbuf
  simp only [NewBuf, hn₁] at hbuf
  have hlen : (s.getReg .x14 + s.getReg .x12).toNat = (s.getReg .x12).toNat + (s.getReg .x14).toNat := by
    addr_omega [hn8, hm48]
  rw [hlen] at hbuf
  -- `0x80010b30`: the `Vec` at `S - 104`, then `reserve`
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 112 := (k₃ .x2 (by decide)).trans hsp₂
  obtain ⟨t₄, hr₄, h₄⟩ := BlockSpec.reaches b80010b30_spec
    (b80010b28_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)) (by
      rv_eval [hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b80010b30_keeps h₄
  have m₈ := b80010b30_m_x2_8 h₄
  have m₁₆ := b80010b30_m_x2_16 h₄
  have m₂₄ := b80010b30_m_x2_24 h₄
  rw [hsp₃] at m₈ m₁₆ m₂₄
  rv_eval [b80010b28_mem_same h₃] at m₈ m₁₆ m₂₄
  have inv₄ : Inv s t₄ (t₂.getMem nextAddr) := inv₃.frame hpre (b80010b30_frame h₄ (by rw [hsp₃]; addr_omega [hb]))
    (by rw [hsp₃]; addr_omega [hb]) (by decide) (h₄.unaligned (by rv_eval [hsp₃]; and_intros <;> addr_omega [hb]))
    (fun a ha ↦ Or.inl (Or.inr (by rw [hsp₃] at ha; addr_omega [ha, hb]))) k₄
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 112 := (k₄ .x2 (by decide)).trans hsp₃
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 104 := by rw [b80010b30_x10 h₄, hsp₃]; rv_eval []
  have hx11₄ : t₄.getReg .x11 = s.getReg .x14 + s.getReg .x12 := by
    rw [b80010b30_x11 h₄, k₃ .x18 (by decide), hpres₂.reg .x18, b80010acc_x18 h₁]
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hx10₅, hm₅⟩ | hdead⟩ := hR.call hr₄ (b80010b30_pc h₄) ⟨by
      rw [hx10₄]; valid_sub hst.valid [hb], by
      simp only [vecLen, vecCap, hx10₄, hx11₄]
      rv_eval []
      rw [m₂₄, m₈, hcap]
      simp⟩
  swap
  · exact ⟨t₅, hr₂.trans (hr₃.trans hr₅), Or.inr hdead⟩
  have inv₅ := inv₄.same hpre hm₅ (l := calleeSaved) (fun r hr ↦ hpres₅ r hr)
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 112 := (hpres₅.reg .x2).trans hsp₄
  obtain ⟨t₆, hr₆, h₆⟩ := BlockSpec.reaches b80010b54_spec
    (by rw [hpc₅, returnAddress_eq, b80010b30_x1 h₄]; decide) (by
      rv_eval [hsp₅]
      and_intros <;> valid_access hst.valid [hb])
  have k₆ := b80010b54_keeps h₆
  have hm₆ := b80010b54_mem_same h₆
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x20, .x21, .x22, .x24, .x25, .x26, .x27]) :
      t₆.getReg r = t₁.getReg r := by
    rw [k₆ r (by revert hr; revert r; decide), hpres₅ r (by unfold calleeSaved; revert hr; revert r; decide),
      k₄ r (by revert hr; revert r; decide), k₃ r (by revert hr; revert r; decide),
      hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide)]
  have hx18 : t₆.getReg .x18 = P := by
    rw [b80010b54_x18 h₆, hsp₅]; rv_eval [hm₅, m₁₆, hP]
  have hz : t₅.getMem (s.getReg .x2 - 88) = 0 := by rw [hm₅, m₂₄]
  have x8₆ : t₆.getReg .x8 = s.getReg .x12 := by rw [hreg .x8 (by decide), b80010acc_x8 h₁]
  refine ⟨t₆, hr₂.trans (hr₃.trans (hr₅.trans hr₆)), Or.inl
    ⟨t₂.getMem nextAddr, P, {
      inv := inv₅.same hpre hm₆ k₆
      x8 := x8₆
      x9 := by rw [hreg .x9 (by decide), b80010acc_x9 h₁]
      x18 := hx18
      align := hbuf.1
      buf := by
        rcases hbuf.2 with h0 | h0
        · exact Or.inl (by omega)
        · exact Or.inr ⟨h0.1, by simp only [heapNext] at h0; omega⟩
      words := fun i hi ↦ absurd hi (Nat.not_lt_zero _)
      le := Nat.zero_le _ }, ?_, ?_, by rw [hreg .x20 (by decide), b80010acc_x20 h₁],
      by rw [hreg .x21 (by decide), b80010acc_x21 h₁], by rw [hreg .x22 (by decide), b80010acc_x22 h₁],
      ?_⟩⟩
  · have x8₅ : t₅.getReg .x8 = s.getReg .x12 := (k₆ .x8 (by decide)).symm.trans x8₆
    by_cases h0 : s.getReg .x12 = 0
    · rw [b80010b54_pc_taken h₆ (by rw [x8₅, h0])]; simp [h0]
    · rw [b80010b54_pc_not_taken h₆ (by rw [x8₅]; exact h0)]; simp only [h0, ↓reduceIte]
  · rw [b80010b54_x19 h₆, hsp₅]; rv_eval [hz]
  · rw [b80010b54_x23 h₆, hsp₅]; rv_eval [hz]


/-- `0x80010b64`: the rows, `memcpy`d into `P`. -/
theorem rows (hM : MemcpySpec 0x800126e4) {s u : MachineState} (hpre : BusLayoutPre s)
    {nx P : Word} (h : Fill s u nx P 0) (hpc : u.pc = 0x80010b64) (hn : s.getReg .x12 ≠ 0)
    (x22 : u.getReg .x22 = s.getReg .x11) (x23 : u.getReg .x23 = 0) :
    ∃ v, Reaches Image.code u v ∧ ((Fill s v nx P (s.getReg .x12).toNat ∧ v.pc = 0x80010b80 ∧
      v.getReg .x19 = s.getReg .x12 ∧ ∀ r ∈ [Reg.x20, .x21, .x23], v.getReg r = u.getReg r) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  obtain ⟨-, -, hn8, -, hrows, -⟩ := facts hpre
  have hn0 : (s.getReg .x12).toNat ≠ 0 := fun h0 ↦ hn (BitVec.eq_of_toNat_eq h0)
  obtain ⟨hr8, hrb⟩ := hrows.resolve_left hn0
  obtain ⟨hlo, hhi⟩ := h.buf.resolve_left (by omega)
  have hP8 := h.align
  have hfit := h.inv.fits
  have hlo0 := hpre.heap.lo
  have hsp : u.getReg .x2 = s.getReg .x2 - 112 := h.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches b80010b64_spec hpc (by rv_eval [])
  have k₁ := b80010b64_keeps h₁
  have x10₁ : u₁.getReg .x10 = P := by rw [b80010b64_x10 h₁, x23, h.x18]; rv_eval []
  have x11₁ : u₁.getReg .x11 = s.getReg .x11 := by rw [b80010b64_x11 h₁, x22]
  have x12₁ : u₁.getReg .x12 = s.getReg .x12 * 8 := by rw [b80010b64_x12 h₁, h.x8]
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 112 := (k₁ .x2 (by decide)).trans hsp
  have h12 : (s.getReg .x12 * 8).toNat = 8 * (s.getReg .x12).toNat := by addr_omega [hn8]
  have hsl : stackLo u₁ memcpyStack = s.getReg .x2 - 128 := by
    simp only [stackLo, x2₁, memcpyStack]; rv_eval []
  have hrd := hpre.rows
  have hRr := hrd.region.resolve_left (by omega)
  have hrs := hrd.stack
  have hrf := hrd.free
  simp only [Outside] at hrf
  have hmc : MemcpyPre u₁ := {
    dst := by rw [x10₁, x12₁, h12]; addr_omega [hlo, hhi, hfit, hlo0]
    src := by rw [x11₁, x12₁, h12]; exact hRr.1
    apart := by rw [x10₁, x11₁, x12₁, h12]; addr_omega [hrf, hlo, hhi, hfit]
    stack := (hst.sub 112 x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    dstStack := by rw [x10₁, x12₁, h12, hsl]; addr_omega [hb, hab, hlo, hhi, hfit]
    srcStack := by rw [x11₁, x12₁, h12, hsl]; addr_omega [hb, hrs] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hmp⟩ | hdead⟩ := hM.call hr₁ (b80010b64_pc h₁) hmc
  swap
  · exact ⟨w, hr₂, Or.inr hdead⟩
  have hbytes := hmp.bytes
  rw [x10₁, x11₁, x12₁, h12] at hbytes
  have hfr := hmp.frame
  rw [x10₁, x12₁, h12, hsl] at hfr
  have inv₁ : Inv s u₁ nx := h.inv.same hpre (b80010b64_mem_same h₁) k₁
  have hnext : w.getMem nextAddr = nx := by
    rw [hfr.getMem fun i hi hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hw, hi, hhi, hfit, hb, hnx8],
      inv₁.next]
  have inv₂ : Inv s w nx := inv₁.step hpre hfr (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (by addr_omega [ha, hlo, hhi]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb])))
    hnext (Nat.le_refl _) hfit fun r hr ↦ hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide)
  obtain ⟨v, hr₃, h₃⟩ := BlockSpec.reaches b80010b7c_spec
    (by rw [hpc₂, returnAddress_eq, b80010b64_x1 h₁]; decide) (by rv_eval [])
  have k₃ := b80010b7c_keeps h₃
  have hm₃ := b80010b7c_mem_same h₃
  have hreg (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27]) :
      v.getReg r = u.getReg r := by
    rw [k₃ r (by revert hr; revert r; decide), hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide),
      k₁ r (by revert hr; revert r; decide)]
  refine ⟨v, hr₂.trans hr₃, Or.inl ⟨{
      inv := inv₂.same hpre hm₃ k₃
      x8 := (hreg .x8 (by decide)).trans h.x8
      x9 := (hreg .x9 (by decide)).trans h.x9
      x18 := (hreg .x18 (by decide)).trans h.x18
      align := hP8
      buf := h.buf
      words := fun i hi ↦ ?_
      le := by omega }, b80010b7c_pc h₃, ?_, fun r hr ↦ hreg r (by revert hr; revert r; decide)⟩⟩
  · rw [hm₃, getMem_eq_of_bytesAt hbytes hP8 hr8 (k := 8 * i) (by omega) (by omega),
      b80010b64_mem_same h₁, h.inv.read hpre hrd (by addr_omega [hrb, hi]) (by addr_omega [hrb, hi])]
    simp only [srcWord, hi, ↓reduceIte]
  · rw [b80010b7c_x19 h₃, hpres₂.reg .x23, k₁ .x23 (by decide), x23, hpres₂.reg .x8,
      k₁ .x8 (by decide), h.x8]
    exact BitVec.zero_add _

/-- At the head of the loop that copies block `j`'s `log_rows`. -/
structure Loop (s u : MachineState) (nx P : Word) (j : Nat) : Prop where
  fill : Fill s u nx P ((s.getReg .x12).toNat + j)
  lt : j < (s.getReg .x14).toNat
  pc : u.pc = 0x80010ba4
  x10 : u.getReg .x10 = P + BitVec.ofNat 64 (8 * ((s.getReg .x12).toNat + j))
  x11 : u.getReg .x11 = P + BitVec.ofNat 64 (8 * ((s.getReg .x12).toNat + (s.getReg .x14).toNat))
  x19 : u.getReg .x19 = BitVec.ofNat 64 ((s.getReg .x12).toNat + (s.getReg .x14).toNat)
  x21 : u.getReg .x21 = s.getReg .x13 + BitVec.ofNat 64 (48 * j + 24)

/-- The sizes in `P`, at `0x80010bb8`. -/
structure Filled (s u : MachineState) (nx P : Word) : Prop where
  fill : Fill s u nx P ((s.getReg .x12).toNat + (s.getReg .x14).toNat)
  pc : u.pc = 0x80010bb8
  x19 : u.getReg .x19 = BitVec.ofNat 64 ((s.getReg .x12).toNat + (s.getReg .x14).toNat)

theorem body {s u : MachineState} (hpre : BusLayoutPre s) {nx P : Word} {j : Nat}
    (h : Loop s u nx P j) :
    ∃ v, Reaches Image.code u v ∧ ((Loop s v nx P (j + 1) ∧
      (v.getReg .x11).toNat - (v.getReg .x10).toNat < (u.getReg .x11).toNat - (u.getReg .x10).toNat) ∨
      Filled s v nx P) := by
  obtain ⟨-, -, hn8, hm48, -, hblk⟩ := facts hpre
  have hlt := h.lt
  obtain ⟨hk8, hkb⟩ := hblk.resolve_left (by omega)
  have hF := h.fill
  obtain ⟨hlo, hhi⟩ := hF.buf.resolve_left (by omega)
  have hP8 := hF.align
  have hfit := hF.inv.fits
  have hlo0 := hpre.heap.lo
  have hbr := hpre.blocks
  have hR := hbr.region.resolve_left (by omega)
  have x10 := h.x10
  have x11 := h.x11
  have x21 := h.x21
  obtain ⟨v, hr, hv⟩ := BlockSpec.reaches b80010ba4_spec h.pc (by
    rv_eval [x10, x21]
    and_intros
    · exact Mapped.valid8 (a := P) (n := 8 * ((s.getReg .x12).toNat + (s.getReg .x14).toNat))
        (by simp only [Mapped]; addr_omega [hlo, hhi, hfit, hlo0, hlt]) (by addr_omega [hhi, hfit, hlt])
        (by addr_omega [hhi, hfit, hlt]) (by addr_omega [hhi, hfit, hP8, hlt])
    · exact Transcript.Region.valid hR (by addr_omega [hkb, hlt]) (by addr_omega [hkb, hlt])
        (by addr_omega [hkb, hk8, hlt]))
  have k := b80010ba4_keeps hv
  have hw := b80010ba4_m_x10_0 hv
  rw [x10, x21, hF.inv.read hpre hbr (by addr_omega [hkb, hlt]) (by addr_omega [hkb, hlt])] at hw
  have hfr := b80010ba4_frame hv (by rw [x10]; addr_omega [hhi, hfit, hlt])
  rw [x10] at hfr
  have inv := hF.inv.frame hpre hfr (by addr_omega [hhi, hfit, hP8, hlt]) (by decide)
    (hv.unaligned (by rv_eval [x10]; addr_omega [hhi, hfit, hP8, hlt]))
    (fun a ha ↦ Or.inr (by addr_omega [ha, hlo, hhi, hlt])) k
  have hF' : Fill s v nx P ((s.getReg .x12).toNat + (j + 1)) := {
    inv := inv
    x8 := (k .x8 (by decide)).trans hF.x8
    x9 := (k .x9 (by decide)).trans hF.x9
    x18 := (k .x18 (by decide)).trans hF.x18
    align := hP8
    buf := hF.buf
    words := fun i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : i < (s.getReg .x12).toNat + j + 1) with hi' | rfl
      · rw [hfr _ fun hw' ↦ by addr_omega [hw', hi', hhi, hfit, hlt]]
        exact hF.words i hi'
      · rw [hw]
        have hn : ¬ (s.getReg .x12).toNat + j < (s.getReg .x12).toNat := by omega
        simp only [srcWord, hn, ↓reduceIte, Nat.add_sub_cancel_left]
        congr 1
        addr_omega [hkb, hlt]
    le := by omega }
  have y10 : v.getReg .x10 = P + BitVec.ofNat 64 (8 * ((s.getReg .x12).toNat + (j + 1))) := by
    rw [b80010ba4_x10 hv, x10]; addr_omega [hhi, hfit, hlt]
  have y11 : v.getReg .x11 = u.getReg .x11 := k .x11 (by decide)
  refine ⟨v, hr, ?_⟩
  by_cases hj : j + 1 < (s.getReg .x14).toNat
  · refine Or.inl ⟨{
      fill := hF'
      lt := hj
      pc := b80010ba4_pc_taken hv (by rw [x10, x11]; addr_omega [hhi, hfit, hj])
      x10 := y10
      x11 := y11.trans x11
      x19 := (k .x19 (by decide)).trans h.x19
      x21 := by rw [b80010ba4_x21 hv, x21]; addr_omega [hkb, hj] }, ?_⟩
    rw [y10, y11, x10, x11]
    addr_omega [hhi, hfit, hj]
  · have hj' : j + 1 = (s.getReg .x14).toNat := by omega
    rw [hj'] at hF'
    exact Or.inr {
      fill := hF'
      pc := b80010ba4_pc_not_taken hv (by rw [x10, x11]; addr_omega [hhi, hfit, hj'])
      x19 := (k .x19 (by decide)).trans h.x19 }

/-- From the entry to `0x80010bb8`, the sizes in `P`. -/
theorem filled (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x8000d628)
    (hM : MemcpySpec 0x800126e4) {s : MachineState} (hpc : s.pc = 0x80010acc)
    (hpre : BusLayoutPre s) :
    ∃ u, Reaches Image.code s u ∧ ((∃ nx P, Filled s u nx P) ∨ Dead Image.code u) := by
  obtain ⟨-, -, hn8, hm48, -, -⟩ := facts hpre
  obtain ⟨u, hr, ⟨nx, P, hF, hpcu, x19, x20, x21, x22, x23⟩ | hd⟩ := start hT hR hpc hpre
  swap
  · exact ⟨u, hr, Or.inr hd⟩
  have hmid : ∃ v, Reaches Image.code u v ∧ ((Fill s v nx P (s.getReg .x12).toNat ∧
      v.pc = 0x80010b80 ∧ v.getReg .x19 = s.getReg .x12 ∧ v.getReg .x20 = s.getReg .x14 ∧
      v.getReg .x21 = s.getReg .x13 ∧ v.getReg .x23 = 0) ∨ Dead Image.code v) := by
    by_cases hn : s.getReg .x12 = 0
    · have hn' : (s.getReg .x12).toNat = 0 := by rw [hn]; rfl
      exact ⟨u, Reaches.refl u, Or.inl ⟨hn' ▸ hF, by rw [hpcu]; simp [hn], by rw [x19, hn], x20,
        x21, x23⟩⟩
    · obtain ⟨v, hr', ⟨hF', hpc', x19', hk⟩ | hd⟩ :=
        rows hM hpre hF (by rw [hpcu]; simp only [hn, ↓reduceIte]) hn x22 x23
      · exact ⟨v, hr', Or.inl ⟨hF', hpc', x19', (hk .x20 (by decide)).trans x20,
          (hk .x21 (by decide)).trans x21, (hk .x23 (by decide)).trans x23⟩⟩
      · exact ⟨v, hr', Or.inr hd⟩
  obtain ⟨v, hr', ⟨hF, hpcv, y19, y20, y21, y23⟩ | hd⟩ := hmid
  swap
  · exact ⟨v, hr.trans hr', Or.inr hd⟩
  obtain ⟨w, hr₁, h₁⟩ := BlockSpec.reaches b80010b80_spec hpcv (by rv_eval [])
  have k₁ := b80010b80_keeps h₁
  have hF₁ := hF.mono hpre (b80010b80_mem_same h₁) fun r hr ↦ k₁ r (by revert hr; revert r; decide)
  by_cases hm : s.getReg .x14 = 0
  · have hm' : (s.getReg .x14).toNat = 0 := by rw [hm]; rfl
    refine ⟨w, hr.trans (hr'.trans hr₁), Or.inl ⟨nx, P, {
      fill := by rw [hm', Nat.add_zero]; exact hF₁
      pc := b80010b80_pc_taken h₁ (by rw [y20, hm])
      x19 := by rw [k₁ .x19 (by decide), y19, hm', Nat.add_zero]; addr_omega [hn8] }⟩⟩
  have hm0 : (s.getReg .x14).toNat ≠ 0 := fun h0 ↦ hm (BitVec.eq_of_toNat_eq h0)
  obtain ⟨hlo, hhi⟩ := hF.buf.resolve_left (by omega)
  have hfit := hF.inv.fits
  obtain ⟨w₂, hr₂, h₂⟩ := BlockSpec.reaches b80010b84_spec (b80010b80_pc_not_taken h₁ (by rw [y20]; exact hm))
    (by rv_eval [])
  have k₂ := b80010b84_keeps h₂
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x18, .x19, .x20, .x21, .x23]) : w.getReg r = v.getReg r :=
    k₁ r (by revert hr; revert r; decide)
  have L0 : Loop s w₂ nx P 0 := {
    fill := by
      rw [Nat.add_zero]
      exact hF₁.mono hpre (b80010b84_mem_same h₂) fun r hr ↦ k₂ r (by revert hr; revert r; decide)
    lt := by omega
    pc := b80010b84_pc h₂
    x10 := by
      rw [b80010b84_x10 h₂, hreg .x18 (by decide), hreg .x19 (by decide), hF.x18, y19]
      addr_omega [hn8, hhi, hfit]
    x11 := by
      rw [b80010b84_x11 h₂, hreg .x18 (by decide), hreg .x19 (by decide), hreg .x20 (by decide),
        hF.x18, y19, y20]
      addr_omega [hn8, hm48, hhi, hfit]
    x19 := by
      rw [b80010b84_x19 h₂, hreg .x23 (by decide), hreg .x20 (by decide), hreg .x8 (by decide),
        y23, y20, hF.x8]
      addr_omega [hn8, hm48]
    x21 := by rw [b80010b84_x21 h₂, hreg .x21 (by decide), y21]; rfl }
  obtain ⟨t, ht, hdone⟩ := Reaches.loop (code := Image.code) (fun u ↦ ∃ j, Loop s u nx P j)
    (fun u ↦ (u.getReg .x11).toNat - (u.getReg .x10).toNat) (fun u ↦ Filled s u nx P)
    (fun u ⟨j, hj⟩ ↦ by
      obtain ⟨y, hry, ⟨hl, hlt⟩ | hd⟩ := body hpre hj
      · exact Or.inr ⟨y, hry, ⟨j + 1, hl⟩, hlt⟩
      · exact Or.inl ⟨y, hry, hd⟩) w₂ ⟨0, L0⟩
  exact ⟨t, hr.trans (hr'.trans (hr₁.trans (hr₂.trans ht))), Or.inl ⟨nx, P, hdone⟩⟩

end Rv64Verifier.Layout.BusLayout
