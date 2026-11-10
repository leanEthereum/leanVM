import Rv64Verifier.Proofs.Layout.BusLayoutZip

/-!
# `bus_layout`: the split

From `0x80010c04` through the pairs' loop, `try_allocate_in(m, 8, 16)` (`T` its buffer) and the
`memcpy` of the last `m` pairs to `T`, up to `0x80010c88`.
-/

namespace Rv64Verifier.Layout.BusLayout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Bus Rv64Verifier.Blocks.F82
  Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- From `0x80010c04`'s branch to `0x80010c38`, every pair written. -/
theorem zipped {s u : MachineState} (hpre : BusLayoutPre s) {nx P Q R : Word}
    (h : Zip s u nx P Q R 0) (hpc : u.pc = (if nn s = 0 then 0x80010c38 else 0x80010c0c))
    (x18 : u.getReg .x18 = P) (x22 : u.getReg .x22 = Q) :
    ∃ v, Reaches Image.code u v ∧ Zip s v nx P Q R (nn s) ∧ v.pc = 0x80010c38 := by
  by_cases hz : nn s = 0
  · simp only [hz, ↓reduceIte] at hpc
    exact ⟨u, Reaches.refl u, hz ▸ h, hpc⟩
  simp only [hz, ↓reduceIte] at hpc
  have hbuf := h.bufs.resolve_left hz
  have hfit := h.inv.fits
  obtain ⟨-, -, hn8, hm48, -, -⟩ := facts hpre
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches b80010c0c_spec hpc (by rv_eval [])
  have k₁ := b80010c0c_keeps h₁
  have L0 : ZLoop s u₁ nx P Q R 0 := {
    zip := h.mono hpre (b80010c0c_mem_same h₁) fun r hr ↦ k₁ r (by revert hr; revert r; decide)
    lt := by omega
    pc := b80010c0c_pc h₁
    x10 := by rw [b80010c0c_x10 h₁, h.x21]; rfl
    x11 := by rw [b80010c0c_x11 h₁, h.x21, h.x19]; addr_omega [hbuf, hfit, hn8, hm48]
    x18 := by rw [k₁ .x18 (by decide), x18]; simp
    x22 := by rw [k₁ .x22 (by decide), x22]; simp }
  obtain ⟨t, ht, hZ, hpct⟩ := Reaches.loop (code := Image.code) (fun u ↦ ∃ k, ZLoop s u nx P Q R k)
    (fun u ↦ (u.getReg .x11).toNat - (u.getReg .x10).toNat)
    (fun u ↦ Zip s u nx P Q R (nn s) ∧ u.pc = 0x80010c38)
    (fun u ⟨k, hk⟩ ↦ by
      obtain ⟨y, hry, ⟨hl, hlt⟩ | hd⟩ := zbody hpre hk
      · exact Or.inr ⟨y, hry, ⟨k + 1, hl⟩, hlt⟩
      · exact Or.inl ⟨y, hry, hd⟩) u₁ ⟨0, L0⟩
  exact ⟨t, hr₁.trans ht, hZ, hpct⟩

/-- At `0x80010c88`: the first `n` pairs at `R`, the last `m` at `T`. -/
structure Final (s u : MachineState) (nx R T : Word) : Prop where
  inv : Inv s u nx
  pc : u.pc = 0x80010c88
  x8 : u.getReg .x8 = s.getReg .x12
  x9 : u.getReg .x9 = s.getReg .x10
  x18 : u.getReg .x18 = s.getReg .x14
  x19 : u.getReg .x19 = T
  x20 : (u.getReg .x20).toNat = (Model.stackOffsetsRust (sizesList s)).2
  x21 : u.getReg .x21 = R
  x22 : u.getReg .x22 = BitVec.ofNat 64 (nn s)
  x23 : u.getReg .x23 = s.getReg .x14
  ralign : R.toNat % 8 = 0
  talign : T.toNat % 8 = 0
  rbuf : nn s = 0 ∨ heapNext s ≤ R.toNat ∧ R.toNat + 16 * nn s ≤ nx.toNat
  tbuf : (s.getReg .x14).toNat = 0 ∨ heapNext s ≤ T.toNat ∧
    T.toNat + 16 * (s.getReg .x14).toNat ≤ nx.toNat
  head : ∀ i < (s.getReg .x12).toNat, u.getMem (R + BitVec.ofNat 64 (16 * i)) = srcWord s i ∧
    u.getMem (R + BitVec.ofNat 64 (16 * i) + 8) = (offs s).getD i 0
  tail : ∀ i < (s.getReg .x14).toNat,
    u.getMem (T + BitVec.ofNat 64 (16 * i)) = srcWord s ((s.getReg .x12).toNat + i) ∧
    u.getMem (T + BitVec.ofNat 64 (16 * i) + 8) = (offs s).getD ((s.getReg .x12).toNat + i) 0
  offsLen : (offs s).length = nn s

/-- From `0x80010c38` through `try_allocate_in` and `memcpy` to `0x80010c88`. -/
theorem split (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s u : MachineState}
    (hpre : BusLayoutPre s) {nx P Q R : Word} (h : Zip s u nx P Q R (nn s))
    (hpc : u.pc = 0x80010c38) :
    ∃ v, Reaches Image.code u v ∧ ((∃ nx' T, Final s v nx' R T) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  obtain ⟨-, -, hn8, hm48, -, -⟩ := facts hpre
  have hfit := h.inv.fits
  have hmono := h.inv.mono
  have hlo0 := hpre.heap.lo
  have hR8 := h.ralign
  have hsp : u.getReg .x2 = s.getReg .x2 - 112 := h.inv.sp
  have hnn : nn s = (s.getReg .x12).toNat + (s.getReg .x14).toNat := rfl
  have hN : (BitVec.ofNat 64 (nn s)).toNat = nn s := by addr_omega [hn8, hm48]
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches b80010c38_spec hpc (by rv_eval [])
  have k₁ := b80010c38_keeps h₁
  obtain ⟨u₂, hr₂, h₂⟩ := BlockSpec.reaches b80010c3c_spec
    (b80010c38_pc_not_taken h₁ (by rw [h.x8, h.x19, hN]; omega)) (by
      rv_eval [k₁ .x2 (by decide), hsp]; valid_access hst.valid [hb])
  have k₂ := b80010c3c_keeps h₂
  have inv₂ := (h.inv.same hpre (b80010c38_mem_same h₁) k₁).same hpre (b80010c3c_mem_same h₂) k₂
  have x2₂ : u₂.getReg .x2 = s.getReg .x2 - 112 := by rw [k₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 104 := by
    rw [b80010c3c_x10 h₂, k₁ .x2 (by decide), hsp]; rv_eval []
  have hM' : BitVec.ofNat 64 (nn s) - s.getReg .x12 = s.getReg .x14 := by addr_omega [hn8, hm48]
  have x11₂ : u₂.getReg .x11 = s.getReg .x14 := by
    rw [b80010c3c_x11 h₂, k₁ .x19 (by decide), k₁ .x8 (by decide), h.x19, h.x8, hM']
  have x18₂ : u₂.getReg .x18 = s.getReg .x14 := by
    rw [b80010c3c_x18 h₂, k₁ .x19 (by decide), k₁ .x8 (by decide), h.x19, h.x8, hM']
  have x22₂ : u₂.getReg .x22 = BitVec.ofNat 64 (nn s) := by
    rw [b80010c3c_x22 h₂, k₁ .x2 (by decide), hsp]; rv_eval [b80010c38_mem_same h₁, h.cap]
  have hn₂ : heapNext u₂ = nx.toNat := by simp only [heapNext, inv₂.next]
  have hsl : stackLo u₂ tryAllocStack = s.getReg .x2 - 160 := by
    simp only [stackLo, tryAllocStack, x2₂]; rv_eval []
  have hpre₂ : TryAllocPre .x13 .x14 u₂ := {
    heap := ⟨by rw [hn₂]; exact Nat.le_trans hlo0 hmono, by rw [hn₂]; exact hfit⟩
    out := by rw [x10₂]; valid_sub hst.valid [hb]
    align := by rw [b80010c3c_x13 h₂]; decide
    size := by rw [b80010c3c_x14 h₂]; decide
    stack := hst.sub 112 x2₂ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₂]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [x10₂, hsl]; addr_omega [hb] }
  obtain ⟨u₃, hr₃, ⟨hpc₃, hpres₃, hpost₃, -⟩ | hdead⟩ := hT.call hr₂ (b80010c3c_pc h₂) hpre₂
  swap
  · exact ⟨u₃, hr₁.trans hr₃, Or.inr hdead⟩
  have hfr₃ := hpost₃.frame
  rw [x10₂, hsl] at hfr₃
  have inv₃ : Inv s u₃ (u₃.getMem nextAddr) := inv₂.step hpre hfr₃ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₂] at ha
        exact Or.inr (Or.inr ⟨Nat.le_trans hmono ha.1, ha.2⟩))
    rfl (by have := hpost₃.mono; rw [hn₂] at this; exact this) hpost₃.heap.hi
    fun r hr ↦ hpres₃ r (by unfold calleeSaved; revert hr; revert r; decide)
  have kb₃ {p : Word} (hp : p.toNat + 8 ≤ nx.toNat) : u₃.getMem p = u.getMem p := by
    rw [keep_below hfr₃ (fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · rw [hn₂]; addr_omega [ha, hb, hab, hfit]
        · rw [hn₂]; addr_omega [ha, hb, hab, hfit]
        · rw [hn₂]; addr_omega [ha, hfit]
        · exact ha.1) (by rw [hn₂]; exact hp), b80010c3c_mem_same h₂, b80010c38_mem_same h₁]
  have x2₃ : u₃.getReg .x2 = s.getReg .x2 - 112 := (hpres₃.reg .x2).trans x2₂
  obtain ⟨u₄, hr₄, h₄⟩ := BlockSpec.reaches b80010c60_spec
    (by rw [hpc₃, returnAddress_eq, b80010c3c_x1 h₂]; decide) (by
      rv_eval [x2₃]; valid_access hst.valid [hb])
  rcases eq_or_ne (u₃.getMem (s.getReg .x2 - 104)) 0 with htag | htag
  swap
  · refine ⟨u₄, hr₁.trans (hr₃.trans hr₄), Or.inr (dead_of_fetch ?_)⟩
    rw [b80010c60_pc_taken h₄ (by rv_eval [x2₃]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₄ := b80010c60_keeps h₄
  obtain ⟨hcap, hbufT⟩ := hpost₃.ok (by rw [x10₂]; exact htag)
  rw [x10₂, x11₂] at hcap hbufT
  rw [b80010c3c_x14 h₂, b80010c3c_x13 h₂] at hbufT
  rv_eval [] at hcap hbufT
  obtain ⟨T, hTd⟩ : ∃ T, T = u₃.getMem (s.getReg .x2 - 88) := ⟨_, rfl⟩
  rw [← hTd] at hbufT
  simp only [NewBuf, hn₂] at hbufT
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 112 := (k₄ .x2 (by decide)).trans x2₃
  obtain ⟨u₅, hr₅, h₅⟩ := BlockSpec.reaches b80010c68_spec
    (b80010c60_pc_not_taken h₄ (by rv_eval [x2₃]; exact htag)) (by
      rv_eval [x2₄]; and_intros <;> valid_access hst.valid [hb])
  have k₅ := b80010c68_keeps h₅
  have hm₅ (a : Word) : u₅.getMem a = u₃.getMem a := by
    rw [b80010c68_mem_same h₅, b80010c60_mem_same h₄]
  have inv₅ := (inv₃.same hpre (b80010c60_mem_same h₄) k₄).same hpre (b80010c68_mem_same h₅) k₅
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 112 := (k₅ .x2 (by decide)).trans x2₄
  have hreg₃ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x20, .x21, .x22]) : u₄.getReg r = u₂.getReg r := by
    rw [k₄ r (by revert hr; revert r; decide), hpres₃ r (by unfold calleeSaved; revert hr; revert r; decide)]
  have y8 : u₄.getReg .x8 = s.getReg .x12 := by
    rw [hreg₃ .x8 (by decide), k₂ .x8 (by decide), k₁ .x8 (by decide), h.x8]
  have y21 : u₄.getReg .x21 = R := by
    rw [hreg₃ .x21 (by decide), k₂ .x21 (by decide), k₁ .x21 (by decide), h.x21]
  have x10₅ : u₅.getReg .x10 = T := by rw [b80010c68_x10 h₅, x2₄]; rv_eval [b80010c60_mem_same h₄, hTd]
  have x11₅ : u₅.getReg .x11 = R + s.getReg .x12 * 16 := by rw [b80010c68_x11 h₅, y21, y8]
  have x12₅ : u₅.getReg .x12 = s.getReg .x14 * 16 := by
    rw [b80010c68_x12 h₅, hreg₃ .x18 (by decide), x18₂]
  have hrbuf := h.bufs
  have h16 : (s.getReg .x14 * 16).toNat = 16 * (s.getReg .x14).toNat := by addr_omega [hm48]
  have hRn : R + s.getReg .x12 * 16 = R + BitVec.ofNat 64 (16 * (s.getReg .x12).toNat) := by
    addr_omega [hn8, hrbuf, hfit]
  -- the copy, then `0x80010c88`
  have fin (w : MachineState) (hrw : Reaches Image.code u₅ w) (hpcw : w.pc = 0x80010c88)
      (inv : Inv s w (u₃.getMem nextAddr))
      (hk : ∀ r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23], w.getReg r = u₅.getReg r)
      (hR : ∀ i < (s.getReg .x12).toNat, ∀ d < 2,
        w.getMem (R + BitVec.ofNat 64 (16 * i + 8 * d)) = u₃.getMem (R + BitVec.ofNat 64 (16 * i + 8 * d)))
      (hT : ∀ i < (s.getReg .x14).toNat, ∀ d < 2,
        w.getMem (T + BitVec.ofNat 64 (16 * i + 8 * d)) =
          u₃.getMem (R + BitVec.ofNat 64 (16 * ((s.getReg .x12).toNat + i) + 8 * d))) :
      ∃ v, Reaches Image.code u v ∧ ((∃ nx' T, Final s v nx' R T) ∨ Dead Image.code v) := by
    have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x20, .x21]) : w.getReg r = u₂.getReg r := by
      rw [hk r (by revert hr; revert r; decide), k₅ r (by revert hr; revert r; decide),
        hreg₃ r (by revert hr; revert r; decide)]
    have word (i : Nat) (hi : i < nn s) (d : Nat) (hd : d < 2) :
        u₃.getMem (R + BitVec.ofNat 64 (16 * i + 8 * d)) = u.getMem (R + BitVec.ofNat 64 (16 * i + 8 * d)) :=
      kb₃ (by addr_omega [hrbuf, hi, hd, hfit])
    have hRw (i : Nat) (hi : i < nn s) :
        u₃.getMem (R + BitVec.ofNat 64 (16 * i)) = srcWord s i ∧
          u₃.getMem (R + BitVec.ofNat 64 (16 * i) + 8) = (offs s).getD i 0 := by
      have h0 := word i hi 0 (by decide)
      have h1 := word i hi 1 (by decide)
      rw [show 16 * i + 8 * 0 = 16 * i by omega] at h0
      rw [show R + BitVec.ofNat 64 (16 * i + 8 * 1) = R + BitVec.ofNat 64 (16 * i) + 8 by
        addr_omega [hrbuf, hi, hfit]] at h1
      rw [h0, h1]
      exact h.words i hi
    refine ⟨w, hr₁.trans (hr₃.trans (hr₄.trans (hr₅.trans hrw))), Or.inl
      ⟨u₃.getMem nextAddr, T, {
        inv := inv
        pc := hpcw
        x8 := (hreg .x8 (by decide)).trans (by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), h.x8])
        x9 := (hreg .x9 (by decide)).trans (by rw [k₂ .x9 (by decide), k₁ .x9 (by decide), h.x9])
        x18 := by rw [hk .x18 (by decide), k₅ .x18 (by decide), hreg₃ .x18 (by decide), x18₂]
        x19 := by rw [hk .x19 (by decide), b80010c68_x19 h₅, x2₄]; rv_eval [b80010c60_mem_same h₄, hTd]
        x20 := by
          rw [hreg .x20 (by decide), k₂ .x20 (by decide), k₁ .x20 (by decide)]; exact h.x20
        x21 := (hreg .x21 (by decide)).trans (by rw [k₂ .x21 (by decide), k₁ .x21 (by decide), h.x21])
        x22 := by rw [hk .x22 (by decide), k₅ .x22 (by decide), hreg₃ .x22 (by decide), x22₂]
        x23 := by
          rw [hk .x23 (by decide), b80010c68_x23 h₅, x2₄]; rv_eval [b80010c60_mem_same h₄, hcap]
        ralign := hR8
        talign := hbufT.1
        rbuf := by
          rcases hrbuf with h0 | h0
          · exact Or.inl h0
          · refine Or.inr ⟨by omega, ?_⟩
            have := hpost₃.mono
            rw [hn₂] at this
            have h' := h0.2.2.2.2
            simp only [heapNext] at this
            omega
        tbuf := by
          rcases hbufT.2 with h0 | h0
          · exact Or.inl (by omega)
          · refine Or.inr ⟨by omega, ?_⟩
            simp only [heapNext] at h0
            omega
        head := fun i hi ↦ by
          have h0 := hR i hi 0 (by decide)
          have h1 := hR i hi 1 (by decide)
          rw [show 16 * i + 8 * 0 = 16 * i by omega] at h0
          rw [show R + BitVec.ofNat 64 (16 * i + 8 * 1) = R + BitVec.ofNat 64 (16 * i) + 8 by
            addr_omega [hrbuf, hi, hfit]] at h1
          rw [h0, h1]
          exact hRw i (by omega)
        tail := fun i hi ↦ by
          have h0 := hT i hi 0 (by decide)
          have h1 := hT i hi 1 (by decide)
          have hTb := hbufT.2.resolve_left (by omega)
          rw [show 16 * i + 8 * 0 = 16 * i by omega, show 16 * ((s.getReg .x12).toNat + i) + 8 * 0 =
            16 * ((s.getReg .x12).toNat + i) by omega] at h0
          rw [show T + BitVec.ofNat 64 (16 * i + 8 * 1) = T + BitVec.ofNat 64 (16 * i) + 8 by
              addr_omega [hTb, hi, hfit],
            show R + BitVec.ofNat 64 (16 * ((s.getReg .x12).toNat + i) + 8 * 1) =
              R + BitVec.ofNat 64 (16 * ((s.getReg .x12).toNat + i)) + 8 by
              addr_omega [hrbuf, hi, hfit]] at h1
          rw [h0, h1]
          exact hRw _ (by omega)
        offsLen := h.offsLen }⟩⟩
  have hpc₅ := b80010c68_pc h₅
  have hret (w : MachineState) (hpcw : w.pc = returnAddress u₅) : w.pc = 0x80010c88 := by
    rw [hpcw, returnAddress_eq, b80010c68_x1 h₅]; decide
  have hfit₃ := hpost₃.heap.hi
  by_cases hm0 : s.getReg .x14 = 0
  · obtain ⟨w, hrw, ⟨hpcw, hpresw, -, hmw⟩ | hdead⟩ := memcpy_zero.call (Reaches.refl u₅) hpc₅
      (by rw [x12₅, hm0]; rfl)
    swap
    · exact ⟨w, hr₁.trans (hr₃.trans (hr₄.trans (hr₅.trans hrw))), Or.inr hdead⟩
    refine fin w hrw (hret w hpcw) (inv₅.same hpre hmw (l := calleeSaved) fun r hr ↦ hpresw r hr)
      (fun r hr ↦ hpresw r (by unfold calleeSaved; revert hr; revert r; decide))
      (fun i _ d _ ↦ by rw [hmw, hm₅]) fun i hi ↦ absurd hi (by rw [hm0]; exact Nat.not_lt_zero _)
  have hm0' : (s.getReg .x14).toNat ≠ 0 := fun h0 ↦ hm0 (BitVec.eq_of_toNat_eq h0)
  have hTb := hbufT.2.resolve_left (by omega)
  have hRb := hrbuf.resolve_left (by omega)
  have hT8 := hbufT.1
  have hsl₅ : stackLo u₅ memcpyStack = s.getReg .x2 - 128 := by
    simp only [stackLo, x2₅, memcpyStack]; rv_eval []
  have hmc : MemcpyPre u₅ := {
    dst := by rw [x10₅, x12₅, h16]; addr_omega [hTb, hfit₃, hlo0, hmono, hfit]
    src := by rw [x11₅, x12₅, h16, hRn]; addr_omega [hRb, hfit, hlo0]
    apart := by rw [x10₅, x11₅, x12₅, h16, hRn]; addr_omega [hRb, hTb, hfit]
    stack := (hst.sub 112 x2₅ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    dstStack := by rw [x10₅, x12₅, h16, hsl₅]; addr_omega [hTb, hfit₃, hb, hab]
    srcStack := by rw [x11₅, x12₅, h16, hRn, hsl₅]; addr_omega [hRb, hfit, hb, hab] }
  obtain ⟨w, hrw, ⟨hpcw, hpresw, hmp⟩ | hdead⟩ := hM.call (Reaches.refl u₅) hpc₅ hmc
  swap
  · exact ⟨w, hr₁.trans (hr₃.trans (hr₄.trans (hr₅.trans hrw))), Or.inr hdead⟩
  have hbytes := hmp.bytes
  rw [x10₅, x11₅, x12₅, h16, hRn] at hbytes
  have hfr := hmp.frame
  rw [x10₅, x12₅, h16, hsl₅] at hfr
  have hnext : w.getMem nextAddr = u₃.getMem nextAddr := by
    rw [hfr.getMem fun i hi hw ↦ by
        rcases hw with hw | hw <;> addr_omega [hw, hi, hTb, hfit₃, hb, hnx8], hm₅]
  have inv : Inv s w (u₃.getMem nextAddr) := inv₅.step hpre hfr (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (by addr_omega [ha, hTb, hmono]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb])))
    hnext (Nat.le_refl _) hfit₃ fun r hr ↦ hpresw r (by unfold calleeSaved; revert hr; revert r; decide)
  refine fin w hrw (hret w hpcw) inv
    (fun r hr ↦ hpresw r (by unfold calleeSaved; revert hr; revert r; decide)) (fun i hi d hd ↦ ?_)
    fun i hi d hd ↦ ?_
  · rw [hfr.getMem fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hi, hd, hRb, hTb, hfit, hb, hab], hm₅]
  · rw [getMem_eq_of_bytesAt hbytes hT8 (by addr_omega [hR8, hRb, hfit]) (k := 16 * i + 8 * d)
      (by omega) (by omega), hm₅]
    congr 1
    addr_omega [hRb, hfit, hi, hd]

end Rv64Verifier.Layout.BusLayout
