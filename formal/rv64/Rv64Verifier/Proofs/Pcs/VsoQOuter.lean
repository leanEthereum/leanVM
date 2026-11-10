import Rv64Verifier.Proofs.Pcs.VsoQInner

/-!
# `verify_stacked_opening`'s level loop: `sample_queries`

From `0x8000a8dc`: a sample (`duplex`, its lanes to `S - 384`, `0` after them), then
`min(192 / d, cnt - len)` chunks (`chunk`), then `0x8000a8cc` loops while `len < cnt` and else goes
on at `0x8000a9d8` (`qloop`). The mirror is `sampleQueriesLoop`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- A frame slot `QW` misses keeps its value from `w`. -/
theorem QW.keep {s w u : MachineState} (hpre : VsoPre s) (hfr : DFrame w u (QW s w u))
    (hhi : heapNext u ≤ heapEnd) {o : ℕ}
    (ho : o = 816 ∨ o = 808 ∨ o = 792) :
    u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = w.getMem (s.getReg .x2 - BitVec.ofNat 64 o) := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  obtain ⟨hnx, -⟩ := sfacts hpre
  refine hfr _ fun i hi hw ↦ ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw
  · simp only [W] at hw; rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hS, hIs, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb]
  · rcases ho with rfl | rfl | rfl <;> addr_omega [hw, hi, hb, hnx]
  · simp only [Fresh, heapNext, heapEnd] at hw hhi
    rcases ho with rfl | rfl | rfl <;> addr_omega [hw.2, hi, hb, hhi]

/-- The positions' `Vec` is kept by a frame within the sponge and the stack below `S - 360` but
its header. -/
theorem QVec.keep {s w u v : MachineState} {cnt : ℕ} {r : List Word} {X : Word → Prop}
    (hpre : VsoPre s) (h : QVec s w u cnt r) (hX : DFrame u v X)
    (hXs : ∀ a, X a → W s a ∨ Within a (s.getReg .x2 - 2464) 1424 ∨ Within a (s.getReg .x2 - 384) 32)
    (hn : heapNext v = heapNext u) (hhi : heapNext u ≤ heapEnd) : QVec s w v cnt r := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hd (y : Word) (h1 : (s.getReg .x2 - 464).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2 - 440).toNat) : v.getMem y = u.getMem y :=
    hX y fun i hi hw ↦ by
      rcases hXs _ hw with hw | hw | hw
      · simp only [W] at hw; addr_omega [hw, hi, h1, h2, hS, hIs, hb]
      · addr_omega [hw, hi, h1, h2, hb]
      · addr_omega [hw, hi, h1, h2, hb]
  have ep : vecPtr v (s.getReg .x2 - 464) = vecPtr u (s.getReg .x2 - 464) :=
    hd _ (by addr_omega [hb]) (by addr_omega [hb])
  have hbuf := h.buf
  have hle := h.le
  refine ⟨?_, ?_, ?_, ?_, hle, h.hw, h.hs⟩
  · rw [← h.cap]; exact hd _ (Nat.le_refl _) (by addr_omega [hb])
  · rw [← h.len]; exact hd _ (by addr_omega [hb]) (by addr_omega [hb])
  · rw [ep]; simp only [NewBuf] at hbuf ⊢; rw [hn]; exact hbuf
  · have hk : v.readWords (vecPtr u (s.getReg .x2 - 464)) r.length =
        u.readWords (vecPtr u (s.getReg .x2 - 464)) r.length := by
      refine DFrame.readWords' hX (fun a ha hw ↦ ?_) ?_
      · rcases hbuf.2 with h0 | h0
        · simp only [Within] at hw; omega
        · rcases hXs _ ha with ha | ha | ha
          · simp only [W] at ha
            have hf := hI.free
            simp only [Outside] at hf
            rcases hf.1 with h1 | h1
            · have hs' := h.hs
              simp only [heapNext] at hs' h1 h0
              addr_omega [ha, hw, h1, h0.1, hS, hs']
            · simp only [heapNext, heapEnd] at h0 hhi
              addr_omega [ha, hw, h1, h0.2, hhi, hS, hle]
          · simp only [heapNext, heapEnd] at h0 hhi; addr_omega [ha, hw, h0.2, hhi, hb, hle]
          · simp only [heapNext, heapEnd] at h0 hhi; addr_omega [ha, hw, h0.2, hhi, hb, hle]
      · rcases hbuf.2 with h0 | h0
        · have : r.length = 0 := by omega
          rw [this]; addr_omega [hb]
        · simp only [heapNext, heapEnd] at h0 hhi; omega
    rw [ep, hk]; exact h.elems

/-- **A sample**, from `0x8000a8dc` to its first chunk at `0x8000a970`. -/
theorem sampleStep (hD : DuplexSpec) {s w u : MachineState} {d cnt : ℕ} {r : List Word}
    {T : Model.TState} (hpre : VsoPre s) (h : QOuter s w u d cnt r)
    (h248w : w.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8)
    (hT : TranscriptAt u (s.getReg .x10) T) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨
      (QInner s w v d cnt r (spSqueeze T.sponge).1 0 ∧
        TranscriptAt v (s.getReg .x10) { T with sponge := spDuplex T.sponge })) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hhi := (h.inv.heap hpre.heap).hi
  have h248 : u.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8 :=
    (QW.keep hpre h.fr hhi (o := 792) (by decide)).trans h248w
  have hsp := h.sp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a8dc_spec h.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have hm₁ := b8000a8dc_mem_same h₁
  have k₁ := b8000a8dc_keeps h₁
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [hm₁]; exact Inv.same' h.inv hm₁ (k₁ .x2 (by decide))
  obtain ⟨t₂, hr₂, hv₂⟩ := callDuplex hD hpre inv₁ (b8000a8dc_pc h₁)
    (by rw [b8000a8dc_x10 h₁, hsp]; rv_eval [h248])
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, X₂, hsp₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have hfS := hI.free.2
  have nx₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := X₂ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hS, hfS]
    · addr_omega [hw, hi, hb, hnx]
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by
    rw [hpres₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  have inv₂ : InvR s t₂ (t₂.getMem nextAddr) := by
    rw [nx₂]
    refine Inv.step' hpre inv₁ X₂ (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx₂ (le_refl _) inv₁.fits
      (hpres₂ .x2 (by decide))
    · rcases ha with ha | ha
      · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · rcases ha with ha | ha
      · addr_omega [ha, hS, hIs, hb]
      · addr_omega [ha, hb]
  have hT₁ : TranscriptAt t₁ (s.getReg .x10) T :=
    tr_keep hpre h.inv hT (DFrame.of_same hm₁ fun _ ↦ False) fun _ h ↦ h.elim
  have hT₂ := tr_duplex hpre inv₁ hT₁ X₂ hsp₂
  have x20₂ : t₂.getReg .x20 = s.getReg .x10 := by
    rw [hpres₂ .x20 (by decide), k₁ .x20 (by decide), h.x20]
  have hlt := h.lt
  have hbuf := h.vec.buf
  have hcb : cnt * 8 ≤ heapEnd := by
    have hf := h.inv.fits
    rcases hbuf.2 with h0 | h0
    · omega
    · simp only [heapNext] at h0 hf; omega
  have hd0 := h.d0
  have hd64 := h.d64
  have kk (r' : Reg) (h1 : r' ∈ [Reg.x8, .x9, .x18, .x19, .x24, .x26]) :
      t₂.getReg r' = u.getReg r' := by
    rw [hpres₂ r' (by simp only [calleeSaved]; exact mem_of_mem h1 _), k₁ r' (mem_of_mem h1 _)]
  have x22₂ : t₂.getReg .x22 = u.getReg .x1 := by
    rw [hpres₂ .x22 (by decide), b8000a8dc_x22 h₁]
  have hcap64 : cnt < 2 ^ 64 := by simp only [heapEnd] at hcb; omega
  -- the lanes
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000a8ec_spec
    (by rw [hpc₂, returnAddress_eq, b8000a8dc_x1 h₁]; decide) (by
      rv_eval [sp₂, x20₂]
      and_intros <;> first
        | valid_access hst.valid [hb]
        | exact Region.valid hI.ok.self (by addr_omega [hS]) (by addr_omega [hS])
            (by addr_omega [hS]))
  have k₃ := b8000a8ec_keeps h₃
  have f₃ := DFrame.of_memFrame (b8000a8ec_frame h₃ (by rw [sp₂]; addr_omega [hb]))
  rw [sp₂, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at f₃
  have x24₂ : t₂.getReg .x24 = BitVec.ofNat 64 cnt := by rw [kk .x24 (by decide), h.x24]
  have x26₂ : t₂.getReg .x26 = BitVec.ofNat 64 r.length := by rw [kk .x26 (by decide), h.x26]
  have hsub : t₂.getReg .x24 - t₂.getReg .x26 = BitVec.ofNat 64 (cnt - r.length) := by
    rw [x24₂, x26₂]; addr_omega [hlt, hcap64]
  have s824₂ : t₂.getMem (t₂.getReg .x2 + 216) = BitVec.ofNat 64 (192 / d) := by
    rw [sp₂, show s.getReg .x2 - 1040 + 216 = s.getReg .x2 - 824 by rv_eval [], ← h.s824, ← hm₁]
    exact X₂ _ fun i hi hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hi, hS, hIs, hb]
      · addr_omega [hw, hi, hb]
  have h192 : 192 / d ≤ 192 := Nat.div_le_self _ _
  obtain ⟨t₄, hr₄, hpc₄, x21₄, hm₄, k₄⟩ : ∃ t₄, Reaches Image.code t₃ t₄ ∧ t₄.pc = 0x8000a91c ∧
      t₄.getReg .x21 = BitVec.ofNat 64 (min (192 / d) (cnt - r.length)) ∧
      (∀ a, t₄.getMem a = t₃.getMem a) ∧
      ∀ r' ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x22, .x24, .x26], t₄.getReg r' = t₃.getReg r' := by
    by_cases hc : 192 / d < cnt - r.length
    · refine ⟨t₃, Reaches.refl _, b8000a8ec_pc_taken h₃ (by
          rw [s824₂, hsub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]; exact hc), ?_, fun _ ↦ rfl, fun _ _ ↦ rfl⟩
      rw [b8000a8ec_x21 h₃, s824₂, min_eq_left hc.le]
    · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a918_spec (b8000a8ec_pc_not_taken h₃ (by
          rw [s824₂, hsub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]; omega)) trivial
      exact ⟨t₄, hr₄, b8000a918_pc h₄, by
        rw [b8000a918_x21 h₄, b8000a8ec_x10 h₃, hsub, min_eq_right (by omega)],
        b8000a918_mem_same h₄, fun r' hr' ↦ b8000a918_keeps h₄ r' (mem_of_mem hr' _)⟩
  have kk₄ (r' : Reg) (h1 : r' ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x22, .x24, .x26]) :
      t₄.getReg r' = t₂.getReg r' := by
    rw [k₄ r' h1, k₃ r' (mem_of_mem h1 _)]
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000a91c_spec hpc₄ trivial
  have hpc₅ := b8000a91c_pc_not_taken h₅ (by
    rw [kk₄ .x24 (by decide), kk₄ .x26 (by decide), x24₂, x26₂]
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64,
      Nat.mod_eq_of_lt (by omega)] at this
    omega)
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000a920_spec hpc₅ trivial
  have k₅ := b8000a91c_keeps h₅
  have k₆ := b8000a920_keeps h₆
  have hm₆ : ∀ a, t₆.getMem a = t₃.getMem a := fun a ↦ by
    rw [b8000a920_mem_same h₆, b8000a91c_mem_same h₅, hm₄]
  have kk₆ (r' : Reg) (h1 : r' ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x26]) :
      t₆.getReg r' = t₂.getReg r' := by
    rw [k₆ r' (mem_of_mem h1 _), k₅ r' (mem_of_mem h1 _), kk₄ r' (mem_of_mem h1 _)]
  -- what the sample wrote
  have X : DFrame u t₆ fun a ↦ W s a ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a (s.getReg .x2 - 384) 32 := by
    have X₂' : DFrame u t₂ fun a ↦ W s a ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
        Within a (s.getReg .x2 - 384) 32 := (DFrame.of_same hm₁ _).trans X₂ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by simp only [W]; addr_omega [ha, hS])
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    exact (X₂'.trans f₃ fun a ha ↦ Or.inr (Or.inr ha)).trans (DFrame.of_same hm₆ _) fun _ h ↦ h
  have nx₆ : t₆.getMem nextAddr = u.getMem nextAddr := X _ fun i hi hw ↦ by
    rcases hw with hw | hw | hw
    · simp only [W] at hw; addr_omega [hw, hi, hS, hfS]
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hb, hnx]
  have hn₆ : heapNext t₆ = heapNext u := by simp only [heapNext, nx₆]
  have inv₆ : InvR s t₆ (t₆.getMem nextAddr) := by
    rw [nx₆]
    refine Inv.step' hpre h.inv X (fun a ha ↦ ?_) (fun a ha ↦ ?_) nx₆ (le_refl _) h.inv.fits
      (by rw [kk₆ .x2 (by decide), sp₂, hsp])
    · rcases ha with ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
      · exact frame_wr hpre (by addr_omega [ha, hb])
    · rcases ha with ha | ha | ha
      · simp only [W] at ha; addr_omega [ha, hS, hIs, hb]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb]
  have hsmp : (spSqueeze T.sponge).1 = eAt t₂ (s.getReg .x10 + 136) := by
    have hsq : (spSqueeze T.sponge).1 = Compile.challengeOf (spDuplex T.sponge).state := rfl
    have hs2 : spongeAt t₂ (s.getReg .x10 + 8) = spDuplex T.sponge := hT₂.sponge
    rw [hsq, ← hs2]
    show Compile.challengeOf (stateAt t₂ (s.getReg .x10 + 8 + 128)) = _
    rw [show s.getReg .x10 + 8 + 128 = s.getReg .x10 + 136 by rv_eval [],
      Samples.challengeOf_stateAt]
  have hvec := QVec.keep hpre h.vec X (fun _ h ↦ h) hn₆ hhi
  rw [show r = r ++ chunksOf (spSqueeze T.sponge).1 d 0 by simp [chunksOf]] at hvec
  have hm192 : 0 < min (192 / d) (cnt - r.length) :=
    lt_min (Nat.div_pos (by omega) hd0) (by omega)
  refine ⟨t₆, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))), Or.inr ⟨{
    pc := b8000a920_pc h₆
    sp := by rw [kk₆ .x2 (by decide), sp₂]
    inv := inv₆
    fr := (h.fr.mono fun a ha ↦ QW.of_heap (by rw [hn₆]) ha).trans X fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    mono := by rw [hn₆]; exact h.mono
    x1 := by
      rw [b8000a920_x1 h₆, k₅ .x22 (by decide), kk₄ .x22 (by decide), x22₂, h.x1]
      symm
      exact X _ fun i hi hw ↦ by
        rcases hw with hw | hw | hw
        · simp only [W] at hw; addr_omega [hw, hi, hS, hIs, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
    x8 := by rw [kk₆ .x8 (by decide), kk .x8 (by decide), h.x8]
    x9 := by rw [kk₆ .x9 (by decide), kk .x9 (by decide), h.x9]
    x18 := by rw [kk₆ .x18 (by decide), kk .x18 (by decide), h.x18]
    x19 := by rw [kk₆ .x19 (by decide), kk .x19 (by decide), h.x19]
    x21 := by rw [k₆ .x21 (by decide), k₅ .x21 (by decide), x21₄]
    x22 := b8000a920_x22 h₆
    x23 := by rw [b8000a920_x23 h₆, Nat.zero_mul]; rfl
    x24 := by
      rw [b8000a920_x24 h₆, k₅ .x26 (by decide), kk₄ .x26 (by decide), x26₂]
      simp only [heapEnd] at hcb
      addr_omega [hlt, hcb]
    x26 := by rw [kk₆ .x26 (by decide), x26₂]; rfl
    s832 := by
      rw [← h.s832]
      exact X _ fun i hi hw ↦ by
        rcases hw with hw | hw | hw
        · simp only [W] at hw; addr_omega [hw, hi, hS, hIs, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
    s824 := by
      rw [← h.s824]
      exact X _ fun i hi hw ↦ by
        rcases hw with hw | hw | hw
        · simp only [W] at hw; addr_omega [hw, hi, hS, hIs, hb]
        · addr_omega [hw, hi, hb]
        · addr_omega [hw, hi, hb]
    l0 := by
      rw [hsmp, hm₆]
      have := b8000a8ec_m_x2_656 h₃
      rw [sp₂, x20₂] at this; rv_eval [] at this
      exact this
    l1 := by
      rw [hsmp, hm₆]
      have := b8000a8ec_m_x2_664 h₃
      rw [sp₂, x20₂] at this; rv_eval [] at this
      rw [this]
      show _ = t₂.getMem (s.getReg .x10 + 136 + 8)
      rw [show s.getReg .x10 + 136 + 8 = s.getReg .x10 + 144 by rv_eval []]
    l2 := by
      rw [hsmp, hm₆]
      have := b8000a8ec_m_x2_672 h₃
      rw [sp₂, x20₂] at this; rv_eval [] at this
      rw [this]
      show _ = t₂.getMem (s.getReg .x10 + 136 + 16)
      rw [show s.getReg .x10 + 136 + 16 = s.getReg .x10 + 152 by rv_eval []]
    l3 := by
      rw [hm₆]
      have := b8000a8ec_m_x2_680 h₃
      rw [sp₂] at this; rv_eval [] at this
      exact this
    vec := hvec
    jlt := hm192
    d0 := hd0
    d64 := hd64 }, ?_⟩⟩
  exact tr_keep hpre inv₂ hT₂ (f₃.trans (DFrame.of_same hm₆ _) fun _ h ↦ h) fun a ha ↦
    Or.inl (by addr_omega [ha, hb])

/-- **Back from a sample**, at `0x8000a8cc`: the next sample, or the positions done at
`0x8000a9d8`. -/
theorem backStep {s w u : MachineState} {d cnt : ℕ} {r : List Word} (hpre : VsoPre s)
    (h : QBack s w u d cnt r) (h224w : w.getMem (s.getReg .x2 - 816) = s.getReg .x10) :
    ∃ v, Reaches Image.code u v ∧ (∀ a, v.getMem a = u.getMem a) ∧
      ((r.length < cnt ∧ QOuter s w v d cnt r) ∨ (r.length = cnt ∧ QDone s w v d r)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hhi := (h.inv.heap hpre.heap).hi
  have hsp := h.sp
  have h224 : u.getMem (s.getReg .x2 - 816) = s.getReg .x10 :=
    (QW.keep hpre h.fr hhi (o := 816) (by decide)).trans h224w
  have hle := h.vec.le
  have hbuf := h.vec.buf
  have hcb : cnt * 8 ≤ heapEnd := by
    have hf := h.inv.fits
    rcases hbuf.2 with h0 | h0
    · omega
    · simp only [heapNext] at h0 hf; omega
  have hcap64 : cnt + 1 < 2 ^ 64 := by simp only [heapEnd] at hcb; omega
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a8cc_spec h.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have hm₁ := b8000a8cc_mem_same h₁
  have k₁ := b8000a8cc_keeps h₁
  have q208 : u.getMem (u.getReg .x2 + 208) = BitVec.ofNat 64 cnt := by
    rw [hsp]; rv_eval [h.s832]
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, hm₁]
  have hvec₁ : QVec s w t₁ cnt r :=
    QVec.keep hpre h.vec (DFrame.of_same hm₁ fun _ ↦ False) (fun _ h ↦ h.elim) hn₁ hhi
  have fr₁ : DFrame w t₁ (QW s w t₁) :=
    (h.fr.mono fun a ha ↦ QW.of_heap (by rw [hn₁]) ha).trans (DFrame.of_same hm₁ _) fun _ h ↦ h
  have inv₁ : InvR s t₁ (t₁.getMem nextAddr) := by
    rw [hm₁]; exact Inv.same' h.inv hm₁ (k₁ .x2 (by decide))
  by_cases hlt : r.length < cnt
  · have hpc₁ := b8000a8cc_pc_not_taken h₁ (by
      rw [q208, h.x26, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]; exact hlt)
    refine ⟨t₁, hr₁, hm₁, Or.inl ⟨hlt, {
      pc := hpc₁
      sp := by rw [k₁ .x2 (by decide), hsp]
      inv := inv₁
      fr := fr₁
      mono := by rw [hn₁]; exact h.mono
      x1 := by rw [k₁ .x1 (by decide), h.x1]; exact (hm₁ _).symm
      x8 := by rw [k₁ .x8 (by decide), h.x8]
      x9 := by rw [k₁ .x9 (by decide), h.x9]
      x18 := by rw [k₁ .x18 (by decide), h.x18]
      x19 := by rw [k₁ .x19 (by decide), h.x19]
      x20 := by rw [b8000a8cc_x20 h₁, hsp]; rv_eval [h224]
      x24 := by rw [b8000a8cc_x24 h₁, q208]
      x26 := by rw [k₁ .x26 (by decide), h.x26]
      s832 := by rw [hm₁, h.s832]
      s824 := by rw [hm₁, h.s824]
      vec := hvec₁
      lt := hlt
      d0 := h.d0
      d64 := h.d64 }⟩⟩
  have heq : r.length = cnt := by omega
  have hpc₁ := b8000a8cc_pc_taken h₁ (by
    rw [q208, h.x26, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega)
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₁ .x2 (by decide), hsp]
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a9c8_spec hpc₁ (by
    rv_eval [sp₁]; and_intros <;> valid_access hst.valid [hb])
  have hm₂ := b8000a9c8_mem_same h₂
  have k₂ := b8000a9c8_keeps h₂
  have q576 : t₁.getMem (t₁.getReg .x2 + 576) = BitVec.ofNat 64 cnt := by
    rw [sp₁, show s.getReg .x2 - 1040 + 576 = s.getReg .x2 - 464 by rv_eval []]
    exact hvec₁.cap
  have hpc₂ := b8000a9c8_pc_not_taken h₂ (by
    rw [q576]; intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact absurd this (by
      rw [show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl]; omega))
  have hn₂ : heapNext t₂ = heapNext u := by simp only [heapNext, hm₂, hm₁]
  have hvec₂ : QVec s w t₂ cnt r :=
    QVec.keep hpre hvec₁ (DFrame.of_same hm₂ fun _ ↦ False) (fun _ h ↦ h.elim)
      (by rw [hn₂, hn₁]) (by rw [hn₁]; exact hhi)
  rw [← heq] at hvec₂
  refine ⟨t₂, hr₁.trans hr₂, fun a ↦ by rw [hm₂, hm₁], Or.inr ⟨heq, {
    pc := hpc₂
    sp := by rw [k₂ .x2 (by decide), sp₁]
    inv := by rw [hm₂]; exact Inv.same' inv₁ hm₂ (k₂ .x2 (by decide))
    fr := (fr₁.mono fun a ha ↦ QW.of_heap (by rw [hn₂, hn₁]) ha).trans (DFrame.of_same hm₂ _)
      fun _ h ↦ h
    mono := by rw [hn₂]; exact h.mono
    x1 := by
      rw [b8000a9c8_x1 h₂, sp₁, show s.getReg .x2 - 1040 + 584 = s.getReg .x2 - 464 + 8 by
        rv_eval []]
      simp only [vecPtr]; rw [hm₂]
    x8 := by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), h.x8]
    x9 := by rw [k₂ .x9 (by decide), k₁ .x9 (by decide), h.x9]
    x20 := by rw [k₂ .x20 (by decide), b8000a8cc_x20 h₁, hsp]; rv_eval [h224]
    x26 := by rw [k₂ .x26 (by decide), k₁ .x26 (by decide), h.x26]
    vec := hvec₂ }⟩⟩

/-- **One sample's chunks**, from chunk `j` on. -/
theorem chunks {s w : MachineState} {d cnt : ℕ} {r : List Word} {smp : E} (hpre : VsoPre s) :
    ∀ (k j : ℕ) (u : MachineState), min (192 / d) (cnt - r.length) - j = k →
      QInner s w u d cnt r smp j →
      ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨
        ((∀ T, TranscriptAt u (s.getReg .x10) T → TranscriptAt v (s.getReg .x10) T) ∧
          QBack s w v d cnt (r ++ chunksOf smp d (min (192 / d) (cnt - r.length)))))
  | 0, j, u, hk, h => absurd h.jlt (by omega)
  | k + 1, j, u, hk, h => by
    obtain ⟨v, hr, hv⟩ := chunk hpre h
    rcases hv with hd | ⟨htr, ⟨hlt, hn⟩ | ⟨heq, hb⟩⟩
    · exact ⟨v, hr, Or.inl hd⟩
    · obtain ⟨v', hr', hv'⟩ := chunks hpre k (j + 1) v (by omega) hn
      rcases hv' with hd | ⟨htr', hb'⟩
      · exact ⟨v', hr.trans hr', Or.inl hd⟩
      · exact ⟨v', hr.trans hr', Or.inr ⟨fun T hT ↦ htr' T (htr T hT), hb'⟩⟩
    · rw [heq] at hb
      exact ⟨v, hr, Or.inr ⟨htr, hb⟩⟩

/-- **`sample_queries`' loop**, from `0x8000a8dc` with `r` drawn, to `0x8000a9d8`: the mirror's
`sampleQueriesLoop` with fuel at least the positions left. -/
theorem qloop (hD : DuplexSpec) {s w : MachineState} {d cnt : ℕ} (hpre : VsoPre s)
    (h224w : w.getMem (s.getReg .x2 - 816) = s.getReg .x10)
    (h248w : w.getMem (s.getReg .x2 - 792) = s.getReg .x10 + 8) :
    ∀ (n : ℕ) (r : List Word) (u : MachineState) (T : Model.TState) (fuel : ℕ),
      cnt - r.length = n → cnt - r.length ≤ fuel → QOuter s w u d cnt r →
      TranscriptAt u (s.getReg .x10) T →
      ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ ∃ qs T',
        QDone s w v d qs ∧ qs.length = cnt ∧
        (Model.Pcs.sampleQueriesLoop (blOf d) d cnt fuel r).run T = some (qs, T') ∧
        TranscriptAt v (s.getReg .x10) T' ∧ T'.proof = T.proof ∧ T'.roots = T.roots ∧
        T'.openingOffset = T.openingOffset) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro r u T fuel hn hf h hT
  have hlt := h.lt
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  obtain ⟨v₁, hr₁, hv₁⟩ := sampleStep hD hpre h h248w hT
  rcases hv₁ with hd | ⟨hi, hT₁⟩
  · exact ⟨v₁, hr₁, Or.inl hd⟩
  obtain ⟨v₂, hr₂, hv₂⟩ := chunks hpre _ 0 v₁ rfl hi
  rcases hv₂ with hd | ⟨htr, hback⟩
  · exact ⟨v₂, hr₁.trans hr₂, Or.inl hd⟩
  have hT₂ := htr _ hT₁
  obtain ⟨v₃, hr₃, hm₃, hv₃⟩ := backStep hpre hback h224w
  have hT₃ : TranscriptAt v₃ (s.getReg .x10) { T with sponge := spDuplex T.sponge } :=
    tr_keep hpre hback.inv hT₂ (DFrame.of_same hm₃ fun _ ↦ False) fun _ h ↦ h.elim
  have hstep : (Model.Pcs.sampleQueriesLoop (blOf d) d cnt (f + 1) r).run T =
      (Model.Pcs.sampleQueriesLoop (blOf d) d cnt f
        (r ++ chunksOf (spSqueeze T.sponge).1 d (min (192 / d) (cnt - r.length)))).run
        { T with sponge := spDuplex T.sponge } := by
    rw [Model.Pcs.sampleQueriesLoop_step _ _ _ _ _ hlt]
    rfl
  have hm0 : 0 < min (192 / d) (cnt - r.length) := hi.jlt
  have hlen : (r ++ chunksOf (spSqueeze T.sponge).1 d (min (192 / d) (cnt - r.length))).length =
      r.length + min (192 / d) (cnt - r.length) := by simp [chunksOf]
  rcases hv₃ with ⟨hlt', ho⟩ | ⟨heq, hdone⟩
  · obtain ⟨v₄, hr₄, hv₄⟩ := ih _ (by omega) _ v₃ _ f rfl (by omega) ho hT₃
    rcases hv₄ with hd | ⟨qs, T', hq, hql, hrun, hT', p, ro, o⟩
    · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hd⟩
    · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr ⟨qs, T', hq, hql,
        by rw [hstep, hrun], hT', p, ro, o⟩⟩
  · refine ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨_, _, hdone, heq, ?_, hT₃, rfl, rfl, rfl⟩⟩
    rw [hstep, Model.Pcs.sampleQueriesLoop_done _ _ _ _ _ (by omega)]
    rfl

end Rv64Verifier.Proofs.Pcs.Vso
