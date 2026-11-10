import Rv64Verifier.Proofs.Gkr.OpenStart

/-!
# `keccak::open`: the two `eq_kernel`s and the zeroed row

From `sumcheck`'s `Ok`: the value saved at `f + 1704`, the slice bound on the point checked,
`eq_kernel` of the point's segment part into `f + 120` and of the slot into `f + 144`
(`to_zero`), then the row at `f + 168` zeroed (`zero_loop`).
-/

namespace Rv64Verifier.Gkr.Open
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F75
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem trap : Image.code.fetch 0x80010534 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem newVecE_keep' {m u v : MachineState} {a : Word} {xs : List E} (h : NewVecE m u a xs)
    {w : Word → Prop} (hf : DFrame u v w) (hN : heapNext u ≤ heapNext v)
    (ha : ∀ i < 24, ¬ w (a + BitVec.ofNat 64 i)) (hb : ∀ y, y.toNat < heapNext u → ¬ w y) :
    NewVecE m v a xs := by
  have e0 : v.getMem a = u.getMem a := hf a fun i hi ↦ ha i (by omega)
  have e8 : v.getMem (a + 8) = u.getMem (a + 8) := hf _ fun i hi ↦ by
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, add_ofNat_add]; exact ha _ (by omega)
  have e16 : v.getMem (a + 16) = u.getMem (a + 16) := hf _ fun i hi ↦ by
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, add_ofNat_add]; exact ha _ (by omega)
  have hv := h.vec
  have hbuf := h.buf
  have hl := hv.len
  have hr := hv.raw
  simp only [NewBuf] at hbuf
  simp only [RawVecOk, Buf] at hr
  simp only [vecCap, vecPtr, vecLen] at hl hr hbuf
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, vecCap, vecPtr, e0, e8]; omega
  · simp only [vecLen, vecCap, e0, e16]; exact hl
  · simp only [NewBuf, vecCap, vecPtr, e0, e8]; omega
  · rw [← h.elems]
    simp only [vecEs, vecPtr, vecLen, e8, e16]
    by_cases hl0 : (u.getMem (a + 16)).toNat = 0
    · simp only [hl0]; rfl
    · exact hf.eListAt fun i hi ↦ hb _ (by addr_omega [hi, hbuf, hl, hl0])

/-- At the zeroing loop's head. -/
structure Z0 (s m u : MachineState) : Prop where
  pc : u.pc = 0x80010360
  mid : Mid s m u
  x10 : u.getReg .x10 = s.getReg .x2 - 1688
  x11 : u.getReg .x11 = s.getReg .x2 - 152
  x21 : u.getReg .x21 = s.getReg .x14

/-- Back from the first `eq_kernel`. -/
structure E1 (s m u : MachineState) : Prop where
  pc : u.pc = 0x8001033c
  x2 : u.getReg .x2 = s.getReg .x2 - 1856
  x9 : u.getReg .x9 = m.getMem (s.getReg .x2 - 1672)
  x18 : u.getReg .x18 = m.getMem (s.getReg .x2 - 1680)
  x21 : u.getReg .x21 = s.getReg .x14
  saved : Saved s u
  cap : u.getMem (s.getReg .x2 - 1848) = m.getMem (s.getReg .x2 - 1688)
  out : u.getMem (s.getReg .x2 - 1824) = s.getReg .x10
  first : u.getMem (s.getReg .x2 - 1792) = s.getReg .x15
  count : u.getMem (s.getReg .x2 - 1784) = s.getReg .x16
  value : eAt u (s.getReg .x2 - 152) = eAt m (s.getReg .x2 - 1664)
  sg : NewVecE m u (s.getReg .x2 - 1736) (sgOf s)
  heap : HeapOk u
  mono : heapNext m ≤ heapNext u
  rodata : RodataOk u
  frame : DFrame m u fun a ↦ Within a (s.getReg .x2 - 152) 24 ∨
    Within a (s.getReg .x2 - 1848) 32 ∨ Within a (s.getReg .x2 - 1736) 48 ∨
    Within a (stackLo s openStack) 1632 ∨ Within a nextAddr 8 ∨ Fresh m u a

set_option maxHeartbeats 4000000 in
theorem to_ek1 (hEK : EqKernelSpec) {s m : MachineState} (hpre : OpenPre s) (P : P2 s m)
    (hok : m.getMem (s.getReg .x2 - 1688) ≠ 0xffffffffffffffff) :
    ∃ u, Reaches Image.code m u ∧ (E1 s m u ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  have hc := hpre.claim
  have hHm := P.heap
  have hHm' := hHm.hi
  have monoSm := P.mono
  obtain ⟨hvec, hnb⟩ := slotOk P hok
  have hvl := hvec.len
  have hvr := hvec.raw
  simp only [RawVecOk, Buf] at hvr
  simp only [NewBuf] at hnb
  -- the claim and its point, as they were at the entry
  have mc : Misses (OpenW s m) (oClaim s) 96 := missOpenW hHm hpre.claimOut hpre.claimValue
    hpre.claimSelf hpre.claimStack hpre.claimFree (by addr_omega [hc])
  have cm (y : Word) (h1 : (s.getReg .x14).toNat ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x14).toNat + 96) : m.getMem y = s.getMem y :=
    P.frame y (mc.bytes h1 h2 (by addr_omega [hc]))
  have pR := hpre.point
  have pS := hpre.pointStack
  have pF := hpre.pointFree
  have pO := hpre.pointOut
  have pV := hpre.pointValue
  have pP := hpre.pointSelf
  simp only [VecRegion, VecApart, VecOutside, vecPtr, vecLen, oClaim, oOut, oValue, oP] at pR pS pF pO pV pP
  rv_eval [] at pR pS pF pO pV pP
  have mp : Misses (OpenW s m) (s.getMem (s.getReg .x14 + 32))
      (24 * (s.getMem (s.getReg .x14 + 40)).toNat) := by
    rcases pR with h0 | hR
    · intro y hy; simp only [Within, h0] at hy; omega
    · exact missOpenW hHm pO pV pP pS pF (by addr_omega [hR])
  have cvec : (claimAt s (oClaim s)).point =
      eListAt s (s.getMem (s.getReg .x14 + 32)) (s.getMem (s.getReg .x14 + 40)).toNat := by
    simp only [claimAt, vecEs, vecPtr, vecLen, oClaim]; rv_eval []
  -- `0x800102d8`: `Ok`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800102d8_spec P.pc (by
    rv_eval [P.x2]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b800102d8_keeps h₁
  have hm₁ := b800102d8_mem_same h₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1856 := (k₁ .x2 (by decide)).trans P.x2
  have x21₁ : t₁.getReg .x21 = s.getReg .x14 := (k₁ .x21 (by decide)).trans P.x21
  have x22₁ : t₁.getReg .x22 = s.getReg .x12 := (k₁ .x22 (by decide)).trans P.x22
  have x8₁ : t₁.getReg .x8 = s.getReg .x10 := (k₁ .x8 (by decide)).trans P.x8
  have x9₁ : t₁.getReg .x9 = m.getMem (s.getReg .x2 - 1672) := by
    rw [b800102d8_x9 h₁, P.x2]; rv_eval []
  have x14₁ : t₁.getReg .x14 = m.getMem (s.getReg .x2 - 1688) := by
    rw [b800102d8_x14 h₁, P.x2]; rv_eval []
  have x18₁ : t₁.getReg .x18 = m.getMem (s.getReg .x2 - 1680) := by
    rw [b800102d8_x18 h₁, P.x2]; rv_eval []
  -- `0x800102ec`: the value saved, the point's length checked
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800102ec_spec
    (b800102d8_pc_not_taken h₁ (by rw [P.x2]; rv_eval []; exact hok)) (by
      rv_eval [x2₁, x21₁]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc]))
  have k₂ := b800102ec_keeps h₂
  have f₂ := b800102ec_frame h₂ (by rw [x2₁]; addr_omega [hb])
  rw [x2₁] at f₂
  have hlen : t₁.getMem (s.getReg .x14 + 40) = s.getMem (s.getReg .x14 + 40) := by
    rw [hm₁, cm _ (by addr_omega [hc]) (by addr_omega [hc])]
  by_cases hlt : (s.getMem (s.getReg .x14 + 40)).toNat < (s.getReg .x12 - 4).toNat
  · refine ⟨t₂, hr₁.trans hr₂, Or.inr (dead_of_fetch ?_)⟩
    rw [b800102ec_pc_taken h₂ (by rw [x21₁, x22₁, hlen]; exact hlt)]
    exact trap
  have hpb : 4 ≤ (s.getReg .x12).toNat ∧ (s.getReg .x12 - 4).toNat = (s.getReg .x12).toNat - 4 := by
    have hsub : (s.getReg .x12 - 4).toNat = ((s.getReg .x12).toNat + (2 ^ 64 - 4)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub, show (4 : Word).toNat = 4 from rfl]; omega
    have := (s.getReg .x12).isLt
    rcases pR with h0 | hR
    · rw [h0] at hlt; omega
    · have hR' : (s.getMem (s.getReg .x14 + 40)).toNat < 2 ^ 59 := by addr_omega [hR]
      omega
  obtain ⟨hpb4, hpbn⟩ := hpb
  have pbLen : (s.getReg .x12).toNat - 4 ≤ (s.getMem (s.getReg .x14 + 40)).toNat := by omega
  -- `0x80010310`: `eq_kernel(&claim.point[pack_bits..])` into `f + 120`
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1856 := (k₂ .x2 (by decide)).trans x2₁
  have x21₂ : t₂.getReg .x21 = s.getReg .x14 := (k₂ .x21 (by decide)).trans x21₁
  have x22₂ : t₂.getReg .x22 = s.getReg .x12 - 4 := by rw [b800102ec_x22 h₂, x22₁]
  have hc32 : t₂.getMem (s.getReg .x14 + 32) = s.getMem (s.getReg .x14 + 32) := by
    rw [f₂ _ (by addr_omega [hc, pS, hb, hpre.claimStack]), hm₁,
      cm _ (by addr_omega [hc]) (by addr_omega [hc])]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80010310_spec
    (b800102ec_pc_not_taken h₂ (by rw [x21₁, x22₁, hlen]; omega)) (by
      rv_eval [x2₂, x21₂]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hc ?_ ?_ ?_ <;> addr_omega [hc])
        | addr_omega [hc, hpre.claimStack, hb])
  have k₃ := b80010310_keeps h₃
  have f₃ := b80010310_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1856 := (k₃ .x2 (by decide)).trans x2₂
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 1736 := by rw [b80010310_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = s.getMem (s.getReg .x14 + 32) +
      BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 4)) := by
    rw [b80010310_x11 h₃, x21₂, hc32, x22₂, mul24, hpbn]
  have x12₃ : (t₃.getReg .x12).toNat = (s.getMem (s.getReg .x14 + 40)).toNat -
      ((s.getReg .x12).toNat - 4) := by
    rw [b80010310_x12 h₃, b800102ec_x10 h₂, x22₂, x21₁, hlen, BitVec.toNat_sub, hpbn]
    have := (s.getMem (s.getReg .x14 + 40)).isLt
    omega
  have Fm3 : DFrame m t₃ (Within · (stackLo s openStack) openStack) :=
    ((DFrame.of_same hm₁ _).trans (DFrame.of_memFrame f₂) fun a h ↦ by addr_omega [h, hb]).trans
      (DFrame.of_memFrame f₃) fun a h ↦ by addr_omega [h, hb]
  have hN₃ : t₃.getMem nextAddr = m.getMem nextAddr := Fm3 _ fun i hi h ↦ by addr_omega [h, hi, hnx]
  have hH₃ : HeapOk t₃ := ⟨by simp only [heapNext, hN₃]; exact hHm.lo,
    by simp only [heapNext, hN₃]; exact hHm.hi⟩
  have hmono₃ : heapNext m = heapNext t₃ := by simp only [heapNext, hN₃]
  have Fs3 : DFrame s t₃ (OpenW s t₃) :=
    (P.frame.mono fun a h ↦ by
      simp only [OpenW, Fresh] at h ⊢; rw [← hmono₃]; exact h).trans Fm3 fun a h ↦ by
      simp only [OpenW]; exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  have rmM : RodataOk m := hpre.rodata.dframe P.frame fun a ha hw ↦ by
    have := hpre.outRodata
    have := hpre.valueRodata
    have := hpre.selfRodata
    have := hpre.self.self
    simp only [OpenW, Fresh] at hw
    rcases hw with hw | hw | hw | hw | hw | hw <;>
      addr_omega [ha, hw, hrs, hpre.outRodata, hpre.valueRodata, hpre.selfRodata, hpre.self.self,
        hHm', monoSm]
  have rm₃ : RodataOk t₃ := rmM.dframe Fm3 fun a ha hw ↦ by addr_omega [ha, hw, hrs]
  have hPs : (s.getReg .x12).toNat - 4 ≤ (s.getMem (s.getReg .x14 + 40)).toNat := pbLen
  have hek : EqKernelPre t₃ := {
    heap := hH₃
    out := by rw [x10₃]; addr_omega [hb, hsm]
    point := by
      rw [x12₃, x11₃]
      rcases pR with h0 | hR
      · left; omega
      · by_cases h0 : (s.getMem (s.getReg .x14 + 40)).toNat - ((s.getReg .x12).toNat - 4) = 0
        · left; exact h0
        · right; addr_omega [hR, hPs, h0]
    stack := hpre.stack.sub 1856 x2₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [x10₃]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x12₃, x11₃]
      right
      rcases pR with h0 | hR
      · rw [show (s.getReg .x12).toNat - 4 = 0 by omega, h0]
        refine ⟨?_, Or.inl rfl⟩
        have := pF.1
        addr_omega [this, monoSm, hmono₃]
      · addr_omega [pF, monoSm, hmono₃, hR, hPs]
    outStack := by rw [x10₃]; simp only [stackLo, x2₃]; addr_omega [hb]
    pointStack := by
      rw [x12₃, x11₃]; simp only [stackLo, x2₃]
      rcases pR with h0 | hR
      · rw [show (s.getReg .x12).toNat - 4 = 0 by omega, h0]; exact Or.inl rfl
      · addr_omega [pS, hR, hPs, hb]
    pointOut := by
      rw [x12₃, x11₃, x10₃]
      rcases pR with h0 | hR
      · rw [show (s.getReg .x12).toNat - 4 = 0 by omega, h0]; exact Or.inl rfl
      · addr_omega [pS, hR, hPs, hb]
    rodata := rm₃
    outRodata := by rw [x10₃]; addr_omega [hrs, hb] }
  obtain ⟨e₁, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hd⟩ := hEK.call (hr₁.trans (hr₂.trans hr₃))
    (b80010310_pc h₃) hek
  swap
  · exact ⟨_, hr₄, Or.inr hd⟩
  have G₄ := hpost₄.frame
  have V₄ := hpost₄.value
  rw [x10₃] at G₄ V₄
  rw [x11₃, x12₃] at V₄
  simp only [stackLo, x2₃] at G₄
  have hH₄ := hpost₄.heap
  have mono₄ := hpost₄.mono
  have x2e₁ : e₁.getReg .x2 = s.getReg .x2 - 1856 := (hpres₄.reg .x2).trans x2₃
  have x9e₁ : e₁.getReg .x9 = m.getMem (s.getReg .x2 - 1672) := by
    rw [hpres₄.reg .x9, k₃ .x9 (by decide), k₂ .x9 (by decide), x9₁]
  have x18e₁ : e₁.getReg .x18 = m.getMem (s.getReg .x2 - 1680) := by
    rw [hpres₄.reg .x18, k₃ .x18 (by decide), k₂ .x18 (by decide), x18₁]
  have x21e₁ : e₁.getReg .x21 = s.getReg .x14 := by
    rw [hpres₄.reg .x21, k₃ .x21 (by decide), x21₂]
  have mp3 : Misses (OpenW s t₃) (s.getMem (s.getReg .x14 + 32))
      (24 * (s.getMem (s.getReg .x14 + 40)).toNat) := by
    rcases pR with h0 | hR
    · intro y hy; simp only [Within, h0] at hy; omega
    · exact missOpenW hH₃ pO pV pP pS pF (by addr_omega [hR])
  have sgv : eqKernelRust (eListAt t₃ (s.getMem (s.getReg .x14 + 32) +
      BitVec.ofNat 64 (24 * ((s.getReg .x12).toNat - 4)))
      ((s.getMem (s.getReg .x14 + 40)).toNat - ((s.getReg .x12).toNat - 4))) = sgOf s := by
    rw [sgOf, cvec, eListAt_drop]
    congr 1
    rcases pR with h0 | hR
    · simp only [h0, Nat.zero_sub]; rfl
    · exact Fs3.eListAt fun i hi ↦ mp3 _ (by addr_omega [hi, hR, hPs])
  have hH4e := hH₄.hi
  have FWe : DFrame m e₁ fun a ↦ Within a (s.getReg .x2 - 152) 24 ∨
      Within a (s.getReg .x2 - 1848) 32 ∨ Within a (s.getReg .x2 - 1736) 48 ∨
      Within a (stackLo s openStack) 1632 ∨ Within a nextAddr 8 ∨ Fresh m e₁ a := by
    refine (((DFrame.of_same hm₁ _).trans (DFrame.of_memFrame f₂) fun a h ↦ Or.inl
      (by addr_omega [h, hb])).trans (DFrame.of_memFrame f₃) fun a h ↦ Or.inr (Or.inl
      (by addr_omega [h, hb]))).trans G₄ ?_
    intro a h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hmono₃ ▸ h.1, h.2⟩))))
  have keepE (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1848 ∨ (s.getReg .x2).toNat - 1816 ≤ y.toNat)
      (h4 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1736 ∨ (s.getReg .x2).toNat - 1688 ≤ y.toNat)
      (h5 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 152 ∨ (s.getReg .x2).toNat - 128 ≤ y.toNat) :
      e₁.getMem y = m.getMem y :=
    FWe y fun i hi h ↦ by
      rcases h with h | h | h | h | h | h <;>
        addr_omega [h, hi, h1, h2, h3, h4, h5, hb, hnx, hab, hH4e]
  have from₃ (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h4 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1736 ∨ (s.getReg .x2).toNat - 1712 ≤ y.toNat) :
      e₁.getMem y = t₃.getMem y :=
    G₄ y fun i hi h ↦ by
      rcases h with h | h | h | h <;> addr_omega [h, hi, h1, h2, h4, hb, hnx, hab, hH4e]
  have hcap : e₁.getMem (s.getReg .x2 - 1848) = m.getMem (s.getReg .x2 - 1688) := by
    rw [from₃ _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]
    have := b80010310_m_x2_8 h₃
    rw [x2₂] at this; rv_eval [] at this
    rw [this, k₂ .x14 (by decide), x14₁]
  have hout : e₁.getMem (s.getReg .x2 - 1824) = s.getReg .x10 := by
    rw [from₃ _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]
    have := b80010310_m_x2_32 h₃
    rw [x2₂] at this; rv_eval [] at this
    rw [this, k₂ .x8 (by decide), x8₁]
  have hval : eAt e₁ (s.getReg .x2 - 152) = eAt m (s.getReg .x2 - 1664) := by
    have v0 := b800102ec_m_x2_1704 h₂
    have v8 := b800102ec_m_x2_1712 h₂
    have v16 := b800102ec_m_x2_1720 h₂
    rw [x2₁, hm₁] at v0 v8 v16
    rv_eval [] at v0 v8 v16
    have t32 (y : Word) (h1 : (s.getReg .x2).toNat - 152 ≤ y.toNat)
        (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 128) : e₁.getMem y = t₂.getMem y := by
      rw [from₃ y (by addr_omega [h1, hb]) (by addr_omega [h2, hb]) (Or.inr (by addr_omega [h1, hb])),
        f₃ y (by addr_omega [h1, h2, hb])]
    unfold Rv64Verifier.eAt
    rw [show s.getReg .x2 - 152 + 8 = s.getReg .x2 - 144 by rv_eval [],
      show s.getReg .x2 - 152 + 16 = s.getReg .x2 - 136 by rv_eval [],
      show s.getReg .x2 - 1664 + 8 = s.getReg .x2 - 1656 by rv_eval [],
      show s.getReg .x2 - 1664 + 16 = s.getReg .x2 - 1648 by rv_eval [],
      t32 _ (by addr_omega [hb]) (by addr_omega [hb]), t32 _ (by addr_omega [hb]) (by addr_omega [hb]),
      t32 _ (by addr_omega [hb]) (by addr_omega [hb]), v0, v8, v16]
  refine ⟨e₁, hr₄, Or.inl {
    pc := by rw [hpc₄, returnAddress_eq, b80010310_x1 h₃]; decide
    x2 := x2e₁
    x9 := x9e₁
    x18 := x18e₁
    x21 := x21e₁
    saved := P.saved.keep (by addr_omega [hb]) fun y h1 h2 ↦
      keepE y (by addr_omega [h1, hb]) h2 (Or.inr (by addr_omega [h1, hb]))
        (Or.inr (by addr_omega [h1, hb])) (Or.inr (by addr_omega [h1, hb]))
    cap := hcap
    out := hout
    first := by
      rw [keepE _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))
        (Or.inl (by addr_omega [hb])) (Or.inl (by addr_omega [hb])), P.first]
    count := by
      rw [keepE _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))
        (Or.inl (by addr_omega [hb])) (Or.inl (by addr_omega [hb])), P.count]
    value := hval
    sg := by
      have h1 := newVecE_mono V₄ (le_of_eq hmono₃)
      rw [sgv] at h1; exact h1
    heap := hH₄
    mono := hmono₃ ▸ mono₄
    rodata := rm₃.dframe G₄ fun a ha hw ↦ by
      rcases hw with hw | hw | hw | hw <;> addr_omega [ha, hw, hrs, hb, hH4e]
    frame := FWe }⟩

set_option maxHeartbeats 4000000 in
theorem to_zero (hEK : EqKernelSpec) {s m e₁ : MachineState} (hpre : OpenPre s) (P : P2 s m)
    (hok : m.getMem (s.getReg .x2 - 1688) ≠ 0xffffffffffffffff) (E : E1 s m e₁) :
    ∃ u, Reaches Image.code e₁ u ∧ (Z0 s m u ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  have hHm := P.heap
  have hHm' := hHm.hi
  obtain ⟨hvec, hnb⟩ := slotOk P hok
  have hvl := hvec.len
  have hvr := hvec.raw
  simp only [RawVecOk, Buf] at hvr
  simp only [NewBuf] at hnb
  have x2e₁ := E.x2
  have x9e₁ := E.x9
  have x18e₁ := E.x18
  have x21e₁ := E.x21
  have hH₄ := E.heap
  have monoE := E.mono
  -- `0x8001033c`: `eq_kernel(&slot)` into `f + 144`
  obtain ⟨t₄, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8001033c_spec
    E.pc (by
      rv_eval [x2e₁]
      and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b8001033c_keeps h₅
  have f₅ := b8001033c_frame h₅ (by rw [x2e₁]; addr_omega [hb])
  rw [x2e₁] at f₅
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1856 := (k₅ .x2 (by decide)).trans x2e₁
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 1712 := by rw [b8001033c_x10 h₅, x2e₁]; rv_eval []
  have x11₄ : t₄.getReg .x11 = m.getMem (s.getReg .x2 - 1680) := by rw [b8001033c_x11 h₅, x18e₁]
  have x12₄ : t₄.getReg .x12 = m.getMem (s.getReg .x2 - 1672) := by rw [b8001033c_x12 h₅, x9e₁]
  have hN₄ : t₄.getMem nextAddr = e₁.getMem nextAddr := f₅ _ (by addr_omega [hb, hnx])
  have hH₄' : HeapOk t₄ := ⟨by simp only [heapNext, hN₄]; exact hH₄.lo,
    by simp only [heapNext, hN₄]; exact hH₄.hi⟩
  have monoM4 : heapNext m ≤ heapNext t₄ := by
    have : heapNext m ≤ heapNext e₁ := monoE
    simp only [heapNext, hN₄] at this ⊢; exact this
  simp only [vecPtr, vecLen, vecCap] at hvr hvl hnb
  rv_eval [] at hvr hvl hnb
  have hH4hi := hH₄'.hi
  have hek₂ : EqKernelPre t₄ := {
    heap := hH₄'
    out := by rw [x10₄]; addr_omega [hb, hsm]
    point := by
      rw [x12₄, x11₄]
      by_cases h0 : (m.getMem (s.getReg .x2 - 1672)).toNat = 0
      · left; exact h0
      · right; addr_omega [hvr, hvl, h0, hHm']
    stack := hpre.stack.sub 1856 x2₄ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [x10₄]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    pointFree := by
      rw [x12₄, x11₄]
      by_cases h0 : (m.getMem (s.getReg .x2 - 1672)).toNat = 0
      · left; exact h0
      · right; addr_omega [hvr, hvl, h0, hHm', monoM4]
    outStack := by rw [x10₄]; simp only [stackLo, x2₄]; addr_omega [hb]
    pointStack := by
      rw [x12₄, x11₄]; simp only [stackLo, x2₄]
      by_cases h0 : (m.getMem (s.getReg .x2 - 1672)).toNat = 0
      · rw [h0]; exact Or.inl rfl
      · addr_omega [hvr, hvl, h0, hHm', hab, hb]
    pointOut := by
      rw [x12₄, x11₄, x10₄]
      by_cases h0 : (m.getMem (s.getReg .x2 - 1672)).toNat = 0
      · rw [h0]; exact Or.inl rfl
      · addr_omega [hvr, hvl, h0, hHm', hab, hb]
    rodata := E.rodata.dframe (DFrame.of_memFrame f₅) fun a ha hw ↦ by addr_omega [ha, hw, hrs, hb]
    outRodata := by rw [x10₄]; addr_omega [hrs, hb] }
  obtain ⟨e₂, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hd⟩ := hEK.call hr₅ (b8001033c_pc h₅) hek₂
  swap
  · exact ⟨_, hr₆, Or.inr hd⟩
  have G₆ := hpost₆.frame
  have V₆ := hpost₆.value
  rw [x10₄] at G₆ V₆
  rw [x11₄, x12₄] at V₆
  simp only [stackLo, x2₄] at G₆
  have x2e₂ : e₂.getReg .x2 = s.getReg .x2 - 1856 := (hpres₆.reg .x2).trans x2₄
  -- `0x80010358`: the row's bounds
  obtain ⟨u, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80010358_spec
    (by rw [hpc₆, returnAddress_eq, b8001033c_x1 h₅]; decide) trivial
  have k₇ := b80010358_keeps h₇
  have hm₇ := b80010358_mem_same h₇
  have hHu : HeapOk u := ⟨by simp only [heapNext, hm₇]; exact hpost₆.heap.lo,
    by simp only [heapNext, hm₇]; exact hpost₆.heap.hi⟩
  have mono₆ := hpost₆.mono
  have hmu : heapNext m ≤ heapNext u := by
    simp only [heapNext, hm₇] at mono₆ ⊢; exact monoM4.trans mono₆
  have hHuh := hHu.hi
  have hmu4 : heapNext t₄ ≤ heapNext u := by
    have := hpost₆.mono; simp only [heapNext, hm₇] at this ⊢; exact this
  have he2u : heapNext e₂ = heapNext u := by simp only [heapNext, hm₇]
  have hHe2 := hpost₆.heap.hi
  have hH4e := hH₄.hi
  have hNe : heapNext t₄ = heapNext e₁ := by simp only [heapNext, hN₄]
  have FW4 : DFrame m t₄ fun a ↦ Within a (s.getReg .x2 - 152) 24 ∨
      Within a (s.getReg .x2 - 1848) 32 ∨ Within a (s.getReg .x2 - 1736) 48 ∨
      Within a (stackLo s openStack) 1632 ∨ Within a nextAddr 8 ∨ Fresh m t₄ a :=
    (E.frame.mono fun a h ↦ by
        rcases h with h | h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, hNe ▸ h.2⟩))))).trans
      (DFrame.of_memFrame f₅) fun a h ↦ Or.inr (Or.inl (by addr_omega [h, hb]))
  have FW : DFrame m u fun a ↦ Within a (s.getReg .x2 - 152) 24 ∨
      Within a (s.getReg .x2 - 1848) 32 ∨ Within a (s.getReg .x2 - 1736) 48 ∨
      Within a (stackLo s openStack) 1632 ∨ Within a nextAddr 8 ∨ Fresh m u a := by
    refine ((FW4.mono fun a h ↦ ?_).trans G₆ ?_).trans (DFrame.of_same hm₇ _) fun _ h ↦ h
    · rcases h with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, lt_of_lt_of_le h.2 hmu4⟩))))
    · intro a h
      rcases h with h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨monoM4.trans h.1, he2u ▸ h.2⟩))))
  -- what `e₁` held, past the second call
  have fromE (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1840 ∨ (s.getReg .x2).toNat - 1824 ≤ y.toNat)
      (h4 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1712 ∨ (s.getReg .x2).toNat - 1688 ≤ y.toNat) :
      u.getMem y = e₁.getMem y := by
    rw [hm₇, G₆ y fun i hi h ↦ by
        rcases h with h | h | h | h <;> addr_omega [h, hi, h1, h2, h4, hb, hnx, hab, hHe2],
      f₅ y (by addr_omega [h1, h2, h3, hb])]
  have from₄ (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat)
      (h4 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1712 ∨ (s.getReg .x2).toNat - 1688 ≤ y.toNat) :
      u.getMem y = t₄.getMem y := by
    rw [hm₇, G₆ y fun i hi h ↦ by
        rcases h with h | h | h | h <;> addr_omega [h, hi, h1, h2, h4, hb, hnx, hab, hHe2]]
  have x2u : u.getReg .x2 = s.getReg .x2 - 1856 := (k₇ .x2 (by decide)).trans x2e₂
  have hptr : u.getMem (s.getReg .x2 - 1840) = m.getMem (s.getReg .x2 - 1680) := by
    rw [from₄ _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]
    have := b8001033c_m_x2_16 h₅
    rw [x2e₁] at this; rv_eval [] at this
    rw [this, x18e₁]
  have hlen' : u.getMem (s.getReg .x2 - 1832) = m.getMem (s.getReg .x2 - 1672) := by
    rw [from₄ _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))]
    have := b8001033c_m_x2_24 h₅
    rw [x2e₁] at this; rv_eval [] at this
    rw [this, x9e₁]
  have hval : eAt u (s.getReg .x2 - 152) = eAt m (s.getReg .x2 - 1664) := by
    rw [← E.value]
    unfold Rv64Verifier.eAt
    rw [fromE _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))
        (Or.inr (by addr_omega [hb])),
      fromE (s.getReg .x2 - 152 + 8) (by addr_omega [hb]) (by addr_omega [hb])
        (Or.inr (by addr_omega [hb])) (Or.inr (by addr_omega [hb])),
      fromE (s.getReg .x2 - 152 + 16) (by addr_omega [hb]) (by addr_omega [hb])
        (Or.inr (by addr_omega [hb])) (Or.inr (by addr_omega [hb]))]
  have kE (y : Word) (h1 : (s.getReg .x2).toNat - 1856 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat) (h3 : (s.getReg .x2).toNat - 1824 ≤ y.toNat ∨
        y.toNat + 8 ≤ (s.getReg .x2).toNat - 1840)
      (h4 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1712 ∨ (s.getReg .x2).toNat - 1688 ≤ y.toNat) :
      u.getMem y = e₁.getMem y := fromE y h1 h2 (h3.symm) h4
  have sg : NewVecE m u (s.getReg .x2 - 1736) (sgOf s) := by
    have h2 := newVecE_keep' E.sg (DFrame.of_memFrame f₅)
      (by simp only [heapNext, hN₄]; exact le_refl _)
      (fun i hi h ↦ by addr_omega [h, hi, hb]) (fun y hy h ↦ by addr_omega [h, hy, hb, hab, hH4e])
    have h3 := newVecE_keep' h2 G₆ hpost₆.mono
      (fun i hi h ↦ by rcases h with h | h | h | h <;> addr_omega [h, hi, hb, hnx, hab, hHe2])
      (fun y hy h ↦ by rcases h with h | h | h | h <;> addr_omega [h, hy, hb, hnx, hab, hH4hi])
    exact newVecE_keep' h3 (DFrame.of_same hm₇ fun _ ↦ False)
      (by simp only [heapNext, hm₇]; exact le_refl _) (fun _ _ h ↦ h) (fun _ _ h ↦ h)
  have slv : eqKernelRust (eListAt t₄ (m.getMem (s.getReg .x2 - 1680))
      (m.getMem (s.getReg .x2 - 1672)).toNat) = slOf s m := by
    rw [slOf]
    congr 1
    simp only [vecEs, vecPtr, vecLen]
    rw [show s.getReg .x2 - 1688 + 8 = s.getReg .x2 - 1680 by rv_eval [],
      show s.getReg .x2 - 1688 + 16 = s.getReg .x2 - 1672 by rv_eval []]
    by_cases h0 : (m.getMem (s.getReg .x2 - 1672)).toNat = 0
    · rw [h0]; rfl
    · exact FW4.eListAt fun i hi h ↦ by
        rcases h with h | h | h | h | h | h <;>
          addr_omega [h, hi, hvr, hvl, h0, hHm', hb, hnx, hab]
  have sl : NewVecE m u (s.getReg .x2 - 1712) (slOf s m) := by
    have h1 := newVecE_mono V₆ monoM4
    rw [slv] at h1
    exact newVecE_keep' h1 (DFrame.of_same hm₇ fun _ ↦ False)
      (by simp only [heapNext, hm₇]; exact le_refl _) (fun _ _ h ↦ h) (fun _ _ h ↦ h)
  refine ⟨u, hr₆.trans hr₇, Or.inl {
    pc := b80010358_pc h₇
    mid := {
      x2 := x2u
      saved := E.saved.keep (by addr_omega [hb]) fun y h1 h2 ↦
        kE y (by addr_omega [h1, hb]) h2 (Or.inl (by addr_omega [h1, hb]))
          (Or.inr (by addr_omega [h1, hb]))
      cap := by
        rw [kE _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inr (by addr_omega [hb]))
          (Or.inl (by addr_omega [hb])), E.cap]
      ptr := hptr
      len := hlen'
      out := by
        rw [kE _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))
          (Or.inl (by addr_omega [hb])), E.out]
      first := by
        rw [kE _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))
          (Or.inl (by addr_omega [hb])), E.first]
      count := by
        rw [kE _ (by addr_omega [hb]) (by addr_omega [hb]) (Or.inl (by addr_omega [hb]))
          (Or.inl (by addr_omega [hb])), E.count]
      value := hval
      sg
      sl
      heap := hHu
      mono := hmu
      frame := FW.mono fun a h ↦ by
        rcases h with h | h | h | h | h | h
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inl (by addr_omega [h, hb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h) }
    x10 := by rw [b80010358_x10 h₇, x2e₂]; rv_eval []
    x11 := by rw [b80010358_x11 h₇, x2e₂]; rv_eval []
    x21 := by rw [k₇ .x21 (by decide), hpres₆.reg .x21, k₅ .x21 (by decide), x21e₁] }⟩

end Rv64Verifier.Gkr.Open
