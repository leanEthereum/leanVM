import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F70

/-!
# `Vec<E>::spec_extend` from a slice, with room enough

compiled at `0x8000e520` (`Blocks/F70.lean`), with `S` the entry's `sp`: `0x8000e520` saves
`ra`, `s0`..`s4` in a 48-byte frame and computes the slice's length (`(a2 - a1) / 24`, the
division by 3 as a product by its inverse); `reserve` returns at once (`reserve_fast`);
`0x8000e574` reads the length and skips an empty slice; `0x8000e580` calls
`memcpy(ptr + 24 len, a1, a2 - a1)`; `0x8000e5a0` grows the length, restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.SpecExtend
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts
  Rv64Verifier.MultilinearWords Rv64Verifier.Blocks.F70
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Division by 24 as compiled: by 8, then the product by 3's inverse. -/
theorem div24 (x : Word) (n : Nat) (hx : x.toNat = 24 * n) :
    (x >>> 3) * (0xaaaaaaaaaaaaaaab : Word) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, hx, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, show (24 * n) / 2 ^ 3 = 3 * n by omega]
  simp only [Sym.wordToNatLit]
  rw [show 3 * n * 12297829382473034411 = n + 2 ^ 64 * (2 * n) by ring, Nat.add_mul_mod_self_left]

theorem bounds {s : MachineState} (h : ExtendPre s) :
    0x78000040 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.vec (by decide)
  simp only [extendStack, memcpyStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- **`spec_extend` with room enough meets its contract**, given `memcpy`'s. -/
theorem extend_spec (hC : MemcpySpec 0x800126e4) : ExtendSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hvs := hpre.vecStack
  have hvh := hpre.vecHeap
  simp only [Outside] at hvh
  have hS := hpre.src
  have hss := hpre.srcStack
  have hsv := hpre.srcVec
  have hsd := hpre.srcDst
  have hdv := hpre.dstVec
  have hroom := hpre.room
  have hraw := hpre.ok.raw
  simp only [RawVecOk, Buf] at hraw
  have hfit := hpre.heap.hi
  have hlo := hpre.heap.lo
  obtain ⟨n, hn⟩ : ∃ n, n = extendLen s := ⟨_, rfl⟩
  have hbytes : (s.getReg .x12 - s.getReg .x11).toNat = 24 * n := by
    rw [BitVec.toNat_sub, hn, extendLen]; have := hpre.bounds; have := hpre.whole; omega
  rw [← hn] at hroom hS hss hsv hsd hdv
  -- the buffer's free part
  obtain ⟨L, hL⟩ : ∃ L, L = (vecLen s (s.getReg .x10)).toNat := ⟨_, rfl⟩
  obtain ⟨C, hC'⟩ : ∃ C, C = (vecCap s (s.getReg .x10)).toNat := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = vecPtr s (s.getReg .x10) := ⟨_, rfl⟩
  rw [← hL, ← hC'] at hroom
  rw [← hQ, ← hC'] at hraw
  have hdst : extendDst s = Q + BitVec.ofNat 64 (24 * L) := by rw [extendDst, ← hQ, ← hL]
  rw [hdst] at hsd hdv
  have hQr : n = 0 ∨ (heapStart ≤ Q.toNat ∧ Q.toNat + 24 * (L + n) ≤ heapNext s) := by
    rcases hraw.2 with h | h
    · exact Or.inl (by rcases Nat.mul_eq_zero.mp h with h | h <;> omega)
    · exact Or.inr ⟨h.1, by have := Nat.mul_le_mul_right 24 hroom; omega⟩
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000e520_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000e520_keeps h₁
  have hm₁ := b8000e520_frame h₁ (by addr_omega [hb])
  have hvec₁ (o : Word) (ho : o = 0 ∨ o = 8 ∨ o = 16) :
      t₁.getMem (s.getReg .x10 + o) = s.getMem (s.getReg .x10 + o) :=
    hm₁ _ (by rcases ho with rfl | rfl | rfl <;> addr_omega [hb, hvs])
  have v0 := hvec₁ 0 (Or.inl rfl)
  have v8 := hvec₁ 8 (Or.inr (Or.inl rfl))
  have v16 := hvec₁ 16 (Or.inr (Or.inr rfl))
  rv_eval [] at v0 v8 v16
  have hcount : t₁.getReg .x18 = BitVec.ofNat 64 n := by
    rw [b8000e520_x18 h₁]; exact div24 _ n hbytes
  have hx10₁ : t₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
  obtain ⟨t₂, hr₂, hpc₂, hpres₂, hx10₂, hm₂⟩ := reserve_fast (b8000e520_pc h₁)
    (by rw [hx10₁]; exact hpre.vec)
    (by
      rw [hx10₁, v0, v16, b8000e520_x11 h₁, div24 _ n hbytes, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      simp only [vecLen, vecCap] at hL hC'
      omega)
  have hreg₂ (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20]) :
      t₂.getReg r = t₁.getReg r := hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000e574_spec
    (by rw [hpc₂, returnAddress_eq, b8000e520_x1 h₁]; decide) (by
      rv_eval [hreg₂ .x8 (by decide), b8000e520_x8 h₁]
      valid_access hpre.vec [hb])
  have k₃ := b8000e574_keeps h₃
  have hm₃ := b8000e574_mem_same h₃
  have hlen₃ : t₃.getReg .x20 = vecLen s (s.getReg .x10) := by
    rw [b8000e574_x20 h₃, hreg₂ .x8 (by decide), b8000e520_x8 h₁, hm₂, v16, vecLen]
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 48 := b8000e520_x2 h₁
  -- the epilogue, from a state at `0x8000e5a0` whose memory differs from `t₁`'s only in the
  -- new elements and `memcpy`'s stack
  have fin (u : MachineState) (hu : Reaches Image.code s u) (hpcu : u.pc = 0x8000e5a0)
      (hreg : ∀ r ∈ [Reg.x2, .x8, .x18, .x20], u.getReg r = t₃.getReg r)
      (hkeep : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27], u.getReg r = s.getReg r)
      (hbf : ByteFrame t₁ u fun a ↦ Within a (Q + BitVec.ofNat 64 (24 * L)) (24 * n) ∨
        Within a (s.getReg .x2 - 64) 16)
      (hnew : eListAt u (Q + BitVec.ofNat 64 (24 * L)) n = eListAt s (s.getReg .x11) n) :
      ∃ t, Reaches Image.code s t ∧
        ((t.pc = returnAddress s ∧ Preserves s t ∧ ExtendPost s t) ∨ Dead Image.code t) := by
    have hu2 : u.getReg .x2 = s.getReg .x2 - 48 := by
      rw [hreg .x2 (by decide), k₃ .x2 (by decide), hreg₂ .x2 (by decide), hsp₁]
    have hu8 : u.getReg .x8 = s.getReg .x10 := by
      rw [hreg .x8 (by decide), k₃ .x8 (by decide), hreg₂ .x8 (by decide), b8000e520_x8 h₁]
    have hbuf (a : Word) (ha : Within a (Q + BitVec.ofNat 64 (24 * L)) (24 * n)) :
        ¬ Within a (s.getReg .x2 - 64) 64 ∧ ¬ Within a (s.getReg .x10) 24 := by
      rcases hQr with h0 | h0
      · subst h0; simp only [Within] at ha; omega
      · exact ⟨by addr_omega [ha, h0, hfit, hab, hb], by addr_omega [ha, hdv]⟩
    have keepu (a : Word) (ha : a.toNat % 8 = 0) (h1 : ¬ Within a (s.getReg .x2 - 64) 16)
        (h2 : ∀ i < 8, ¬ Within (a + BitVec.ofNat 64 i) (Q + BitVec.ofNat 64 (24 * L)) (24 * n)) :
        u.getMem a = t₁.getMem a :=
      hbf.getMem fun i hi hw ↦ by
        rcases hw with hw | hw
        · exact h2 i hi hw
        · exact h1 (by addr_omega [hw, hi, ha, hb])
    have sl (o : Nat) (ho1 : 8 ≤ o) (ho2 : o ≤ 48) (ho3 : o % 8 = 0) :
        u.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = t₁.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
      keepu _ (by addr_omega [hb, ho1, ho2, ho3]) (by addr_omega [hb, ho1, ho2])
        fun i hi hw ↦ (hbuf _ hw).1 (by addr_omega [hb, ho1, ho2, hi])
    have sl8 := sl 8 (by decide) (by decide) rfl
    have sl16 := sl 16 (by decide) (by decide) rfl
    have sl24 := sl 24 (by decide) (by decide) rfl
    have sl32 := sl 32 (by decide) (by decide) rfl
    have sl40 := sl 40 (by decide) (by decide) rfl
    have sl48 := sl 48 (by decide) (by decide) rfl
    rv_eval [b8000e520_m_x2_n8 h₁, b8000e520_m_x2_n16 h₁, b8000e520_m_x2_n24 h₁,
      b8000e520_m_x2_n32 h₁, b8000e520_m_x2_n40 h₁, b8000e520_m_x2_n48 h₁]
      at sl8 sl16 sl24 sl32 sl40 sl48
    obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000e5a0_spec hpcu (by
      rv_eval [hu2, hu8]
      and_intros <;> first
        | addr_omega [hb, hvs]
        | valid_access hst.valid [hb]
        | valid_access hpre.vec [hb])
    have k := b8000e5a0_keeps ht
    have hm := b8000e5a0_frame ht (by rw [hu8]; addr_omega [hb])
    rw [hu8] at hm
    have pc := b8000e5a0_pc ht
    have x2 := b8000e5a0_x2 ht
    have x8 := b8000e5a0_x8 ht
    have x9 := b8000e5a0_x9 ht
    have x18 := b8000e5a0_x18 ht
    have x19 := b8000e5a0_x19 ht
    have x20 := b8000e5a0_x20 ht
    have ml := b8000e5a0_m_x8_16 ht
    rv_eval [hu2, sl8, sl16, sl24, sl32, sl40, sl48, hu8] at pc x2 x8 x9 x18 x19 x20 ml
    have bfe := ByteFrame.of_memFrame hm (by addr_omega [hb]) (by decide)
      (ht.unaligned (by rv_eval [hu8]; addr_omega [hb]))
    have bf₁ := ByteFrame.of_memFrame hm₁ (by addr_omega [hb]) (by decide)
      (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb]))
    have hall : ByteFrame s t fun a ↦ Within a (s.getReg .x10 + 16) 8 ∨
        Within a (extendDst s) (24 * extendLen s) ∨
        Within a (stackLo s extendStack) extendStack := by
      rw [hdst, ← hn]
      refine ((bf₁.mono fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hb]))).trans hbf
        fun a ha ↦ ?_).trans bfe fun a ha ↦ Or.inl ha
      rcases ha with ha | ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (by addr_omega [ha, hb]))
    have hmem (a : Word) (ha : a.toNat % 8 = 0) (h1 : ¬ Within a (s.getReg .x2 - 64) 64)
        (h2 : ∀ i < 8, ¬ Within (a + BitVec.ofNat 64 i) (Q + BitVec.ofNat 64 (24 * L)) (24 * n))
        (h3 : a ≠ s.getReg .x10 + 16) : t.getMem a = s.getMem a := by
      rw [hm a (by addr_omega [h3, ha, hb]), keepu a ha (by addr_omega [h1, hb]) h2,
        hm₁ a (by addr_omega [h1, hb])]
    have hu18 : u.getReg .x18 = BitVec.ofNat 64 n := by
      rw [hreg .x18 (by decide), k₃ .x18 (by decide), hreg₂ .x18 (by decide), hcount]
    have hu20 : u.getReg .x20 = vecLen s (s.getReg .x10) := by
      rw [hreg .x20 (by decide), hlen₃]
    have hL64 : L + n < 2 ^ 64 := by
      have := (vecCap s (s.getReg .x10)).isLt; rw [← hC'] at this; omega
    have hword (o : Word) (ho : o = 0 ∨ o = 8) :
        t.getMem (s.getReg .x10 + o) = s.getMem (s.getReg .x10 + o) :=
      hmem _ (by rcases ho with rfl | rfl <;> addr_omega [hb])
        (by rcases ho with rfl | rfl <;> addr_omega [hb, hvs])
        (fun i hi hw ↦ (hbuf _ hw).2 (by rcases ho with rfl | rfl <;> addr_omega [hb, hi]))
        (by rcases ho with rfl | rfl <;> addr_omega [hb])
    have w0 := hword 0 (Or.inl rfl)
    have w8 := hword 8 (Or.inr rfl)
    rv_eval [] at w0
    have hnt : t.getMem nextAddr = s.getMem nextAddr := hall.getMem fun i hi hw ↦ by
      rcases hw with hw | hw | hw
      · addr_omega [hw, hi, hvh.2, hb]
      · rw [hdst, ← hn] at hw
        rcases hQr with h0 | h0
        · subst h0; simp only [Within] at hw; omega
        · addr_omega [hw, hi, h0, hfit]
      · addr_omega [hw, hi, hnx8, hb]
    refine ⟨t, hu.trans hr, Or.inl ⟨pc.trans (returnAddress_eq s).symm,
      preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_, {
        len := ?_
        cap := by rw [vecCap, vecCap, w0]
        ptr := by rw [vecPtr, vecPtr, w8]
        new := ?_
        next := by simp only [heapNext, hnt]
        frame := hall }⟩⟩
    · rcases List.mem_cons.mp hr' with rfl | hr'
      · exact x20
      · exact (k r (mem_of_mem hr' _)).trans (hkeep r hr')
    · rw [vecLen, ml, hu20, hu18, BitVec.toNat_add, BitVec.toNat_ofNat, ← hn, ← hL]
      rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (by omega)]
    · rw [hdst, ← hn, ← hnew]
      simp only [eListAt]
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      rcases hQr with h0 | h0
      · omega
      exact hm.eAt (by addr_omega [hj, h0, hdv, hb]) (by addr_omega [hj, h0, hfit])
  -- an empty slice, or the copy
  have hkeep₃ (r : Reg) (hr : r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27]) :
      t₃.getReg r = s.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  have bf₁ := ByteFrame.of_memFrame hm₁ (by addr_omega [hb]) (by decide)
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb]))
  have hm31 (a : Word) : t₃.getMem a = t₁.getMem a := (hm₃ a).trans (hm₂ a)
  have hx19 : t₂.getReg .x19 = s.getReg .x12 := by
    rw [hreg₂ .x19 (by decide), b8000e520_x19 h₁]
  have hx20 : t₂.getReg .x20 = s.getReg .x11 := by
    rw [hreg₂ .x20 (by decide), b8000e520_x20 h₁]
  by_cases h0 : n = 0
  · subst h0
    have heq : s.getReg .x12 = s.getReg .x11 := by
      apply BitVec.eq_of_toNat_eq; have := hpre.bounds; rw [BitVec.toNat_sub] at hbytes; omega
    exact fin t₃ (hr₁.trans (hr₂.trans hr₃))
      (b8000e574_pc_taken h₃ (by rw [hx19, hx20, heq]))
      (fun r _ ↦ rfl) hkeep₃
      (ByteFrame.of_same hm31 _) (by simp [eListAt])
  have hQr' : heapStart ≤ Q.toNat ∧ Q.toNat + 24 * (L + n) ≤ heapNext s := by
    rcases hQr with h | h
    · omega
    · exact h
  replace hS := hS.resolve_left h0
  have hne : s.getReg .x12 ≠ s.getReg .x11 := by
    intro heq; rw [heq, BitVec.sub_self] at hbytes; simp at hbytes; omega
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000e580_spec
    (b8000e574_pc_not_taken h₃ (by rw [hx19, hx20]; exact hne)) (by
      rv_eval [k₃ .x8 (by decide), hreg₂ .x8 (by decide), b8000e520_x8 h₁]
      valid_access hpre.vec [hb])
  have k₄ := b8000e580_keeps h₄
  have hm₄ := b8000e580_mem_same h₄
  have hd₄ : t₄.getReg .x10 = Q + BitVec.ofNat 64 (24 * L) := by
    rw [b8000e580_x10 h₄, k₃ .x8 (by decide), hreg₂ .x8 (by decide), b8000e520_x8 h₁, hm31,
      v8, hlen₃]
    have hQ' : s.getMem (s.getReg .x10 + 8) = Q := by rw [hQ, vecPtr]
    rw [hQ']
    addr_omega [hQr', hL, hfit]
  have hs₄ : t₄.getReg .x11 = s.getReg .x11 := by
    rw [k₄ .x11 (by decide), b8000e574_x11 h₃, hreg₂ .x20 (by decide), b8000e520_x20 h₁]
  have hn₄ : (t₄.getReg .x12).toNat = 24 * n := by
    rw [b8000e580_x12 h₄, k₃ .x9 (by decide), hreg₂ .x9 (by decide), b8000e520_x9 h₁, hbytes]
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 48 := by
    rw [k₄ .x2 (by decide), k₃ .x2 (by decide), hreg₂ .x2 (by decide), hsp₁]
  have hpre₄ : MemcpyPre t₄ := {
    dst := by rw [hd₄, hn₄]; addr_omega [hQr', hfit]
    src := by rw [hs₄, hn₄]; exact hS
    apart := by rw [hd₄, hs₄, hn₄]; addr_omega [hsd]
    stack := ⟨by
        refine ValidMemRange.sub hst.valid ?_ ?_ ?_ <;> simp only [stackLo] <;> rw [hsp₄] <;>
          addr_omega [hb],
      by rw [hsp₄]; addr_omega [hb]⟩
    dstStack := by
      rw [hd₄, hn₄]; simp only [stackLo]; rw [hsp₄]; addr_omega [hQr', hfit, hab, hb]
    srcStack := by rw [hs₄, hn₄]; simp only [stackLo]; rw [hsp₄]; addr_omega [hss, hb] }
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hcpy⟩ | hdead⟩ := hC.call hr₄ (b8000e580_pc h₄) hpre₄
  swap
  · exact ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans hr₅)), Or.inr hdead⟩
  have hfr₅ := hcpy.frame
  rw [hd₄, hn₄] at hfr₅
  simp only [stackLo, hsp₄] at hfr₅
  have hby := hcpy.bytes
  rw [hd₄, hs₄, hn₄] at hby
  have hreg₅ (r : Reg) (hr : r ∈ [Reg.x2, .x8, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27]) : t₅.getReg r = t₃.getReg r := by
    rw [hpres₅ r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _)]
  refine fin t₅ (hr₁.trans (hr₂.trans (hr₃.trans hr₅)))
    (by rw [hpc₅, returnAddress_eq, b8000e580_x1 h₄]; decide)
    (fun r hr ↦ hreg₅ r (mem_of_mem hr _))
    (fun r hr ↦ (hreg₅ r (mem_of_mem hr _)).trans (hkeep₃ r hr))
    ((ByteFrame.of_same (fun a ↦ (hm₄ a).trans (hm31 a)) fun a ↦
        Within a (Q + BitVec.ofNat 64 (24 * L)) (24 * n) ∨ Within a (s.getReg .x2 - 64) 16).trans
      (hfr₅.mono fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (by addr_omega [ha, hb])) fun _ h ↦ h) ?_
  refine eListAt_eq_of_bytesAt ?_ (by addr_omega [hraw.1, hQr'])
    (hpre.srcAlign.resolve_left (by rw [← hn]; exact h0))
  rw [hby]
  refine ((ByteFrame.of_same (fun a ↦ (hm₄ a).trans (hm31 a)) fun _ ↦ False).bytesAt
    fun _ _ h ↦ h).trans (bf₁.bytesAt fun i hi hw ↦ ?_)
  addr_omega [hw, hi, hss, hb, hS]

end Rv64Verifier.Proofs.Multilinear.SpecExtend
