import Rv64Verifier.Proofs.Pcs.VsoGlueRootsHead

/-!
# `verify_stacked_opening`'s final level: the subspace roots' first layer

With `n ≠ 0`: `0x8000bc50` keeps the counts at `S - 888` and `S - 800`, `reserve(S - 160, n)` has
room enough; `0x8000bc68` keeps `n` at `S - 832` and the layer's pointer at `S - 784`; with `n ≠ 1`
`0x8000bc80` and the loop at `0x8000bcac` write `1 << i` for `i < n` at `L + 8 (i - 1)`, and
`0x8000bcc4` writes `1 << n` last and enters the rounds' loop at `0x8000bd1c` (`rootsFill`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The first layer, word by word. -/
theorem kListAt_layer0 {t : MachineState} {L : Word} {n : ℕ}
    (h : ∀ j < n, t.getMem (L + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 (2 ^ ((j + 1) % 64))) :
    kListAt t L n = layer0 n := by
  apply List.ext_getElem (by simp [kListAt_length, layer0])
  intro j h1 h2
  rw [kListAt_getElem, h j (by rw [kListAt_length] at h1; exact h1)]
  simp only [layer0, List.getElem_map, List.getElem_range', Nat.add_comm 1 j, Nat.one_mul]
  rw [Sym.shiftLeft_eq_mul, BitVec.one_mul]

theorem notAdd (f p : Word) (n : ℕ) (hp : p.toNat = f.toNat + n) (hn : 1 ≤ n) :
    (f ^^^ (0xffffffffffffffff : Word)) + (p + 0) = BitVec.ofNat 64 (n - 1) := by
  have e : (0xffffffffffffffff : Word) = BitVec.allOnes 64 := by decide
  rw [e, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  have := p.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, hp, show (0 : Word).toNat = 0 from rfl]
  omega

/-- The fill loop at `0x8000bcac`, `i` words of `n - 1` to go from `t₀`. -/
theorem fillLoop {t₀ : MachineState} {L : Word} {n : ℕ} (hL8 : L.toNat % 8 = 0)
    (hL1 : 0x20 ≤ L.toNat) (hL2 : L.toNat + 8 * n ≤ heapEnd) :
    ∀ m i t, n - i = m → t.pc = 0x8000bcac → 1 ≤ i → i < n →
      t.getReg .x10 = L + BitVec.ofNat 64 (8 * (i - 1)) → t.getReg .x11 = BitVec.ofNat 64 i →
      t.getReg .x13 = 1 → t.getReg .x14 = BitVec.ofNat 64 n →
      t.getReg .x2 = t₀.getReg .x2 → t.getReg .x9 = t₀.getReg .x9 → t.getReg .x21 = t₀.getReg .x21 →
      DFrame t₀ t (fun y ↦ Within y L (8 * (i - 1))) →
      (∀ j < i - 1, t.getMem (L + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 (2 ^ ((j + 1) % 64))) →
      ∃ t', Reaches Image.code t t' ∧ t'.pc = 0x8000bcc4 ∧ t'.getReg .x2 = t₀.getReg .x2 ∧
        t'.getReg .x9 = t₀.getReg .x9 ∧ t'.getReg .x21 = t₀.getReg .x21 ∧
        DFrame t₀ t' (fun y ↦ Within y L (8 * (n - 1))) ∧
        ∀ j < n - 1, t'.getMem (L + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 (2 ^ ((j + 1) % 64)) := by
  simp only [heapEnd] at hL2
  intro m
  induction m with
  | zero => intro i t hm _ _ hi; omega
  | succ m ih =>
    intro i t hm hpc hi1 hi hx10 hx11 hx13 hx14 hx2 hx9 hx21 hfr hmem
    obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bcac_spec hpc (by
      rv_eval [hx10]
      exact Region.valid (heap_region (a := L) (n := 8 * n) hL1 (by simp only [heapEnd]; omega) hL8)
        (by addr_omega [hi, hL2]) (by addr_omega [hi, hL2, hi1]) (by addr_omega [hi, hL2, hL8]))
    have k₁ := b8000bcac_keeps h₁
    have hw := h₁.mem_eq 0 (by decide) (a := t.getReg .x10) (by rv_eval []) rfl
    rv_eval [hx13, hx11] at hw
    rw [hx10] at hw
    have hw' : t₁.getMem (L + BitVec.ofNat 64 (8 * (i - 1))) = BitVec.ofNat 64 (2 ^ (i % 64)) := by
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (b := 2 ^ 64) (by omega)]
      exact BitVec.one_mul _
    have F₁ : DFrame t t₁ fun y ↦ Within y (L + BitVec.ofNat 64 (8 * (i - 1))) 8 := by
      have := DFrame.of_memFrame (b8000bcac_frame h₁ (by rw [hx10]; addr_omega [hi, hL2]))
      rw [hx10] at this; exact this
    have hfr₁ : DFrame t₀ t₁ (fun y ↦ Within y L (8 * i)) :=
      (hfr.mono fun y hy ↦ by simp only [Within] at hy ⊢; omega).trans F₁
        fun y hy ↦ by addr_omega [hy, hi, hL2, hi1]
    have hmem₁ : ∀ j < i, t₁.getMem (L + BitVec.ofNat 64 (8 * j)) =
        BitVec.ofNat 64 (2 ^ ((j + 1) % 64)) := by
      intro j hj
      by_cases hji : j = i - 1
      · subst hji; rw [hw', show i - 1 + 1 = i by omega]
      · rw [F₁ _ fun k hk hk' ↦ by addr_omega [hk, hk', hj, hji, hi, hL2], hmem j (by omega)]
    by_cases hlast : i + 1 = n
    · refine ⟨t₁, r₁, b8000bcac_pc_not_taken h₁ (by
          rw [hx14, hx11, ← hlast]; apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
          omega),
        by rw [k₁ .x2 (by decide), hx2], by rw [k₁ .x9 (by decide), hx9],
        by rw [k₁ .x21 (by decide), hx21], ?_, fun j hj ↦ hmem₁ j (by omega)⟩
      exact hfr₁.mono fun y hy ↦ by simp only [Within] at hy ⊢; omega
    · have pc₁ := b8000bcac_pc_taken h₁ (by
        rw [hx14, hx11]; intro he
        have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat] at this
        simp only [show (1 : Word).toNat = 1 from rfl] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega)
      obtain ⟨t', r', h'⟩ := ih (i + 1) t₁ (by omega) pc₁ (by omega) (by omega)
        (by rw [b8000bcac_x10 h₁, hx10, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
            omega)
        (by rw [b8000bcac_x11 h₁, hx11]; apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
            omega)
        (by rw [k₁ .x13 (by decide), hx13]) (by rw [k₁ .x14 (by decide), hx14])
        (by rw [k₁ .x2 (by decide), hx2]) (by rw [k₁ .x9 (by decide), hx9])
        (by rw [k₁ .x21 (by decide), hx21])
        (hfr₁.mono fun y hy ↦ by simp only [Within] at hy ⊢; omega)
        (fun j hj ↦ hmem₁ j (by omega))
      exact ⟨t', r₁.trans r', h'⟩

theorem ofNat_mul8 (k : ℕ) : BitVec.ofNat 64 k * 8 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
  omega

set_option maxHeartbeats 1000000 in
/-- **The first layer**: from `0x8000bc50`, `n ≠ 0`, to the rounds' loop with none done. -/
theorem rootsFill (hRF : ReserveFastSpec 0x8000d628) {s v w t : MachineState} {a R L : Word} {n : ℕ}
    (hpre : VsoPre s) (h : RA s v w t a n R L) (hn0 : n ≠ 0) :
    ∃ t', Reaches Image.code t t' ∧
      (Dead Image.code t' ∨ RH s v w t' a n 0 ([1], layer0 n) L) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have sp := h.pf.sp
  obtain ⟨hR8, hRw, hRt⟩ := h.Rb
  obtain ⟨hL8, hRL, hLt⟩ := h.Lb.resolve_left hn0
  have hht := h.pf.heap.hi
  simp only [heapEnd] at hht
  have hwL := h.pf.wt
  have hsw := h.pf.sw
  have hhs := hpre.heap.lo
  have hL1 : 0x20 ≤ L.toNat := by simp only [heapStart] at hhs; omega
  have hn64 : n < 2 ^ 64 := by omega
  have hnn : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  -- `0x8000bc50`
  have pc₀ : t.pc = 0x8000bc50 := by rw [h.pc]; simp only [hn0, ↓reduceIte]
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bc50_spec pc₀ (by
    rv_eval [sp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000bc50_keeps h₁
  have F₁ : DFrame t t₁ fun y ↦ Within y (s.getReg .x2 - 800) 8 ∨ Within y (s.getReg .x2 - 888) 8 :=
    (holds_dframe h₁).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000bc50, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (by addr_omega [hw, hb])
  obtain ⟨P₁, n₁⟩ := h.pf.stepS hpre F₁ (fun y hy ↦ by
    rcases hy with hy | hy
    · exact Or.inr (Or.inl (by addr_omega [hy, hb]))
    · exact Or.inl (by addr_omega [hy, hb])) (k₁ .x2 (by decide))
  have kS₁ (y : Word) (hy : ¬ Within y (s.getReg .x2 - 800) 8 ∧ ¬ Within y (s.getReg .x2 - 888) 8)
      (hy8 : y.toNat % 8 = 0) (hyb : y.toNat + 8 ≤ 2 ^ 64) : t₁.getMem y = t.getMem y :=
    F₁ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hy.1, hy.2, hy8, hyb, hb]
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 160 := by rw [b8000bc50_x10 h₁, sp]; rv_eval []
  -- `reserve(S - 160, n)`: room enough
  obtain ⟨t₂, r₂, ⟨hpc₂, hpres₂, hx₂, hm₂⟩ | hd₂⟩ := hRF.call (Reaches.refl t₁) (b8000bc50_pc h₁) ⟨by
      rw [x10₁]; valid_sub hst.valid [hb], by
      rw [x10₁, b8000bc50_x11 h₁, h.x26]; simp only [vecLen, vecCap]; rv_eval []
      rw [kS₁ (s.getReg .x2 - 144) ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
          (by addr_omega [hb]),
        kS₁ (s.getReg .x2 - 160) ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
          (by addr_omega [hb]), h.m144, h.m160]
      simp only [show (0 : Word).toNat = 0 from rfl, hnn, Nat.zero_add, Nat.le_refl]⟩
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd₂⟩
  have P₂ := P₁.same hpre hm₂ (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₂.sp
  -- `0x8000bc68`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000bc68_spec
    (by rw [hpc₂, returnAddress_eq, b8000bc50_x1 h₁]; decide) (by
      rv_eval [sp₂]; and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000bc68_keeps h₃
  have F₃ : DFrame t₂ t₃ fun y ↦ Within y (s.getReg .x2 - 832) 8 ∨ Within y (s.getReg .x2 - 784) 8 :=
    (holds_dframe h₃).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000bc68, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [sp₂] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (by addr_omega [hw, hb])
  obtain ⟨P₃, n₃⟩ := P₂.stepS hpre F₃ (fun y hy ↦ by
    rcases hy with hy | hy <;> exact Or.inr (Or.inl (by addr_omega [hy, hb]))) (k₃ .x2 (by decide))
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₃.sp
  have kS₃ (y : Word) (hy : ¬ Within y (s.getReg .x2 - 832) 8 ∧ ¬ Within y (s.getReg .x2 - 784) 8)
      (hy8 : y.toNat % 8 = 0) (hyb : y.toNat + 8 ≤ 2 ^ 64) : t₃.getMem y = t₂.getMem y :=
    F₃ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hy.1, hy.2, hy8, hyb, hb]
  have m784₃ : t₃.getMem (s.getReg .x2 - 784) = L := by
    have := b8000bc68_m_x2_256 h₃; rw [sp₂] at this; rv_eval [] at this
    rw [this, hm₂, kS₁ (s.getReg .x2 - 152) ⟨by addr_omega [hb], by addr_omega [hb]⟩
      (by addr_omega [hb]) (by addr_omega [hb])]; exact h.m152
  have x26₂ : t₂.getReg .x26 = BitVec.ofNat 64 n := by
    rw [hpres₂ .x26 (by decide), k₁ .x26 (by decide), h.x26]
  have m832₃ : t₃.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 n := by
    have := b8000bc68_m_x2_208 h₃; rw [sp₂, x26₂] at this; rv_eval [] at this; exact this
  have x9₃ : t₃.getReg .x9 = 0 := by
    rw [b8000bc68_x9 h₃, sp₂]; rv_eval [hm₂]
    rw [kS₁ (s.getReg .x2 - 144) ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
      (by addr_omega [hb])]
    exact h.m144
  have x21₃ : t₃.getReg .x21 = R := by
    rw [k₃ .x21 (by decide), hpres₂ .x21 (by decide), k₁ .x21 (by decide), h.x21]
  -- the layer's words below the last
  obtain ⟨te, re, pce, x2e, x9e, x21e, Fe, meme⟩ : ∃ te, Reaches Image.code t₃ te ∧
      te.pc = 0x8000bcc4 ∧ te.getReg .x2 = t₃.getReg .x2 ∧
      te.getReg .x9 = BitVec.ofNat 64 (n - 1) ∧ te.getReg .x21 = R ∧
      DFrame t₃ te (fun y ↦ Within y L (8 * (n - 1))) ∧
      ∀ j < n - 1, te.getMem (L + BitVec.ofNat 64 (8 * j)) = BitVec.ofNat 64 (2 ^ ((j + 1) % 64)) := by
    by_cases h1 : n = 1
    · subst h1
      exact ⟨t₃, Reaches.refl _, b8000bc68_pc_taken h₃ (by rw [x26₂]; rfl), rfl,
        by rw [x9₃]; rfl, x21₃, DFrame.refl _ _, fun j hj ↦ absurd hj (by omega)⟩
    have pc₃ := b8000bc68_pc_not_taken h₃ (by
      rw [x26₂]; intro he; have := congrArg BitVec.toNat he
      rw [hnn] at this; exact h1 this)
    obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000bc80_spec pc₃ (by
      rv_eval [sp₃]; and_intros <;> valid_access hst.valid [hb])
    have hm₄ := b8000bc80_mem_same h₄
    have k₄ := b8000bc80_keeps h₄
    have x9₄ : t₄.getReg .x9 = BitVec.ofNat 64 (n - 1) := by
      rw [b8000bc80_x9 h₄, sp₃, x9₃]
      rw [show s.getReg .x2 - BitVec.ofNat 64 1040 + 232 = s.getReg .x2 - 808 by addr_omega [hb],
        show s.getReg .x2 - BitVec.ofNat 64 1040 + 224 = s.getReg .x2 - 816 by addr_omega [hb],
        kS₃ (s.getReg .x2 - 808) ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
          (by addr_omega [hb]),
        kS₃ (s.getReg .x2 - 816) ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
          (by addr_omega [hb]),
        hm₂ (s.getReg .x2 - 808), hm₂ (s.getReg .x2 - 816),
        kS₁ (s.getReg .x2 - 808) ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
          (by addr_omega [hb]),
        kS₁ (s.getReg .x2 - 816) ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
          (by addr_omega [hb]), h.m808, h.m816]
      exact notAdd _ _ n h.hn (by omega)
    obtain ⟨te, re, pce, x2e, x9e, x21e, Fe, meme⟩ := fillLoop (t₀ := t₄) (n := n) hL8 hL1
      (by simp only [heapEnd]; omega) (n - 1) 1 t₄ rfl (b8000bc80_pc h₄) (Nat.le_refl _) (by omega)
      (by rw [b8000bc80_x10 h₄, sp₃, x9₃]; rv_eval [m784₃]; simp) (b8000bc80_x11 h₄)
      (b8000bc80_x13 h₄)
      (by rw [b8000bc80_x14 h₄, sp₃]; rv_eval [m832₃]) rfl rfl rfl (DFrame.refl _ _)
      (fun j hj ↦ absurd hj (by omega))
    exact ⟨te, r₄.trans re, pce, by rw [x2e, k₄ .x2 (by decide)], by rw [x9e, x9₄],
      by rw [x21e, k₄ .x21 (by decide), x21₃], DFrame.trans (DFrame.of_same hm₄ _) Fe fun _ h ↦ h,
      meme⟩
  -- the rest of the frame, kept
  have nx₃ : t₃.getMem nextAddr = t.getMem nextAddr := by rw [n₃, hm₂, n₁]
  have ne : te.getMem nextAddr = t₃.getMem nextAddr :=
    Fe _ fun i hi hw ↦ by addr_omega [hw, hi, hLt, hht]
  have hne : heapNext te = heapNext t := by simp only [heapNext, ne, nx₃]
  have Pe := P₃.step hpre Fe (fun y hy ↦ glw_heap (by simp only [Within] at hy; omega)
      (by have : (te.getMem nextAddr).toNat = heapNext te := rfl
          simp only [Within] at hy; omega))
    ⟨by rw [hne]; exact h.pf.heap.lo, by rw [hne]; exact h.pf.heap.hi⟩
    (by simp only [heapNext, ne]; exact Nat.le_refl _) x2e
  have spe : te.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := Pe.sp
  have kSe (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      te.getMem y = t₃.getMem y :=
    Fe y fun i hi hw ↦ by addr_omega [hw, hi, hy, hb, hLt, hht, hab]
  have m784e : te.getMem (s.getReg .x2 - 784) = L := by
    rw [kSe _ ⟨by addr_omega [hb], by addr_omega [hb]⟩]; exact m784₃
  have m832e : te.getMem (s.getReg .x2 - 832) = BitVec.ofNat 64 n := by
    rw [kSe _ ⟨by addr_omega [hb], by addr_omega [hb]⟩]; exact m832₃
  -- `0x8000bcc4`: the last word, `1 << n`
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b8000bcc4_spec pce (by
    rv_eval [spe, x9e, m784e]
    rw [ofNat_mul8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid (heap_region (a := L) (n := 8 * n) hL1 (by simp only [heapEnd]; omega) hL8)
          (by addr_omega [hLt, hht]) (by addr_omega [hLt, hht, hn0]) (by addr_omega [hLt, hht, hL8])
      | addr_omega [hLt, hht, hab, hb])
  have k₅ := b8000bcc4_keeps h₅
  have F₅ : DFrame te t₅ fun y ↦ Within y (s.getReg .x2 - 840) 8 ∨
      Within y (L + BitVec.ofNat 64 (8 * (n - 1))) 8 :=
    (holds_dframe h₅).mono fun y ⟨k, hk, hw⟩ ↦ by
      simp only [b8000bcc4, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> rv_eval [spe, x9e, m784e] at hw
      · exact Or.inl (by addr_omega [hw, hb])
      · rw [ofNat_mul8] at hw; exact Or.inr hw
  have n₅ : t₅.getMem nextAddr = te.getMem nextAddr := F₅ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · addr_omega [hw, hi, hLt, hht, hn0]
  have hn₅ : heapNext t₅ = heapNext t := by simp only [heapNext, n₅]; exact hne
  have P₅ := Pe.step hpre F₅ (fun y hy ↦ by
      rcases hy with hy | hy
      · exact Or.inr (Or.inl (by addr_omega [hy, hb]))
      · exact glw_heap (by addr_omega [hy, hRL, hRw, hLt, hht, hn0])
          (by have : (t₅.getMem nextAddr).toNat = heapNext t₅ := rfl
              addr_omega [hy, this, hn₅, hLt, hht, hn0]))
    ⟨by rw [hn₅]; exact h.pf.heap.lo, by rw [hn₅]; exact h.pf.heap.hi⟩
    (by rw [hn₅, hne]) (k₅ .x2 (by decide))
  have w0 := h₅.mem_eq 0 (by decide) rfl rfl
  have w1 := h₅.mem_eq 1 (by decide) rfl rfl
  rv_eval [spe, x9e, m784e, m832e] at w0 w1
  rw [ofNat_mul8, hnn] at w1
  have w1' : t₅.getMem (L + BitVec.ofNat 64 (8 * (n - 1))) = BitVec.ofNat 64 (2 ^ (n % 64)) := by
    rw [w1]; exact BitVec.one_mul _
  have kS5 (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 840).toNat ∨
      (s.getReg .x2 - 832).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₅.getMem y = t₃.getMem y := by
    rw [F₅ y fun i hi hw ↦ by
      rcases hw with hw | hw <;> rcases hy with hy | hy
      all_goals first | addr_omega [hw, hi, hy, hb] | addr_omega [hw, hi, hy, hb, hLt, hht, hab, hn0]]
    exact kSe _ (by rcases hy with hy | hy <;> exact ⟨by addr_omega [hy, hb], by addr_omega [hy, hb]⟩)
  have kS3 (y : Word) (hy8 : y.toNat % 8 = 0)
      (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 888).toNat ∨
      (s.getReg .x2 - 880).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 832).toNat ∨
      (s.getReg .x2 - 824).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 800).toNat ∨
      (s.getReg .x2 - 792).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 784).toNat ∨
      (s.getReg .x2 - 776).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₃.getMem y = t.getMem y := by
    have hyb : y.toNat + 8 ≤ 2 ^ 64 := by
      rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hy, hb]
    rw [kS₃ y ⟨fun hw ↦ by rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hy, hb, hy8],
        fun hw ↦ by rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hy, hb, hy8]⟩ hy8 hyb,
      hm₂, kS₁ y ⟨fun hw ↦ by rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hy, hb, hy8],
        fun hw ↦ by rcases hy with hy | hy | hy | hy | hy <;> addr_omega [hw, hy, hb, hy8]⟩ hy8 hyb]
  have m120 : t₅.getMem (s.getReg .x2 - 120) = R := by
    rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
      kS3 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩))))]
    exact h.m120
  have m128 : t₅.getMem (s.getReg .x2 - 128) = 1 := by
    rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
      kS3 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩))))]
    exact h.m128
  have m112 : t₅.getMem (s.getReg .x2 - 112) = 1 := by
    rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
      kS3 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩))))]
    exact h.m112
  have r0 : t₅.getMem R = 1 := by
    rw [F₅ R fun i hi hw ↦ by
        rcases hw with hw | hw
        · addr_omega [hw, hi, hb, hRt, hht, hab]
        · addr_omega [hw, hi, hRL, hLt, hht, hn0],
      Fe R fun i hi hw ↦ by addr_omega [hw, hi, hRL], kS₃ R ⟨fun hw ↦ by addr_omega [hw, hRt, hht, hab, hb],
        fun hw ↦ by addr_omega [hw, hRt, hht, hab, hb]⟩ hR8 (by omega), hm₂,
      kS₁ R ⟨fun hw ↦ by addr_omega [hw, hRt, hht, hab, hb], fun hw ↦ by addr_omega [hw, hRt, hht, hab, hb]⟩
        hR8 (by omega)]
    exact h.r0
  have x21₅ : t₅.getReg .x21 = R := by rw [k₅ .x21 (by decide), x21e]
  refine ⟨t₅, r₁.trans (r₂.trans (r₃.trans (re.trans r₅))), Or.inr {
    pf := P₅
    sl := {
      m856 := by
        rw [kS5 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
          kS3 _ (by addr_omega [hb]) (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))]
        exact h.m856
      m824 := by
        rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
          kS3 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))]
        exact h.m824
      m816 := by
        rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
          kS3 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))]
        exact h.m816
      m808 := by
        rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
          kS3 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))]
        exact h.m808
      m800 := by
        rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩),
          kS₃ _ ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb]) (by addr_omega [hb]), hm₂]
        have := b8000bc50_m_x2_240 h₁; rw [sp, h.x19] at this; rv_eval [] at this; exact this
      m888 := by
        rw [kS5 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩),
          kS₃ _ ⟨by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb]) (by addr_omega [hb]), hm₂]
        have := b8000bc50_m_x2_152 h₁; rw [sp, h.x23] at this; rv_eval [] at this; exact this
      m784 := by rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact m784₃
      m840 := w0
      m832 := by rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact m832₃
      keep := fun y hy ↦ by
        rw [← h.keep y hy]
        simp only [GK] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | (rw [kS5 _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]
             exact kS3 _ (by addr_omega [hb]) (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
          | (rw [kS5 _ (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)]
             exact kS3 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inr (Or.inr
               ⟨by addr_omega [hb], by addr_omega [hb]⟩))))) }
    pc := b8000bcc4_pc h₅
    klt := Nat.pos_of_ne_zero hn0
    loop := by rw [Nat.sub_zero]; exact roots_eq n
    len1 := rfl
    len2 := by simp [layer0]
    x9 := by
      rw [b8000bcc4_x9 h₅, x9e]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]; omega
    x13 := b8000bcc4_x13 h₅
    x19 := by
      rw [b8000bcc4_x19 h₅, x9e, ofNat_mul8]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]; omega
    x20 := b8000bcc4_x20 h₅
    x21 := by rw [x21₅, m120]
    Lb := ⟨hL8, by omega, by rw [hn₅]; omega⟩
    lay := by
      rw [Nat.sub_zero]
      refine kListAt_layer0 fun j hj ↦ ?_
      by_cases hjl : j = n - 1
      · subst hjl; rw [w1', show n - 1 + 1 = n by omega]
      · rw [F₅ _ fun i hi hw ↦ by
          rcases hw with hw | hw
          · addr_omega [hw, hi, hb, hLt, hht, hab, hj]
          · addr_omega [hw, hi, hLt, hht, hj, hjl]]
        exact meme j (by omega)
    rcap := by rw [m128]; decide
    rlen := m112
    Rb := by
      rw [m120, m128]
      exact ⟨hR8, hRw, by simp only [show (1 : Word).toNat = 1 from rfl]; rw [hn₅]; omega⟩
    RL := by rw [m120, m128]; exact Or.inl (by simp only [show (1 : Word).toNat = 1 from rfl]; omega)
    rts := by rw [m120]; exact kListAt_one _ _ r0 }⟩

end Rv64Verifier.Proofs.Pcs.Vso
