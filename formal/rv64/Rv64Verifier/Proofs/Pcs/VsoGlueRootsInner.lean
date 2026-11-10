import Rv64Verifier.Proofs.Pcs.VsoGlueRootsFill

/-!
# `verify_stacked_opening`'s final level: a round's layer update

The loop at `0x8000bd44` runs over the layer's `m` words at `L`, the cursor in `s5`, the end in
`s2`: `K::square` of the word, `base_mul(root, word)`, and `0x8000bd6c` stores their `xor`, the
word's `sqAdd root` (`innerLoop`), until `0x8000bd7c`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The registers the layer's loop keeps. -/
def innerRegs : List Reg := [.x2, .x9, .x18, .x19, .x20, .x22, .x23, .x26, .x27]

theorem innerRegs_saved {r : Reg} (h : r ∈ innerRegs) : r ∈ calleeSaved := by
  simp only [innerRegs, calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **The layer's update**: from word `i`, every word `x` from there replaced by `sqAdd root x`. -/
theorem innerLoop (hS : KSquareSpec) (hBM : BaseMulSpec) {s v w t₀ : MachineState} {L r : Word}
    {m : ℕ} {lay : List K} (hpre : VsoPre s) (hL8 : L.toNat % 8 = 0) (hL1 : 0x20 ≤ L.toNat)
    (hLw : heapNext w ≤ L.toNat) (hL2 : L.toNat + 8 * m ≤ heapNext t₀)
    (hlay : kListAt t₀ L m = lay) :
    ∀ c i t, m - i = c → i < m → RPF s v w t → t.pc = 0x8000bd44 →
      t.getReg .x21 = L + BitVec.ofNat 64 (8 * i) → t.getReg .x18 = L + BitVec.ofNat 64 (8 * m) →
      t.getReg .x23 = r → (∀ q ∈ innerRegs, t.getReg q = t₀.getReg q) →
      t.getMem nextAddr = t₀.getMem nextAddr →
      DFrame t₀ t (fun y ↦ Within y L (8 * m) ∨ Within y (s.getReg .x2 - 1152) 112) →
      kListAt t L i = (lay.take i).map (sqAdd (kOf r)) →
      (∀ j, i ≤ j → j < m → t.getMem (L + BitVec.ofNat 64 (8 * j)) =
        t₀.getMem (L + BitVec.ofNat 64 (8 * j))) →
      ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨ (t'.pc = 0x8000bd7c ∧ RPF s v w t' ∧
        (∀ q ∈ innerRegs, t'.getReg q = t₀.getReg q) ∧ t'.getMem nextAddr = t₀.getMem nextAddr ∧
        DFrame t₀ t' (fun y ↦ Within y L (8 * m) ∨ Within y (s.getReg .x2 - 1152) 112) ∧
        kListAt t' L m = lay.map (sqAdd (kOf r)))) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have hro := hst.rodata
  rw [stackLo_vso] at hro
  have hlen : lay.length = m := by rw [← hlay, kListAt_length]
  intro c
  induction c with
  | zero => intro i t hc hi; omega
  | succ c ih =>
    intro i t hc hi P hpc hx21 hx18 hx23 hreg hnx hfr hdone hrest
    have sp := P.sp
    have hht := P.heap.hi
    simp only [heapEnd] at hht
    have hn : heapNext t = heapNext t₀ := by simp only [heapNext, hnx]
    have hLe : L.toNat + 8 * m ≤ 2013265920 := by rw [← hn] at hL2; omega
    have hRL : Region L (8 * m) := heap_region hL1 (by simp only [heapEnd]; omega) hL8
    -- `0x8000bd44`, `K::square(word)`
    obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bd44_spec hpc (by
      rv_eval [hx21]
      exact Region.valid hRL (by addr_omega [hi, hLe]) (by addr_omega [hi, hLe])
        (by addr_omega [hi, hLe, hL8]))
    have hm₁ := b8000bd44_mem_same h₁
    have k₁ := b8000bd44_keeps h₁
    have hv : t₁.getReg .x24 = t₀.getMem (L + BitVec.ofNat 64 (8 * i)) := by
      rw [b8000bd44_x24 h₁, hx21, hrest i (Nat.le_refl _) hi]
    obtain ⟨t₂, r₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd₂⟩ := hS.call (Reaches.refl t₁) (b8000bd44_pc h₁) trivial
    swap
    · exact ⟨t₂, r₁.trans r₂, Or.inl hd₂⟩
    have hsq := hpost₂.value
    rw [b8000bd44_x10 h₁, hx21, hrest i (Nat.le_refl _) hi] at hsq
    -- `0x8000bd58`, `base_mul(root, word)`
    obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000bd58_spec
      (by rw [hpc₂, returnAddress_eq, b8000bd44_x1 h₁]; decide) trivial
    have hm₃ := b8000bd58_mem_same h₃
    have k₃ := b8000bd58_keeps h₃
    have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := by
      rw [k₃ .x2 (by decide), hpres₂ .x2 (by decide), k₁ .x2 (by decide), sp]
    have hsl : stackLo t₃ baseMulStack = s.getReg .x2 - 1152 := by
      simp only [stackLo, sp₃, baseMulStack]; rv_eval []
    have hmem₃ (y : Word) : t₃.getMem y = t.getMem y := by rw [hm₃, hpost₂.mem, hm₁]
    have P₃ : RPF s v w t₃ :=
      (P.same hpre hm₁ (k₁ .x2 (by decide))).same hpre (fun y ↦ by rw [hpost₂.mem])
        (hpres₂ .x2 (by decide)) |>.same hpre hm₃ (k₃ .x2 (by decide))
    obtain ⟨t₄, r₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hd₄⟩ := hBM.call (Reaches.refl t₃) (b8000bd58_pc h₃)
      ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [sp₃]; addr_omega [hb]⟩,
        poolOk_of_rodata (InvR.rodata' hpre P₃.inv) (by rw [hsl]; simp only [vsoStack, basisStack,
          ringEvalStack, mulStack, roundPolyStack, nextScalarsStack, shuntNextStack, nextScalarStack,
          absorbStack, duplexStack, keccakFStack, memStack] at hro; addr_omega [hro, hb])⟩
    swap
    · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inl hd₄⟩
    have hbm := hpost₄.value
    rw [b8000bd58_x10 h₃, b8000bd58_x11 h₃, hpres₂ .x23 (by decide),
      k₁ .x23 (by decide), hx23, hpres₂ .x24 (by decide), hv] at hbm
    have F₄ : DFrame t₃ t₄ fun y ↦ Within y (s.getReg .x2 - 1152) 112 := by
      have := DFrame.of_memFrame hpost₄.frame; rw [hsl] at this; exact this
    have P₄ := P₃.stepS hpre F₄ (fun y hy ↦ Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hy, hb])))))
      (hpres₄ .x2 (by decide))
    have sp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₄.1.sp
    -- `0x8000bd6c`, the word's update
    have x21₄ : t₄.getReg .x21 = L + BitVec.ofNat 64 (8 * i) := by
      rw [hpres₄ .x21 (by decide), k₃ .x21 (by decide), hpres₂ .x21 (by decide), k₁ .x21 (by decide), hx21]
    obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b8000bd6c_spec
      (by rw [hpc₄, returnAddress_eq, b8000bd58_x1 h₃]; decide) (by
        rv_eval [x21₄]
        exact Region.valid hRL (by addr_omega [hi, hLe]) (by addr_omega [hi, hLe])
          (by addr_omega [hi, hLe, hL8]))
    have k₅ := b8000bd6c_keeps h₅
    have F₅ : DFrame t₄ t₅ fun y ↦ Within y (L + BitVec.ofNat 64 (8 * i)) 8 := by
      have := DFrame.of_memFrame (b8000bd6c_frame h₅ (by rw [x21₄]; addr_omega [hi, hLe]))
      rw [x21₄] at this; exact this
    have hw₅ := b8000bd6c_m_x21_0 h₅
    rw [x21₄, hbm, hpres₄ .x25 (by decide), b8000bd58_x25 h₃, hsq] at hw₅
    have hnx₅ : t₅.getMem nextAddr = t₀.getMem nextAddr := by
      rw [F₅ _ fun j hj hw ↦ by addr_omega [hw, hj, hi, hLe], P₄.2, hmem₃, hnx]
    have hn₅ : heapNext t₅ = heapNext t := by simp only [heapNext, hnx₅, hnx]
    have P₅ := P₄.1.step hpre F₅ (fun y hy ↦ glw_heap (by addr_omega [hy, hi, hL2, hLw, hht])
        (by have : (t₅.getMem nextAddr).toNat = heapNext t₅ := rfl
            addr_omega [hy, hi, hLe, hL2, this, hn₅, hn]))
      ⟨by rw [hn₅]; exact P.heap.lo, by rw [hn₅]; exact P.heap.hi⟩
      (by simp only [heapNext, hnx₅, P₄.2, hmem₃, hnx]; exact Nat.le_refl _) (k₅ .x2 (by decide))
    have hreg₅ : ∀ q ∈ innerRegs, t₅.getReg q = t₀.getReg q := by
      intro q hq
      have hs := innerRegs_saved hq
      rw [← hreg q hq]
      simp only [innerRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [k₅ _ (by decide), hpres₄ _ hs, k₃ _ (by decide), hpres₂ _ hs, k₁ _ (by decide)]
    have hfr₅ : DFrame t₀ t₅ (fun y ↦ Within y L (8 * m) ∨ Within y (s.getReg .x2 - 1152) 112) :=
      ((hfr.trans (DFrame.of_same hmem₃ fun _ ↦ False) fun _ h ↦ h.elim).trans F₄ fun y hy ↦ Or.inr hy).trans F₅
        fun y hy ↦ Or.inl (by addr_omega [hy, hi, hLe])
    have hmem (j : ℕ) (hj : j < m) (hji : j ≠ i) :
        t₅.getMem (L + BitVec.ofNat 64 (8 * j)) = t.getMem (L + BitVec.ofNat 64 (8 * j)) := by
      rw [F₅ _ fun k hk hw ↦ by addr_omega [hw, hk, hj, hji, hi, hLe], F₄ _ fun k hk hw ↦ by
        addr_omega [hw, hk, hj, hLe, hab, hb], hmem₃]
    have hli : i < lay.length := by omega
    have hget : lay[i]'hli = kOf (t₀.getMem (L + BitVec.ofNat 64 (8 * i))) := by
      rw [List.getElem_of_eq hlay.symm hli, kListAt_getElem]
    have hdone₅ : kListAt t₅ L (i + 1) = (lay.take (i + 1)).map (sqAdd (kOf r)) := by
      rw [kListAt_succ, List.take_add_one, List.getElem?_eq_getElem hli, Option.toList_some,
        List.map_append, List.map_singleton, ← hdone,
        kListAt_congr fun j hj ↦ hmem j (by omega) (by omega), hw₅, sqAdd_word, hget]
    have x8₄ : t₄.getReg .x8 = L + BitVec.ofNat 64 (8 * (i + 1)) := by
      rw [hpres₄ .x8 (by decide), k₃ .x8 (by decide), hpres₂ .x8 (by decide), b8000bd44_x8 h₁, hx21,
        BitVec.add_assoc]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]; omega
    have x18₄ : t₄.getReg .x18 = L + BitVec.ofNat 64 (8 * m) := by
      rw [hpres₄ .x18 (by decide), k₃ .x18 (by decide), hpres₂ .x18 (by decide),
        k₁ .x18 (by decide), hx18]
    by_cases hlast : i + 1 = m
    · refine ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inr ⟨?_, P₅, hreg₅, hnx₅, hfr₅, ?_⟩⟩
      · exact b8000bd6c_pc_not_taken h₅ (by rw [x8₄, x18₄, hlast])
      · have e : lay.take (i + 1) = lay := List.take_of_length_le (by omega)
        rw [e] at hdone₅; rw [← hlast]; exact hdone₅
    · have pc₅ := b8000bd6c_pc_taken h₅ (by
        rw [x8₄, x18₄]; intro he
        addr_omega [he, hLe, hi, hlast])
      obtain ⟨t', r', h'⟩ := ih (i + 1) t₅ (by omega) (by omega) P₅ pc₅
        (by rw [b8000bd6c_x21 h₅, x8₄]) (by rw [k₅ .x18 (by decide), x18₄])
        (by rw [hreg₅ .x23 (by simp [innerRegs]), ← hreg .x23 (by simp [innerRegs]), hx23])
        hreg₅ hnx₅ hfr₅ hdone₅
        (fun j hj1 hj2 ↦ by rw [hmem j hj2 (by omega)]; exact hrest j (by omega) hj2)
      exact ⟨t', r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r')))), h'⟩

end Rv64Verifier.Proofs.Pcs.Vso
