import Rv64Verifier.Proofs.Pcs.VsoGlueRootsInner

/-!
# `verify_stacked_opening`'s final level: a round's root and layer

From `RH` at `0x8000bd1c`: a trap on an empty layer; `0x8000bd20` takes the last root into `s7`,
the layer's end into `s2`, and counts the round at `S - 792`; the layer's update (`innerLoop`);
`0x8000bd7c` takes the layer's first word, the round's root, into `s7` and `memmove`s the rest one
word down (`layer.remove(0)`), returning at `0x8000bd94` (`RM`, `rootsMove`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol Rv64Verifier.FieldContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The layer `st.2` updated by the last root. -/
def layM (st : List K × List K) : List K := st.2.map (sqAdd (st.1.getLastD 0))

/-- One step, `headD` and `tail` of the updated layer. -/
theorem rootsStep' {st : List K × List K} (hl : st.2 ≠ []) :
    Model.Pcs.subspaceRootsStep st = some (st.1 ++ [(layM st).headD 0], (layM st).tail) := by
  obtain ⟨roots, layer⟩ := st
  rw [rootsStep hl]
  cases layer with
  | nil => exact absurd rfl hl
  | cons x xs => rfl

theorem getLastD_kList (t : MachineState) (R : Word) (k : ℕ) :
    (kListAt t R (k + 1)).getLastD 0 = kOf (t.getMem (R + BitVec.ofNat 64 (8 * k))) := by
  rw [kListAt_succ]; simp

theorem word_last (R : Word) (k : ℕ) :
    R + BitVec.ofNat 64 (k + 1) * 8 - 8 = R + BitVec.ofNat 64 (8 * k) := by
  rw [ofNat_mul8, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

/-- At `0x8000bd94`, round `k`'s root `(layM st).headD 0` in `s7`, the rest of the layer moved down. -/
structure RM (s v w t u : MachineState) (a : Word) (n k : ℕ) (st : List K × List K) (L : Word) :
    Prop where
  h : RH s v w t a n k st L
  pf : RPF s v w u
  sl : RSL s w u a n L
  pc : u.pc = 0x8000bd94
  x9 : u.getReg .x9 = BitVec.ofNat 64 (n - k)
  x19 : u.getReg .x19 = BitVec.ofNat 64 (8 * (n - k))
  x20 : u.getReg .x20 = BitVec.ofNat 64 (k + 1)
  x23 : kOf (u.getReg .x23) = (layM st).headD 0
  x26 : u.getReg .x26 = t.getMem (s.getReg .x2 - 120)
  x27 : u.getReg .x27 = BitVec.ofNat 64 (k + 1) * 8
  m792 : u.getMem (s.getReg .x2 - 792) = BitVec.ofNat 64 (k + 1)
  m128 : u.getMem (s.getReg .x2 - 128) = t.getMem (s.getReg .x2 - 128)
  m120 : u.getMem (s.getReg .x2 - 120) = t.getMem (s.getReg .x2 - 120)
  m112 : u.getMem (s.getReg .x2 - 112) = t.getMem (s.getReg .x2 - 112)
  nx : u.getMem nextAddr = t.getMem nextAddr
  rts : kListAt u (t.getMem (s.getReg .x2 - 120)) (k + 1) = st.1
  lay : kListAt u L (n - k - 1) = (layM st).tail

theorem kListAt_headD (t : MachineState) (p : Word) {m : ℕ} (hm : 0 < m) :
    (kListAt t p m).headD 0 = kOf (t.getMem p) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp [kListAt, List.range_succ_eq_map]

set_option maxHeartbeats 1000000 in
/-- **A round's root and layer**: `0x8000bd1c` to `0x8000bd94`. -/
theorem rootsMove (hS : KSquareSpec) (hBM : BaseMulSpec) (hMM : MemmoveSpec 0x800126ec)
    {s v w t : MachineState} {a L : Word} {n k : ℕ} {st : List K × List K}
    (hpre : VsoPre s) (h : RH s v w t a n k st L) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨ RM s v w t u a n k st L) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have sp := h.pf.sp
  obtain ⟨hL8, hLw, hLt⟩ := h.Lb
  obtain ⟨hR8, hRw, hRt⟩ := h.Rb
  have hht := h.pf.heap.hi
  simp only [heapEnd] at hht
  have hsw := h.pf.sw
  have hhs := hpre.heap.lo
  have hk := h.klt
  have hrc := h.rcap
  generalize hRdef : t.getMem (s.getReg .x2 - 120) = R at hR8 hRw hRt h
  generalize hCdef : t.getMem (s.getReg .x2 - 128) = C at hrc hRt
  have hL1 : 0x20 ≤ L.toNat := by simp only [heapStart] at hhs; omega
  have hRL : Region R (8 * C.toNat) := heap_region (by simp only [heapStart] at hhs; omega)
    (by simp only [heapEnd]; omega) hR8
  -- `0x8000bd1c`: a trap on an empty layer
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bd1c_spec h.pc trivial
  have hm₁ := b8000bd1c_mem_same h₁
  have k₁ := b8000bd1c_keeps h₁
  have pc₁ := b8000bd1c_pc_not_taken h₁ (by
    rw [h.x9]; intro he; have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat] at this; simp only [show (0 : Word).toNat = 0 from rfl] at this; omega)
  have P₁ := h.pf.same hpre hm₁ (k₁ .x2 (by decide))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₁.sp
  have m784 : t₁.getMem (s.getReg .x2 - 784) = L := by rw [hm₁]; exact h.sl.m784
  -- `0x8000bd20`
  have x21₁ : t₁.getReg .x21 = R := by rw [k₁ .x21 (by decide), h.x21, hRdef]
  have x20₁ : t₁.getReg .x20 = BitVec.ofNat 64 (k + 1) := by rw [k₁ .x20 (by decide), h.x20]
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000bd20_spec pc₁ (by
    rv_eval [sp₁, x21₁, x20₁]
    rw [word_last]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hRL (by addr_omega [hRt, hht, hrc]) (by addr_omega [hRt, hht, hrc])
          (by addr_omega [hRt, hht, hR8, hrc]))
  have k₂ := b8000bd20_keeps h₂
  have F₂ : DFrame t₁ t₂ fun y ↦ Within y (s.getReg .x2 - 792) 8 := by
    have := DFrame.of_memFrame (b8000bd20_frame h₂ (by rw [sp₁]; addr_omega [hb]))
    rw [sp₁] at this; exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  obtain ⟨P₂, n₂⟩ := P₁.stepS hpre F₂ (fun y hy ↦ Or.inr (Or.inl (by addr_omega [hy, hb])))
    (k₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₂.sp
  have hn₂ : heapNext t₂ = heapNext t := by simp only [heapNext, n₂, hm₁]
  have x23₂ : t₂.getReg .x23 = t.getMem (R + BitVec.ofNat 64 (8 * k)) := by
    rw [b8000bd20_x23 h₂, x21₁, x20₁, word_last, hm₁]
  have kL₂ : kListAt t₂ L (n - k) = st.2 := by
    rw [← h.lay, DFrame.kList F₂ (by omega) fun y hy hw ↦ by addr_omega [hy, hw, hb, hLt, hht, hab]]
    exact kListAt_congr fun i _ ↦ hm₁ _
  have hlast : st.1.getLastD 0 = kOf (t.getMem (R + BitVec.ofNat 64 (8 * k))) := by
    rw [← h.rts, hRdef, getLastD_kList]
  -- the layer's update
  obtain ⟨t₃, r₃, hv₃⟩ := innerLoop (t₀ := t₂) (r := t.getMem (R + BitVec.ofNat 64 (8 * k)))
    hS hBM hpre hL8 hL1 hLw (by rw [hn₂]; omega) kL₂ (n - k) 0 t₂ (by omega) (by omega) P₂
    (b8000bd20_pc h₂) (by
      rw [b8000bd20_x21 h₂, sp₁, show s.getReg .x2 - BitVec.ofNat 64 1040 + 256 = s.getReg .x2 - 784 by
        addr_omega [hb], m784]; simp)
    (by rw [b8000bd20_x18 h₂, sp₁, k₁ .x19 (by decide), h.x19]; rv_eval [m784])
    x23₂ (fun _ _ ↦ rfl) rfl (DFrame.refl _ _) (by simp [kListAt])
    (fun _ _ _ ↦ rfl)
  rcases hv₃ with hd₃ | ⟨pc₃, P₃, reg₃, nx₃, F₃, lay₃⟩
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl hd₃⟩
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₃.sp
  have kS₃ (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₃.getMem y = t₂.getMem y :=
    F₃ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hy, hb, hLt, hht, hab]
  have m784₃ : t₃.getMem (s.getReg .x2 - 784) = L := by
    rw [kS₃ _ ⟨by addr_omega [hb], by addr_omega [hb]⟩, F₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb]]
    exact m784
  -- `0x8000bd7c`: the round's root, `memmove`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000bd7c_spec pc₃ (by
    rv_eval [sp₃, m784₃]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid (heap_region (a := L) (n := 8 * (n - k)) hL1
          (by simp only [heapEnd]; omega) hL8) (by addr_omega [hLt, hht]) (by addr_omega [hLt, hht, hk])
          (by addr_omega [hLt, hht, hL8]))
  have hm₄ := b8000bd7c_mem_same h₄
  have k₄ := b8000bd7c_keeps h₄
  have P₄ := P₃.same hpre hm₄ (k₄ .x2 (by decide))
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₄.sp
  have x10₄ : t₄.getReg .x10 = L := by rw [b8000bd7c_x10 h₄, sp₃]; rv_eval [m784₃]
  have x11₄ : t₄.getReg .x11 = L + 8 := by
    rw [b8000bd7c_x11 h₄, sp₃]; rv_eval []
    rw [kS₃ _ ⟨by addr_omega [hb], by addr_omega [hb]⟩, F₂ _ fun i hi hw ↦ by addr_omega [hw, hi, hb], hm₁]
    exact h.sl.m840
  have x22₃ : t₃.getReg .x22 = BitVec.ofNat 64 (8 * (n - k)) := by
    rw [reg₃ .x22 (by simp [innerRegs]), b8000bd20_x22 h₂, k₁ .x9 (by decide), h.x9, ofNat_mul8]
  have hN : (t₄.getReg .x12).toNat = 8 * (n - k) - 8 := by
    rw [b8000bd7c_x12 h₄, x22₃, BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [show (8 : Word).toNat = 8 from rfl]; omega
  have hsl₄ : stackLo t₄ memmoveStack = s.getReg .x2 - 1056 := by
    simp only [stackLo, sp₄, memmoveStack]; rv_eval []
  obtain ⟨t₅, r₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hd₅⟩ := hMM.call (Reaches.refl t₄) (b8000bd7c_pc h₄)
    { dst := by rw [x10₄, hN]; simp only [Mapped]; omega
      src := by rw [x11₄, hN]; simp only [Mapped]; addr_omega [hLt, hht, hL1, hk]
      stack := ⟨by rw [hsl₄]; valid_sub hst.valid [hb], by rw [sp₄]; addr_omega [hb]⟩
      dstStack := by rw [x10₄, hN, hsl₄]; addr_omega [hLt, hht, hab, hb]
      srcStack := by rw [x11₄, hN, hsl₄]; addr_omega [hLt, hht, hab, hb] }
  swap
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl hd₅⟩
  have F₅ := DFrame.of_byteFrame hpost₅.frame
  have hsl₄' : stackLo t₄ memcpyStack = s.getReg .x2 - 1056 := by
    simp only [stackLo, sp₄, memcpyStack]; rv_eval []
  rw [x10₄, hN, hsl₄'] at F₅
  have hby := hpost₅.bytes
  rw [x10₄, x11₄, hN] at hby
  have n₅ : t₅.getMem nextAddr = t₄.getMem nextAddr := F₅ _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hLt, hht]
    · addr_omega [hw, hi, hb, hnx]
  have nx₃' : t₃.getMem nextAddr = t.getMem nextAddr := by rw [nx₃, n₂, hm₁]
  have hn₅ : heapNext t₅ = heapNext t := by simp only [heapNext, n₅, hm₄, nx₃']
  have P₅ := P₄.step hpre F₅ (fun y hy ↦ by
      rcases hy with hy | hy
      · exact glw_heap (by addr_omega [hy, hLw]) (by
          have : (t₅.getMem nextAddr).toNat = heapNext t₅ := rfl
          addr_omega [hy, this, hn₅, hLt, hht])
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb]))))))
    ⟨by rw [hn₅]; exact h.pf.heap.lo, by rw [hn₅]; exact h.pf.heap.hi⟩
    (by simp only [heapNext, n₅]; exact Nat.le_refl _) (hpres₅ .x2 (by decide))
  -- what the round kept
  have kS (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₅.getMem y = t₂.getMem y := by
    rw [F₅ y fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hy, hb, hLt, hht, hab],
      hm₄, kS₃ y hy]
  have kS' (y : Word) (hy : (s.getReg .x2 - 784).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat) :
      t₅.getMem y = t.getMem y := by
    rw [kS y ⟨by addr_omega [hy, hb], hy.2⟩, F₂ y fun i hi hw ↦ by addr_omega [hw, hi, hy, hb], hm₁]
  have hRL' := h.RL
  rw [hRdef, hCdef] at hRL'
  have rts₅ : kListAt t₅ R (k + 1) = st.1 := by
    rw [← h.rts, hRdef, DFrame.kList F₅ (by omega) fun y hy hw ↦ by
        rcases hw with hw | hw
        · rcases hRL' with h0 | h0 <;> addr_omega [hy, hw, h0, hrc, hLt, hht]
        · addr_omega [hy, hw, hRt, hht, hab, hb, hrc],
      kListAt_congr fun i _ ↦ hm₄ _, DFrame.kList F₃ (by omega) fun y hy hw ↦ by
        rcases hw with hw | hw
        · rcases hRL' with h0 | h0 <;> addr_omega [hy, hw, h0, hrc, hLt, hht]
        · addr_omega [hy, hw, hRt, hht, hab, hb, hrc],
      DFrame.kList F₂ (by omega) fun y hy hw ↦ by addr_omega [hy, hw, hRt, hht, hab, hb, hrc]]
    exact kListAt_congr fun i _ ↦ hm₁ _
  have hlayM : layM st = kListAt t₃ L (n - k) := by rw [layM, hlast, lay₃]
  have r5 (q : Reg) (hq : q ∈ innerRegs) (h4 : t₄.getReg q = t₃.getReg q) :
      t₅.getReg q = t₂.getReg q := by
    rw [hpres₅ q (innerRegs_saved hq), h4, reg₃ q hq]
  have m792 : t₂.getMem (s.getReg .x2 - 792) = BitVec.ofNat 64 (k + 1) := by
    have := b8000bd20_m_x2_248 h₂
    rw [sp₁, k₁ .x13 (by decide), h.x13] at this; rv_eval [] at this
    rw [this]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
    have := hR8; omega
  have rsl : RSL s w t₅ a n L := by
    have hsl := ((((h.sl.keep' hpre (DFrame.of_same hm₁ fun _ ↦ False) fun _ h ↦ h.elim).keep' hpre F₂
      fun y hy ↦ Or.inl hy).keep' hpre F₃ fun y hy ↦ ?_).keep' hpre (DFrame.of_same hm₄ fun _ ↦ False)
        fun _ h ↦ h.elim).keep' hpre F₅ fun y hy ↦ ?_
    · exact hsl
    · rcases hy with hy | hy
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hy, hLw, hsw], by addr_omega [hy, hLt, hht]⟩)))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))
    · rcases hy with hy | hy
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hy, hLw, hsw], by addr_omega [hy, hLt, hht]⟩)))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))
  refine ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inr {
    h := h
    pf := P₅
    sl := rsl
    pc := by rw [hpc₅, returnAddress_eq, b8000bd7c_x1 h₄]; decide
    x9 := by
      rw [r5 .x9 (by simp [innerRegs]) (k₄ .x9 (by decide)), k₂ .x9 (by decide), k₁ .x9 (by decide), h.x9]
    x19 := by
      rw [r5 .x19 (by simp [innerRegs]) (k₄ .x19 (by decide)), k₂ .x19 (by decide),
        k₁ .x19 (by decide), h.x19]
    x20 := by
      rw [r5 .x20 (by simp [innerRegs]) (k₄ .x20 (by decide)), k₂ .x20 (by decide), x20₁]
    x23 := by
      rw [hpres₅ .x23 (by decide), b8000bd7c_x23 h₄, sp₃]; rv_eval [m784₃]
      rw [hlayM, kListAt_headD _ _ (by omega)]
    x26 := by
      rw [r5 .x26 (by simp [innerRegs]) (k₄ .x26 (by decide)), b8000bd20_x26 h₂, x21₁, hRdef]
    x27 := by
      rw [r5 .x27 (by simp [innerRegs]) (k₄ .x27 (by decide)), b8000bd20_x27 h₂, x20₁]
    m792 := by rw [kS _ ⟨by addr_omega [hb], by addr_omega [hb]⟩]; exact m792
    m128 := kS' _ ⟨by addr_omega [hb], by addr_omega [hb]⟩
    m120 := kS' _ ⟨by addr_omega [hb], by addr_omega [hb]⟩
    m112 := kS' _ ⟨by addr_omega [hb], by addr_omega [hb]⟩
    nx := by rw [n₅, hm₄, nx₃']
    rts := by rw [hRdef]; exact rts₅
    lay := by
      rw [hlayM]
      apply List.ext_getElem (by simp [kListAt_length])
      intro j h1 h2
      rw [kListAt_length] at h1
      rw [kListAt_getElem, List.getElem_tail, kListAt_getElem,
        getMem_eq_of_bytesAt hby hL8 (by addr_omega [hL8, hLt, hht]) (k := 8 * j) (by omega) (by omega),
        hm₄]
      congr 2
      rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, add_ofNat_add]
      congr 2; omega }⟩

end Rv64Verifier.Proofs.Pcs.Vso
