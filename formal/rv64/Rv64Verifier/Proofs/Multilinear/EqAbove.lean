import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.EqEval
import Rv64Verifier.Blocks.F67

/-!
# `Placement::eq_above`

```rust
pub fn eq_above(&self, point: &[E]) -> E {
    let bits = selector_point(self.index >> self.variables, point.len() - self.variables);
    eq_eval(&bits, &point[self.variables..])
}
```

compiled at `0x8000e12c` (`Blocks/F67.lean`), the `Placement` in `a1` (`variables`), `a2`
(`index`), with `S` the entry's `sp`: `0x8000e12c` saves `ra`, `s0`..`s4` in an 80-byte frame
and calls `selector_point(S - 72, index >> variables, len - variables)`; `0x8000e170` traps if
`len < variables`; `0x8000e174` restores the frame and jumps to `eq_eval(ret, bits, point +
24 variables, len - variables)`, which returns to the caller.
-/

namespace Rv64Verifier.Proofs.Multilinear.EqAbove
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F67
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem bounds {s : MachineState} (h : EqAbovePre s) :
    0x78000000 + 1136 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  simp only [eqAboveStack, mulStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- **`eq_above` meets its contract**, given `selector_point`'s and `eq_eval`'s. -/
theorem eq_above_spec (hSel : SelectorSpec)
    (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post) :
    EqAboveSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hret := ValidMemRange.bounds hpre.ret (by decide)
  have hrf := hpre.retFree
  have hpf := hpre.pointFree
  have hrs := hpre.retStack
  have hps := hpre.pointStack
  simp only [Outside] at hrf hpf
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000e12c_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000e12c_keeps h₁
  have hm₁ := b8000e12c_frame h₁ (by addr_omega [hb])
  have hsp₁ := b8000e12c_x2 h₁
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hb, hnx8])]
  have hsl : stackLo t₁ selectorStack = s.getReg .x2 - 192 := by
    simp only [stackLo, selectorStack, tryAllocStack, hsp₁]; rv_eval [Nat.reduceAdd]
  have hx11₁ : t₁.getReg .x11 = s.getReg .x12 >>> ((s.getReg .x11).toNat % 64) := by
    rw [h₁.reg .x11 rfl]; rv_eval []
  have hpre₁ : SelectorPre t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [b8000e12c_x10 h₁]; valid_sub hst.valid [hb]
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [b8000e12c_x10 h₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [b8000e12c_x10 h₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hSel.call hr₁ (b8000e12c_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hbf₂ := hpost₂.frame
  rw [b8000e12c_x10 h₁, hsl] at hbf₂
  have hfit₂ := hpost₂.heap.hi
  have hmono₂ := hpost₂.mono
  rw [hn₁] at hmono₂
  -- `t₂` and `s` agree on a doubleword none of whose bytes `selector_point` or the frame wrote
  have keep (a : Word) (h : ∀ i < 8, ¬ (Within (a + BitVec.ofNat 64 i) (s.getReg .x2 - 192) 192 ∨
      Within (a + BitVec.ofNat 64 i) nextAddr 8 ∨ Fresh t₁ t₂ (a + BitVec.ofNat 64 i))) :
      t₂.getMem a = s.getMem a := by
    rw [hbf₂.getMem fun i hi hw ↦ h i hi (by
      rcases hw with hw | hw | hw | hw
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inl (by addr_omega [hw, hb])
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr hw))]
    exact hm₁ a (by have := h 0 (by decide); simp only [BitVec.add_zero] at this
                    addr_omega [this, hb])
  have hslot (o : Nat) (ho₁ : 8 ≤ o) (ho₂ : o ≤ 48) (ho₃ : o % 8 = 0) :
      t₂.getMem (s.getReg .x2 - BitVec.ofNat 64 o) = t₁.getMem (s.getReg .x2 - BitVec.ofNat 64 o) :=
    hbf₂.getMem fun i hi hw ↦ by
      have := hpost₂.heap.hi
      rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hi, hb, ho₁, ho₂]
      · addr_omega [hw, hi, hb, ho₁, ho₂]
      · addr_omega [hw, hi, hb, ho₁, ho₂, hnx8]
      · simp only [Fresh] at hw
        addr_omega [hw, hi, hb, ho₁, ho₂, hab, this]
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 80 := (hpres₂.reg .x2).trans hsp₁
  have hreg₂ (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27]) : t₂.getReg r = t₁.getReg r :=
    hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hx19 : t₂.getReg .x19 = s.getReg .x11 := by rw [hreg₂ .x19 (by decide), b8000e12c_x19 h₁]
  have hx20 : t₂.getReg .x20 = s.getReg .x14 := by rw [hreg₂ .x20 (by decide), b8000e12c_x20 h₁]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000e170_spec
    (by rw [hpc₂, returnAddress_eq, b8000e12c_x1 h₁]; decide) trivial
  by_cases hlt : (s.getReg .x14).toNat < (s.getReg .x11).toNat
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b8000e170_pc_taken h₃ (by rw [hx19, hx20]; exact hlt)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b8000e170_keeps h₃
  have hm₃ := b8000e170_mem_same h₃
  obtain ⟨u, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000e174_spec
    (b8000e170_pc_not_taken h₃ (by rw [hx19, hx20]; omega)) (by
      rv_eval [k₃ .x2 (by decide), hsp₂]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000e174_keeps h₄
  have hmu (a : Word) : u.getMem a = t₂.getMem a := (b8000e174_mem_same h₄ a).trans (hm₃ a)
  have hsl8 := hslot 8 (by decide) (by decide) (by decide)
  have hsl16 := hslot 16 (by decide) (by decide) (by decide)
  have hsl24 := hslot 24 (by decide) (by decide) (by decide)
  have hsl32 := hslot 32 (by decide) (by decide) (by decide)
  have hsl40 := hslot 40 (by decide) (by decide) (by decide)
  have hsl48 := hslot 48 (by decide) (by decide) (by decide)
  rv_eval [b8000e12c_m_x2_n8 h₁, b8000e12c_m_x2_n16 h₁, b8000e12c_m_x2_n24 h₁,
    b8000e12c_m_x2_n32 h₁, b8000e12c_m_x2_n40 h₁, b8000e12c_m_x2_n48 h₁]
    at hsl8 hsl16 hsl24 hsl32 hsl40 hsl48
  have u1 := b8000e174_x1 h₄
  have u2 := b8000e174_x2 h₄
  have u8 := b8000e174_x8 h₄
  have u9 := b8000e174_x9 h₄
  have u10 := b8000e174_x10 h₄
  have u11 := b8000e174_x11 h₄
  have u12 := b8000e174_x12 h₄
  have u13 := b8000e174_x13 h₄
  have u14 := b8000e174_x14 h₄
  have u18 := b8000e174_x18 h₄
  have u19 := b8000e174_x19 h₄
  have u20 := b8000e174_x20 h₄
  rv_eval [k₃ .x2 (by decide), hsp₂, hm₃, hsl8, hsl16, hsl24, hsl32, hsl40, hsl48,
    k₃ .x9 (by decide), k₃ .x18 (by decide), k₃ .x19 (by decide), k₃ .x8 (by decide),
    hreg₂ .x9 (by decide), hreg₂ .x18 (by decide), hreg₂ .x8 (by decide), hx19,
    b8000e12c_x9 h₁, b8000e12c_x18 h₁, b8000e12c_x8 h₁]
    at u1 u2 u8 u9 u10 u11 u12 u13 u14 u18 u19 u20
  have hsaved : ∀ r ∈ calleeSaved, u.getReg r = s.getReg r := by
    intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact u2
    · exact u8
    · exact u9
    · exact u18
    · exact u19
    · exact u20
    all_goals rw [k₄ _ (by decide), k₃ _ (by decide), hreg₂ _ (by decide), k₁ _ (by decide)]
  -- the bits
  have hvec := hpost₂.vec
  have hfresh := hpost₂.fresh
  have hlen₂ := hpost₂.len
  have hel₂ := hpost₂.elems
  rw [b8000e12c_x10 h₁] at hvec hfresh hlen₂ hel₂
  rw [b8000e12c_x12 h₁] at hlen₂ hfresh hel₂
  rw [hx11₁] at hel₂
  obtain ⟨P, hP⟩ : ∃ P, P = vecPtr t₂ (s.getReg .x2 - 72) := ⟨_, rfl⟩
  rw [← hP] at hfresh
  have hn : (s.getReg .x14 - s.getReg .x11).toNat =
      (s.getReg .x14).toNat - (s.getReg .x11).toNat := by
    rw [BitVec.toNat_sub]; omega
  rw [hn] at hfresh hel₂
  have hu11 : u.getReg .x11 = P := by rw [u11, hP, vecPtr]; rv_eval []
  have hu12 : u.getReg .x12 = s.getReg .x14 - s.getReg .x11 := by
    rw [u12, ← hlen₂, vecLen]; rv_eval []
  have hPt := ValidMemRange.bounds hpre.point
  have hPr : (s.getReg .x14).toNat - (s.getReg .x11).toNat = 0 ∨
      (heapNext s ≤ P.toNat ∧ P.toNat + 24 * ((s.getReg .x14).toNat - (s.getReg .x11).toNat) ≤
        heapNext t₂) := by
    simp only [NewBuf, hn₁] at hfresh
    rcases hfresh.2 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  have hPa : P.toNat % 8 = 0 := by simp only [NewBuf] at hfresh; exact hfresh.1
  have hu2 : u.getReg .x2 = s.getReg .x2 := u2
  have hstk : stackLo u Proofs.EqEval.stackSize = stackLo s eqAboveStack := by
    simp only [stackLo, hu2]; rfl
  have hu13 : u.getReg .x13 = s.getReg .x13 + BitVec.ofNat 64 (24 * (s.getReg .x11).toNat) := by
    rw [u13]
    rcases Nat.eq_zero_or_pos (s.getReg .x14).toNat with h0 | h0
    · have : (s.getReg .x11).toNat = 0 := by omega
      have h11 : s.getReg .x11 = 0 := BitVec.eq_of_toNat_eq this
      rw [h11]; simp
    · have := hPt (by omega)
      addr_omega [this, h0, hlt]
  have hpt0 : (s.getReg .x14).toNat = 0 ∨ (0x20 ≤ (s.getReg .x13).toNat ∧
      (s.getReg .x13).toNat % 8 = 0 ∧
      (s.getReg .x13).toNat + 8 * (3 * (s.getReg .x14).toNat) ≤ 0xc0000008) := by
    rcases Nat.eq_zero_or_pos (s.getReg .x14).toNat with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (hPt (by omega))
  have hrod : RodataOk u := by
    have r₁ := hpre.rodata.frame hm₁ (by addr_omega [hb, hro])
    have r₂ := rodataOk_of_byteFrame r₁ hbf₂ fun a hw ↦ by
      have := hpost₂.heap.hi
      rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hb, hro]
      · addr_omega [hw, hb, hro]
      · addr_omega [hw]
      · simp only [Fresh] at hw; addr_omega [hw, this]
    exact fun p hp ↦ (hmu _).trans (r₂ p hp)
  have hpre₄ : Proofs.EqEval.Pre u := {
    ret := by rw [u10]; exact hpre.ret
    left := by
      rw [hu11, hu12, hn]
      rcases hPr with h0 | h0
      · rw [h0]; intro i hi; omega
      · have := hheap.lo
        exact heap_valid_range hPa (by omega) (by have := hpost₂.heap.hi; omega)
    right := by
      rw [hu13, u14, hn]
      rcases hpt0 with h0 | h0
      · have : (s.getReg .x14).toNat - (s.getReg .x11).toNat = 0 := by omega
        rw [this]; intro i hi; omega
      · exact ValidMemRange.sub hpre.point (by addr_omega [h0, hlt]) (by addr_omega [h0, hlt])
          (by addr_omega [h0, hlt])
    stack := ⟨by rw [hstk]; exact hst.valid, by rw [hu2]; exact hst.aligned⟩
    retStack := by rw [u10, hstk]; exact hrs
    leftStack := by
      rw [hu11, hu12, hn, hstk]
      rcases hPr with h0 | h0
      · rw [h0]; exact Or.inl (by omega)
      · have := hpost₂.heap.hi; addr_omega [h0, this, hab]
    rightStack := by
      rw [hu13, u14, hn, hstk]
      rcases hpt0 with h0 | h0
      · exact Or.inl (by omega)
      · addr_omega [h0, hlt, hps]
    rodata := hrod
    stackRodata := by rw [hstk]; addr_omega [hro, hb] }
  obtain ⟨t, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hdead⟩ := hEq.call (hr₂.trans (hr₃.trans hr₄))
    (b8000e174_pc h₄) hpre₄
  swap
  · exact ⟨t, hr₅, Or.inr hdead⟩
  have hfr := hpost₅.frame
  rw [u10, hstk] at hfr
  have hnt : t.getMem nextAddr = t₂.getMem nextAddr :=
    (hfr _ (by addr_omega [hrf.2]) (by addr_omega [hnx8, hb])).trans (hmu _)
  have hnT : heapNext t = heapNext t₂ := by simp only [heapNext, hnt]
  have hfit := hpost₂.heap.hi
  -- the point is untouched up to `u`
  have hpoint (a : Word) (h1 : (s.getReg .x13).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x13).toNat + 24 * (s.getReg .x14).toNat) :
      u.getMem a = s.getMem a := by
    rw [hmu]
    refine keep a fun i hi hw ↦ ?_
    rcases hpt0 with h0 | h0
    · omega
    rcases hw with hw | hw | hw
    · addr_omega [hw, hi, h1, h2, h0, hps, hb]
    · addr_omega [hw, hi, h1, h2, h0, hpf.2]
    · simp only [Fresh] at hw
      rw [hn₁] at hw
      addr_omega [hw, hi, h1, h2, h0, hpf.1, hfit]
  refine ⟨t, hr₅, Or.inl ⟨by rw [hpc₅]; simp only [returnAddress, u1],
    fun r hr ↦ (hpres₅ r hr).trans (hsaved r hr), {
      heap := ⟨by have := hheap.lo; omega, by rw [hnT]; exact hfit⟩
      mono := by rw [hnT]; exact hmono₂
      value := ?_
      frame := fun a ha ↦ ?_ }⟩⟩
  · have hv := hpost₅.value
    rw [u10] at hv
    rw [hv, Model.PlacementRust.eqAbove, Model.eqEvalRust_eq]
    simp only [Proofs.EqEval.left, Proofs.EqEval.right, Proofs.EqEval.len, hu11, hu12, hu13,
      hn, eListAt_length]
    congr 1
    · rw [← hel₂, vecEs, ← hP, hlen₂, hn]
      simp only [eListAt, eAt, hmu]
    · rw [eListAt_drop]
      simp only [eListAt]
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      rcases hpt0 with h0 | h0
      · omega
      obtain ⟨A, hA⟩ : ∃ A, A = s.getReg .x13 + BitVec.ofNat 64 (24 * (s.getReg .x11).toNat) +
          BitVec.ofNat 64 (24 * j) := ⟨_, rfl⟩
      rw [← hA]
      unfold eAt
      rw [hpoint A (by addr_omega [hA, h0, hj, hlt]) (by addr_omega [hA, h0, hj, hlt]),
        hpoint (A + 8) (by addr_omega [hA, h0, hj, hlt]) (by addr_omega [hA, h0, hj, hlt]),
        hpoint (A + 16) (by addr_omega [hA, h0, hj, hlt]) (by addr_omega [hA, h0, hj, hlt])]
  · have h0 := ha 0 (by decide)
    simp only [BitVec.add_zero, EqAboveW, not_or] at h0
    rw [hfr a h0.1 h0.2.1, hmu]
    refine keep a fun i hi hw ↦ ha i hi ?_
    rcases hw with hw | hw | hw
    · exact Or.inr (Or.inl (by addr_omega [hw, hb]))
    · exact Or.inr (Or.inr (Or.inl hw))
    · simp only [Fresh, hn₁] at hw
      exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hnT]; exact hw)))

end Rv64Verifier.Proofs.Multilinear.EqAbove
