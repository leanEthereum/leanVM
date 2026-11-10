import Rv64Verifier.Proofs.Layout.Contracts
import Rv64Verifier.Blocks.F10

/-!
# `col`, at `0x80004b34`

```rust
fn col(index: usize, exponent: u64) -> Form {
    Form::term(Monomial::X(index), gpow(exponent))
}
```

compiled (`Blocks/F10.lean`): `0x80004b34` makes a 96-byte frame (`sp'` = the entry's `sp - 96`),
writes `X(index)` at `sp' + 8` and `GEN` at `sp' + 56`, and calls `E::pow(sp' + 32, sp' + 56,
exponent)`; `0x80004b70` calls `Form::term(a0, sp' + 8, sp' + 32)`; `0x80004b84` restores and
returns.
-/

namespace Rv64Verifier.Layout.Col
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F10 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem eAt_gen {t : MachineState} {a : Word} (h0 : t.getMem a = 2) (h1 : t.getMem (a + 8) = 0)
    (h2 : t.getMem (a + 16) = 0) : eAt t a = genRust :=
  eq_of_limbs (by rw [limbs_eAt, h0, h1, h2]; rfl)

/-- **`col` meets its contract**, given `pow`'s and `Form::term`'s. -/
theorem col_spec (hP : PowSpec) (hT : TermSpec) : ColSpec := by
  intro s hpc hpre
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hob := ValidMemRange.bounds hpre.out (by decide)
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [colStack, powStack, Contracts.mulStack] at hsb hab hnx hro hos
  -- the frame, `X(index)` and `GEN`, and the call to `pow`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004b34_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80004b34_keeps h₁
  have hm₁ := b80004b34_frame h₁ (by addr_omega [hsb])
  have x2₁ := b80004b34_x2 h₁
  have x10₁ := b80004b34_x10 h₁
  have x11₁ := b80004b34_x11 h₁
  have x12₁ : t₁.getReg .x12 = s.getReg .x12 := k₁ .x12 (by decide)
  have hst₁ : RtStack t₁ powStack := hpre.stack.inner (k := 96) x2₁ (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hsb₁ := hst₁.bounds (by decide) (by decide)
  have hrod₁ : RodataOk t₁ := hpre.rodata.frame hm₁ (by addr_omega [hsb, hro])
  have hpow : PowPre t₁ := {
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hsb]
    base := by rw [x11₁]; valid_sub hpre.stack.valid [hsb]
    stack := hst₁.toStackOk
    pool := poolOk_of_rodata hrod₁ (by have := hst₁.rodata; addr_omega [this])
    outBase := by rw [x10₁, x11₁]; addr_omega [hsb]
    outStack := by rw [x10₁]; addr_omega [hsb, x2₁]
    baseStack := by rw [x11₁]; addr_omega [hsb, x2₁]
    basePool := by rw [x11₁]; addr_omega [hsb, hro] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hP.call hr₁ (b80004b34_pc h₁) hpow
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hf₂ := dframe_of_three hpost₂.frame
  rw [x10₁, x11₁, show stackLo t₁ powStack = s.getReg .x2 - 1200 by
    simp only [stackLo, x2₁, powStack, Contracts.mulStack]; rv_eval [Nat.reduceAdd]] at hf₂
  -- the call to `Form::term`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004b70_spec
    (by rw [hpc₂, returnAddress_eq, b80004b34_x1 h₁]; decide) trivial
  have k₃ := b80004b70_keeps h₃
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 96 := (hpres₂.reg .x2).trans x2₁
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 96 := (k₃ .x2 (by decide)).trans x2₂
  have x10₃ : t₃.getReg .x10 = s.getReg .x10 := by
    rw [b80004b70_x10 h₃, hpres₂.reg .x8, b80004b34_x8 h₁]
  have x11₃ : t₃.getReg .x11 = s.getReg .x2 - 88 := by
    rw [b80004b70_x11 h₃, x2₂]; rv_eval []
  have x12₃ : t₃.getReg .x12 = s.getReg .x2 - 64 := by
    rw [b80004b70_x12 h₃, x2₂]; rv_eval []
  -- memory at the call: the entry's but for the frame
  have hf₃ : DFrame s t₃ fun a ↦ Within a (stackLo s 1200) 1200 :=
    ((hm₁.dframe.union hf₂).union (DFrame.of_same (b80004b70_mem_same h₃) fun _ ↦ False)).mono
      fun a ha ↦ by
        rcases ha with (ha | ha | ha | ha) | ha
        · addr_omega [ha, hsb]
        · addr_omega [ha, hsb]
        · addr_omega [ha, hsb]
        · addr_omega [ha, hsb]
        · exact ha.elim
  have hn₃ : t₃.getMem nextAddr = s.getMem nextAddr :=
    hf₃.getMem_of (fun x hx h ↦ by addr_omega [hx, h, hnx, hsb]) (by decide)
  have hnext₃ : heapNext t₃ = heapNext s := by simp only [heapNext, hn₃]
  -- what the frame holds at the call, from the block's writes and `pow`'s result
  have hkeep (a : Word) (ha₁ : (s.getReg .x2).toNat - 96 ≤ a.toNat) (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat)
      (hout : a.toNat + 8 ≤ (s.getReg .x2).toNat - 64 ∨ (s.getReg .x2).toNat - 16 ≤ a.toNat) :
      t₃.getMem a = t₁.getMem a :=
    ((b80004b70_mem_same h₃ a).trans (hf₂.getMem_of (fun x hx h ↦ by
      rcases h with h | h | h <;> addr_omega [hx, h, hsb, ha₁, ha₂, hout]) (by addr_omega [hsb, ha₂])))
  have tag : t₃.getMem (s.getReg .x2 - 88) = 1 := by
    rw [hkeep _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])]
    exact b80004b34_m_x2_n88 h₁
  have idx : t₃.getMem (s.getReg .x2 - 80) = s.getReg .x11 := by
    rw [hkeep _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])]
    exact b80004b34_m_x2_n80 h₁
  have hpowv : eAt t₃ (s.getReg .x2 - 64) = genRust ^ (s.getReg .x12).toNat := by
    have hv := hpost₂.value
    rw [x10₁, x11₁, x12₁, eAt_gen (b80004b34_m_x2_n40 h₁)
      (by rw [show s.getReg .x2 - 40 + 8 = s.getReg .x2 - 32 by rv_eval []]; exact b80004b34_m_x2_n32 h₁)
      (by rw [show s.getReg .x2 - 40 + 16 = s.getReg .x2 - 24 by rv_eval []]; exact b80004b34_m_x2_n24 h₁)] at hv
    rw [← hv]
    exact eAt_congr (b80004b70_mem_same h₃ _) (b80004b70_mem_same h₃ _) (b80004b70_mem_same h₃ _)
  have hterm : TermPre t₃ := {
    heap := ⟨hnext₃ ▸ hpre.heap.lo, hnext₃ ▸ hpre.heap.hi⟩
    stack := hpre.stack.inner (k := 96) x2₃ (by decide) (by decide) (by decide) (by decide) (by decide)
    out := by rw [x10₃]; exact hpre.out
    mono := by rw [x11₃]; valid_sub hpre.stack.valid [hsb]
    coeff := by rw [x12₃]; valid_sub hpre.stack.valid [hsb]
    monoOk := by rw [x11₃]; simp only [MonoOk, tag]; decide
    outFree := by
      rw [x10₃]; simp only [Outside, hnext₃]; exact hof
    monoNext := by rw [x11₃]; addr_omega [hsb, hnx]
    coeffNext := by rw [x12₃]; addr_omega [hsb, hnx]
    outStack := by rw [x10₃]; addr_omega [hsb, hos, x2₃]
    monoStack := by rw [x11₃]; addr_omega [hsb, x2₃]
    coeffStack := by rw [x12₃]; addr_omega [hsb, x2₃] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hnew₄, hval₄⟩ | hdead⟩ :=
    hT.call hr₃ (b80004b70_pc h₃) hterm
  swap
  · exact ⟨t₄, hr₂.trans hr₄, Or.inr hdead⟩
  rw [x10₃, x11₃, x12₃] at hval₄
  rw [x10₃] at hnew₄
  -- the epilogue
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 96 := (hpres₄.reg .x2).trans x2₃
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004b84_spec
    (by rw [hpc₄, returnAddress_eq, b80004b70_x1 h₃]; decide) (by
      rv_eval [x2₄]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hnew₅ := hnew₄.same (b80004b84_mem_same h₅) (by addr_omega [hob])
  have hsave (a : Word) (ha₁ : (s.getReg .x2).toNat - 16 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₄.getMem a = t₁.getMem a := by
    have hfr := hnew₄.frame
    rw [← hkeep a (by omega) ha₂ (Or.inr ha₁)]
    refine hfr.getMem_of (fun x hx h ↦ ?_) (by addr_omega [hsb, ha₂])
    have hhi := hnew₄.heap.hi
    simp only [heapEnd, heapNext] at hhi
    rcases h with h | h | h | h
    · addr_omega [hx, h, hsb, hos, ha₁, ha₂]
    · addr_omega [hx, h, hsb, x2₃, ha₁, ha₂]
    · addr_omega [hx, h, hsb, hnx, ha₁, ha₂]
    · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hsb, hab, hhi, ha₁, ha₂]
  have pc₅ := b80004b84_pc h₅
  have r₁ := b80004b84_x1 h₅
  have r₂ := b80004b84_x2 h₅
  have r₈ := b80004b84_x8 h₅
  have k₅ := b80004b84_keeps h₅
  rw [x2₄] at pc₅ r₁ r₂ r₈
  rv_eval [] at pc₅ r₁ r₂ r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80004b34_m_x2_n8 h₁] at pc₅ r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), b80004b34_m_x2_n16 h₁] at r₈
  refine ⟨t₅, hr₂.trans (hr₄.trans hr₅), Or.inl ⟨pc₅.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ ?_ ?_ ?_ fun r hr ↦ ?_, ?_, ?_⟩⟩
  · rw [k₅ .x9 (by decide), hpres₄.reg .x9, k₃ .x9 (by decide), hpres₂.reg .x9, k₁ .x9 (by decide)]
  · rw [k₅ .x18 (by decide), hpres₄.reg .x18, k₃ .x18 (by decide), hpres₂.reg .x18,
      k₁ .x18 (by decide)]
  · rw [k₅ .x19 (by decide), hpres₄.reg .x19, k₃ .x19 (by decide), hpres₂.reg .x19,
      k₁ .x19 (by decide)]
  · rw [k₅ r (mem_of_mem hr _), hpres₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  · exact hnew₅.1.lift hnext₃ hf₃ (fun a ha ↦ Or.inl ha)
      (fun a ha ↦ by addr_omega [ha, hsb, x2₃])
  · rw [hnew₅.2, hval₄, colRust, gpowRust, ← hpowv]
    simp only [monoOf, tag, show (1 : Word) ≠ 0 by decide, ite_false, ite_true,
      show s.getReg .x2 - 88 + 8 = s.getReg .x2 - 80 by rv_eval [], idx]

end Rv64Verifier.Layout.Col
