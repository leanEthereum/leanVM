import Rv64Verifier.Proofs.Layout.Col
import Rv64Verifier.Blocks.F15

/-!
# `prod`, at `0x80005138`

```rust
fn prod(a: usize, b: usize, exponent: u64) -> Form {
    Form::term(Monomial::Xy(a.min(b), a.max(b)), gpow(exponent))
}
```

compiled (`Blocks/F15.lean`): `0x80005138` makes a 96-byte frame (`sp'` = the entry's `sp - 96`)
and puts `a.min(b)` in `a0` (`0x80005150` when `b ≤ a`), `0x80005154` `a.max(b)` in `a1`
(`0x80005158` when `a ≤ b`); `0x8000515c` writes `Xy(a0, a1)` at `sp' + 8` and `GEN` at `sp' + 56`
and calls `E::pow(sp' + 32, sp' + 56, exponent)`; `0x8000518c` calls `Form::term(out, sp' + 8,
sp' + 32)`; `0x800051a0` restores and returns.
-/

namespace Rv64Verifier.Layout.Prod
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F15 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000515c`: the frame made, the return address and `s0` saved, `a0`/`a1` the smaller and
the larger column. -/
structure AtCall (s t : MachineState) : Prop where
  pc : t.pc = 0x8000515c
  sp : t.getReg .x2 = s.getReg .x2 - 96
  out : t.getReg .x8 = s.getReg .x10
  lo : (t.getReg .x10).toNat = min (s.getReg .x11).toNat (s.getReg .x12).toNat
  hi : (t.getReg .x11).toNat = max (s.getReg .x11).toNat (s.getReg .x12).toNat
  exp : t.getReg .x13 = s.getReg .x13
  kept : ∀ r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
    t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  mem : MemFrame s t (s.getReg .x2 - 16) 16

/-- The two branches to `0x8000515c`. -/
theorem toCall {s : MachineState} (hpc : s.pc = 0x80005138) (hpre : ColPre s) :
    ∃ t, Reaches Image.code s t ∧ AtCall s t := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  simp only [colStack, powStack, Contracts.mulStack] at hsb
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005138_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80005138_keeps h₁
  have hm₁ := b80005138_frame h₁ (by addr_omega [hsb])
  have x10₁ := b80005138_x10 h₁
  -- `a0 = a.min(b)` at `0x80005154`
  obtain ⟨t₂, hr₂, pc₂, x10₂, k₂, hm₂⟩ : ∃ t₂, Reaches Image.code t₁ t₂ ∧ t₂.pc = 0x80005154 ∧
      (t₂.getReg .x10).toNat = min (s.getReg .x11).toNat (s.getReg .x12).toNat ∧
      (∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x11, .x12, .x13, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
        .x25, .x26, .x27], t₂.getReg r = t₁.getReg r) ∧ ∀ a, t₂.getMem a = t₁.getMem a := by
    by_cases hc : (s.getReg .x11).toNat < (s.getReg .x12).toNat
    · exact ⟨t₁, Reaches.refl _, b80005138_pc_taken h₁ hc, by rw [x10₁]; omega,
        fun _ _ ↦ rfl, fun _ ↦ rfl⟩
    · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005150_spec
        (b80005138_pc_not_taken h₁ (by omega)) trivial
      have k := b80005150_keeps h₂
      refine ⟨t₂, hr₂, b80005150_pc h₂, ?_, fun r hr ↦ k r (mem_of_mem hr _), b80005150_mem_same h₂⟩
      rw [b80005150_x10 h₂, k₁ .x12 (by decide)]
      omega
  -- `a1 = a.max(b)` at `0x8000515c`
  have x11₂ : t₂.getReg .x11 = s.getReg .x11 := by rw [k₂ .x11 (by decide), k₁ .x11 (by decide)]
  have x12₂ : t₂.getReg .x12 = s.getReg .x12 := by rw [k₂ .x12 (by decide), k₁ .x12 (by decide)]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005154_spec pc₂ trivial
  have k₃ := b80005154_keeps h₃
  obtain ⟨t₄, hr₄, pc₄, x11₄, k₄, hm₄⟩ : ∃ t₄, Reaches Image.code t₃ t₄ ∧ t₄.pc = 0x8000515c ∧
      (t₄.getReg .x11).toNat = max (s.getReg .x11).toNat (s.getReg .x12).toNat ∧
      (∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x10, .x12, .x13, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
        .x25, .x26, .x27], t₄.getReg r = t₃.getReg r) ∧ ∀ a, t₄.getMem a = t₃.getMem a := by
    by_cases hc : (s.getReg .x12).toNat < (s.getReg .x11).toNat
    · refine ⟨t₃, Reaches.refl _, b80005154_pc_taken h₃ (by rw [x11₂, x12₂]; exact hc), ?_,
        fun _ _ ↦ rfl, fun _ ↦ rfl⟩
      rw [k₃ .x11 (by decide), x11₂]
      omega
    · obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80005158_spec
        (b80005154_pc_not_taken h₃ (by rw [x11₂, x12₂]; omega)) trivial
      have k := b80005158_keeps h₄
      refine ⟨t₄, hr₄, b80005158_pc h₄, ?_, fun r hr ↦ k r (mem_of_mem hr _), b80005158_mem_same h₄⟩
      rw [b80005158_x11 h₄, k₃ .x12 (by decide), x12₂]
      omega
  have hm (a : Word) : t₄.getMem a = t₁.getMem a :=
    (hm₄ a).trans ((b80005154_mem_same h₃ a).trans (hm₂ a))
  have hk (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x8, .x9, .x13, .x18, .x19, .x20, .x21, .x22, .x23,
      .x24, .x25, .x26, .x27]) : t₄.getReg r = t₁.getReg r := by
    rw [k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _)]
  refine ⟨t₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), pc₄, ?_, ?_, ?_, x11₄, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk .x2 (by decide), b80005138_x2 h₁]
  · rw [hk .x8 (by decide), b80005138_x8 h₁]
  · rw [k₄ .x10 (by decide), k₃ .x10 (by decide)]; exact x10₂
  · rw [hk .x13 (by decide), k₁ .x13 (by decide)]
  · intro r hr
    rw [hk r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  · rw [hm]; exact b80005138_m_x2_n8 h₁
  · rw [hm]; exact b80005138_m_x2_n16 h₁
  · intro a ha
    rw [hm]; exact hm₁ a ha

/-- **`prod` meets its contract**, given `pow`'s and `Form::term`'s. -/
theorem prod_spec (hP : PowSpec) (hT : TermSpec) : ProdSpec := by
  intro s hpc hpre
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hob := ValidMemRange.bounds hpre.out (by decide)
  have hos := hpre.outStack
  have hof := hpre.outFree
  simp only [colStack, powStack, Contracts.mulStack] at hsb hab hnx hro hos
  obtain ⟨t₀, hr₀, ht₀⟩ := toCall hpc hpre
  -- `Xy(min, max)` and `GEN`, and the call to `pow`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000515c_spec ht₀.pc (by
    rv_eval [ht₀.sp]
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b8000515c_keeps h₁
  have hf₀₁ := b8000515c_frame h₁ (by rw [ht₀.sp]; addr_omega [hsb])
  rw [ht₀.sp] at hf₀₁
  have hm₁ : MemFrame s t₁ (s.getReg .x2 - 88) 88 :=
    (ht₀.mem.mono fun a ha ↦ by addr_omega [ha, hsb]).trans
      (hf₀₁.mono fun a ha ↦ by addr_omega [ha, hsb]) fun _ ha ↦ ha
  have ra₁ : t₁.getMem (s.getReg .x2 - 8) = s.getReg .x1 :=
    (hf₀₁ _ (by addr_omega [hsb])).trans ht₀.ra
  have s0₁ : t₁.getMem (s.getReg .x2 - 16) = s.getReg .x8 :=
    (hf₀₁ _ (by addr_omega [hsb])).trans ht₀.s0
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 96 := (k₁ .x2 (by decide)).trans ht₀.sp
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 64 := by rw [b8000515c_x10 h₁, ht₀.sp]; rv_eval []
  have x11₁ : t₁.getReg .x11 = s.getReg .x2 - 40 := by rw [b8000515c_x11 h₁, ht₀.sp]; rv_eval []
  have x12₁ : t₁.getReg .x12 = s.getReg .x13 := by rw [b8000515c_x12 h₁, ht₀.exp]
  have hst₁ : RtStack t₁ powStack := hpre.stack.inner (k := 96) x2₁ (by decide) (by decide)
    (by decide) (by decide) (by decide)
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
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hP.call (hr₀.trans hr₁) (b8000515c_pc h₁) hpow
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hf₂ := dframe_of_three hpost₂.frame
  rw [x10₁, x11₁, show stackLo t₁ powStack = s.getReg .x2 - 1200 by
    simp only [stackLo, x2₁, powStack, Contracts.mulStack]; rv_eval [Nat.reduceAdd]] at hf₂
  -- the call to `Form::term`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000518c_spec
    (by rw [hpc₂, returnAddress_eq, b8000515c_x1 h₁]; decide) trivial
  have k₃ := b8000518c_keeps h₃
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 96 := (hpres₂.reg .x2).trans x2₁
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 96 := (k₃ .x2 (by decide)).trans x2₂
  have x10₃ : t₃.getReg .x10 = s.getReg .x10 := by
    rw [b8000518c_x10 h₃, hpres₂.reg .x8, k₁ .x8 (by decide), ht₀.out]
  have x11₃ : t₃.getReg .x11 = s.getReg .x2 - 88 := by
    rw [b8000518c_x11 h₃, x2₂]; rv_eval []
  have x12₃ : t₃.getReg .x12 = s.getReg .x2 - 64 := by
    rw [b8000518c_x12 h₃, x2₂]; rv_eval []
  have hf₃ : DFrame s t₃ fun a ↦ Within a (stackLo s 1200) 1200 :=
    ((hm₁.dframe.union hf₂).union (DFrame.of_same (b8000518c_mem_same h₃) fun _ ↦ False)).mono
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
  have hkeep (a : Word) (ha₁ : (s.getReg .x2).toNat - 96 ≤ a.toNat) (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat)
      (hout : a.toNat + 8 ≤ (s.getReg .x2).toNat - 64 ∨ (s.getReg .x2).toNat - 16 ≤ a.toNat) :
      t₃.getMem a = t₁.getMem a :=
    ((b8000518c_mem_same h₃ a).trans (hf₂.getMem_of (fun x hx h ↦ by
      rcases h with h | h | h <;> addr_omega [hx, h, hsb, ha₁, ha₂, hout]) (by addr_omega [hsb, ha₂])))
  have m₈ := b8000515c_m_x2_8 h₁
  have m₁₆ := b8000515c_m_x2_16 h₁
  have m₂₄ := b8000515c_m_x2_24 h₁
  have m₅₆ := b8000515c_m_x2_56 h₁
  have m₆₄ := b8000515c_m_x2_64 h₁
  have m₇₂ := b8000515c_m_x2_72 h₁
  rw [ht₀.sp] at m₈ m₁₆ m₂₄ m₅₆ m₆₄ m₇₂
  rv_eval [] at m₈ m₁₆ m₂₄ m₅₆ m₆₄ m₇₂
  have tag : t₃.getMem (s.getReg .x2 - 88) = 2 := by
    rw [hkeep _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])]
    exact m₈
  have idx₁ : t₃.getMem (s.getReg .x2 - 80) = t₀.getReg .x10 := by
    rw [hkeep _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])]
    exact m₁₆
  have idx₂ : t₃.getMem (s.getReg .x2 - 72) = t₀.getReg .x11 := by
    rw [hkeep _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])]
    exact m₂₄
  have hpowv : eAt t₃ (s.getReg .x2 - 64) = genRust ^ (s.getReg .x13).toNat := by
    have hv := hpost₂.value
    rw [x10₁, x11₁, x12₁, Col.eAt_gen m₅₆
      (by rw [show s.getReg .x2 - 40 + 8 = s.getReg .x2 - 32 by rv_eval []]; exact m₆₄)
      (by rw [show s.getReg .x2 - 40 + 16 = s.getReg .x2 - 24 by rv_eval []]; exact m₇₂)] at hv
    rw [← hv]
    exact eAt_congr (b8000518c_mem_same h₃ _) (b8000518c_mem_same h₃ _) (b8000518c_mem_same h₃ _)
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
    hT.call hr₃ (b8000518c_pc h₃) hterm
  swap
  · exact ⟨t₄, hr₂.trans hr₄, Or.inr hdead⟩
  rw [x10₃, x11₃, x12₃] at hval₄
  rw [x10₃] at hnew₄
  -- the epilogue
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 96 := (hpres₄.reg .x2).trans x2₃
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800051a0_spec
    (by rw [hpc₄, returnAddress_eq, b8000518c_x1 h₃]; decide) (by
      rv_eval [x2₄]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hnew₅ := hnew₄.same (b800051a0_mem_same h₅) (by addr_omega [hob])
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
  have pc₅ := b800051a0_pc h₅
  have r₁ := b800051a0_x1 h₅
  have r₂ := b800051a0_x2 h₅
  have r₈ := b800051a0_x8 h₅
  have k₅ := b800051a0_keeps h₅
  rw [x2₄] at pc₅ r₁ r₂ r₈
  rv_eval [] at pc₅ r₁ r₂ r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), ra₁] at pc₅ r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), s0₁] at r₈
  have hk (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]) :
      t₅.getReg r = s.getReg r := by
    rw [k₅ r (mem_of_mem hr _), hpres₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), ht₀.kept r hr]
  refine ⟨t₅, hr₂.trans (hr₄.trans hr₅), Or.inl ⟨pc₅.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ (hk .x9 (by decide)) (hk .x18 (by decide)) (hk .x19 (by decide))
      fun r hr ↦ hk r (mem_of_mem hr _), ?_, ?_⟩⟩
  · exact hnew₅.1.lift hnext₃ hf₃ (fun a ha ↦ Or.inl ha)
      (fun a ha ↦ by addr_omega [ha, hsb, x2₃])
  · rw [hnew₅.2, hval₄, prodRust, gpowRust, ← hpowv]
    simp only [monoOf, tag, show (2 : Word) ≠ 0 by decide, show (2 : Word) ≠ 1 by decide,
      ite_false, show s.getReg .x2 - 88 + 8 = s.getReg .x2 - 80 by rv_eval [],
      show s.getReg .x2 - 88 + 16 = s.getReg .x2 - 72 by rv_eval [], idx₁, idx₂, ht₀.lo, ht₀.hi]

end Rv64Verifier.Layout.Prod
