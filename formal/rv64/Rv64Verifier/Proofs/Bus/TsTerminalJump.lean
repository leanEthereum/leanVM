import Rv64Verifier.Proofs.Bus.TsTerminalCalls

/-!
# `table_sumcheck`: JUMP's summand

```rust
fn jump_constraints(columns: &[E]) -> Vec<E> {
    let (condition, inverse, flag) = (columns[V_COND], columns[W], columns[B]);
    vec![flag + condition * inverse, condition * (flag + ONE)]
}
```

`0x80008694` reads the evaluations' columns 5, 12 and 13 (trapping on a row shorter than 14),
`mul`s twice (`jumpA`, to `0x8000877c`), allocates the two constraints and `dot`s them with the
slice of `constraint_powers` into `sp + 248` (`jumpB`, to `0x8000880c`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What JUMP's summand writes from `v` on: `sp + 136` and `sp + 144`, `sp + 248` up to the saved
registers, the callees' stacks, `NEXT` and the heap allocated. -/
def JW (s v w : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 360) 16 ∨ Within a (s.getReg .x2 - 248) 144 ∨
    Within a (s.getReg .x2 - 2128) 1632 ∨ Within a nextAddr 8 ∨ Fresh v w a

theorem JW.mono {s v w x : MachineState} (h : heapNext w ≤ heapNext x) {a : Word}
    (ha : JW s v w a) : JW s v x a := by
  rcases ha with ha | ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩)))

theorem jw_step {s v w x : MachineState} (h₁ : DFrame v w (JW s v w)) (h₂ : DFrame w x (JW s v x))
    (hm : heapNext w ≤ heapNext x) : DFrame v x (JW s v x) :=
  (h₁.mono fun _ ha ↦ JW.mono hm ha).trans h₂ fun _ h ↦ h

theorem jw_tw {s u₀ v w : MachineState} (hpre : TableSumcheckPre s)
    (h₁ : DFrame u₀ v (TW s u₀ v)) (h₂ : DFrame v w (JW s v w)) (hm₁ : heapNext u₀ ≤ heapNext v)
    (hm₂ : heapNext v ≤ heapNext w) : DFrame u₀ w (TW s u₀ w) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine (h₁.mono fun _ ha ↦ TW.mono hm₂ ha).trans h₂ fun a ha ↦ ?_
  rcases ha with ha | ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))

/-- A frame of the stack keeps `NEXT`. -/
theorem next_of_stack {s a b : MachineState} {lo : Word} {m : Nat} (hpre : TableSumcheckPre s)
    (hf : DFrame a b (Within · lo m)) (h1 : (s.getReg .x2 - 2128).toNat ≤ lo.toNat)
    (h2 : lo.toNat + m ≤ (s.getReg .x2).toNat) : heapNext b = heapNext a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [heapNext]
  rw [hf _ fun j hj hw ↦ by addr_omega [hw, hj, h1, h2, hb1]]

theorem eListAt_two (s : MachineState) (p : Word) :
    eListAt s p 2 = [eAt s p, eAt s (p + 24)] := by
  simp [eListAt, List.range_succ]

theorem jump_list (ev : List E) : (tables.getD 4 default).constraints ev =
    [ev.getD 13 0 + ev.getD 5 0 * ev.getD 12 0, ev.getD 5 0 * (ev.getD 13 0 + 1)] := by
  rw [constraints_jump, ← LayoutMirror.jumpConstraintsRust_eq]
  rfl

/-- At `0x8000877c`: the two constraints, the first's limbs in `s10`, `s4`, `s11`, the second at
`sp + 272`; `sp + 136` the slice, `sp + 144` the terminal's top limb. -/
structure JumpMid (s v w : MachineState) (rows : List (List E × List E)) (i : ℕ) : Prop where
  sp : w.getReg .x2 = s.getReg .x2 - 496
  heapEq : heapNext w = heapNext v
  frame : DFrame v w (JW s v w)
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x21, .x24, .x25] : List Reg), w.getReg r = v.getReg r
  c1 : Model.limbs ((rows.getD i ([], [])).2.getD 13 0 +
      (rows.getD i ([], [])).2.getD 5 0 * (rows.getD i ([], [])).2.getD 12 0) =
    (w.getReg .x26, w.getReg .x20, w.getReg .x27)
  c2 : eAt w (s.getReg .x2 - 224) =
    (rows.getD i ([], [])).2.getD 5 0 * ((rows.getD i ([], [])).2.getD 13 0 + 1)
  m136 : w.getMem (s.getReg .x2 - 360) = v.getReg .x11
  m144 : w.getMem (s.getReg .x2 - 352) = v.getReg .x27

/-- The columns and the two `mul`s, from `0x80008694` to `0x8000877c`. -/
theorem jumpA (hMul : MulSpec) {s u₀ v : MachineState} {rows : List (List E × List E)}
    {ws : List E} {W : Word} {n i : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n)
    (hi : i < n) (h : AtSum s u₀ v rows ws i) (hpc : v.pc = 0x80008694) :
    ∃ w, Reaches Image.code v w ∧
      ((w.pc = 0x8000877c ∧ JumpMid s v w rows i) ∨ Dead Image.code w) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hsp := h.sp
  obtain ⟨R, hR, hR1, hR2, hR3, EP, EL, hEP, hEL, hE3, hEb, hEl⟩ := C.row hpre hi
  have hx19 : v.getReg .x19 = R + BitVec.ofNat 64 (48 * i) := by rw [h.x19, hR]
  have hh0 := C.inv.heap.hi
  have hmv := h.mono
  simp only [heapStart, heapEnd] at hR1 hEb hh0
  have hRv : ValidMemRange R (6 * n) := heap_range (by omega) (by omega) hR3
  set ev := (rows.getD i ([], [])).2
  -- what the row's `Vec`s hold, read below `u₀`
  have rd (x : MachineState) (hf : DFrame v x (JW s v x)) (a : Word) (h1 : 0x20000000 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ heapNext u₀) : x.getMem a = u₀.getMem a := by
    rw [hf a fun j hj hw ↦ ?_,
      h.frame a (tw_old hpre C.inv.heap (by simp only [heapStart]; omega) h2)]
    rcases hw with hw | hw | hw | hw | ⟨hw, -⟩ <;> addr_omega [hw, hj, h1, h2, hb1, hh0, hmv]
  have hEP1 : 0x20000000 ≤ EP.toNat ∧ EP.toNat + 24 * EL.toNat ≤ heapNext u₀ ∨ EL.toNat = 0 := by
    rcases hEb with h0 | h0
    · exact Or.inr h0
    · exact Or.inl h0
  have col (x : MachineState) (hf : DFrame v x (JW s v x)) (k : ℕ) (hk : k < EL.toNat) :
      eAt x (EP + BitVec.ofNat 64 (24 * k)) = ev.getD k 0 := by
    have hE : 0x20000000 ≤ EP.toNat ∧ EP.toNat + 24 * EL.toNat ≤ heapNext u₀ := by
      rcases hEP1 with h0 | h0
      · exact h0
      · omega
    rw [eAt_congr (rd x hf _ (by addr_omega [hE, hk]) (by addr_omega [hE, hk]))
      (rd x hf _ (by addr_omega [hE, hk]) (by addr_omega [hE, hk]))
      (rd x hf _ (by addr_omega [hE, hk]) (by addr_omega [hE, hk])), ← hEl, eListAt_getD _ _ hk]
  have eEL : v.getMem (R + BitVec.ofNat 64 (48 * i) + 40) = EL := by
    rw [rd v (DFrame.refl _ _) _ (by addr_omega [hR1, hR2, hi]) (by addr_omega [hR1, hR2, hi]),
      ← hEL]
    simp only [vecLen]
    exact congrArg _ (by addr_omega [hR1, hR2, hi])
  -- `0x80008694`: the evaluations' length, the slice and `s11` to `sp + 136`, `sp + 144`
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008694_spec hpc (by
    rv_eval [hsp, hx19]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hRv [hR1, hR2, hi]
      | addr_omega [hR1, hR2, hi, hb1, hh0])
  by_cases h5 : EL.toNat ≤ 5
  · exact ⟨v₁, hr₁, Or.inr (trap (b80008694_pc_taken h₁ (by
      rw [hx19, eEL]; simp only [Sym.wordToNatLit]; exact h5)))⟩
  have hpc₁ := b80008694_pc_not_taken h₁ (by
    rw [hx19, eEL]; simp only [Sym.wordToNatLit]; omega)
  have hE : 0x20000000 ≤ EP.toNat ∧ EP.toNat + 24 * EL.toNat ≤ heapNext u₀ := by
    rcases hEP1 with h0 | h0
    · exact h0
    · omega
  have hEPv : ValidMemRange EP (3 * EL.toNat) := heap_range (by omega) (by omega) hE3
  have k₁ := b80008694_keeps h₁
  have hf₁ := DFrame.of_memFrame (b80008694_frame h₁ (by rw [hsp]; addr_omega [hb1]))
  rw [hsp, show s.getReg .x2 - 496 + 136 = s.getReg .x2 - 360 by addr_omega [hb1]] at hf₁
  have F₁ : DFrame v v₁ (JW s v v₁) := hf₁.mono fun _ ha ↦ Or.inl ha
  have n₁ := next_of_stack hpre hf₁ (by addr_omega [hb1]) (by addr_omega [hb1])
  have hsp₁ : v₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  have hx19₁ : v₁.getReg .x19 = R + BitVec.ofNat 64 (48 * i) := (k₁ .x19 (by decide)).trans hx19
  have hx11₁ : v₁.getReg .x11 = EL := by rw [b80008694_x11 h₁, hx19, eEL]
  have eEP₁ : v₁.getMem (R + BitVec.ofNat 64 (48 * i) + 32) = EP := by
    rw [rd v₁ F₁ _ (by addr_omega [hR1, hR2, hi]) (by addr_omega [hR1, hR2, hi]), ← hEP]
    simp only [vecPtr]
    exact congrArg _ (by addr_omega [hR1, hR2, hi])
  have m136₁ : v₁.getMem (s.getReg .x2 - 360) = v.getReg .x11 := by
    have e := b80008694_m_x2_136 h₁; rw [hsp] at e; rv_eval [] at e; exact e
  have m144₁ : v₁.getMem (s.getReg .x2 - 352) = v.getReg .x27 := by
    have e := b80008694_m_x2_144 h₁; rw [hsp] at e; rv_eval [] at e; exact e
  -- `0x800086a8`: column 5 to `sp + 344`
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800086a8_spec hpc₁ (by
    rv_eval [hsp₁, hx19₁, eEP₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hRv [hR1, hR2, hi]
      | valid_access hEPv [hE, h5])
  have hx10₂ : v₂.getReg .x10 = EP := by rw [b800086a8_x10 h₂, hx19₁, eEP₁]
  by_cases h13 : EL.toNat < 13
  · exact ⟨v₂, hr₁.trans hr₂, Or.inr (trap (b800086a8_pc_taken h₂ (by
      rw [hx11₁]; simp only [Sym.wordToNatLit]; exact h13)))⟩
  have hpc₂ := b800086a8_pc_not_taken h₂ (by rw [hx11₁]; simp only [Sym.wordToNatLit]; omega)
  have k₂ := b800086a8_keeps h₂
  have hf₂ := DFrame.of_memFrame (b800086a8_frame h₂ (by rw [hsp₁]; addr_omega [hb1]))
  rw [hsp₁, show s.getReg .x2 - 496 + 344 = s.getReg .x2 - 152 by addr_omega [hb1]] at hf₂
  have n₂ := next_of_stack hpre hf₂ (by addr_omega [hb1]) (by addr_omega [hb1])
  have F₂ : DFrame v v₂ (JW s v v₂) :=
    jw_step F₁ (hf₂.mono fun _ ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb1]))) n₂.ge
  have hsp₂ : v₂.getReg .x2 = s.getReg .x2 - 496 := (k₂ .x2 (by decide)).trans hsp₁
  have hc5 : eAt v₂ (s.getReg .x2 - 152) = ev.getD 5 0 := by
    have m0 := b800086a8_m_x2_344 h₂
    have m1 := b800086a8_m_x2_352 h₂
    have m2 := b800086a8_m_x2_360 h₂
    rw [hsp₁, hx19₁, eEP₁] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2])]
    exact col v₁ F₁ 5 (by omega)
  -- `0x800086cc`: column 12 to `sp + 368`
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800086cc_spec hpc₂ (by
    rv_eval [hsp₂, hx10₂]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hEPv [hE, h13])
  have hx11₂ : v₂.getReg .x11 = EL := (k₂ .x11 (by decide)).trans hx11₁
  by_cases h13' : EL.toNat = 13
  · refine ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr (trap (b800086cc_pc_taken h₃ ?_))⟩
    rw [hx11₂]
    exact BitVec.eq_of_toNat_eq (by rw [h13']; rfl)
  have hpc₃ := b800086cc_pc_not_taken h₃ (by
    rw [hx11₂]; intro e; apply h13'; rw [e]; rfl)
  have k₃ := b800086cc_keeps h₃
  have hf₃ := DFrame.of_memFrame (b800086cc_frame h₃ (by rw [hsp₂]; addr_omega [hb1]))
  rw [hsp₂, show s.getReg .x2 - 496 + 368 = s.getReg .x2 - 128 by addr_omega [hb1]] at hf₃
  have n₃ := next_of_stack hpre hf₃ (by addr_omega [hb1]) (by addr_omega [hb1])
  have F₃ : DFrame v v₃ (JW s v v₃) :=
    jw_step F₂ (hf₃.mono fun _ ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb1]))) n₃.ge
  have hsp₃ : v₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  have hx10₃ : v₃.getReg .x10 = EP := (k₃ .x10 (by decide)).trans hx10₂
  have hc12 : eAt v₃ (s.getReg .x2 - 128) = ev.getD 12 0 := by
    have m0 := b800086cc_m_x2_368 h₃
    have m1 := b800086cc_m_x2_376 h₃
    have m2 := b800086cc_m_x2_384 h₃
    rw [hsp₂, hx10₂] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2])]
    exact col v₂ F₂ 12 (by omega)
  -- `0x800086f0`: column 13 to `s4`, `s7`, `s6`, the two columns to `sp + 296`, `mul`
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800086f0_spec hpc₃ (by
    rv_eval [hsp₃, hx10₃]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hEPv [hE, h13, h13'])
  have k₄ := b800086f0_keeps h₄
  have hf₄ := DFrame.of_memFrame (b800086f0_frame h₄ (by rw [hsp₃]; addr_omega [hb1]))
  rw [hsp₃, show s.getReg .x2 - 496 + 296 = s.getReg .x2 - 200 by addr_omega [hb1]] at hf₄
  have n₄ := next_of_stack hpre hf₄ (by addr_omega [hb1]) (by addr_omega [hb1])
  have F₄ : DFrame v v₄ (JW s v v₄) :=
    jw_step F₃ (hf₄.mono fun _ ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb1]))) n₄.ge
  have hsp₄ : v₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hsp₃
  have hc13 : Model.limbs (ev.getD 13 0) = (v₄.getReg .x20, v₄.getReg .x23, v₄.getReg .x22) := by
    have c13 : eAt v₃ (EP + 312) = ev.getD 13 0 := col v₃ F₃ 13 (by omega)
    rw [← c13, limbs_eAt, b800086f0_x20 h₄, b800086f0_x23 h₄, b800086f0_x22 h₄, hx10₃]
    rv_eval []
  have hS200 : eAt v₄ (s.getReg .x2 - 200) = ev.getD 5 0 := by
    have m0 := b800086f0_m_x2_296 h₄
    have m1 := b800086f0_m_x2_304 h₄
    have m2 := b800086f0_m_x2_312 h₄
    rw [hsp₃] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2]),
      hf₃.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
    exact hc5
  have hS176 : eAt v₄ (s.getReg .x2 - 176) = ev.getD 12 0 := by
    have m0 := b800086f0_m_x2_320 h₄
    have m1 := b800086f0_m_x2_328 h₄
    have m2 := b800086f0_m_x2_336 h₄
    rw [hsp₃] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2])]
    exact hc12
  have nv₄ : heapNext v₄ = heapNext v := by rw [n₄, n₃, n₂, n₁]
  have I₄ : Inv s v₄ := C.invAt hpre (jw_tw hpre h.frame F₄ h.mono nv₄.ge)
    ⟨nv₄ ▸ h.heap.lo, nv₄ ▸ h.heap.hi⟩ (nv₄ ▸ h.mono) hsp₄
  obtain ⟨w₁, hrw₁, ⟨hpcw₁, hpw₁, hvw₁, hfw₁⟩ | hd⟩ := mulCall hMul hpre
    (hr₁.trans (hr₂.trans (hr₃.trans hr₄))) (b800086f0_pc h₄) hsp₄ (I₄.rodata hpre)
    (o := 152) (l := 200) (r := 176)
    (by rw [b800086f0_x10 h₄, hsp₃]; addr_omega [hb1])
    (by rw [b800086f0_x11 h₄, hsp₃]; addr_omega [hb1])
    (by rw [b800086f0_x12 h₄, hsp₃]; addr_omega [hb1])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  swap
  · exact ⟨w₁, hrw₁, Or.inr hd⟩
  rw [hS200, hS176] at hvw₁
  have nw₁ : heapNext w₁ = heapNext v₄ := by
    simp only [heapNext]
    rw [hfw₁ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1]]
  have Fw₁ : DFrame v w₁ (JW s v w₁) := jw_step F₄ (hfw₁.mono fun _ ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))) nw₁.ge
  have hspw₁ : w₁.getReg .x2 = s.getReg .x2 - 496 := (hpw₁.reg .x2).trans hsp₄
  -- `0x80008740`: the first constraint's limbs, `flag + 1` at `sp + 344`, `mul`
  obtain ⟨w₂, hrw₂, hw₂⟩ := Sym.BlockSpec.reaches b80008740_spec
    (by rw [hpcw₁, returnAddress_eq, b800086f0_x1 h₄]; decide) (by
      rv_eval [hspw₁]; and_intros <;> valid_access hval [hb1])
  have kw₂ := b80008740_keeps hw₂
  have hfw₂ := DFrame.of_memFrame (b80008740_frame hw₂ (by rw [hspw₁]; addr_omega [hb1]))
  rw [hspw₁, show s.getReg .x2 - 496 + 344 = s.getReg .x2 - 152 by addr_omega [hb1]] at hfw₂
  have nw₂ := next_of_stack hpre hfw₂ (by addr_omega [hb1]) (by addr_omega [hb1])
  have Fw₂ : DFrame v w₂ (JW s v w₂) :=
    jw_step Fw₁ (hfw₂.mono fun _ ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb1]))) nw₂.ge
  have hspw₂ : w₂.getReg .x2 = s.getReg .x2 - 496 := (kw₂ .x2 (by decide)).trans hspw₁
  have hc1 : Model.limbs (ev.getD 13 0 + ev.getD 5 0 * ev.getD 12 0) =
      (w₂.getReg .x26, w₂.getReg .x20, w₂.getReg .x27) := by
    rw [limbs_add, hc13, ← hvw₁, limbs_eAt, b80008740_x26 hw₂, b80008740_x20 hw₂,
      b80008740_x27 hw₂, hspw₁, hpw₁.reg .x20, hpw₁.reg .x23, hpw₁.reg .x22]
    rv_eval []
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ac_rfl
  have hS152 : eAt w₂ (s.getReg .x2 - 152) = ev.getD 13 0 + 1 := by
    apply eAt_eq_of_limbs
    have m0 := b80008740_m_x2_344 hw₂
    have m1 := b80008740_m_x2_352 hw₂
    have m2 := b80008740_m_x2_360 hw₂
    rw [hspw₁, hpw₁.reg .x20] at m0
    rw [hspw₁, hpw₁.reg .x23] at m1
    rw [hspw₁, hpw₁.reg .x22] at m2
    rv_eval [] at m0 m1 m2
    rw [limbs_add, limbs_one, hc13]
    rv_eval [m0, m1, m2]
  have hS200w : eAt w₂ (s.getReg .x2 - 200) = ev.getD 5 0 := by
    rw [hfw₂.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1],
      hfw₁.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1]]
    exact hS200
  have nw₂' : heapNext w₂ = heapNext v := by rw [nw₂, nw₁, nv₄]
  have Iw₂ : Inv s w₂ := C.invAt hpre (jw_tw hpre h.frame Fw₂ h.mono nw₂'.ge)
    ⟨nw₂' ▸ h.heap.lo, nw₂' ▸ h.heap.hi⟩ (nw₂' ▸ h.mono) hspw₂
  obtain ⟨w₃, hrw₃, ⟨hpcw₃, hpw₃, hvw₃, hfw₃⟩ | hd⟩ := mulCall hMul hpre hrw₂ (b80008740_pc hw₂)
    hspw₂ (Iw₂.rodata hpre) (o := 224) (l := 200) (r := 152)
    (by rw [b80008740_x10 hw₂, hspw₁]; addr_omega [hb1])
    (by rw [b80008740_x11 hw₂, hspw₁]; addr_omega [hb1])
    (by rw [b80008740_x12 hw₂, hspw₁]; addr_omega [hb1])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  swap
  · exact ⟨w₃, hrw₁.trans hrw₃, Or.inr hd⟩
  rw [hS200w, hS152] at hvw₃
  have nw₃ : heapNext w₃ = heapNext w₂ := by
    simp only [heapNext]
    rw [hfw₃ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1]]
  have Fw₃ : DFrame v w₃ (JW s v w₃) := jw_step Fw₂ (hfw₃.mono fun _ ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))) nw₃.ge
  -- the slots `sp + 136` and `sp + 144`, written at `0x80008694` only
  have keep (a : Word) (ha1 : (s.getReg .x2 - 360).toNat ≤ a.toNat)
      (ha2 : a.toNat + 8 ≤ (s.getReg .x2 - 344).toNat) : w₃.getMem a = v₁.getMem a := by
    rw [hfw₃ a fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, ha1, ha2, hb1],
      hfw₂ a fun j hj hw ↦ by addr_omega [hw, hj, ha1, ha2, hb1],
      hfw₁ a fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, ha1, ha2, hb1],
      hf₄ a fun j hj hw ↦ by addr_omega [hw, hj, ha1, ha2, hb1],
      hf₃ a fun j hj hw ↦ by addr_omega [hw, hj, ha1, ha2, hb1],
      hf₂ a fun j hj hw ↦ by addr_omega [hw, hj, ha1, ha2, hb1]]
  have R (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x19, .x21, .x24, .x25] : List Reg)) :
      w₃.getReg r = v.getReg r := by
    rw [hpw₃ r (by unfold calleeSaved; exact mem_of_mem hr _), kw₂ r (mem_of_mem hr _),
      hpw₁ r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _),
      k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  refine ⟨w₃, hrw₁.trans hrw₃, Or.inl ⟨by rw [hpcw₃, returnAddress_eq, b80008740_x1 hw₂]; decide, {
    sp := (hpw₃.reg .x2).trans hspw₂
    heapEq := by rw [nw₃, nw₂']
    frame := Fw₃
    regs := R
    c1 := by rw [hpw₃.reg .x26, hpw₃.reg .x20, hpw₃.reg .x27]; exact hc1
    c2 := hvw₃
    m136 := (keep _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans m136₁
    m144 := (keep _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans m144₁ }⟩⟩

/-- The constraints' buffer and `dot`, from `0x8000877c` to `0x8000880c`. -/
theorem jumpB (hDot : DotSpec) (hA : AllocSpec) {s u₀ v w : MachineState}
    {rows : List (List E × List E)} {ws : List E} {W : Word} {n i : ℕ}
    (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) (h : AtSum s u₀ v rows ws i)
    (h4 : opAt s i = 4) (M : JumpMid s v w rows i) (hpc : w.pc = 0x8000877c) :
    ∃ t, Reaches Image.code w t ∧
      ((t.pc = 0x8000880c ∧ AtForms s u₀ t rows ws i) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hn2 : (tables.getD (opAt s i) default).nConstraints = 2 := by rw [h4]; exact nc_jump
  set ev := (rows.getD i ([], [])).2
  -- `0x8000877c`: the first constraint to `sp + 248`, `alloc(8, 48)`
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000877c_spec hpc (by
    rv_eval [M.sp]; and_intros <;> valid_access hval [hb1])
  have k₁ := b8000877c_keeps h₁
  have hf₁ := DFrame.of_memFrame (b8000877c_frame h₁ (by rw [M.sp]; addr_omega [hb1]))
  rw [M.sp, show s.getReg .x2 - 496 + 248 = s.getReg .x2 - 248 by addr_omega [hb1]] at hf₁
  have n₁ := next_of_stack hpre hf₁ (by addr_omega [hb1]) (by addr_omega [hb1])
  have hsp₁ : w₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans M.sp
  have hc1 : eAt w₁ (s.getReg .x2 - 248) = ev.getD 13 0 + ev.getD 5 0 * ev.getD 12 0 := by
    apply eAt_eq_of_limbs
    have m0 := b8000877c_m_x2_248 h₁
    have m1 := b8000877c_m_x2_256 h₁
    have m2 := b8000877c_m_x2_264 h₁
    rw [M.sp] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [M.c1]
    rv_eval [m0, m1, m2]
  have nw₁ : heapNext w₁ = heapNext v := n₁.trans M.heapEq
  have hheap₁ : HeapOk w₁ := ⟨nw₁ ▸ h.heap.lo, nw₁ ▸ h.heap.hi⟩
  obtain ⟨w₂, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hA.call hr₁ (b8000877c_pc h₁)
    ⟨hheap₁, by rw [b8000877c_x10 h₁]; decide⟩
  swap
  · exact ⟨w₂, hr₂, Or.inr hd⟩
  have hal := post.aligned
  have hab := post.above
  have hnx := post.next
  have hh₂ := post.heap.hi
  have hl₁ := hheap₁.lo
  rw [b8000877c_x10 h₁] at hal
  rw [b8000877c_x11 h₁] at hnx
  simp only [Sym.wordToNatLit, heapStart, heapEnd] at hal hnx hh₂ hl₁
  have hB1 : 0x20000000 ≤ (w₂.getReg .x10).toNat := by omega
  have hB2 : (w₂.getReg .x10).toNat + 48 ≤ 0x78000000 := by omega
  have hfa : DFrame w₁ w₂ (Within · nextAddr 8) := fun a ha ↦
    post.mem a fun e ↦ ha 0 (by decide) (by rw [add_ofNat_zero, e]; simp only [Within]; omega)
  have hsp₂ : w₂.getReg .x2 = s.getReg .x2 - 496 := (hp₂.reg .x2).trans hsp₁
  -- `0x80008798`: the buffer is not null
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008798_spec
    (by rw [hpc₂, returnAddress_eq, b8000877c_x1 h₁]; decide) trivial
  have hpc₃ := b80008798_pc_not_taken h₃ (by
    intro e; rw [e] at hB1; simp at hB1)
  have k₃ := b80008798_keeps h₃
  have hm₃ := b80008798_mem_same h₃
  have hsp₃ : w₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  have hx10₃ : w₃.getReg .x10 = w₂.getReg .x10 := k₃ .x10 (by decide)
  have hBv : ValidMemRange (w₂.getReg .x10) 6 := heap_range (by omega) (by omega) hal
  -- `0x8000879c`: the constraints to the buffer, `dot`
  obtain ⟨w₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000879c_spec hpc₃ (by
    rv_eval [hsp₃, hx10₃]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hBv [hB1, hB2]
      | addr_omega [hB1, hB2, hb1])
  have k₄ := b8000879c_keeps h₄
  have hf₄ := DFrame.of_memFrame (b8000879c_frame h₄ (by rw [hx10₃]; addr_omega [hB2]))
  rw [hx10₃] at hf₄
  have nw₄ : heapNext w₄ = heapNext w₂ := by
    simp only [heapNext]
    rw [hf₄ _ fun j hj hw ↦ by addr_omega [hw, hj, hB2], hm₃]
  have hsp₄ : w₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hsp₃
  have mid (a : Word) (h1 : (s.getReg .x2 - 2128).toNat + 1632 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2 - 248).toNat ∨ (s.getReg .x2 - 224).toNat ≤ a.toNat)
      (h3 : a.toNat + 8 ≤ (s.getReg .x2).toNat) : w₄.getMem a = w.getMem a := by
    rw [hf₄ a fun j hj hw ↦ by rcases h2 with h2 | h2 <;> addr_omega [hw, hj, hB2, h1, h3, hb1],
      hm₃, hfa a fun j hj hw ↦ by rcases h2 with h2 | h2 <;> addr_omega [hw, hj, h1, h3, hb1],
      hf₁ a fun j hj hw ↦ by rcases h2 with h2 | h2 <;> addr_omega [hw, hj, h1, h2, h3, hb1]]
  have hx11₄ : w₄.getReg .x11 =
      s.getReg .x17 + BitVec.ofNat 64 (24 * (tAcc s rows ws i).2) := by
    rw [b8000879c_x11 h₄, hsp₃]
    rv_eval []
    rw [hm₃, hfa _ fun j hj hw ↦ by addr_omega [hw, hj, hb1],
      hf₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1], M.m136, h.x11]
  have hx12₄ : w₄.getReg .x12 = BitVec.ofNat 64 2 := by
    rw [b8000879c_x12 h₄, k₃ .x8 (by decide), hp₂.reg .x8, k₁ .x8 (by decide),
      M.regs .x8 (by decide), h.x8, hn2]
  have hB0 : eAt w₄ (w₂.getReg .x10) = ev.getD 13 0 + ev.getD 5 0 * ev.getD 12 0 := by
    have m0 := b8000879c_m_x10_0 h₄
    have m1 := b8000879c_m_x10_8 h₄
    have m2 := b8000879c_m_x10_16 h₄
    rw [hsp₃, hx10₃] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2]), ← hc1,
      (DFrame.of_same hm₃ fun _ ↦ False).eAt (fun _ _ h ↦ h),
      hfa.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
  have hB24 : eAt w₄ (w₂.getReg .x10 + 24) = ev.getD 5 0 * (ev.getD 13 0 + 1) := by
    have m0 := b8000879c_m_x10_24 h₄
    have m1 := b8000879c_m_x10_32 h₄
    have m2 := b8000879c_m_x10_40 h₄
    rw [hsp₃, hx10₃] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2]), ← M.c2,
      (DFrame.of_same hm₃ fun _ ↦ False).eAt (fun _ _ h ↦ h),
      hfa.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1],
      hf₁.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
  have Fv₄ : DFrame v w₄ (JW s v w₄) := by
    refine jw_step (jw_step (jw_step M.frame (hf₁.mono fun _ ha ↦ Or.inr (Or.inl
      (by addr_omega [ha, hb1]))) n₁.ge) (hfa.mono fun _ ha ↦ Or.inr (Or.inr (Or.inr (Or.inl ha))))
      (by omega)) ((DFrame.of_same hm₃ _).trans hf₄ fun a ha ↦ ?_) nw₄.ge
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
    · simp only [Within] at ha; omega
    · simp only [Within] at ha; omega
  have nv₄ : heapNext v ≤ heapNext w₄ := by rw [nw₄]; omega
  have I₄ : Inv s w₄ := C.invAt hpre (jw_tw hpre h.frame Fv₄ h.mono nv₄)
    ⟨by have := h.heap.lo; omega, by rw [nw₄]; exact post.heap.hi⟩ (h.mono.trans nv₄) hsp₄
  have hcur := h.cur
  rw [hn2] at hcur
  have hCv : ValidMemRange (s.getReg .x17) (3 * (s.getReg .x28).toNat) :=
    RO.range (by rw [show 8 * (3 * (s.getReg .x28).toNat) = 24 * (s.getReg .x28).toNat by ring]
                 exact hpre.constraintPowers)
  have hCb := hpre.constraintPowers.bound
  have hCs := hpre.constraintPowers.stack
  rw [stackLo_eq, stack_eq] at hCs
  obtain ⟨w₅, hr₅, ⟨hpc₅, hp₅, -, hv₅, hf₅⟩ | hd⟩ := dotCall hDot hpre
    (hr₂.trans (hr₃.trans hr₄)) (b8000879c_pc h₄) hsp₄ (I₄.rodata hpre) (o := 248)
    (by rw [b8000879c_x10 h₄, hsp₃]; addr_omega [hb1]) (by decide)
    (by rw [hx11₄, hx12₄]; valid_sub hCv [hCb, hcur])
    (by rw [b8000879c_x14 h₄, b8000879c_x13 h₄, hx10₃]; exact hBv)
    (by rw [hx11₄, hx12₄]; addr_omega [hCs, hCb, hcur])
    (by rw [b8000879c_x14 h₄, b8000879c_x13 h₄, hx10₃]; addr_omega [hB2, hb1])
  swap
  · exact ⟨w₅, hr₅, Or.inr hd⟩
  rw [hx11₄, hx12₄, b8000879c_x13 h₄, hx10₃] at hv₅
  have hsum : eAt w₅ (s.getReg .x2 - 248) = sumOf s rows ws i := by
    rw [hv₅, sumOf, h4, nc_jump, jump_list, show (BitVec.ofNat 64 2).toNat = 2 from rfl,
      eListAt_two w₄ (w₂.getReg .x10), hB0, hB24,
      I₄.frame.eListAt ((I₄.miss hpre.constraintPowers).bytes (by addr_omega [hCb, hcur])
        (by addr_omega [hCb, hcur]) hCb), ← eListAt_drop_take _ _ hcur]
    rfl
  have nw₅ : heapNext w₅ = heapNext w₄ := by
    simp only [heapNext]
    rw [hf₅ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1]]
  have Fv₅ : DFrame v w₅ (JW s v w₅) := jw_step Fv₄ (hf₅.mono fun _ ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))) nw₅.ge
  have hsp₅ : w₅.getReg .x2 = s.getReg .x2 - 496 := (hp₅.reg .x2).trans hsp₄
  -- `0x800087e8`: `s6` and `s11` back
  obtain ⟨w₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800087e8_spec
    (by rw [hpc₅, returnAddress_eq, b8000879c_x1 h₄]; decide) (by
      rv_eval [hsp₅]; and_intros <;> valid_access hval [hb1])
  have k₆ := b800087e8_keeps h₆
  have hm₆ := b800087e8_mem_same h₆
  have nw₆ : heapNext w₆ = heapNext w₅ := by simp only [heapNext, hm₆]
  have Fv₆ : DFrame v w₆ (JW s v w₆) :=
    jw_step Fv₅ (DFrame.of_same hm₆ _) nw₆.ge
  have hmono : heapNext v ≤ heapNext w₆ := by rw [nw₆, nw₅]; exact nv₄
  have Fu₆ := jw_tw hpre h.frame Fv₆ h.mono hmono
  have hh₆ : heapNext w₆ ≤ 0x78000000 := by rw [nw₆, nw₅, nw₄]; omega
  have R (r : Reg) (hr : r ∈ ([.x9, .x18, .x19, .x21, .x24, .x25] : List Reg)) :
      w₆.getReg r = v.getReg r := by
    rw [k₆ r (mem_of_mem hr _), hp₅ r (by unfold calleeSaved; exact mem_of_mem hr _),
      k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      hp₂ r (by unfold calleeSaved; exact mem_of_mem hr _), k₁ r (mem_of_mem hr _),
      M.regs r (mem_of_mem hr _)]
  have hheap₆ : HeapOk w₆ := ⟨by have := h.heap.lo; omega, by simp only [heapEnd]; omega⟩
  refine ⟨w₆, hr₅.trans hr₆, Or.inl ⟨b800087e8_pc h₆, {
    sp := (k₆ .x2 (by decide)).trans hsp₅
    heap := hheap₆
    mono := h.mono.trans hmono
    frame := Fu₆
    x18 := (R .x18 (by decide)).trans h.x18
    x19 := (R .x19 (by decide)).trans h.x19
    x21 := (R .x21 (by decide)).trans h.x21
    x9 := (R .x9 (by decide)).trans h.x9
    x22 := by
      rw [b800087e8_x22 h₆, hsp₅]
      rv_eval []
      rw [← hm₆, Fu₆ _ (tw_slot hpre hheap₆ (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1])))]
      exact C.formLen
    acc := by
      rw [R .x25 (by decide), R .x24 (by decide), b800087e8_x27 h₆, hsp₅]
      rv_eval []
      rw [hf₅ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1],
        mid _ (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1])) (by addr_omega [hb1]), M.m144]
      exact h.acc
    weight := by
      rw [Fv₆.eAt fun j hj hw ↦ by
        rcases hw with hw | hw | hw | hw | ⟨-, hw⟩ <;> addr_omega [hw, hj, hb1, hh₆]]
      exact h.weight
    summand := by rw [(DFrame.of_same hm₆ fun _ ↦ False).eAt fun _ _ h ↦ h]; exact hsum
    cur := h.cur }⟩⟩

/-- The summand, from the head to `0x8000880c`. -/
theorem sumStep (hMul : MulSpec) (hDot : DotSpec) (hA : AllocSpec) {s u₀ v : MachineState}
    {rows : List (List E × List E)} {ws : List E} {W : Word} {n i : ℕ}
    (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) (hi : i < n)
    (h : AtSum s u₀ v rows ws i)
    (hpc : (opAt s i = 4 ∧ v.pc = 0x80008694) ∨ (opAt s i ≠ 4 ∧ v.pc = 0x800087f4)) :
    ∃ w, Reaches Image.code v w ∧
      ((w.pc = 0x8000880c ∧ AtForms s u₀ w rows ws i) ∨ Dead Image.code w) := by
  rcases hpc with ⟨h4, hpc⟩ | ⟨h4, hpc⟩
  · obtain ⟨w, hr, ⟨hpcw, M⟩ | hd⟩ := jumpA hMul hpre C hi h hpc
    · obtain ⟨t, hrt, ht⟩ := jumpB hDot hA hpre C h h4 M hpcw
      exact ⟨t, hr.trans hrt, ht⟩
    · exact ⟨w, hr, Or.inr hd⟩
  · exact otherSum hDot hpre C h h4 hpc

end Rv64Verifier.Proofs.Bus.TableSumcheck
