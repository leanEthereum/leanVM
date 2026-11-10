import Rv64Verifier.Proofs.Bus.TsTerminalValues

/-!
# `table_sumcheck`: the terminal's loop

```rust
terminal += weight * (summand + dot(form_powers, &form_values));
cursor += n_constraints;
```

`0x80008578` calls `dot(form_powers, form_values)`, adds the summand, multiplies by the weight and
adds the product to the terminal in `s9`, `s8`, `s11` (`tailStep`); `termLoop` runs the items,
from the head at `0x80008600` to `0x800088e8` with every item done.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- One item of the mirror. -/
theorem tAcc_step {s : MachineState} {rows : List (List E × List E)} {ws : List E} {i : ℕ}
    (hi : i < (tItems s rows ws).length) :
    tAcc s rows ws (i + 1) = ((tAcc s rows ws i).1 + ws.getD i 0 * (sumOf s rows ws i +
      dotRust (fpOf s) ((formVecAt s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).map
        (formEvaluateRust · (rows.getD i ([], [])).2))),
      (tAcc s rows ws i).2 + (tables.getD (opAt s i) default).nConstraints) := by
  obtain ⟨hr, hw, he⟩ := tItems_getElem hi
  rw [tAcc_succ _ _ _ _ hi, he, ← List.getD_eq_getElem rows ([], []) hr,
    ← List.getD_eq_getElem ws 0 hw]
  rfl

/-- The item's product added, from `0x80008578` to the head or `0x800088e8`. -/
theorem tailStep (hMul : MulSpec) (hDot : DotSpec) {s u₀ v : MachineState}
    {rows : List (List E × List E)} {ws : List E} {W : Word} {n i : ℕ}
    (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) (hi : i < n)
    (h : AtTail s u₀ v rows ws i) (hpc : v.pc = 0x80008578) :
    ∃ t, Reaches Image.code v t ∧ (((t.pc = 0x80008600 ∧ i + 1 < n) ∨
      (t.pc = 0x800088e8 ∧ i + 1 = n)) ∧ LoopAt s u₀ t rows ws (i + 1) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hsp := h.sp
  have I := C.invAt hpre h.frame h.heap h.mono hsp
  have hhv := h.heap.hi
  simp only [heapEnd] at hhv
  obtain ⟨-, hn12, -, -⟩ := C.lens
  have e432 : v.getMem (s.getReg .x2 - 432) = s.getReg .x29 :=
    (h.frame _ (tw_slot hpre h.heap (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1])))).trans
      C.args.formPowers
  -- `0x80008578`: the summand's limbs, `dot(form_powers, form_values)` into `sp + 344`
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008578_spec hpc (by
    rv_eval [hsp]; and_intros <;> valid_access hval [hb1])
  have k₁ := b80008578_keeps h₁
  have hm₁ := b80008578_mem_same h₁
  have hsp₁ : v₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  have I₁ : Inv s v₁ := I.same hpre hm₁ (k₁ .x2 (by decide))
  have hx11₁ : v₁.getReg .x11 = s.getReg .x29 := by rw [b80008578_x11 h₁, hsp]; rv_eval [e432]
  have hx12₁ : v₁.getReg .x12 = s.getReg .x30 := by rw [b80008578_x12 h₁, h.x22]
  have hx13₁ : v₁.getReg .x13 = v.getReg .x8 := b80008578_x13 h₁
  have hx14₁ : v₁.getReg .x14 = v.getReg .x26 := b80008578_x14 h₁
  have hsl : Model.limbs (sumOf s rows ws i) = (v₁.getReg .x9, v₁.getReg .x19, v₁.getReg .x20) := by
    rw [← h.summand, limbs_eAt, b80008578_x9 h₁, b80008578_x19 h₁, b80008578_x20 h₁, hsp]
    rv_eval []
  have hFPv : ValidMemRange (s.getReg .x29) (3 * (s.getReg .x30).toNat) :=
    RO.range (by rw [show 8 * (3 * (s.getReg .x30).toNat) = 24 * (s.getReg .x30).toNat by ring]
                 exact hpre.formPowers)
  have hFPs := hpre.formPowers.stack
  rw [stackLo_eq, stack_eq] at hFPs
  have hbuf := h.buf
  have hal := h.align
  obtain ⟨w₁, hrw₁, ⟨hpcw₁, hpw₁, hlen, hvw₁, hfw₁⟩ | hd⟩ := dotCall hDot hpre hr₁ (b80008578_pc h₁)
    hsp₁ (I₁.rodata hpre) (o := 152) (by rw [b80008578_x10 h₁, hsp]; addr_omega [hb1]) (by decide)
    (by rw [hx11₁, hx12₁]; exact hFPv)
    (by
      rw [hx13₁, hx14₁]
      rcases hbuf with h0 | h0
      · rw [h0]; intro j hj; omega
      · simp only [heapStart] at h0
        exact heap_range (by omega) (by omega) hal)
    (by rw [hx11₁, hx12₁]; addr_omega [hFPs, hb1])
    (by rw [hx13₁, hx14₁]; rcases hbuf with h0 | h0 <;> addr_omega [h0, hb1, hhv])
  swap
  · exact ⟨w₁, hrw₁, Or.inr hd⟩
  rw [hx12₁, hx14₁] at hlen
  have hd₁ : eAt w₁ (s.getReg .x2 - 152) = dotRust (fpOf s)
      ((formVecAt s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).map
        (formEvaluateRust · (rows.getD i ([], [])).2)) := by
    rw [hvw₁, hx11₁, hx12₁, hx13₁, I₁.elems hpre.formPowers, hlen,
      show eListAt v₁ (v.getReg .x8) (v.getReg .x26).toNat =
        eListAt v (v.getReg .x8) (v.getReg .x26).toNat from
        (DFrame.of_same hm₁ fun _ ↦ False).eListAt fun _ _ h ↦ h, h.vals, ← hlen]
    rfl
  have hfw₁' : DFrame v₁ w₁ (TW s v w₁) := hfw₁.mono fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
  have nw₁ : heapNext w₁ = heapNext v := by
    simp only [heapNext]
    rw [hfw₁ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1], hm₁]
  have hspw₁ : w₁.getReg .x2 = s.getReg .x2 - 496 := (hpw₁.reg .x2).trans hsp₁
  -- `0x800085a4`: `summand + dot` at `sp + 296`, `mul(weight, ..)` into `sp + 344`
  obtain ⟨w₂, hrw₂, hw₂⟩ := Sym.BlockSpec.reaches b800085a4_spec
    (by rw [hpcw₁, returnAddress_eq, b80008578_x1 h₁]; decide) (by
      rv_eval [hspw₁]; and_intros <;> valid_access hval [hb1])
  have kw₂ := b800085a4_keeps hw₂
  have hfw₂ := DFrame.of_memFrame (b800085a4_frame hw₂ (by rw [hspw₁]; addr_omega [hb1]))
  rw [hspw₁, show s.getReg .x2 - 496 + 296 = s.getReg .x2 - 200 by addr_omega [hb1]] at hfw₂
  have nw₂ := next_of_stack hpre hfw₂ (by addr_omega [hb1]) (by addr_omega [hb1])
  have hspw₂ : w₂.getReg .x2 = s.getReg .x2 - 496 := (kw₂ .x2 (by decide)).trans hspw₁
  have hsd : eAt w₂ (s.getReg .x2 - 200) = sumOf s rows ws i + eAt w₁ (s.getReg .x2 - 152) := by
    apply eAt_eq_of_limbs
    have m0 := b800085a4_m_x2_296 hw₂
    have m1 := b800085a4_m_x2_304 hw₂
    have m2 := b800085a4_m_x2_312 hw₂
    rw [hspw₁, hpw₁.reg .x9] at m0
    rw [hspw₁, hpw₁.reg .x19] at m1
    rw [hspw₁, hpw₁.reg .x20] at m2
    rv_eval [] at m0 m1 m2
    rw [limbs_add, hsl, limbs_eAt]
    rv_eval [m0, m1, m2]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ac_rfl
  have Fw₂ : DFrame v w₂ (TW s v w₂) :=
    ((((DFrame.of_same hm₁ _).trans hfw₁' fun _ h ↦ h).mono fun _ ha ↦ TW.mono nw₂.ge ha).trans
      hfw₂ fun _ ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb1])))
  have nw₂' : heapNext w₂ = heapNext v := nw₂.trans nw₁
  have Iw₂ : Inv s w₂ := C.invAt hpre (tw_comp h.frame Fw₂ h.mono nw₂'.ge)
    ⟨nw₂' ▸ h.heap.lo, nw₂' ▸ h.heap.hi⟩ (nw₂' ▸ h.mono) hspw₂
  have hwt : eAt w₂ (s.getReg .x2 - 272) = ws.getD i 0 := by
    rw [hfw₂.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb1],
      hfw₁.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1],
      (DFrame.of_same hm₁ fun _ ↦ False).eAt fun _ _ h ↦ h]
    exact h.weight
  obtain ⟨w₃, hrw₃, ⟨hpcw₃, hpw₃, hvw₃, hfw₃⟩ | hd⟩ := mulCall hMul hpre hrw₂ (b800085a4_pc hw₂)
    hspw₂ (Iw₂.rodata hpre) (o := 152) (l := 272) (r := 200)
    (by rw [b800085a4_x10 hw₂, hspw₁]; addr_omega [hb1])
    (by rw [b800085a4_x11 hw₂, hspw₁]; addr_omega [hb1])
    (by rw [b800085a4_x12 hw₂, hspw₁]; addr_omega [hb1])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  swap
  · exact ⟨w₃, hrw₁.trans hrw₃, Or.inr hd⟩
  rw [hwt, hsd, hd₁] at hvw₃
  have nw₃ : heapNext w₃ = heapNext w₂ := by
    simp only [heapNext]
    rw [hfw₃ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1]]
  have Fw₃ : DFrame v w₃ (TW s v w₃) := (Fw₂.mono fun _ ha ↦ TW.mono nw₃.ge ha).trans hfw₃
    fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
  have hspw₃ : w₃.getReg .x2 = s.getReg .x2 - 496 := (hpw₃.reg .x2).trans hspw₂
  -- `0x800085dc`: the terminal's limbs, the next cursor, the count
  obtain ⟨w₄, hrw₄, hw₄⟩ := Sym.BlockSpec.reaches b800085dc_spec
    (by rw [hpcw₃, returnAddress_eq, b800085a4_x1 hw₂]; decide) (by
      rv_eval [hspw₃]; and_intros <;> valid_access hval [hb1])
  have kw₄ := b800085dc_keeps hw₄
  have hmw₄ := b800085dc_mem_same hw₄
  have nw₄ : heapNext w₄ = heapNext v := by simp only [heapNext, hmw₄]; exact nw₃.trans nw₂'
  have Fw₄ : DFrame v w₄ (TW s v w₄) := (Fw₃.mono fun _ ha ↦ TW.mono (by rw [nw₄, nw₃, nw₂'])
    ha).trans (DFrame.of_same hmw₄ _) fun _ h ↦ h
  have Fu₄ := tw_comp h.frame Fw₄ h.mono nw₄.ge
  have hheap₄ : HeapOk w₄ := ⟨nw₄ ▸ h.heap.lo, nw₄ ▸ h.heap.hi⟩
  have R (r : Reg) (hr : r ∈ ([.x2, .x21, .x22, .x24, .x25, .x27] : List Reg)) :
      w₃.getReg r = v.getReg r := by
    rw [hpw₃ r (by unfold calleeSaved; exact mem_of_mem hr _), kw₂ r (mem_of_mem hr _),
      hpw₁ r (by unfold calleeSaved; exact mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hx18₃ : w₃.getReg .x18 = BitVec.ofNat 64 (i + 1) := by
    rw [hpw₃.reg .x18, kw₂ .x18 (by decide), hpw₁.reg .x18, b80008578_x18 h₁, h.x18]
    addr_omega [hn12, hi]
  have hcnt : w₃.getMem (w₃.getReg .x2 + 104) = BitVec.ofNat 64 n := by
    rw [hspw₃, show s.getReg .x2 - 496 + 104 = s.getReg .x2 - 392 by addr_omega [hb1],
      ← hmw₄, Fu₄ _ (tw_slot hpre hheap₄ (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1])))]
    exact C.count
  have hlen' : i < (tItems s rows ws).length := by rw [C.len]; exact hi
  have hL : LoopAt s u₀ w₄ rows ws (i + 1) := {
    sp := (kw₄ .x2 (by decide)).trans ((R .x2 (by decide)).trans hsp)
    heap := hheap₄
    mono := nw₄ ▸ h.mono
    frame := Fu₄
    x18 := (kw₄ .x18 (by decide)).trans hx18₃
    x10 := by rw [b800085dc_x10 hw₄, R .x21 (by decide), h.x21, tAcc_step hlen']
    x22 := by rw [kw₄ .x22 (by decide), R .x22 (by decide)]; exact h.x22
    acc := by
      rw [tAcc_step hlen', limbs_add, h.acc, ← hvw₃, limbs_eAt, b800085dc_x25 hw₄,
        b800085dc_x24 hw₄, b800085dc_x27 hw₄, hspw₃, R .x25 (by decide), R .x24 (by decide),
        R .x27 (by decide)]
      rv_eval []
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ac_rfl
    cur := by rw [tAcc_step hlen']; exact h.cur }
  have hne : ∀ k, k < 2 ^ 64 → (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 k ↔ i + 1 = k) := by
    intro k hk
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt hk] at this
      exact this
    · intro e; rw [e]
  have hn64 : n < 2 ^ 64 := by have := (s.getReg .x12).isLt; omega
  by_cases hlast : i + 1 = n
  · exact ⟨w₄, hrw₁.trans (hrw₃.trans hrw₄), Or.inl ⟨Or.inr ⟨b800085dc_pc_taken hw₄
      (by rw [hx18₃, hcnt]; exact (hne n hn64).mpr hlast), hlast⟩, hL⟩⟩
  · exact ⟨w₄, hrw₁.trans (hrw₃.trans hrw₄), Or.inl ⟨Or.inl ⟨b800085dc_pc_not_taken hw₄
      (by rw [hx18₃, hcnt]; exact fun e ↦ hlast ((hne n hn64).mp e)), by omega⟩, hL⟩⟩

/-- One item, from the head back to it or to `0x800088e8`. -/
theorem itemStep (hMul : MulSpec) (hDot : DotSpec) (hA : AllocSpec) (hTA : TryAllocZeroedSpec)
    (hR : ReserveFreshSpec 0x80008a10 24 8) (hFE : FormEvaluateSpecE) {s u₀ u : MachineState}
    {rows : List (List E × List E)} {ws : List E} {W : Word} {n i : ℕ}
    (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) (hi : i < n)
    (L : LoopAt s u₀ u rows ws i) (hpc : u.pc = 0x80008600) :
    ∃ t, Reaches Image.code u t ∧ (((t.pc = 0x80008600 ∧ i + 1 < n) ∨
      (t.pc = 0x800088e8 ∧ i + 1 = n)) ∧ LoopAt s u₀ t rows ws (i + 1) ∨ Dead Image.code t) := by
  obtain ⟨v₁, hr₁, ⟨A, hpc₁⟩ | hd⟩ := headStep hpre C L hpc hi
  swap
  · exact ⟨v₁, hr₁, Or.inr hd⟩
  obtain ⟨v₂, hr₂, ⟨hpc₂, F⟩ | hd⟩ := sumStep hMul hDot hA hpre C hi A hpc₁
  swap
  · exact ⟨v₂, hr₁.trans hr₂, Or.inr hd⟩
  obtain ⟨v₃, hr₃, ⟨hpc₃, B⟩ | hd⟩ := formsA hTA hR hpre C hi F hpc₂
  swap
  · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  obtain ⟨v₄, hr₄, ⟨hpc₄, T⟩ | hd⟩ := formsB hFE hpre C hi F B hpc₃
  swap
  · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr hd⟩
  obtain ⟨t, hrt, ht⟩ := tailStep hMul hDot hpre C hi T hpc₄
  exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hrt))), ht⟩

/-- The loop: every item, to `0x800088e8`. -/
theorem termLoop (hMul : MulSpec) (hDot : DotSpec) (hA : AllocSpec) (hTA : TryAllocZeroedSpec)
    (hR : ReserveFreshSpec 0x80008a10 24 8) (hFE : FormEvaluateSpecE) {s u₀ : MachineState}
    {rows : List (List E × List E)} {ws : List E} {W : Word} {n : ℕ}
    (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) :
    ∀ k i u, n - i = k → i < n → u.pc = 0x80008600 → LoopAt s u₀ u rows ws i →
      ∃ t, Reaches Image.code u t ∧
        ((t.pc = 0x800088e8 ∧ LoopAt s u₀ t rows ws n) ∨ Dead Image.code t) := by
  intro k
  induction k with
  | zero => intro i u hk hi; omega
  | succ k ih =>
    intro i u hk hi hpc L
    obtain ⟨v, hr, ⟨⟨hpcv, hlt⟩ | ⟨hpcv, heq⟩, Lv⟩ | hd⟩ :=
      itemStep hMul hDot hA hTA hR hFE hpre C hi L hpc
    · obtain ⟨t, hrt, ht⟩ := ih (i + 1) v (by omega) hlt hpcv Lv
      exact ⟨t, hr.trans hrt, ht⟩
    · exact ⟨v, hr, Or.inl ⟨hpcv, heq ▸ Lv⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
