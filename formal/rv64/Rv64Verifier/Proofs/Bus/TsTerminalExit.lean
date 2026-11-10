import Rv64Verifier.Proofs.Bus.TsTerminal

/-!
# `table_sumcheck`: the terminal's check and `Ok(rows)`

```rust
require(terminal == claim, VerifierError::TableSumcheckTerminal)?;
Ok(rows)
```

`0x800088e8` compares the terminal's limbs with the claim's (`AtCompare`): a difference returns
`Err` through `0x80008928`, equality copies the rows' `Vec` to the result at `0x80008908` and
returns it (`okExit`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem zext_beq_zero {b : BitVec 8} (h : b ≠ 0) : (BitVec.zeroExtend 64 b == 0) = false := by
  apply beq_false_of_ne
  intro e
  apply h
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat e
  have hb := b.isLt
  simp at this ⊢
  omega

theorem limbs_zero' : Model.limbs (0 : E) = (0, 0, 0) := by
  rw [Model.limbs_zero]; rfl

/-- The rows, their header moved to `b`, kept by a frame that misses the heap allocated since the
entry. -/
theorem _root_.Rv64Verifier.Bus.RowsAt.move {s u t : MachineState} {a b : Word}
    {rows : List (List E × List E)} {w : Word → Prop} (h : RowsAt s u a rows) (hf : DFrame u t w)
    (hn : heapNext u ≤ heapNext t) (hc : vecCap t b = vecCap u a) (hp : vecPtr t b = vecPtr u a)
    (hl : vecLen t b = vecLen u a)
    (hb : ∀ x : Word, heapNext s ≤ x.toNat → x.toNat < heapNext u → ¬ w x)
    (hhi : heapNext u ≤ heapEnd) : RowsAt s t b rows := by
  have hv := h.vec
  have hfr := h.fresh
  have hlen := h.len
  simp only [heapEnd] at hhi
  obtain ⟨⟨hr1, hr2⟩, hvl⟩ := hv
  simp only [NewBuf] at hfr
  refine ⟨⟨?_, ?_⟩, ?_, ?_, fun i hi ↦ ?_⟩
  · simp only [RawVecOk, Buf, hc, hp]
    exact ⟨hr1, by omega⟩
  · rw [hc, hl]; exact hvl
  · simp only [NewBuf, hc, hp]; omega
  · rw [hl]; exact hlen
  · have hi' : i < (vecLen u a).toNat := by omega
    obtain ⟨h1, h2⟩ := h.pairs i hi
    have hR : (vecPtr u a).toNat + 48 * (vecCap u a).toNat ≤ heapNext u ∧
        heapNext s ≤ (vecPtr u a).toNat := by
      rcases hfr.2 with h0 | h0
      · omega
      · exact ⟨h0.2, h0.1⟩
    have miss (q : Word) (m : Nat) (hq : m = 0 ∨ heapNext s ≤ q.toNat ∧ q.toNat + m ≤ heapNext u) :
        ∀ j < m, ¬ w (q + BitVec.ofNat 64 j) := fun j hj ↦ by
      rcases hq with h0 | ⟨h1, h2⟩
      · omega
      · exact hb _ (by addr_omega [h1, h2, hj, hhi]) (by addr_omega [h1, h2, hj, hhi])
    have inner (x : List E) (k : Nat) (hk : k + 24 ≤ 48 * (vecLen u a).toNat)
        (hx : NewVecE s u (vecPtr u a + BitVec.ofNat 64 k) x) :
        NewVecE s t (vecPtr t b + BitVec.ofNat 64 k) x := by
      rw [hp]
      have hb' := hx.buf
      have hvl' := hx.vec.len
      simp only [NewBuf] at hb'
      exact hx.dframe hf hn
        (miss _ 24 (Or.inr ⟨by addr_omega [hR.2, hR.1, hk, hvl, hhi],
          by addr_omega [hR.2, hR.1, hk, hvl, hhi]⟩))
        (miss _ _ (by rcases hb'.2 with h0 | h0 <;> omega))
    exact ⟨inner _ (48 * i) (by omega) h1, inner _ (48 * i + 24) (by omega) h2⟩

/-- `Ok(rows)` at `0x8000893c`: the function returns it. -/
theorem okExit {s u : MachineState} {rows : List (List E × List E)} (hpre : TableSumcheckPre s)
    (h : Inv s u) (hpc : u.pc = 0x8000893c) (hrows : RowsAt s u (s.getReg .x10) rows)
    (hcap : vecCap u (s.getReg .x10) ≠ errNiche)
    (hsome : ∀ T, TranscriptAt s (tsSelf s) T → ∃ T', (mirror s).run T = some (rows, T') ∧
      TranscriptAt u (tsSelf s) T') :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  obtain ⟨t, hr, hpc', hp, hm⟩ := epilogue hpre h hpc
  have hn : heapNext t = heapNext u := by simp only [heapNext, hm]
  have hf : DFrame u t fun _ ↦ False := DFrame.of_same hm _
  refine ⟨t, hr, Or.inl ⟨hpc', hp, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn ▸ h.mono,
    fun T hT ↦ ?_, fun a ha ↦ ?_⟩⟩
  · obtain ⟨T', e, hT'⟩ := hsome T hT
    simp only [mirror] at e
    rw [e]
    exact ⟨by rw [vecCap, hm]; exact hcap,
      hrows.move hf hn.ge (by simp only [vecCap, hm]) (by simp only [vecPtr, hm])
        (by simp only [vecLen, hm]) (fun _ _ _ h ↦ h) h.heap.hi,
      hf.transcriptAt hT' (h.tok hpre) (fun _ _ h ↦ h) (fun _ _ h ↦ h) (fun _ _ h ↦ h)
        (fun _ _ h ↦ h)⟩
  · rw [hm a]
    exact h.frame a fun i hi hw ↦ ha i hi (W.mono hn.ge hw)

/-- At `0x800088e8`: the terminal's limbs in `s9`, `s8`, `s11`, the rows at `S - 296`. -/
structure AtCompare (s t : MachineState) (ch : List E) (cl : E) (P : Word)
    (rows : List (List E × List E)) : Prop where
  inv : Inv s t
  kept : Kept s t cl P
  rowsAt : RowsAt s t (s.getReg .x2 - 296) rows
  acc : Model.limbs (terminalOf s rows (weightsOf s ch)) =
    (t.getReg .x25, t.getReg .x24, t.getReg .x27)
  run : ∀ T, TranscriptAt s (tsSelf s) T → ∃ T₁ T₂,
    (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T₁) ∧ (readRowsM ch.reverse (rowItems s) []).run T₁ = some (rows, T₂) ∧
      TranscriptAt t (tsSelf s) T₂

/-- `Ok(rows)`, from `0x80008908`. -/
theorem okPath {s t t₃ : MachineState} {ch : List E} {cl : E} {P : Word}
    {rows : List (List E × List E)} (hpre : TableSumcheckPre s) (A : AtCompare s t ch cl P rows)
    (heq : terminalOf s rows (weightsOf s ch) = cl) (hm₃ : ∀ a, t₃.getMem a = t.getMem a)
    (hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 496) (hpc : t₃.pc = 0x80008908) :
    ∃ t', Reaches Image.code t₃ t' ∧ Done s t' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I₃ : Inv s t₃ := A.inv.same hpre hm₃ (hsp₃.trans A.inv.sp.symm)
  have ho := hpre.out
  have os := hpre.outStack
  have ox := hpre.outFree
  simp only [stack_eq] at os
  have hout : t₃.getMem (s.getReg .x2 - 456) = s.getReg .x10 := by rw [hm₃]; exact A.kept.out
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008908_spec hpc (by
    rv_eval [hsp₃, hout]
    and_intros <;> first
      | valid_access hval [hb1]
      | exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho]) (by addr_omega [ho]))
  have hf₄ : DFrame t₃ t₄ (Within · (s.getReg .x10) 24) := fun a ha ↦
    h₄.2.2.2 a (by
      rv_eval [hsp₃, hout]
      have h0 := ha 0 (by decide)
      rw [add_ofNat_zero] at h0
      exact ⟨fun e ↦ h0 (by rw [e]; addr_omega [ho]), fun e ↦ h0 (by rw [e]; addr_omega [ho]),
        fun e ↦ h0 (by rw [e]; addr_omega [ho])⟩)
  have hn₄ : heapNext t₄ = heapNext t₃ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf₄ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, ox.2])
  have I₄ : Inv s t₄ := I₃.step hpre hf₄ (fun a ha ↦ ⟨Or.inl ha, by addr_omega [ha, os, hb1]⟩)
    ⟨hn₄ ▸ I₃.heap.lo, hn₄ ▸ I₃.heap.hi⟩ hn₄.ge (b80008908_keeps h₄ .x2 (by decide))
  have word (k : Word) (hk : k = 0 ∨ k = 8 ∨ k = 16) :
      t₄.getMem (s.getReg .x10 + k) = t.getMem (s.getReg .x2 - 296 + k) := by
    have m0 := b80008908_m0 h₄
    have m1 := b80008908_m1 h₄
    have m2 := b80008908_m2 h₄
    rw [hsp₃] at m0 m1 m2
    rv_eval [hout] at m0 m1 m2
    rcases hk with rfl | rfl | rfl
    · rw [Sym.add_zero_lit, Sym.add_zero_lit, m2, hm₃]
    · rw [m1, hm₃]; congr 1; addr_omega [hb1]
    · rw [m0, hm₃]; congr 1; addr_omega [hb1]
  have hc : vecCap t₄ (s.getReg .x10) = vecCap t (s.getReg .x2 - 296) := by
    have := word 0 (Or.inl rfl)
    rw [Sym.add_zero_lit, Sym.add_zero_lit] at this
    exact this
  have hft : DFrame t t₄ (Within · (s.getReg .x10) 24) :=
    (DFrame.of_same hm₃ _).trans hf₄ fun _ h ↦ h
  have hhi := A.inv.heap.hi
  have hrows : RowsAt s t₄ (s.getReg .x10) rows :=
    A.rowsAt.move hft (by rw [hn₄]; simp only [heapNext, hm₃]; exact le_refl _) hc
      (word 8 (Or.inr (Or.inl rfl))) (word 16 (Or.inr (Or.inr rfl)))
      (fun x h1 h2 hw ↦ by
        simp only [Outside, heapEnd] at ox hhi
        addr_omega [hw, h1, h2, ox.1, hhi]) hhi
  have hcap : vecCap t₄ (s.getReg .x10) ≠ errNiche := by
    rw [hc]
    intro e
    have hfr := A.rowsAt.fresh
    simp only [NewBuf, heapEnd] at hfr hhi
    rw [e] at hfr
    simp only [errNiche, Sym.wordToNatLit] at hfr
    omega
  obtain ⟨e0, e1, e2⟩ := A.inv.stream hpre
  have so := hpre.selfOut
  have hS := hpre.self.self
  have po := hpre.proofOut
  simp only [ProofApart] at po
  have hsome (T : TState) (hT : TranscriptAt s (tsSelf s) T) : ∃ T', (mirror s).run T =
      some (rows, T') ∧ TranscriptAt t₄ (tsSelf s) T' := by
    obtain ⟨T₁, T₂, h1, h2, hT₂⟩ := A.run T hT
    refine ⟨T₂, by rw [mirror_run s h1 h2]; simp only [heq, ↓reduceIte], ?_⟩
    exact hft.transcriptAt hT₂ (A.inv.tok hpre) (fun y hy hw ↦ by addr_omega [hy, hw, so])
      (by rw [e0]; exact fun y hy hw ↦ by addr_omega [hy, hw, po.1])
      (by rw [e1, e2]; exact fun y hy hw ↦ by addr_omega [hy, hw, po.2])
      (fun y hy hw ↦ by addr_omega [hy, hw, so, hS])
  obtain ⟨t', hr', ht'⟩ := okExit hpre I₄ (b80008908_pc h₄) hrows hcap hsome
  exact ⟨t', hr₄.trans hr', ht'⟩

/-- The comparison at `0x800088e8`, to the function's return. -/
theorem finishF {s t : MachineState} {ch : List E} {cl : E} {P : Word}
    {rows : List (List E × List E)} (hpre : TableSumcheckPre s) (A : AtCompare s t ch cl P rows)
    (hpc : t.pc = 0x800088e8) :
    ∃ t', Reaches Image.code t t' ∧ Done s t' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := A.inv
  have hsp := I.sp
  have hcl := A.kept.claim
  have hnone (hne : terminalOf s rows (weightsOf s ch) ≠ cl) :
      ∀ T, TranscriptAt s (tsSelf s) T → (mirror s).run T = none := fun T hT ↦ by
    obtain ⟨T₁, T₂, h1, h2, -⟩ := A.run T hT
    rw [mirror_run s h1 h2]
    simp only [hne, ↓reduceIte]
  have hlimb := A.acc
  have e (k : Word) (hk : k = 8 ∨ k = 16 ∨ k = 32) :
      t.getReg .x2 + k = s.getReg .x2 - (496 - k) := by
    rw [hsp]; rcases hk with rfl | rfl | rfl <;> addr_omega [hb1]
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800088e8_spec hpc (by
    rv_eval [hsp]; valid_access hval [hb1])
  have hm₁ := b800088e8_mem_same h₁
  have k₁ := b800088e8_keeps h₁
  have hx10₁ := b800088e8_x10 h₁
  have I₁ : Inv s t₁ := I.same hpre hm₁ (k₁ .x2 (by decide))
  have hout₁ : t₁.getMem (s.getReg .x2 - 456) = s.getReg .x10 := by rw [hm₁]; exact A.kept.out
  have m32 : t.getMem (t.getReg .x2 + 32) = t.getMem (s.getReg .x2 - 464) := by
    rw [e 32 (Or.inr (Or.inr rfl))]; rfl
  by_cases h0 : t.getReg .x25 = t.getMem (s.getReg .x2 - 464)
  swap
  · obtain ⟨t', hr', ht'⟩ := err928 hpre I₁ (b800088e8_pc_taken h₁ (by rw [m32]; exact h0)) hout₁
      (Or.inl hx10₁) (hnone fun he ↦ h0 (by
        have := congrArg Model.limbs he; rw [hlimb, hcl] at this; exact (Prod.mk.inj this).1))
    exact ⟨t', hr₁.trans hr', ht'⟩
  have hpc₁ := b800088e8_pc_not_taken h₁ (by rw [m32]; exact h0)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800088f8_spec hpc₁ (by
    rv_eval [hsp₁]; valid_access hval [hb1])
  have hm₂ := b800088f8_mem_same h₂
  have k₂ := b800088f8_keeps h₂
  have I₂ : Inv s t₂ := I₁.same hpre hm₂ (k₂ .x2 (by decide))
  have m16 : t₁.getMem (t₁.getReg .x2 + 16) = t.getMem (s.getReg .x2 - 480) := by
    rw [k₁ .x2 (by decide), e 16 (Or.inr (Or.inl rfl)), hm₁]; rfl
  have hx24₁ : t₁.getReg .x24 = t.getReg .x24 := k₁ .x24 (by decide)
  by_cases h1 : t.getReg .x24 = t.getMem (s.getReg .x2 - 480)
  swap
  · obtain ⟨t', hr', ht'⟩ := err928 hpre I₂ (b800088f8_pc_taken h₂ (by rw [m16, hx24₁]; exact h1))
      (by rw [hm₂]; exact hout₁) (Or.inl (by rw [k₂ .x10 (by decide)]; exact hx10₁))
      (hnone fun he ↦ h1 (by
        have := congrArg Model.limbs he; rw [hlimb, hcl] at this
        exact (Prod.mk.inj (Prod.mk.inj this).2).1))
    exact ⟨t', hr₁.trans (hr₂.trans hr'), ht'⟩
  have hpc₂ := b800088f8_pc_not_taken h₂ (by rw [m16, hx24₁]; exact h1)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 496 := (k₂ .x2 (by decide)).trans hsp₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008900_spec hpc₂ (by
    rv_eval [hsp₂]; valid_access hval [hb1])
  have hm₃ := b80008900_mem_same h₃
  have k₃ := b80008900_keeps h₃
  have m8 : t₂.getMem (t₂.getReg .x2 + 8) = t.getMem (s.getReg .x2 - 488) := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide), e 8 (Or.inl rfl), hm₂, hm₁]; rfl
  have hx27₂ : t₂.getReg .x27 = t.getReg .x27 := by rw [k₂ .x27 (by decide), k₁ .x27 (by decide)]
  by_cases h2 : t.getReg .x27 = t.getMem (s.getReg .x2 - 488)
  swap
  · have I₃ : Inv s t₃ := I₂.same hpre hm₃ (k₃ .x2 (by decide))
    obtain ⟨t', hr', ht'⟩ := err928 hpre I₃ (b80008900_pc_taken h₃ (by rw [m8, hx27₂]; exact h2))
      (by rw [hm₃, hm₂]; exact hout₁)
      (Or.inl (by rw [k₃ .x10 (by decide), k₂ .x10 (by decide)]; exact hx10₁))
      (hnone fun he ↦ h2 (by
        have := congrArg Model.limbs he; rw [hlimb, hcl] at this
        exact (Prod.mk.inj (Prod.mk.inj this).2).2))
    exact ⟨t', hr₁.trans (hr₂.trans (hr₃.trans hr')), ht'⟩
  have hpc₃ := b80008900_pc_not_taken h₃ (by rw [m8, hx27₂]; exact h2)
  have heq : terminalOf s rows (weightsOf s ch) = cl :=
    eq_of_limbs (by rw [hlimb, hcl, h0, h1, h2])
  obtain ⟨t', hr', ht'⟩ := okPath hpre A heq (fun a ↦ by rw [hm₃, hm₂, hm₁])
    ((k₃ .x2 (by decide)).trans hsp₂) hpc₃
  exact ⟨t', hr₁.trans (hr₂.trans (hr₃.trans hr')), ht'⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
