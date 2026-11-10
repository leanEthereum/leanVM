import Rv64Verifier.Proofs.Bus.TsTerminalJump

/-!
# `table_sumcheck`: the forms' values

```rust
let form_values: Vec<E> = forms.iter().map(|form| form.evaluate(evaluations)).collect();
```

The loop at `0x80008898` (`evalLoop`) calls `Form::evaluate` on each form into `sp + 344` and
copies the value into the buffer; it reaches `0x80008578`. `Form::evaluate`'s contract is taken
with either slice possibly empty, and then anywhere (`FormEvaluateSpecE`): an empty form's terms
and an empty row hold a dangling pointer, which `FormEvaluatePre` does not allow.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `FormEvaluatePre` with an empty slice of terms or columns anywhere. -/
structure FormEvaluatePreE (s : MachineState) : Prop where
  ret : Region (s.getReg .x10) 24
  terms : 48 * (s.getReg .x12).toNat = 0 ∨ Region (s.getReg .x11) (48 * (s.getReg .x12).toNat)
  columns : 24 * (s.getReg .x14).toNat = 0 ∨ Region (s.getReg .x13) (24 * (s.getReg .x14).toNat)
  stack : RtStack s formEvaluateStack
  retStack : Apart (s.getReg .x10) 24 (stackLo s formEvaluateStack) formEvaluateStack
  termsStack : Apart (s.getReg .x11) (48 * (s.getReg .x12).toNat) (stackLo s formEvaluateStack)
    formEvaluateStack
  columnsStack : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (stackLo s formEvaluateStack)
    formEvaluateStack
  rodata : RodataOk s
  retRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize

abbrev FormEvaluateSpecE : Prop := FunSpec Image.code 0x80010924 FormEvaluatePreE FormEvaluatePost

/-- The terms whose bytes miss a frame keep their value. -/
theorem _root_.Rv64Verifier.Transcript.DFrame.termsAt {s t : MachineState} {w : Word → Prop}
    (h : DFrame s t w) {p : Word} {n : Nat} (hp : ∀ i < 48 * n, ¬ w (p + BitVec.ofNat 64 i)) :
    termsAt t p n = termsAt s p n := by
  unfold Rv64Verifier.Bus.termsAt
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  have e (o : Nat) (ho : o + 8 ≤ 48) : t.getMem (p + BitVec.ofNat 64 (48 * k) + BitVec.ofNat 64 o) =
      s.getMem (p + BitVec.ofNat 64 (48 * k) + BitVec.ofNat 64 o) :=
    h _ fun i hi ↦ by rw [add_ofNat_add, add_ofNat_add]; exact hp _ (by omega)
  have e0 := e 0 (by omega)
  have e8 := e 8 (by omega)
  have e16 := e 16 (by omega)
  simp only [add_ofNat_zero] at e0
  have he : eAt t (p + BitVec.ofNat 64 (48 * k) + 24) = eAt s (p + BitVec.ofNat 64 (48 * k) + 24) :=
    h.eAt fun i hi ↦ by
      rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, add_ofNat_add, add_ofNat_add]
      exact hp _ (by omega)
  rw [he]
  congr 1
  simp only [monoAt, e0]
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, e8,
    show (16 : Word) = BitVec.ofNat 64 16 from rfl, e16]

theorem formEvaluateRust_toSpec (f : LayoutMirror.FormRust) (column : List E) :
    formEvaluateRust f.toSpec column = f.evaluate column := by
  rw [formEvaluateRust_eq, LayoutMirror.FormRust.evaluate_eq]

/-- What the evaluation loop writes: the result at `sp + 344`, the callees' stacks, the values. -/
def EW (s : MachineState) (VP : Word) (FL : ℕ) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 152) 24 ∨ Within a (s.getReg .x2 - 2128) 1632 ∨ Within a VP (24 * FL)

/-- The loop at `0x80008898`, `j` values copied to the buffer at `VP`: it reaches `0x80008578`
with every form's value. -/
theorem evalLoop (hFE : FormEvaluateSpecE) {s v : MachineState} {FP VP RW EP EL : Word} {FL : ℕ}
    {ev : List E} (hpre : TableSumcheckPre s) (I : Inv s v)
    (hhdr : RO s tableSumcheckStack (tsWrites s) (tsSelf s) FP (24 * FL))
    (hterm : ∀ k < FL, RO s tableSumcheckStack (tsWrites s) (tsSelf s)
      (vecPtr s (FP + BitVec.ofNat 64 (24 * k)))
      (48 * (vecLen s (FP + BitVec.ofNat 64 (24 * k))).toNat))
    (hV1 : 0x20000000 ≤ VP.toNat) (hV2 : VP.toNat + 24 * FL ≤ heapNext v)
    (hV3 : VP.toNat % 8 = 0) (hVs : heapNext s ≤ VP.toNat)
    (hRW1 : 0x20000000 ≤ RW.toNat) (hRW2 : RW.toNat + 48 ≤ VP.toNat) (hRW3 : RW.toNat % 8 = 0)
    (hEP : v.getMem (RW + 32) = EP) (hEL : v.getMem (RW + 40) = EL) (hE3 : EP.toNat % 8 = 0)
    (hEb : EL.toNat = 0 ∨ 0x20000000 ≤ EP.toNat ∧ EP.toNat + 24 * EL.toNat ≤ VP.toNat)
    (hev : eListAt v EP EL.toNat = ev) :
    ∀ m j (x : MachineState), FL - j = m → j < FL → x.pc = 0x80008898 →
      x.getReg .x2 = s.getReg .x2 - 496 →
      x.getReg .x23 = FP + BitVec.ofNat 64 (24 * j + 16) →
      x.getReg .x9 = VP + BitVec.ofNat 64 (24 * j) →
      x.getReg .x20 = FP + BitVec.ofNat 64 (24 * FL + 16) → x.getReg .x19 = RW →
      DFrame v x (EW s VP FL) → heapNext x = heapNext v →
      (∀ k < j, eAt x (VP + BitVec.ofNat 64 (24 * k)) =
        (formAt s (FP + BitVec.ofNat 64 (24 * k))).evaluate ev) →
      ∃ t, Reaches Image.code x t ∧ ((t.pc = 0x80008578 ∧ t.getReg .x2 = s.getReg .x2 - 496 ∧
        DFrame v t (EW s VP FL) ∧ heapNext t = heapNext v ∧
        (∀ k < FL, eAt t (VP + BitVec.ofNat 64 (24 * k)) =
          (formAt s (FP + BitVec.ofNat 64 (24 * k))).evaluate ev) ∧
        ∀ r ∈ ([.x8, .x18, .x21, .x22, .x24, .x25, .x26, .x27] : List Reg),
          t.getReg r = x.getReg r) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hhv := I.heap.hi
  simp only [heapEnd] at hhv
  have hRv : ValidMemRange RW 6 := heap_range (by omega) (by omega) hRW3
  have hVv : ValidMemRange VP (3 * FL) := heap_range (by omega) (by omega) hV3
  have hHv : ValidMemRange FP (3 * FL) :=
    RO.range (by rw [show 8 * (3 * FL) = 24 * FL by ring]; exact hhdr)
  have hHb := hhdr.bound
  have hHm : FL = 0 ∨ FP.toNat + 24 * FL ≤ 0xc0000000 := by
    rcases hhdr.region with h0 | h0
    · left; omega
    · right; simp only [Region, Mapped] at h0; omega
  have hHs := hhdr.stack
  rw [stackLo_eq, stack_eq] at hHs
  -- `Inv` and the row along the loop
  have Ix (x : MachineState) (hf : DFrame v x (EW s VP FL)) (hn : heapNext x = heapNext v)
      (hsp : x.getReg .x2 = s.getReg .x2 - 496) : Inv s x := by
    have hm := I.mono
    refine I.step hpre hf (fun a ha ↦ ?_) ⟨hn ▸ I.heap.lo, hn ▸ I.heap.hi⟩ hn.ge
      (hsp.trans I.sp.symm)
    rcases ha with ha | ha | ha
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1])))),
        by addr_omega [ha, hb1]⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1])))),
        by addr_omega [ha, hb1]⟩
    · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))),
        by addr_omega [ha, hb1, hhv, hV2]⟩
      · simp only [Within] at ha; omega
      · simp only [Within] at ha; rw [hn]; omega
  have old (x : MachineState) (hf : DFrame v x (EW s VP FL)) (a : Word) (h1 : 0x20000000 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ VP.toNat) : x.getMem a = v.getMem a :=
    hf a fun j hj hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hj, h1, h2, hb1, hhv, hV2]
  intro m
  induction m with
  | zero => intro j x hm hj; omega
  | succ m ih =>
    intro j x hm hj hpc hsp h23 h9 h20 h19 hf hn hvals
    have Ix₀ := Ix x hf hn hsp
    -- `0x80008898`: the form's terms, the row, `Form::evaluate`
    obtain ⟨x₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008898_spec hpc (by
      rv_eval [h23, h19]
      and_intros <;> first
        | valid_access hHv [hHb, hj]
        | valid_access hRv [hRW1, hRW2])
    have k₁ := b80008898_keeps h₁
    have hm₁ := b80008898_mem_same h₁
    have hsp₁ : x₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
    have Ix₁ : Inv s x₁ := Ix₀.same hpre hm₁ (k₁ .x2 (by decide))
    have hx11 : x₁.getReg .x11 = vecPtr s (FP + BitVec.ofNat 64 (24 * j)) := by
      rw [b80008898_x11 h₁, h23]
      simp only [vecPtr]
      rw [← Ix₀.word hhdr (x := FP + BitVec.ofNat 64 (24 * j) + 8) (by addr_omega [hHb, hj])
        (by addr_omega [hHb, hj])]
      exact congrArg _ (by addr_omega [hHb, hj])
    have hx12 : x₁.getReg .x12 = vecLen s (FP + BitVec.ofNat 64 (24 * j)) := by
      rw [b80008898_x12 h₁, h23]
      simp only [vecLen]
      rw [← Ix₀.word hhdr (x := FP + BitVec.ofNat 64 (24 * j) + 16) (by addr_omega [hHb, hj])
        (by addr_omega [hHb, hj])]
      exact congrArg _ (by addr_omega [hHb, hj])
    have hx13 : x₁.getReg .x13 = EP := by
      rw [b80008898_x13 h₁, h19, old x hf _ (by addr_omega [hRW1, hRW2, hV2, hhv])
        (by addr_omega [hRW1, hRW2, hV2, hhv]), hEP]
    have hx14 : x₁.getReg .x14 = EL := by
      rw [b80008898_x14 h₁, h19, old x hf _ (by addr_omega [hRW1, hRW2, hV2, hhv])
        (by addr_omega [hRW1, hRW2, hV2, hhv]), hEL]
    have hx10 : x₁.getReg .x10 = s.getReg .x2 - 152 := by
      rw [b80008898_x10 h₁, hsp]; addr_omega [hb1]
    have hT := hterm j hj
    have hTs := hT.stack
    rw [stackLo_eq, stack_eq] at hTs
    have hsl : stackLo x₁ formEvaluateStack = s.getReg .x2 - 1664 := by
      simp only [stackLo, formEvaluateStack, mulStack, Nat.reduceAdd, hsp₁]; addr_omega [hb1]
    have hrs := hpre.stack.rodata
    simp only [stack_eq] at hrs
    have pre : FormEvaluatePreE x₁ := {
      ret := by
        rw [hx10]; simp only [Region, Mapped]
        exact ⟨Or.inr ⟨by addr_omega [hb1], by addr_omega [hb1, hb2]⟩, by addr_omega [hb1, hb3]⟩
      terms := by rw [hx11, hx12]; exact hT.region
      columns := by
        rw [hx14, hx13]
        rcases hEb with h0 | h0
        · exact Or.inl (by omega)
        · right; simp only [Region, Mapped]; exact ⟨Or.inl ⟨by omega, by omega⟩, hE3⟩
      stack := hpre.stack.sub 496 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
      retStack := by rw [hx10, hsl]; addr_omega [hb1]
      termsStack := by rw [hx11, hx12, hsl]; addr_omega [hTs, hb1]
      columnsStack := by
        rw [hx13, hx14, hsl]
        rcases hEb with h0 | h0 <;> addr_omega [h0, hb1, hhv, hV2]
      rodata := Ix₁.rodata hpre
      retRodata := by rw [hx10]; addr_omega [hrs, hb1] }
    obtain ⟨x₂, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hFE.call hr₁ (b80008898_pc h₁) pre
    swap
    · exact ⟨x₂, hr₂, Or.inr hd⟩
    have hf₂ := post.frame
    rw [hx10, hsl] at hf₂
    have hval₂ : eAt x₂ (s.getReg .x2 - 152) =
        (formAt s (FP + BitVec.ofNat 64 (24 * j))).evaluate ev := by
      rw [← hx10, post.value, hx11, hx12, hx13, hx14, ← hev,
        Ix₁.frame.termsAt ((Ix₁.miss hT).bytes (Nat.le_refl _) (Nat.le_refl _) hT.bound)]
      simp only [formAt]
      congr 1
      exact (hf.trans (DFrame.of_same hm₁ _) fun _ h ↦ h).eListAt fun k hk hw ↦ by
        rcases hEb with h0 | h0
        · omega
        · rcases hw with hw | hw | hw <;> addr_omega [hw, hk, h0, hb1, hhv, hV2]
    have hsp₂ : x₂.getReg .x2 = s.getReg .x2 - 496 := (hp₂.reg .x2).trans hsp₁
    -- `0x800088b4`: the value to the buffer
    have hx9₂ : x₂.getReg .x9 = VP + BitVec.ofNat 64 (24 * j) := by
      rw [hp₂.reg .x9, k₁ .x9 (by decide), h9]
    obtain ⟨x₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800088b4_spec
      (by rw [hpc₂, returnAddress_eq, b80008898_x1 h₁]; decide) (by
        rv_eval [hsp₂, hx9₂]
        and_intros <;> first
          | valid_access hval [hb1]
          | valid_access hVv [hV1, hV2, hj]
          | addr_omega [hV1, hV2, hj, hb1, hhv])
    have k₃ := b800088b4_keeps h₃
    have hf₃ := DFrame.of_memFrame (b800088b4_frame h₃ (by rw [hx9₂]; addr_omega [hV2, hj, hhv]))
    rw [hx9₂] at hf₃
    have hnew : eAt x₃ (VP + BitVec.ofNat 64 (24 * j)) =
        (formAt s (FP + BitVec.ofNat 64 (24 * j))).evaluate ev := by
      have m0 := b800088b4_m_x9_0 h₃
      have m1 := b800088b4_m_x9_8 h₃
      have m2 := b800088b4_m_x9_16 h₃
      rw [hx9₂, hsp₂] at m0 m1 m2
      rv_eval [] at m0 m1 m2
      rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2])]
      exact hval₂
    have hf' : DFrame v x₃ (EW s VP FL) :=
      ((hf.trans (DFrame.of_same hm₁ _) fun _ h ↦ h).trans hf₂ fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))).trans hf₃
        fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hj, hV2, hhv]))
    have hn₃ : heapNext x₃ = heapNext v := by
      simp only [heapNext]
      rw [hf' _ fun k hk hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hk, hb1, hhv, hV2]]
    have hvals' (k : ℕ) (hk : k < j + 1) : eAt x₃ (VP + BitVec.ofNat 64 (24 * k)) =
        (formAt s (FP + BitVec.ofNat 64 (24 * k))).evaluate ev := by
      rcases Nat.lt_or_ge k j with hk' | hk'
      · rw [hf₃.eAt fun i hi hw ↦ by addr_omega [hw, hi, hk', hj, hV2, hhv],
          hf₂.eAt fun i hi hw ↦ by
            rcases hw with hw | hw <;> addr_omega [hw, hi, hk', hj, hV1, hV2, hhv, hb1],
          (DFrame.of_same hm₁ fun _ ↦ False).eAt fun _ _ h ↦ h]
        exact hvals k hk'
      · have : k = j := by omega
        subst this
        exact hnew
    have R (r : Reg) (hr : r ∈ ([.x8, .x18, .x21, .x22, .x24, .x25, .x26, .x27] : List Reg)) :
        x₃.getReg r = x.getReg r := by
      rw [k₃ r (mem_of_mem hr _), hp₂ r (by unfold calleeSaved; exact mem_of_mem hr _),
        k₁ r (mem_of_mem hr _)]
    have hx23₂ : x₂.getReg .x23 = FP + BitVec.ofNat 64 (24 * j + 16) := by
      rw [hp₂.reg .x23, k₁ .x23 (by decide), h23]
    have hx20₂ : x₂.getReg .x20 = FP + BitVec.ofNat 64 (24 * FL + 16) := by
      rw [hp₂.reg .x20, k₁ .x20 (by decide), h20]
    have hreach := hr₂.trans hr₃
    by_cases hlast : j + 1 = FL
    · have hpc₃ := b800088b4_pc_not_taken h₃ (by rw [hx23₂, hx20₂]; addr_omega [hHm, hj, hlast])
      obtain ⟨x₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800088d8_spec hpc₃ trivial
      have hm₄ := b800088d8_mem_same h₄
      have k₄ := b800088d8_keeps h₄
      refine ⟨x₄, hreach.trans hr₄, Or.inl ⟨b800088d8_pc h₄,
        (k₄ .x2 (by decide)).trans ((k₃ .x2 (by decide)).trans hsp₂),
        (hf'.trans (DFrame.of_same hm₄ _) fun _ h ↦ h), by rw [← hn₃]; simp only [heapNext, hm₄],
        fun k hk ↦ ?_, fun r hr ↦ (k₄ r (mem_of_mem hr _)).trans (R r hr)⟩⟩
      rw [(DFrame.of_same hm₄ fun _ ↦ False).eAt fun _ _ h ↦ h]
      exact hvals' k (by omega)
    · have hpc₃ := b800088b4_pc_taken h₃ (by rw [hx23₂, hx20₂]; addr_omega [hHm, hlast, hj])
      obtain ⟨t, hrt, ht⟩ := ih (j + 1) x₃ (by omega) (by omega) hpc₃
        ((k₃ .x2 (by decide)).trans hsp₂)
        (by rw [b800088b4_x23 h₃, hx23₂]; addr_omega [hHm, hj, hlast])
        (by rw [b800088b4_x9 h₃, hx9₂]; addr_omega [hV2, hj, hhv])
        (by rw [k₃ .x20 (by decide), hx20₂])
        (by rw [k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide), h19])
        hf' hn₃ hvals'
      refine ⟨t, hreach.trans hrt, ?_⟩
      rcases ht with ⟨a1, a2, a3, a4, a5, a6⟩ | hd
      · exact Or.inl ⟨a1, a2, a3, a4, a5, fun r hr ↦ (a6 r hr).trans (R r hr)⟩
      · exact Or.inr hd

end Rv64Verifier.Proofs.Bus.TableSumcheck
