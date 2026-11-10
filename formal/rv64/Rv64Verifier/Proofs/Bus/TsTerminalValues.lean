import Rv64Verifier.Proofs.Bus.TsTerminalForms

/-!
# `table_sumcheck`: the forms' values' buffer

`0x8000880c` reads the item's `Vec<Form>`, allocates the values' buffer (`try_allocate_in`, then
`reserve`) at `sp + 296`, and runs the evaluation loop (`evalLoop`); it reaches `0x80008578`
(`AtTail`) with the values in `s0` and their number in `s10`.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the values write from `v` on: `sp + 296` up to `sp + 368`, the callees' stacks, `NEXT`
and the heap allocated. -/
def VW (s v w : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 200) 72 ∨ Within a (s.getReg .x2 - 2128) 1632 ∨ Within a nextAddr 8 ∨
    Fresh v w a

theorem VW.mono {s v w x : MachineState} (h : heapNext w ≤ heapNext x) {a : Word}
    (ha : VW s v w a) : VW s v x a := by
  rcases ha with ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))

theorem vw_tw {s u₀ v w : MachineState} (hpre : TableSumcheckPre s)
    (h₁ : DFrame u₀ v (TW s u₀ v)) (h₂ : DFrame v w (VW s v w)) (hm₁ : heapNext u₀ ≤ heapNext v)
    (hm₂ : heapNext v ≤ heapNext w) : DFrame u₀ w (TW s u₀ w) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  refine (h₁.mono fun _ ha ↦ TW.mono hm₂ ha).trans h₂ fun a ha ↦ ?_
  rcases ha with ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))

/-- At `0x80008578`: the item's form values in `s0`, their number in `s10`. -/
structure AtTail (s u₀ v : MachineState) (rows : List (List E × List E)) (ws : List E) (i : ℕ) :
    Prop where
  sp : v.getReg .x2 = s.getReg .x2 - 496
  heap : HeapOk v
  mono : heapNext u₀ ≤ heapNext v
  frame : DFrame u₀ v (TW s u₀ v)
  x18 : v.getReg .x18 = BitVec.ofNat 64 i
  x21 : v.getReg .x21 =
    BitVec.ofNat 64 ((tAcc s rows ws i).2 + (tables.getD (opAt s i) default).nConstraints)
  x22 : v.getReg .x22 = s.getReg .x30
  acc : Model.limbs (tAcc s rows ws i).1 = (v.getReg .x25, v.getReg .x24, v.getReg .x27)
  weight : eAt v (s.getReg .x2 - 272) = ws.getD i 0
  summand : eAt v (s.getReg .x2 - 248) = sumOf s rows ws i
  cur : (tAcc s rows ws i).2 + (tables.getD (opAt s i) default).nConstraints ≤
    (s.getReg .x28).toNat
  len : (v.getReg .x26).toNat = (formVecAt s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).length
  vals : eListAt v (v.getReg .x8) (v.getReg .x26).toNat =
    (formVecAt s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).map
      (formEvaluateRust · (rows.getD i ([], [])).2)
  buf : (v.getReg .x26).toNat = 0 ∨
    heapStart ≤ (v.getReg .x8).toNat ∧
      (v.getReg .x8).toNat + 24 * (v.getReg .x26).toNat ≤ heapNext v
  align : (v.getReg .x8).toNat % 8 = 0

theorem mul24w (x : Word) : x * 16 + x * 8 = BitVec.ofNat 64 (24 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Sym.wordToNatLit]
  omega

theorem formVecAt_eq (s : MachineState) (a : Word) (ev : List E) :
    (formVecAt s a).map (formEvaluateRust · ev) = (List.range (vecLen s a).toNat).map
      fun k ↦ (formAt s (vecPtr s a + BitVec.ofNat 64 (24 * k))).evaluate ev := by
  simp only [formVecAt, List.map_map]
  apply List.map_congr_left
  intro k _
  exact formEvaluateRust_toSpec _ _

/-- At `0x80008864`: the values' `Vec` at `sp + 296`, empty, its buffer allocated since `v`;
`s1` and `s7` the forms' number and buffer. -/
structure AtBuf (s v w : MachineState) (i : ℕ) : Prop where
  sp : w.getReg .x2 = s.getReg .x2 - 496
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  frame : DFrame v w (VW s v w)
  x9 : w.getReg .x9 = vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))
  x23 : w.getReg .x23 = vecPtr s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))
  regs : ∀ r ∈ ([.x18, .x19, .x21, .x22, .x24, .x25, .x27] : List Reg), w.getReg r = v.getReg r
  len : vecLen w (s.getReg .x2 - 200) = 0
  align : (vecPtr w (s.getReg .x2 - 200)).toNat % 8 = 0
  buf : (vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).toNat = 0 ∨
    heapNext v ≤ (vecPtr w (s.getReg .x2 - 200)).toNat ∧ (vecPtr w (s.getReg .x2 - 200)).toNat +
      24 * (vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).toNat ≤ heapNext w

/-- The values' buffer, from `0x8000880c` to `0x80008864`. -/
theorem formsA (hTA : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    {s u₀ v : MachineState} {rows : List (List E × List E)}
    {ws : List E} {W : Word} {n i : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n)
    (hi : i < n) (h : AtForms s u₀ v rows ws i) (hpc : v.pc = 0x8000880c) :
    ∃ t, Reaches Image.code v t ∧ ((t.pc = 0x80008864 ∧ AtBuf s v t i) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hsp := h.sp
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  simp only [stack_eq] at ha hx
  have I := C.invAt hpre h.frame h.heap h.mono hsp
  obtain ⟨-, -, -, hn16⟩ := C.lens
  have hiF : i < (s.getReg .x16).toNat := by omega
  have hFr := hpre.forms.rows
  have hFb := hFr.bound
  have hFv : ValidMemRange (s.getReg .x15) (3 * (s.getReg .x16).toNat) :=
    RO.range (by rw [show 8 * (3 * (s.getReg .x16).toNat) = 24 * (s.getReg .x16).toNat by ring]
                 exact hFr)
  have e424 : v.getMem (s.getReg .x2 - 424) = s.getReg .x15 :=
    (h.frame _ (tw_slot hpre h.heap (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1])))).trans
      C.args.forms
  have eFP : v.getMem (s.getReg .x15 + BitVec.ofNat 64 (24 * i) + 8) =
      vecPtr s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) :=
    I.word hFr (by addr_omega [hFb, hiF]) (by addr_omega [hFb, hiF])
  have eFL : v.getMem (s.getReg .x15 + BitVec.ofNat 64 (24 * i) + 16) =
      vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) :=
    I.word hFr (by addr_omega [hFb, hiF]) (by addr_omega [hFb, hiF])
  -- `0x8000880c`: the forms, `try_allocate_in(len, 0, 8, 24)` into `sp + 344`
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000880c_spec hpc (by
    rv_eval [hsp, h.x9, e424]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hFv [hFb, hiF])
  have k₁ := b8000880c_keeps h₁
  have hm₁ := b8000880c_mem_same h₁
  have hsp₁ : v₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  have hx9₁ : v₁.getReg .x9 = vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) := by
    rw [b8000880c_x9 h₁, hsp, h.x9]
    rv_eval [e424]
    exact (congrArg _ (by addr_omega [hFb, hiF])).trans eFL
  have hx11₁ : v₁.getReg .x11 = vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) := by
    rw [b8000880c_x11 h₁, ← b8000880c_x9 h₁, hx9₁]
  have hx23₁ : v₁.getReg .x23 = vecPtr s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) := by
    rw [b8000880c_x23 h₁, hsp, h.x9]
    rv_eval [e424]
    exact (congrArg _ (by addr_omega [hFb, hiF])).trans eFP
  have h10₁ : v₁.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b8000880c_x10 h₁, hsp]; addr_omega [hb1]
  have hn₁ : heapNext v₁ = heapNext v := by simp only [heapNext, hm₁]
  have hpre₂ : TryAllocPre .x13 .x14 v₁ := {
    heap := ⟨hn₁ ▸ h.heap.lo, hn₁ ▸ h.heap.hi⟩
    out := by rw [h10₁]; valid_sub hval [hb1]
    align := by rw [b8000880c_x13 h₁]; decide
    size := by rw [b8000880c_x14 h₁]; decide
    stack := hpre.stack.sub 496 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [h10₁]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    outStack := by
      rw [h10₁]; simp only [stackLo, tryAllocStack, hsp₁]; addr_omega [hb1] }
  obtain ⟨v₂, hr₂, ⟨hpc₂, hp₂, post₂, -⟩ | hd⟩ := hTA.call hr₁ (b8000880c_pc h₁) hpre₂
  swap
  · exact ⟨v₂, hr₂, Or.inr hd⟩
  have hsp₂ : v₂.getReg .x2 = s.getReg .x2 - 496 := (hp₂.reg .x2).trans hsp₁
  have hf₂ := DFrame.of_byteFrame post₂.frame
  simp only [h10₁, stackLo, tryAllocStack, hsp₁] at hf₂
  -- `0x80008838`: `Ok`
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008838_spec
    (by rw [hpc₂, returnAddress_eq, b8000880c_x1 h₁]; decide) (by
      rv_eval [hsp₂]; valid_access hval [hb1])
  have hm₃ := b80008838_mem_same h₃
  have k₃ := b80008838_keeps h₃
  have e344 : v₂.getMem (v₂.getReg .x2 + 344) = v₂.getMem (v₁.getReg .x10) := by
    rw [hsp₂, h10₁]; congr 1; addr_omega [hb1]
  by_cases hok : v₂.getMem (v₁.getReg .x10) = 0
  swap
  · exact ⟨v₃, hr₂.trans hr₃, Or.inr (trap (b80008838_pc_taken h₃ (by rw [e344]; exact hok)))⟩
  have hpc₃ := b80008838_pc_not_taken h₃ (by rw [e344]; exact hok)
  obtain ⟨hcap₂, hbuf₂⟩ := post₂.ok hok
  rw [h10₁, hx11₁] at hcap₂ hbuf₂
  rw [b8000880c_x14 h₁, b8000880c_x13 h₁] at hbuf₂
  have hsp₃ : v₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  -- `0x80008840`: `Vec { cap: len, ptr, len: 0 }` at `sp + 296`, `reserve(len)`
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008840_spec hpc₃ (by
    rv_eval [hsp₃]; and_intros <;> valid_access hval [hb1])
  have k₄ := b80008840_keeps h₄
  have hf₄ := DFrame.of_memFrame (b80008840_frame h₄ (by rw [hsp₃]; addr_omega [hb1]))
  rw [hsp₃] at hf₄
  have hsp₄ : v₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hsp₃
  have h10₄ : v₄.getReg .x10 = s.getReg .x2 - 200 := by
    rw [b80008840_x10 h₄, hsp₃]; addr_omega [hb1]
  have h11₄ : v₄.getReg .x11 = vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) := by
    rw [b80008840_x11 h₄, k₃ .x9 (by decide), hp₂.reg .x9, hx9₁]
  have c₄ : vecCap v₄ (s.getReg .x2 - 200) =
      vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) := by
    have e := b80008840_m_x2_296 h₄; rw [hsp₃, hm₃] at e; rv_eval [] at e
    rw [vecCap, e, ← hcap₂]; congr 1; addr_omega [hb1]
  have p₄ : vecPtr v₄ (s.getReg .x2 - 200) = v₂.getMem (s.getReg .x2 - 152 + 16) := by
    have e := b80008840_m_x2_304 h₄; rw [hsp₃, hm₃] at e; rv_eval [] at e
    rw [vecPtr, show s.getReg .x2 - 200 + 8 = s.getReg .x2 - 192 by addr_omega [hb1], e]
    congr 1; addr_omega [hb1]
  have l₄ : vecLen v₄ (s.getReg .x2 - 200) = 0 := by
    have e := b80008840_m_x2_312 h₄; rw [hsp₃] at e; rv_eval [] at e
    rw [vecLen, show s.getReg .x2 - 200 + 16 = s.getReg .x2 - 184 by addr_omega [hb1], e]
  have hn₄ : heapNext v₄ = heapNext v₂ := by
    simp only [heapNext, ← hm₃]
    exact congrArg BitVec.toNat (hf₄ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hx, hb1])
  have hl₁ := hpre₂.heap.lo
  have hpre₅ : ReservePre 24 8 v₄ := {
    heap := ⟨hn₄ ▸ post₂.heap.lo, hn₄ ▸ post₂.heap.hi⟩
    self := by rw [h10₄]; valid_sub hval [hb1]
    vec := by
      rw [h10₄]
      refine ⟨?_, by rw [l₄]; exact Nat.zero_le _⟩
      simp only [RawVecOk, Buf, c₄, p₄, hn₄, heapStart]
      simp only [NewBuf, heapStart] at hbuf₂ hl₁
      simp only [Sym.wordToNatLit] at hbuf₂ ⊢
      omega
    stack := hpre.stack.sub 496 hsp₄ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by
      rw [h10₄]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    selfStack := by
      rw [h10₄]; simp only [stackLo, reserveStack, hsp₄]; addr_omega [hb1] }
  obtain ⟨v₅, hr₅, ⟨hpc₅, hp₅, post₅, hfresh⟩ | hd⟩ := hR.call hr₄ (b80008840_pc h₄) hpre₅
  swap
  · exact ⟨v₅, hr₂.trans (hr₃.trans hr₅), Or.inr hd⟩
  have hf₅ := DFrame.of_byteFrame post₅.frame
  simp only [h10₄, stackLo, reserveStack, hsp₄] at hf₅
  have hsp₅ : v₅.getReg .x2 = s.getReg .x2 - 496 := (hp₅.reg .x2).trans hsp₄
  have hm₂ := post₂.mono
  have hm₅ := post₅.mono
  have hh₅ := post₅.heap.hi
  simp only [heapEnd] at hh₅
  -- the values' buffer, allocated since `v`
  have hlen₅ : vecLen v₅ (s.getReg .x2 - 200) = 0 := by
    rw [show vecLen v₅ (s.getReg .x2 - 200) = vecLen v₄ (v₄.getReg .x10) by rw [← post₅.len, h10₄],
      h10₄, l₄]
  have hVP3 : (vecPtr v₅ (s.getReg .x2 - 200)).toNat % 8 = 0 := by
    have := post₅.vec.raw.1; rw [h10₄] at this; exact this
  have hVP : (vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).toNat = 0 ∨
      heapNext v ≤ (vecPtr v₅ (s.getReg .x2 - 200)).toNat ∧ (vecPtr v₅ (s.getReg .x2 - 200)).toNat +
        24 * (vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).toNat ≤ heapNext v₅ := by
    have hc := post₅.cap
    rw [h10₄, l₄, h11₄] at hc
    have h0 : (0 : Word).toNat = 0 := rfl
    rcases hfresh with ⟨e1, -⟩ | hnb
    · rw [h10₄] at e1
      rw [e1, p₄]
      simp only [NewBuf, Sym.wordToNatLit] at hbuf₂
      omega
    · rw [h10₄] at hnb
      simp only [NewBuf] at hnb
      omega
  -- the frame from `v`
  have F₅ : DFrame v v₅ (VW s v v₅) := by
    refine ((((DFrame.of_same hm₁ _).trans hf₂ fun a ha ↦ ?_).trans (DFrame.of_same hm₃ _)
      fun _ h ↦ h).trans hf₄ fun a ha ↦ Or.inl (by addr_omega [ha, hb1])).trans hf₅ fun a ha ↦ ?_
    · rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by rw [hn₄] at h1; omega, h2⟩))
  have hmv : heapNext v ≤ heapNext v₅ := by omega
  have hx9₅ : v₅.getReg .x9 = vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) := by
    rw [hp₅.reg .x9, k₄ .x9 (by decide), k₃ .x9 (by decide), hp₂.reg .x9, hx9₁]
  refine ⟨v₅, hr₂.trans (hr₃.trans hr₅), Or.inl ⟨by
    rw [hpc₅, returnAddress_eq, b80008840_x1 h₄]; decide, {
    sp := hsp₅
    heap := post₅.heap
    mono := hmv
    frame := F₅
    x9 := hx9₅
    x23 := by rw [hp₅.reg .x23, k₄ .x23 (by decide), k₃ .x23 (by decide), hp₂.reg .x23, hx23₁]
    regs := fun r hr ↦ by
      rw [hp₅ r (by unfold calleeSaved; exact mem_of_mem hr _), k₄ r (mem_of_mem hr _),
        k₃ r (mem_of_mem hr _), hp₂ r (by unfold calleeSaved; exact mem_of_mem hr _),
        k₁ r (mem_of_mem hr _)]
    len := hlen₅
    align := hVP3
    buf := hVP }⟩⟩

/-- The values, from `0x80008864` to `0x80008578`. -/
theorem formsB (hFE : FormEvaluateSpecE) {s u₀ v w : MachineState} {rows : List (List E × List E)}
    {ws : List E} {W : Word} {n i : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n)
    (hi : i < n) (h : AtForms s u₀ v rows ws i) (B : AtBuf s v w i) (hpc : w.pc = 0x80008864) :
    ∃ t, Reaches Image.code w t ∧
      ((t.pc = 0x80008578 ∧ AtTail s u₀ t rows ws i) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := C.invAt hpre h.frame h.heap h.mono h.sp
  obtain ⟨-, -, -, hn16⟩ := C.lens
  have hiF : i < (s.getReg .x16).toNat := by omega
  have hsp₅ := B.sp
  have F₅ := B.frame
  have hmv := B.mono
  have hlen₅ := B.len
  have hVP3 := B.align
  have hVP := B.buf
  have hx9₅ := B.x9
  have hh₅ := B.heap.hi
  simp only [heapEnd] at hh₅
  -- `0x80008864`: the buffer and the length
  obtain ⟨v₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80008864_spec hpc (by
      rv_eval [hsp₅]; and_intros <;> valid_access hval [hb1])
  have k₆ := b80008864_keeps h₆
  have hm₆ := b80008864_mem_same h₆
  have hx8₆ : v₆.getReg .x8 = vecPtr w (s.getReg .x2 - 200) := by
    rw [b80008864_x8 h₆, hsp₅, vecPtr]; congr 1; addr_omega [hb1]
  have hx26₆ : v₆.getReg .x26 = 0 := by
    rw [b80008864_x26 h₆, hsp₅, ← hlen₅, vecLen]; congr 1; addr_omega [hb1]
  have hn₆ : heapNext v₆ = heapNext w := by simp only [heapNext, hm₆]
  have F₆ : DFrame v v₆ (VW s v v₆) :=
    (F₅.mono fun _ ha ↦ VW.mono hn₆.ge ha).trans (DFrame.of_same hm₆ _) fun _ h ↦ h
  have hheap₆ : HeapOk v₆ := ⟨by rw [hn₆]; exact B.heap.lo, by rw [hn₆]; exact B.heap.hi⟩
  have Fu₆ := vw_tw hpre h.frame F₆ h.mono (hn₆ ▸ hmv)
  have R6 (r : Reg) (hr : r ∈ ([.x18, .x19, .x21, .x22, .x24, .x25, .x27] : List Reg)) :
      v₆.getReg r = v.getReg r := by
    rw [k₆ r (mem_of_mem hr _), B.regs r hr]
  have hweight (x : MachineState) (hf : DFrame v x (VW s v x)) (hh : heapNext x ≤ 0x78000000) :
      eAt x (s.getReg .x2 - 272) = ws.getD i 0 := by
    rw [hf.eAt fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, hw⟩ <;> addr_omega [hw, hj, hb1, hh]]
    exact h.weight
  have hsummand (x : MachineState) (hf : DFrame v x (VW s v x)) (hh : heapNext x ≤ 0x78000000) :
      eAt x (s.getReg .x2 - 248) = sumOf s rows ws i := by
    rw [hf.eAt fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, hw⟩ <;> addr_omega [hw, hj, hb1, hh]]
    exact h.summand
  by_cases hz : vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) = 0
  · -- no forms
    refine ⟨v₆, hr₆, Or.inl ⟨b80008864_pc_taken h₆ (by rw [hx9₅]; exact hz), {
      sp := (k₆ .x2 (by decide)).trans hsp₅
      heap := hheap₆
      mono := h.mono.trans (hn₆ ▸ hmv)
      frame := Fu₆
      x18 := (R6 .x18 (by decide)).trans h.x18
      x21 := (R6 .x21 (by decide)).trans h.x21
      x22 := (R6 .x22 (by decide)).trans h.x22
      acc := by rw [R6 .x25 (by decide), R6 .x24 (by decide), R6 .x27 (by decide)]; exact h.acc
      weight := hweight v₆ F₆ (by rw [hn₆]; exact hh₅)
      summand := hsummand v₆ F₆ (by rw [hn₆]; exact hh₅)
      cur := h.cur
      len := by rw [hx26₆, formVecAt, List.length_map, List.length_range, hz]
      vals := by
        rw [hx26₆, formVecAt_eq, hz]
        rfl
      buf := Or.inl (by rw [hx26₆]; rfl)
      align := by rw [hx8₆]; exact hVP3 }⟩⟩
  -- `0x80008870`: the loop's pointers
  have hpc₆ := b80008864_pc_not_taken h₆ (by rw [hx9₅]; exact hz)
  obtain ⟨FL, hFL⟩ : ∃ FL, (vecLen s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).toNat = FL :=
    ⟨_, rfl⟩
  have hFpos : 0 < FL := by
    rcases Nat.eq_zero_or_pos FL with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [hFL, h0]; rfl)) hz
    · exact h0
  rw [hFL] at hVP
  obtain ⟨hVa, hVb⟩ : heapNext v ≤ (vecPtr w (s.getReg .x2 - 200)).toNat ∧
      (vecPtr w (s.getReg .x2 - 200)).toNat + 24 * FL ≤ heapNext w := by
    rcases hVP with h0 | h0
    · omega
    · exact h0
  have hFF := hpre.forms.forms i hiF
  rw [hFL] at hFF
  have hFm : (vecPtr s (s.getReg .x15 + BitVec.ofNat 64 (24 * i))).toNat + 24 * FL ≤
      0xc0000000 := by
    rcases hFF.region with h0 | h0
    · omega
    · simp only [Region, Mapped] at h0; omega
  obtain ⟨v₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80008870_spec hpc₆ trivial
  have k₇ := b80008870_keeps h₇
  have hm₇ := b80008870_mem_same h₇
  have hn₇ : heapNext v₇ = heapNext w := by simp only [heapNext, hm₇, hm₆]
  have F₇ : DFrame v v₇ (VW s v v₇) :=
    (F₆.mono fun _ ha ↦ VW.mono (by rw [hn₇, hn₆]) ha).trans (DFrame.of_same hm₇ _) fun _ h ↦ h
  have hsp₇ : v₇.getReg .x2 = s.getReg .x2 - 496 :=
    (k₇ .x2 (by decide)).trans ((k₆ .x2 (by decide)).trans hsp₅)
  have hl0 := h.heap.lo
  simp only [heapStart] at hl0
  have I₇ : Inv s v₇ := C.invAt hpre (vw_tw hpre h.frame F₇ h.mono (by rw [hn₇]; exact hmv))
    ⟨by rw [hn₇]; exact B.heap.lo, by rw [hn₇]; exact B.heap.hi⟩
    (by rw [hn₇]; exact h.mono.trans hmv) hsp₇
  -- the row, below `u₀`
  obtain ⟨R, hR, hR1, hR2, hR3, EP, EL, hEP, hEL, hE3, hEb, hEl⟩ := C.row hpre hi
  have hh0 := C.inv.heap.hi
  have hmu := h.mono
  simp only [heapStart, heapEnd] at hR1 hEb hh0
  have Fu₇ := vw_tw hpre h.frame F₇ h.mono (by rw [hn₇]; exact hmv)
  have rd (a : Word) (h1 : 0x20000000 ≤ a.toNat) (h2 : a.toNat + 8 ≤ heapNext u₀) :
      v₇.getMem a = u₀.getMem a :=
    Fu₇ a (tw_old hpre C.inv.heap (by simp only [heapStart]; omega) h2)
  have hev : eListAt v₇ EP EL.toNat = (rows.getD i ([], [])).2 := by
    rw [← hEl]
    exact Fu₇.eListAt fun j hj ↦ by
      rcases hEb with h0 | h0
      · omega
      · exact tw_old hpre C.inv.heap (a := EP) (m := 24 * EL.toNat)
          (by simp only [heapStart]; omega) h0.2 j hj
  have hterm : ∀ k < FL, RO s tableSumcheckStack (tsWrites s) (tsSelf s)
      (vecPtr s (vecPtr s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) + BitVec.ofNat 64 (24 * k)))
      (48 * (vecLen s (vecPtr s (s.getReg .x15 + BitVec.ofNat 64 (24 * i)) +
        BitVec.ofNat 64 (24 * k))).toNat) :=
    fun k hk ↦ hpre.forms.terms i hiF k (by rw [hFL]; exact hk)
  obtain ⟨t, hrt, ht⟩ := evalLoop hFE hpre I₇ (VP := vecPtr w (s.getReg .x2 - 200))
    (RW := R + BitVec.ofNat 64 (48 * i)) (EP := EP) (EL := EL) hFF hterm (by omega)
    (by rw [hn₇]; exact hVb) hVP3
    (by have := I.mono; omega)
    (by addr_omega [hR1, hR2, hi]) (by addr_omega [hR1, hR2, hi, hVa, hmu])
    (by addr_omega [hR1, hR2, hR3, hi])
    (by rw [rd _ (by addr_omega [hR1, hR2, hi]) (by addr_omega [hR1, hR2, hi]), ← hEP]
        simp only [vecPtr]; exact congrArg _ (by addr_omega [hR1, hR2, hi]))
    (by rw [rd _ (by addr_omega [hR1, hR2, hi]) (by addr_omega [hR1, hR2, hi]), ← hEL]
        simp only [vecLen]; exact congrArg _ (by addr_omega [hR1, hR2, hi]))
    hE3 (by rcases hEb with h0 | h0
            · exact Or.inl h0
            · exact Or.inr ⟨h0.1, by omega⟩) hev
    FL 0 v₇ (by omega) hFpos (b80008870_pc h₇) hsp₇
    (by rw [b80008870_x23 h₇, k₆ .x23 (by decide), B.x23]; rfl)
    (by rw [b80008870_x9 h₇, hx8₆, hx26₆]; simp)
    (by rw [b80008870_x20 h₇, k₆ .x23 (by decide), B.x23, k₆ .x9 (by decide), hx9₅, mul24w, hFL]
        addr_omega [hFm])
    (by rw [k₇ .x19 (by decide), R6 .x19 (by decide), h.x19, hR])
    (DFrame.refl _ _) rfl (fun k hk ↦ absurd hk (Nat.not_lt_zero _))
  refine ⟨t, hr₆.trans (hr₇.trans hrt), ?_⟩
  rcases ht with ⟨hpct, hspt, hft, hnt, hvt, hkt⟩ | hd
  swap
  · exact Or.inr hd
  have F : DFrame v t (VW s v t) := (F₇.mono fun _ ha ↦ VW.mono (by rw [hnt]) ha).trans hft
    fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;> simp only [Within] at ha <;> omega
  have hnt' : heapNext t = heapNext w := by rw [hnt, hn₇]
  have Rt (r : Reg) (hr : r ∈ ([.x18, .x21, .x22, .x24, .x25, .x27] : List Reg)) :
      t.getReg r = v.getReg r := by
    rw [hkt r (mem_of_mem hr _), k₇ r (mem_of_mem hr _), R6 r (mem_of_mem hr _)]
  have hx8t : t.getReg .x8 = vecPtr w (s.getReg .x2 - 200) := by
    rw [hkt .x8 (by decide), k₇ .x8 (by decide), hx8₆]
  have hx26t : (t.getReg .x26).toNat = FL := by
    rw [hkt .x26 (by decide), b80008870_x26 h₇, k₆ .x9 (by decide), hx9₅, hx26₆, Sym.add_zero_lit,
      hFL]
  exact Or.inl ⟨hpct, {
    sp := hspt
    heap := ⟨by rw [hnt']; exact B.heap.lo, by rw [hnt']; exact B.heap.hi⟩
    mono := by rw [hnt']; exact h.mono.trans hmv
    frame := vw_tw hpre h.frame F h.mono (by rw [hnt']; exact hmv)
    x18 := (Rt .x18 (by decide)).trans h.x18
    x21 := (Rt .x21 (by decide)).trans h.x21
    x22 := (Rt .x22 (by decide)).trans h.x22
    acc := by rw [Rt .x25 (by decide), Rt .x24 (by decide), Rt .x27 (by decide)]; exact h.acc
    weight := hweight t F (by rw [hnt']; exact hh₅)
    summand := hsummand t F (by rw [hnt']; exact hh₅)
    cur := h.cur
    len := by rw [hx26t, formVecAt, List.length_map, List.length_range, hFL]
    vals := by
      rw [hx8t, hx26t, formVecAt_eq]
      apply List.ext_getElem (by rw [eListAt_length, List.length_map, List.length_range, hFL])
      intro k h1 h2
      rw [eListAt_getElem, List.getElem_map, List.getElem_range]
      exact hvt k (by rw [eListAt_length] at h1; exact h1)
    buf := Or.inr ⟨by rw [hx8t]; simp only [heapStart]; omega, by rw [hx8t, hx26t, hnt']; exact hVb⟩
    align := by rw [hx8t]; exact hVP3 }⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
