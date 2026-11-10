import Rv64Verifier.Proofs.Bus.TsTerminalExit

/-!
# `table_sumcheck`: stage F, the checked terminal

From `0x80008520` (`AtTerminal`) to the function's return: `transcript.checked()` holds
(`TableSumcheckPre.checked`); the loop runs over `min(tables.len(), rows.len(), bus_forms.len(),
weights.len())` items (`termLoop`, none when that is zero) and the terminal is compared with the
claim (`finishF`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The number of items: `a1`'s count and the weights'. -/
def countOf (s : MachineState) (rows : List (List E × List E)) : ℕ :=
  min (min (s.getReg .x12).toNat rows.length) (s.getReg .x16).toNat

/-- `transcript.checked()`: the flag at `tsSelf + 360`, which the function does not write. -/
theorem checked_byte {s u : MachineState} (hpre : TableSumcheckPre s) (I : Inv s u) :
    (BitVec.zeroExtend 64 (extractByte (u.getMem (tsSelf s + 360)) 0) == 0) = false := by
  have hS := hpre.self.self
  have so := hpre.selfOut
  have st := hpre.targetSelf
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have hn := I.heap.hi
  rw [stackLo_eq, stack_eq] at ss
  simp only [Outside, heapNext, heapEnd] at sf hn
  have e360 : u.getMem (tsSelf s + 360) = s.getMem (tsSelf s + 360) := I.frame _ fun j hj hw ↦ by
    simp only [TableSumcheck.W, Fresh, heapNext, stackLo_eq] at hw
    rcases hw with hw | hw | hw | hw | hw | hw <;> addr_omega [hj, hw, so, st, ss, sf, hn, hS]
  have hS8 : (tsSelf s + 360).toNat % 8 = 0 := by addr_omega [hS]
  apply zext_beq_zero
  rw [e360]
  have := hpre.checked
  rw [byteAt_of_within hS8 (le_refl _) (by omega), Nat.sub_self] at this
  exact this

/-- From `0x80008520` to `0x80008538`: the transcript is checked, `a1` the count. -/
theorem checkStep {s u : MachineState} {ch : List E} {cl : E} {P W : Word}
    {rows : List (List E × List E)} (hpre : TableSumcheckPre s)
    (h : AtTerminal s u ch cl P W rows) (hpc : u.pc = 0x80008520) :
    ∃ u₂, Reaches Image.code u u₂ ∧ u₂.pc = 0x80008538 ∧ (∀ a, u₂.getMem a = u.getMem a) ∧
      u₂.getReg .x11 = BitVec.ofNat 64 (countOf s rows) ∧
      u₂.getReg .x2 = s.getReg .x2 - 496 := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := h.inv
  have hsp := I.sp
  have hA := hpre.args.region
  have e16 : u.getMem (s.getReg .x2 + 16) = tsSelf s :=
    I.word hpre.args (by addr_omega [hb1, hb2]) (by addr_omega [hb1, hb2])
  have hS := hpre.self.self
  have hck := checked_byte hpre I
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008520_spec hpc (by
    rv_eval [hsp, e16]
    refine ⟨by addr_omega [hS], ?_, ?_⟩
    · have h8 : Sym.validAccess 8 (tsSelf s + 360) = true :=
        Region.valid hS (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS])
      simp only [Sym.validAccess, isValidDwordAccess, Bool.and_eq_true] at h8
      simp only [Sym.validAccess, isValidByteAccess]
      exact h8.1
    · rcases hA with h0 | h0
      · omega
      · exact Region.valid h0 (by addr_omega [h0]) (by addr_omega [h0]) (by addr_omega [h0]))
  have hpc₁ : u₁.pc = 0x8000852c := h₁.pc_eq (by
    rv_eval [hsp, e16]
    simp only [hck, Bool.false_eq_true, ↓reduceIte])
  have k₁ := b80008520_keeps h₁
  have hm₁ := b80008520_mem_same h₁
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  -- `0x8000852c`: `min(a1, weights.len())`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000852c_spec hpc₁ (by
    rv_eval [hsp₁]; valid_access hval [hb1])
  have k₂ := b8000852c_keeps h₂
  have hm₂ := b8000852c_mem_same h₂
  have e192 : u₁.getMem (u₁.getReg .x2 + 192) = s.getReg .x12 := by
    rw [hsp₁, hm₁, show s.getReg .x2 - 496 + 192 = s.getReg .x2 - 320 + 16 by addr_omega [hb1]]
    exact h.wlen
  have hx11₁ : u₁.getReg .x11 = BitVec.ofNat 64 (min (min (s.getReg .x12).toNat rows.length)
      (s.getReg .x16).toNat) := (k₁ .x11 (by decide)).trans h.x11
  have hm12 : countOf s rows ≤ (s.getReg .x12).toNat := by
    simp only [countOf]; omega
  have hc64 : (BitVec.ofNat 64 (countOf s rows)).toNat = countOf s rows := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := (s.getReg .x12).isLt; omega)
  by_cases hlt : countOf s rows < (s.getReg .x12).toNat
  · exact ⟨u₂, hr₁.trans hr₂,
      b8000852c_pc_taken h₂ (by rw [hx11₁, e192, ← countOf, hc64]; exact hlt),
      fun a ↦ (hm₂ a).trans (hm₁ a), (k₂ .x11 (by decide)).trans hx11₁,
      (k₂ .x2 (by decide)).trans hsp₁⟩
  · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008534_spec
      (b8000852c_pc_not_taken h₂ (by rw [hx11₁, e192, ← countOf, hc64]; omega)) trivial
    have k₃ := b80008534_keeps h₃
    refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), b80008534_pc h₃,
      fun a ↦ (b80008534_mem_same h₃ a).trans ((hm₂ a).trans (hm₁ a)), ?_,
      (k₃ .x2 (by decide)).trans ((k₂ .x2 (by decide)).trans hsp₁)⟩
    rw [b80008534_x11 h₃, b8000852c_x10 h₂, e192]
    apply BitVec.eq_of_toNat_eq
    rw [hc64]
    omega

theorem weightsOf_length {s u : MachineState} {ch : List E} {cl : E} {P W : Word}
    {rows : List (List E × List E)} (h : AtTerminal s u ch cl P W rows) :
    (weightsOf s ch).length = (s.getReg .x12).toNat := by
  rw [← h.weights, eListAt_length]

theorem tItems_count {s u : MachineState} {ch : List E} {cl : E} {P W : Word}
    {rows : List (List E × List E)} (h : AtTerminal s u ch cl P W rows) :
    (tItems s rows (weightsOf s ch)).length = countOf s rows := by
  rw [tItems_length, weightsOf_length h, countOf]
  omega

/-- At `0x800088e8`, from a frame that keeps `Kept`'s slots, the rows' header and the heap
allocated before `u`. -/
theorem AtTerminal.compare {s u t : MachineState} {ch : List E} {cl : E} {P W : Word}
    {rows : List (List E × List E)} {w : Word → Prop} (hpre : TableSumcheckPre s)
    (h : AtTerminal s u ch cl P W rows) (hf : DFrame u t w)
    (hw : ∀ a, w a → Loc s u t a ∧ ¬ Within a (s.getReg .x2 - 488) 56 ∧
      ¬ Within a (s.getReg .x2 - 296) 24 ∧ ¬ (heapNext s ≤ a.toNat ∧ a.toNat < heapNext u))
    (hheap : HeapOk t) (hmono : heapNext u ≤ heapNext t) (hsp : t.getReg .x2 = s.getReg .x2 - 496)
    (hacc : Model.limbs (terminalOf s rows (weightsOf s ch)) =
      (t.getReg .x25, t.getReg .x24, t.getReg .x27)) :
    AtCompare s t ch cl P rows := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have I := h.inv
  have hL : DFrame u t (Loc s u t) := hf.mono fun a ha ↦ (hw a ha).1
  have hdr (k : Nat) (hk : k + 8 ≤ 24) :
      t.getMem (s.getReg .x2 - 296 + BitVec.ofNat 64 k) =
        u.getMem (s.getReg .x2 - 296 + BitVec.ofNat 64 k) :=
    hf _ fun j hj hwj ↦ (hw _ hwj).2.2.1 (by addr_omega [hb1, hj, hk])
  have h0 := hdr 0 (by omega)
  have h8 := hdr 8 (by omega)
  have h16 := hdr 16 (by omega)
  rw [add_ofNat_zero] at h0
  exact {
    inv := I.loc hpre hL hheap hmono (hsp.trans I.sp.symm)
    kept := h.kept.step hf (fun a ha ↦ (hw a ha).2.1) hb1
    rowsAt := h.rowsAt.move hf hmono h0 h8 h16 (fun x h1 h2 hx ↦ (hw x hx).2.2.2 ⟨h1, h2⟩)
      I.heap.hi
    acc := hacc
    run := fun T hT ↦ by
      obtain ⟨T₁, T₂, e1, e2, hT₂⟩ := h.run T hT
      exact ⟨T₁, T₂, e1, e2, I.transcript hpre hheap hL hT₂⟩ }

/-- No item: the terminal is zero, from `0x80008538` to `0x800088e8`. -/
theorem zeroCase {s u u₂ : MachineState} {ch : List E} {cl : E} {P W : Word}
    {rows : List (List E × List E)} (hpre : TableSumcheckPre s)
    (h : AtTerminal s u ch cl P W rows) (hpc : u₂.pc = 0x80008538)
    (hm : ∀ a, u₂.getMem a = u.getMem a) (hx11 : u₂.getReg .x11 = 0)
    (hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 496) (hz : countOf s rows = 0) :
    ∃ t, Reaches Image.code u₂ t ∧ Done s t := by
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008538_spec hpc trivial
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800088dc_spec (b80008538_pc_taken h₃ hx11) trivial
  have hm₄ : ∀ a, u₄.getMem a = u.getMem a := fun a ↦
    (b800088dc_mem_same h₄ a).trans ((b80008538_mem_same h₃ a).trans (hm a))
  have hn : heapNext u₄ = heapNext u := by simp only [heapNext, hm₄]
  have hsp : u₄.getReg .x2 = s.getReg .x2 - 496 := by
    rw [b800088dc_keeps h₄ .x2 (by decide), b80008538_keeps h₃ .x2 (by decide), hsp₂]
  have A := h.compare hpre (DFrame.of_same hm₄ fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn ▸ h.inv.heap.lo, hn ▸ h.inv.heap.hi⟩ hn.ge hsp (by
      rw [terminalOf_eq, tItems_count h, hz, b800088dc_x25 h₄, b800088dc_x24 h₄,
        b800088dc_x27 h₄]
      exact limbs_zero')
  obtain ⟨t, hrt, ht⟩ := finishF hpre A (b800088dc_pc h₄)
  exact ⟨t, hr₃.trans (hr₄.trans hrt), ht⟩

/-- Some item: `0x8000853c` fills the loop's slots and reaches the head. -/
theorem loopStart {s u u₂ : MachineState} {ch : List E} {cl : E} {P W : Word}
    {rows : List (List E × List E)} (hpre : TableSumcheckPre s)
    (h : AtTerminal s u ch cl P W rows) (hpc : u₂.pc = 0x80008538)
    (hm : ∀ a, u₂.getMem a = u.getMem a)
    (hx11 : u₂.getReg .x11 = BitVec.ofNat 64 (countOf s rows))
    (hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 496) (hz : countOf s rows ≠ 0) :
    ∃ u₀, Reaches Image.code u₂ u₀ ∧ u₀.pc = 0x80008600 ∧
      Ctx s u₀ rows (weightsOf s ch) W (countOf s rows) ∧
      LoopAt s u₀ u₀ rows (weightsOf s ch) 0 ∧
      DFrame u u₀ (Within · (s.getReg .x2 - 392) 72) ∧ heapNext u₀ = heapNext u := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := h.inv
  have hhi := I.heap.hi
  simp only [heapEnd] at hhi
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008538_spec hpc trivial
  have hm12 : countOf s rows ≤ (s.getReg .x12).toNat := by simp only [countOf]; omega
  have hc0 : u₂.getReg .x11 ≠ 0 := by
    rw [hx11]; intro e; apply hz
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.getReg .x12).isLt; omega)] at this
    exact this
  have k₃ := b80008538_keeps h₃
  have hm₃ := b80008538_mem_same h₃
  have hsp₃ : u₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000853c_spec (b80008538_pc_not_taken h₃ hc0) (by
    rv_eval [hsp₃]; and_intros <;> valid_access hval [hb1])
  have k₄ := b8000853c_keeps h₄
  have hf₄ := DFrame.of_memFrame (b8000853c_frame h₄ (by rw [hsp₃]; addr_omega [hb1]))
  rw [hsp₃, show s.getReg .x2 - 496 + 104 = s.getReg .x2 - 392 by addr_omega [hb1]] at hf₄
  have hmu : ∀ a, u₃.getMem a = u.getMem a := fun a ↦ (hm₃ a).trans (hm a)
  have hf : DFrame u u₄ (Within · (s.getReg .x2 - 392) 72) :=
    (DFrame.of_same hmu _).trans hf₄ fun _ h ↦ h
  have hsp₄ : u₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hsp₃
  have hn₄ : heapNext u₄ = heapNext u := by
    simp only [heapNext]
    rw [hf nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
  have out (a : Word) (h1 : a.toNat + 8 ≤ (s.getReg .x2 - 392).toNat ∨
      (s.getReg .x2 - 320).toNat ≤ a.toNat) (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) :
      u₄.getMem a = u.getMem a :=
    hf a fun j hj hw ↦ by rcases h1 with h1 | h1 <;> addr_omega [hw, hj, h1, h2, hb1]
  have prec (a : Word) (ha : a = s.getReg .x2 - 360 ∨ a = s.getReg .x2 - 352) :
      u₄.getMem a = u.getMem a := by
    rcases ha with rfl | rfl <;>
      rw [h₄.2.2.2 _ (by rv_eval [hsp₃]; and_intros <;> addr_omega [hb1]), hmu]
  have m104 := b8000853c_m_x2_104 h₄
  have m152 := b8000853c_m_x2_152 h₄
  have m160 := b8000853c_m_x2_160 h₄
  have m168 := b8000853c_m_x2_168 h₄
  rw [hsp₃] at m104 m152 m160 m168
  rv_eval [] at m104 m152 m160 m168
  have hwb := h.wbuf
  simp only [NewBuf] at hwb
  have C : Ctx s u₄ rows (weightsOf s ch) W (countOf s rows) := {
    inv := I.loc hpre (hf.mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1]))
      ⟨hn₄ ▸ I.heap.lo, hn₄ ▸ I.heap.hi⟩ hn₄.ge (hsp₄.trans I.sp.symm)
    args := {
      formPowers := (out _ (Or.inl (by addr_omega [hb1])) (by addr_omega [hb1])).trans
        h.args.formPowers
      forms := (out _ (Or.inl (by addr_omega [hb1])) (by addr_omega [hb1])).trans h.args.forms
      constraintPowers := (out _ (Or.inl (by addr_omega [hb1])) (by addr_omega [hb1])).trans
        h.args.constraintPowers
      constraintLen := (out _ (Or.inl (by addr_omega [hb1])) (by addr_omega [hb1])).trans
        h.args.constraintLen
      tables := (out _ (Or.inl (by addr_omega [hb1])) (by addr_omega [hb1])).trans h.args.tables
      equalityPoint := (prec _ (Or.inl rfl)).trans h.args.equalityPoint
      heights := (prec _ (Or.inr rfl)).trans h.args.heights }
    formLen := (out _ (Or.inl (by addr_omega [hb1])) (by addr_omega [hb1])).trans h.kept.formLen
    count := by rw [m104, k₃ .x11 (by decide), hx11]
    rowsPtr := by
      rw [m152, hmu, vecPtr, out _ (Or.inr (by addr_omega [hb1])) (by addr_omega [hb1])]
      congr 1; addr_omega [hb1]
    nc := m160
    wptr := by
      rw [m168, hmu, ← h.wptr, vecPtr]; congr 1; addr_omega [hb1]
    rowsAt := h.rowsAt.move hf hn₄.ge
      (out _ (Or.inr (by addr_omega [hb1])) (by addr_omega [hb1]))
      (out _ (Or.inr (by addr_omega [hb1])) (by addr_omega [hb1]))
      (out _ (Or.inr (by addr_omega [hb1])) (by addr_omega [hb1]))
      (fun x _ h2 hw ↦ by addr_omega [hw, h2, hb1, hhi]) I.heap.hi
    wbuf := by simp only [NewBuf]; rw [hn₄]; exact hwb
    weights := by
      rw [hf.eListAt fun j hj hw ↦ by
        rcases hwb.2 with h0 | h0 <;> addr_omega [hw, hj, h0, hb1, hhi]]
      exact h.weights
    len := tItems_count h }
  have h0 : tAcc s rows (weightsOf s ch) 0 = (0, 0) := rfl
  refine ⟨u₄, hr₃.trans hr₄, b8000853c_pc h₄, C, {
    sp := hsp₄
    heap := ⟨hn₄ ▸ I.heap.lo, hn₄ ▸ I.heap.hi⟩
    mono := le_refl _
    frame := DFrame.refl _ _
    x18 := by rw [b8000853c_x18 h₄]; rfl
    x10 := by rw [b8000853c_x10 h₄, h0]; rfl
    x22 := by
      rw [b8000853c_x22 h₄, hsp₃]
      rv_eval []
      rw [hmu]; exact h.kept.formLen
    acc := by rw [b8000853c_x25 h₄, b8000853c_x24 h₄, b8000853c_x27 h₄, h0]; exact limbs_zero'
    cur := by rw [h0]; exact Nat.zero_le _ }, hf, hn₄⟩

/-- Stage F: the checked terminal, from `0x80008520` to the function's return. `Form::evaluate`
is taken with empty slices allowed (`FormEvaluateSpecE`). -/
theorem stageF (hMul : MulSpec) (hDot : DotSpec) (hA : AllocSpec) (hTA : TryAllocZeroedSpec)
    (hR : ReserveFreshSpec 0x80008a10 24 8) (hFE : FormEvaluateSpecE)
    {s u : MachineState} {ch : List E} {cl : E} {P W : Word} {rows : List (List E × List E)}
    (hpre : TableSumcheckPre s) (h : AtTerminal s u ch cl P W rows) (hpc : u.pc = 0x80008520) :
    ∃ t, Reaches Image.code u t ∧ Done s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨u₂, hr₂, hpc₂, hm₂, hx11₂, hsp₂⟩ := checkStep hpre h hpc
  by_cases hz : countOf s rows = 0
  · obtain ⟨t, hrt, ht⟩ := zeroCase hpre h hpc₂ hm₂ (by rw [hx11₂, hz]; rfl) hsp₂ hz
    exact ⟨t, hr₂.trans hrt, ht⟩
  obtain ⟨u₀, hr₀, hpc₀, C, L, hf₀, hn₀⟩ := loopStart hpre h hpc₂ hm₂ hx11₂ hsp₂ hz
  obtain ⟨t, hrt, ⟨hpct, Lt⟩ | hd⟩ :=
    termLoop hMul hDot hA hTA hR hFE hpre C _ 0 u₀ rfl (by omega) hpc₀ L
  swap
  · exact ⟨t, hr₂.trans (hr₀.trans hrt), Or.inr hd⟩
  have hhi := h.inv.heap.hi
  have hht := Lt.heap.hi
  simp only [heapEnd] at hhi hht
  have A := h.compare hpre (w := fun a ↦ Within a (s.getReg .x2 - 392) 72 ∨ TW s u₀ t a)
    ((hf₀.mono fun a ha ↦ Or.inl ha).trans Lt.frame fun a ha ↦ Or.inr ha) (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ⟨h1, h2⟩
      · exact ⟨Or.inl (by addr_omega [ha, hb1]), by addr_omega [ha, hb1], by addr_omega [ha, hb1],
          fun ⟨_, h3⟩ ↦ by addr_omega [ha, h3, hb1, hhi]⟩
      · exact ⟨Or.inl (by addr_omega [ha, hb1]), by addr_omega [ha, hb1], by addr_omega [ha, hb1],
          fun ⟨_, h3⟩ ↦ by addr_omega [ha, h3, hb1, hhi]⟩
      · exact ⟨Or.inl (by addr_omega [ha, hb1]), by addr_omega [ha, hb1], by addr_omega [ha, hb1],
          fun ⟨_, h3⟩ ↦ by addr_omega [ha, h3, hb1, hhi]⟩
      · exact ⟨Or.inl (by addr_omega [ha, hb1]), by addr_omega [ha, hb1], by addr_omega [ha, hb1],
          fun ⟨_, h3⟩ ↦ by addr_omega [ha, h3, hb1, hhi]⟩
      · exact ⟨Or.inr (Or.inl ha), by addr_omega [ha, hb1], by addr_omega [ha, hb1],
          fun ⟨_, h3⟩ ↦ by addr_omega [ha, h3, hhi]⟩
      · exact ⟨Or.inr (Or.inr ⟨by omega, h2⟩), by addr_omega [h2, hb1, hht],
          by addr_omega [h2, hb1, hht], fun ⟨_, h3⟩ ↦ by omega⟩)
    Lt.heap (hn₀ ▸ Lt.mono) Lt.sp (by rw [terminalOf_eq, tItems_count h]; exact Lt.acc)
  obtain ⟨t', hrt', ht'⟩ := finishF hpre A hpct
  exact ⟨t', hr₂.trans (hr₀.trans (hrt.trans hrt')), ht'⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
