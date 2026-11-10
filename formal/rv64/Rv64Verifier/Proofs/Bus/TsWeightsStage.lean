import Rv64Verifier.Proofs.Bus.TsOuter

/-!
# `table_sumcheck`: the weights, from `0x80008210` to `0x80008384`

`vec![ONE; tables.len()]` at `S - 320`, `point.len()` at `sp + 112`, the point loop's slots at
`sp + 120` to `sp + 168` (`0x8000825c`), then `outerLoop`. At `0x80008384` (`AtRows`) the weights
are the mirror's.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The mirror's weights on the entry's arguments. -/
def weightsOf (s : MachineState) (ch : List E) : List E :=
  tableWeightsRust (s.getReg .x12).toNat (natsAt s (s.getReg .x13) (s.getReg .x14).toNat)
    (eListAt s (s.getReg .x31) (tsEqLen s).toNat) ch.reverse

/-- At `0x80008384`: the weights at `W` (their `Vec` at `S - 320`), `tables.len()` and
`point.len()` at `sp + 104` and `sp + 112`. -/
structure AtRows (s u : MachineState) (ch : List E) (cl : E) (P W : Word) : Prop where
  inv : Inv s u
  kept : Kept s u cl P
  args : Args s u
  tablesLen : u.getMem (s.getReg .x2 - 392) = s.getReg .x12
  pointLen : (u.getMem (s.getReg .x2 - 384)).toNat = ch.length
  x26 : u.getReg .x26 = s.getReg .x14
  wptr : vecPtr u (s.getReg .x2 - 320) = W
  wlen : vecLen u (s.getReg .x2 - 320) = s.getReg .x12
  wbuf : NewBuf s u W (24 * (s.getReg .x12).toNat) 8
  weights : eListAt u W (s.getReg .x12).toNat = weightsOf s ch
  buf : NewBuf s u P (24 * ch.length) 8
  point : eListAt u P ch.length = ch.reverse
  run : ∀ T, TranscriptAt s (tsSelf s) T → ∃ T',
    (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T') ∧ TranscriptAt u (tsSelf s) T'

theorem one_at {u : MachineState} (h : RodataOk u) : eAt u 0xa00000b0 = 1 :=
  eAt_eq_of_limbs (by
    rw [limbs_one, h.word (a := 0xa00000b0) (v := 1), h.word (a := 0xa00000b0 + 8) (v := 0),
      h.word (a := 0xa00000b0 + 16) (v := 0)])

/-- What `0x80008210` to `0x8000822c` write: `sp + 104` and `sp + 112`, the weights' `Vec`,
`from_elem`'s stack, `NEXT` and the buffer it allocates. -/
def D1W (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 392) 16 ∨ Within a (s.getReg .x2 - 320) 24 ∨
    Within a (s.getReg .x2 - 2128) 1632 ∨ Within a nextAddr 8 ∨ Fresh u v a

/-- `vec![ONE; tables.len()]`, from `0x80008210` to `0x8000822c`'s end: the `Vec` at `S - 320`,
`tables.len()` at `sp + 104`, `point.len()` at `sp + 112`. -/
theorem stageD1 (hFE : FromElemSpec) {s u : MachineState} {ch : List E} {cl : E} {P : Word}
    (hpre : TableSumcheckPre s) (h : AtWeights s u ch cl P) (hpc : u.pc = 0x80008210) :
    ∃ v, Reaches Image.code u v ∧ ((Inv s v ∧ DFrame u v (D1W s u v) ∧ heapNext u ≤ heapNext v ∧
      v.getMem (s.getReg .x2 - 392) = s.getReg .x12 ∧
      v.getMem (s.getReg .x2 - 384) = u.getReg .x9 ∧
      (∀ r ∈ ([.x2, .x9, .x19, .x26] : List Reg), v.getReg r = u.getReg r) ∧
      (v.pc = if u.getReg .x9 = 0 then 0x80008384 else 0x80008234) ∧
      vecLen v (s.getReg .x2 - 320) = s.getReg .x12 ∧
      NewBuf u v (vecPtr v (s.getReg .x2 - 320)) (24 * (s.getReg .x12).toNat) 8 ∧
      eListAt v (vecPtr v (s.getReg .x2 - 320)) (s.getReg .x12).toNat =
        List.replicate (s.getReg .x12).toNat 1) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := h.inv
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  have hr := hpre.stack.rodata
  simp only [stack_eq] at ha hx hr
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008210_spec hpc (by
    rv_eval [I.sp]; valid_access hval [hb1])
  have k₁ := b80008210_keeps h₁
  have hf₁ := DFrame.of_memFrame (b80008210_frame h₁ (by rw [I.sp]; addr_omega [hb1]))
  rw [I.sp] at hf₁
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf₁ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hx, hb1])
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans I.sp
  have h10₁ : u₁.getReg .x10 = s.getReg .x2 - 320 := by rw [b80008210_x10 h₁, I.sp]; rv_eval []
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hsl : stackLo u₁ fromElemStack = s.getReg .x2 - 608 := by
    simp only [stackLo, fromElemStack, tryAllocStack, hsp₁]; addr_omega [hb1]
  have hpre₂ : FromElemPre u₁ := {
    heap := ⟨hn₁ ▸ I.heap.lo, hn₁ ▸ I.heap.hi⟩
    out := by rw [h10₁]; valid_sub hval [hb1]
    elem := by rw [b80008210_x11 h₁]; exact region_range ⟨Or.inr ⟨by decide, by decide⟩, by decide⟩
    stack := hpre.stack.sub 496 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [h10₁]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    outStack := by rw [h10₁, hsl]; addr_omega [hb1]
    elemFree := by rw [b80008210_x11 h₁]; simp only [Outside, heapEnd]; addr_omega []
    elemStack := by rw [b80008210_x11 h₁, hsl]; addr_omega [hb1, hr]
    elemOut := by rw [b80008210_x11 h₁, h10₁]; addr_omega [hb1, hr] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post₂⟩ | hd⟩ := hFE.call hr₁ (b80008210_pc h₁) hpre₂
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have hf₂ := DFrame.of_byteFrame post₂.frame
  rw [h10₁, hsl] at hf₂
  have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 496 := (hp₂.reg .x2).trans hsp₁
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000822c_spec
    (by rw [hpc₂, returnAddress_eq, b80008210_x1 h₁]; decide) (by
      rv_eval [hsp₂]; valid_access hval [hb1])
  have k₃ := b8000822c_keeps h₃
  have hf₃ := DFrame.of_memFrame (b8000822c_frame h₃ (by rw [hsp₂]; addr_omega [hb1]))
  rw [hsp₂] at hf₃
  have m₂ := post₂.mono
  have hhi := post₂.heap.hi
  simp only [heapEnd] at hhi
  have hn₃ : heapNext u₃ = heapNext u₂ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf₃ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hx, hb1])
  have hfr : DFrame u u₃ (D1W s u u₃) := by
    refine ((hf₁.mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1])).trans hf₂ fun a ha ↦ ?_).trans
      hf₃ fun a ha ↦ Or.inl (by addr_omega [ha, hb1])
    rcases ha with ha | ha | ha | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [← hn₁]; exact h1, by rw [hn₃]; exact h2⟩)))
  have hH₃ : HeapOk u₃ := ⟨hn₃ ▸ post₂.heap.lo, hn₃ ▸ post₂.heap.hi⟩
  have hsp₃ : u₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  have hsame (a : Word) (ha : Apart a 8 (s.getReg .x2 - 384) 8) (hab : a.toNat + 8 ≤ 2 ^ 64) :
      u₃.getMem a = u₂.getMem a :=
    hf₃ a fun i hi hw ↦ by addr_omega [hw, hi, ha, hb1, hab]
  refine ⟨u₃, hr₂.trans hr₃, Or.inl ⟨I.loc hpre (hfr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)) hH₃ (by rw [hn₃, ← hn₁]; exact m₂) (hsp₃.trans I.sp.symm),
    hfr, by rw [hn₃, ← hn₁]; exact m₂, ?_, ?_, fun r hr ↦ ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hsame _ (by addr_omega [hb1]) (by addr_omega [hb1]), hf₂ _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw | ⟨h1, h2⟩
      · addr_omega [hw, hi, hb1]
      · addr_omega [hw, hi, hb1]
      · addr_omega [hw, hi, hb1, hx]
      · addr_omega [h1, h2, hi, hb1, ha, hhi]]
    have := b80008210_m_x2_104 h₁
    rw [I.sp, h.x23] at this; rv_eval [] at this; exact this
  · have := b8000822c_m_x2_112 h₃
    rw [hsp₂, hp₂.reg .x9, k₁ .x9 (by decide)] at this; rv_eval [] at this; exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [k₃ _ (by decide), hp₂ _ (by decide), k₁ _ (by decide)]
  · by_cases hz : u.getReg .x9 = 0
    · simp only [hz, ↓reduceIte]; exact b8000822c_pc_taken h₃ (by rw [hp₂.reg .x9, k₁ .x9 (by decide)]; exact hz)
    · simp only [hz, ↓reduceIte]
      exact b8000822c_pc_not_taken h₃ (by rw [hp₂.reg .x9, k₁ .x9 (by decide)]; exact hz)
  · rw [vecLen, hsame _ (by addr_omega [hb1]) (by addr_omega [hb1]), ← h10₁]
    exact post₂.len.trans (by rw [b80008210_x12 h₁, h.x23])
  · have hp : vecPtr u₃ (s.getReg .x2 - 320) = vecPtr u₂ (s.getReg .x2 - 320) := by
      rw [vecPtr, hsame _ (by addr_omega [hb1]) (by addr_omega [hb1])]; rfl
    have hfr₂ := post₂.fresh
    rw [h10₁, b80008210_x12 h₁, h.x23] at hfr₂
    rw [hp]
    simp only [NewBuf] at hfr₂ ⊢
    rw [hn₃, ← hn₁]
    exact hfr₂
  · have hp : vecPtr u₃ (s.getReg .x2 - 320) = vecPtr u₂ (s.getReg .x2 - 320) := by
      rw [vecPtr, hsame _ (by addr_omega [hb1]) (by addr_omega [hb1])]; rfl
    have hel := post₂.elems
    have hln := post₂.len
    rw [h10₁, b80008210_x12 h₁, h.x23, b80008210_x11 h₁] at hel
    rw [h10₁, b80008210_x12 h₁, h.x23] at hln
    rw [vecEs, hln, one_at (I.rodata hpre |>.dframe (DFrame.of_memFrame (b80008210_frame h₁
      (by rw [I.sp]; addr_omega [hb1]))) fun a ha hw ↦ by
        rw [I.sp] at hw; have := hpre.stack.rodata; simp only [stack_eq] at this
        addr_omega [ha, hw, this, hb1])] at hel
    rw [hp, ← hel]
    have hfr₂ := post₂.fresh
    rw [h10₁, b80008210_x12 h₁, h.x23] at hfr₂
    simp only [NewBuf] at hfr₂
    exact hf₃.eListAt fun i hi hw ↦ by
      rcases hfr₂.2 with h0 | h0
      · omega
      · addr_omega [hw, hi, h0, hhi, hb1, ha]

theorem natsAt_getD (s : MachineState) (a : Word) {n i : Nat} (h : i < n) :
    (natsAt s a n).getD i 0 = (s.getMem (a + BitVec.ofNat 64 (8 * i))).toNat := by
  simp [natsAt, readWords_eq_map, h]

theorem natsAt_length (s : MachineState) (a : Word) (n : Nat) : (natsAt s a n).length = n := by
  simp [natsAt, readWords_eq_map]

theorem D1W.kept {s u v : MachineState} {a : Word} (hb1 : 0xa0000f38 + 2128 ≤ (s.getReg .x2).toNat)
    (hv : heapNext v ≤ heapEnd) (hs : heapEnd ≤ (s.getReg .x2).toNat - 2128)
    (ha : D1W s u v a) : ¬ Within a (s.getReg .x2 - 488) 56 ∧ ¬ Within a (s.getReg .x2 - 432) 40 ∧
      ¬ Within a (s.getReg .x2 - 360) 16 := by
  simp only [heapEnd] at hv hs
  rcases ha with ha | ha | ha | ha | ha <;>
    exact ⟨by addr_omega [ha, hb1, hs, hv], by addr_omega [ha, hb1, hs, hv],
      by addr_omega [ha, hb1, hs, hv]⟩

theorem hlen_pred (x : Word) (h1 : 1 ≤ x.toNat) (h2 : x.toNat < 2 ^ 32) :
    ((x * 8 - 8) >>> 3).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  simp only [Sym.wordToNatLit]
  rw [Nat.mod_eq_of_lt (a := x.toNat * 8) (by omega)]
  omega

set_option maxHeartbeats 1000000 in
theorem stageD (hFE : FromElemSpec) (hMul : MulSpec) {s u : MachineState} {ch : List E} {cl : E}
    {P : Word} (hpre : TableSumcheckPre s) (h : AtWeights s u ch cl P) (hpc : u.pc = 0x80008210) :
    ∃ t, Reaches Image.code u t ∧
      ((∃ W, t.pc = 0x80008384 ∧ AtRows s t ch cl P W) ∨ Dead Image.code t) := by
  obtain ⟨v, hrv, ⟨Iv, hfv, huv, m392, m384, hregs, hpcv, hlenv, hbufv, helv⟩ | hd⟩ :=
    stageD1 hFE hpre h hpc
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hs₂ := hpre.stack.above
  simp only [stack_eq] at hs₂
  have hhv := Iv.heap.hi
  have hhu := h.inv.heap.hi
  have hmu := h.inv.mono
  have hmv := Iv.mono
  set W := vecPtr v (s.getReg .x2 - 320) with hW
  set L := ch.length with hL
  have kd (a : Word) (ha : D1W s u v a) := D1W.kept hb1 hhv (by addr_omega [hs₂, hb1]) ha
  have hLoc : DFrame u v (Loc s u v) := hfv.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ha)
  have hPb := h.buf
  simp only [NewBuf] at hPb
  -- the point is the challenges reversed, at `v` as at `u`
  have hptv : eListAt v P L = ch.reverse := by
    rw [← h.point]
    exact hfv.eListAt fun i hi hw ↦ by
      rcases hPb.2 with h0 | h0
      · omega
      · rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hi, h0, hhu, hs₂, hb1]
  have hKv := h.kept.step hfv (fun a ha ↦ (kd a ha).1) hb1
  have hAv := h.args.step hfv (fun a ha ↦ (kd a ha).2) hb1
  have hrunv (T : TState) (hT : TranscriptAt s (tsSelf s) T) : ∃ T',
      (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
        some ((ch, cl), T') ∧ TranscriptAt v (tsSelf s) T' := by
    obtain ⟨T', e, hT'⟩ := h.run T hT
    exact ⟨T', e, h.inv.transcript hpre Iv.heap hLoc hT'⟩
  have hx9 := h.x9
  by_cases hL0 : u.getReg .x9 = 0
  · -- an empty point: the weights are all `ONE`
    have hch : ch = [] := List.eq_nil_of_length_eq_zero (by rw [← hx9, hL0]; rfl)
    refine ⟨v, hrv, Or.inl ⟨W, by rw [hpcv]; simp only [hL0, ↓reduceIte], {
      inv := Iv, kept := hKv, args := hAv, tablesLen := m392
      pointLen := by rw [m384, hx9]
      x26 := by rw [hregs .x26 (by decide), h.x26]
      wptr := rfl, wlen := hlenv
      wbuf := by simp only [NewBuf] at hbufv ⊢; omega
      weights := by rw [helv, weightsOf, hch]; simp [tableWeightsRust]
      buf := by simp only [NewBuf] at hPb ⊢; omega
      point := hptv
      run := hrunv }⟩⟩
  -- the point loop's slots
  have hsp : v.getReg .x2 = s.getReg .x2 - 496 := (hregs .x2 (by decide)).trans h.inv.sp
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [hx9, ← hL, h0]; rfl)) hL0
    · exact h0
  have hpc₄ : v.pc = 0x80008234 := by rw [hpcv]; simp only [hL0, ↓reduceIte]
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008234_spec hpc₄ (by
    rv_eval [hsp]; and_intros <;> valid_access hval [hb1])
  have hm₄ := b80008234_mem_same h₄
  have k₄ := b80008234_keeps h₄
  have e192 : v.getMem (v.getReg .x2 + 192) = s.getReg .x12 := by
    rw [hsp, show s.getReg .x2 - 496 + 192 = s.getReg .x2 - 320 + 16 by addr_omega [hb1]]
    exact hlenv
  have e112 : v.getMem (v.getReg .x2 + 112) = u.getReg .x9 := by
    rw [hsp, show s.getReg .x2 - 496 + 112 = s.getReg .x2 - 384 by addr_omega [hb1]]; exact m384
  have hx19v : v.getReg .x19 = s.getReg .x14 * 8 := (hregs .x19 (by decide)).trans h.x19
  -- `min(weights.len(), heights.len() - 1)` in `a1` at `0x8000825c`
  obtain ⟨u₅, hr₅, hpc₅, hm₅, hx11₅, k₅⟩ : ∃ u₅, Reaches Image.code u₄ u₅ ∧ u₅.pc = 0x8000825c ∧
      (∀ a, u₅.getMem a = u₄.getMem a) ∧
      (1 ≤ (s.getReg .x14).toNat → (s.getReg .x14).toNat < 2 ^ 32 →
        u₅.getReg .x11 = BitVec.ofNat 64 (min (s.getReg .x12).toNat ((s.getReg .x14).toNat - 1))) ∧
      ∀ r, r ≠ .x11 → u₅.getReg r = u₄.getReg r := by
    by_cases hlt : (v.getMem (v.getReg .x2 + (192 : Word))).toNat <
        ((v.getReg .x19 - (8 : Word)) >>> 3).toNat
    · refine ⟨u₄, Reaches.refl _, b80008234_pc_taken h₄ hlt, fun _ ↦ rfl, fun h1 h2 ↦ ?_,
        fun _ _ ↦ rfl⟩
      rw [hx19v, hlen_pred _ h1 h2] at hlt
      rw [e192] at hlt
      rw [b80008234_x11 h₄, e192, Nat.min_eq_left (by omega)]; simp
    · obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80008258_spec
        (b80008234_pc_not_taken h₄ (by omega)) trivial
      refine ⟨u₅, hr₅, b80008258_pc h₅, b80008258_mem_same h₅, fun h1 h2 ↦ ?_, fun r hr ↦ ?_⟩
      · rw [hx19v, hlen_pred _ h1 h2, e192] at hlt
        rw [b80008258_x11 h₅, b80008234_x13 h₄, hx19v, Nat.min_eq_right (by omega)]
        apply BitVec.eq_of_toNat_eq
        rw [hlen_pred _ h1 h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · have := b80008258_keeps h₅
        rcases r <;> first | (exfalso; exact hr rfl) | exact this _ (by decide) | rfl
  have hm₅ (a : Word) : u₅.getMem a = v.getMem a := (hm₅ a).trans (hm₄ a)
  have hsp₅ : u₅.getReg .x2 = s.getReg .x2 - 496 := by
    rw [k₅ .x2 (by decide), k₄ .x2 (by decide), hsp]
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000825c_spec hpc₅ (by
    rv_eval [hsp₅]; and_intros <;> valid_access hval [hb1])
  have k₆ := b8000825c_keeps h₆
  have hf₆ := DFrame.of_memFrame (b8000825c_frame h₆ (by rw [hsp₅]; addr_omega [hb1]))
  rw [hsp₅, show s.getReg .x2 - 496 + 120 = s.getReg .x2 - 376 by addr_omega [hb1]] at hf₆
  have hsp₆ : u₆.getReg .x2 = s.getReg .x2 - 496 := (k₆ .x2 (by decide)).trans hsp₅
  have hfv₆ : DFrame v u₆ (Within · (s.getReg .x2 - 376) 56) :=
    (DFrame.of_same hm₅ _).trans hf₆ fun _ h ↦ h
  have hn₆ : heapNext u₆ = heapNext v := by
    simp only [heapNext]
    have hx := hpre.stack.next
    simp only [stack_eq] at hx
    exact congrArg BitVec.toNat (hfv₆ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hx, hb1])
  have I₆ : Inv s u₆ := Iv.loc hpre (hfv₆.mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1]))
    ⟨hn₆ ▸ Iv.heap.lo, hn₆ ▸ Iv.heap.hi⟩ hn₆.ge (hsp₆.trans hsp.symm)
  have slot (a : Word) (ha : Apart a 8 (s.getReg .x2 - 376) 56) (hab : a.toNat + 8 ≤ 2 ^ 64) :
      u₆.getMem a = v.getMem a := hfv₆ a fun i hi hw ↦ by addr_omega [hw, hi, ha, hab, hb1]
  have hlo := hpre.heap.lo
  simp only [heapStart] at hlo
  have hHr := hpre.heights.region
  have hEr := hpre.equalityPoint.region
  have hHf := hpre.heights.free
  have hEf := hpre.equalityPoint.free
  have hHs := hpre.heights.stack
  have hEs := hpre.equalityPoint.stack
  simp only [stack_eq, Outside, heapEnd] at hHs hEs hHf hEf
  have hbv := hbufv
  simp only [NewBuf] at hbv
  have hsle : heapNext s ≤ heapNext u := hmu
  simp only [heapEnd] at hhv hhu
  have hpt : (ch.reverse).length = L := by rw [List.length_reverse]
  have hvP (j : ℕ) (hj : j < L) : eAt u₆ (P + BitVec.ofNat 64 (24 * j)) = ch.reverse.getD j 0 := by
    have e : eAt u₆ (P + BitVec.ofNat 64 (24 * j)) = eAt v (P + BitVec.ofNat 64 (24 * j)) :=
      hfv₆.eAt fun i hi hw ↦ by
        rcases hPb.2 with h0 | h0
        · omega
        · addr_omega [hw, hi, h0, hhu, hs₂, hb1, hj]
    rw [e, ← hptv, eListAt_getD _ _ hj]
  have hW1 : (s.getReg .x12).toNat = 0 ∨ (heapNext u ≤ W.toNat ∧
      W.toNat + 24 * (s.getReg .x12).toNat ≤ heapNext v) := by
    rcases hbv.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr h0
  have hn32 : (s.getReg .x12).toNat < 2 ^ 32 := by simp only [heapNext] at hW1 hhv; omega
  have hh32 : (s.getReg .x14).toNat < 2 ^ 32 := by
    rcases hHr with h0 | h0
    · omega
    · simp only [Region, Mapped] at h0; omega
  have he32 : (tsEqLen s).toNat < 2 ^ 32 := by
    rcases hEr with h0 | h0
    · omega
    · simp only [Region, Mapped] at h0; omega
  have hL32 : L < 2 ^ 32 := by
    rcases hPb.2 with h0 | h0
    · omega
    · simp only [heapNext] at h0 hhu; omega
  have hEv : ValidMemRange (s.getReg .x31) (3 * (tsEqLen s).toNat) := by
    rcases hEr with h0 | h0
    · intro i hi; omega
    · refine region_range ?_
      rw [show 8 * (3 * (tsEqLen s).toNat) = 24 * (tsEqLen s).toNat by ring]
      exact h0
  have hc : OuterCtx s u₆ P W (s.getReg .x31) (s.getReg .x13) L (s.getReg .x12).toNat
      (s.getReg .x14).toNat (tsEqLen s).toNat ch.reverse
      (natsAt s (s.getReg .x13) (s.getReg .x14).toNat)
      (eListAt s (s.getReg .x31) (tsEqLen s).toNat) := {
    ro := I₆.rodata hpre
    wb := by
      rcases hW1 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by simp only [heapNext] at h0 hsle hlo ⊢; omega,
          by simp only [heapNext] at h0 hhv; omega⟩
    w3 := hbv.1
    hr := hpre.heights.range
    hW := by
      simp only [heapNext] at hW1 hsle hHf hhv
      rcases hW1 with h0 | h0
      · addr_omega [h0]
      · addr_omega [h0, hHf, hsle, hhv]
    hS := hHs
    hv := fun i hi ↦ by
      rw [natsAt_getD _ _ hi]
      have hb := ValidMemRange.bounds (hpre.heights.range) (by omega)
      rw [I₆.word hpre.heights (by addr_omega [hb, hi]) (by addr_omega [hb, hi])]
    pr := heap_range (by simp only [heapNext] at hPb hsle hlo; omega)
      (by simp only [heapNext] at hPb hhu; omega) hPb.1
    pW := by
      simp only [heapNext] at hW1 hPb
      rcases hW1 with h0 | h0
      · addr_omega [h0]
      · addr_omega [h0, hPb, hL1]
    pS := by
      simp only [heapNext] at hPb hhu
      addr_omega [hPb, hhu, hs₂, hb1, hL1]
    pv := hvP
    er := hEv
    eW := by
      simp only [heapNext] at hW1 hsle hEf hhv
      rcases hW1 with h0 | h0
      · addr_omega [h0]
      · addr_omega [h0, hEf, hsle, hhv]
    eS := hEs
    ev := fun j hj ↦ by
      have hb := ValidMemRange.bounds hEv (by omega)
      rw [eListAt_getD _ _ hj, I₆.elem hpre.equalityPoint (by addr_omega [hb, hj])
        (by addr_omega [hb, hj])]
    eqSlot := by
      rw [I₆.word hpre.args (by addr_omega [hb1, hb2]) (by addr_omega [hb1, hb2])]
      simp [tsEqLen]
    epSlot := by
      rw [h₆.frame _ (by rv_eval [hsp₅]; and_intros <;> addr_omega [hb1]), hm₅]
      exact hAv.equalityPoint
    hpSlot := by
      rw [h₆.frame _ (by rv_eval [hsp₅]; and_intros <;> addr_omega [hb1]), hm₅]
      exact hAv.heights
    endSlot := by
      have e := b8000825c_m_x2_152 h₆
      rw [hsp₅, k₅ .x12 (by decide), b80008234_x12 h₄, hm₅, e112,
        show u.getReg .x9 = BitVec.ofNat 64 L by
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, hx9, Nat.mod_eq_of_lt (by omega)],
        mul24] at e
      rv_eval [] at e
      rw [e, hKv.point]
    hlenSlot := by
      have e := b8000825c_m_x2_160 h₆
      rw [hsp₅, k₅ .x26 (by decide), k₄ .x26 (by decide), hregs .x26 (by decide), h.x26] at e
      rv_eval [] at e
      rw [e]; simp
    countSlot := by
      have e := b8000825c_m_x2_120 h₆
      rw [hsp₅, k₅ .x10 (by decide), b80008234_x10 h₄, e192] at e
      rv_eval [] at e
      rw [e]; addr_omega [hn32]
    wSlot := by
      have e := b8000825c_m_x2_128 h₆
      rw [hsp₅, hm₅] at e
      rv_eval [] at e
      rw [e, hW, vecPtr]; congr 1; addr_omega [hb1]
    ptLen := hpt
    hsLen := natsAt_length _ _ _
    bounds := ⟨hL32, hn32, hh32, he32⟩ }
  have hvW (j : ℕ) (hj : j < (s.getReg .x12).toNat) :
      eAt u₆ (W + BitVec.ofNat 64 (24 * j)) = 1 := by
    have e : eAt u₆ (W + BitVec.ofNat 64 (24 * j)) = eAt v (W + BitVec.ofNat 64 (24 * j)) :=
      hfv₆.eAt fun i hi hw ↦ by
        simp only [heapNext] at hW1 hhv
        rcases hW1 with h0 | h0
        · omega
        · addr_omega [hw, hi, h0, hhv, hs₂, hb1, hj]
    rw [e, ← eListAt_getD _ _ hj, helv]
    simp [hj]
  obtain ⟨t, hrt, ⟨hpct, hx2t, hx26t, hft, helt⟩ | hd⟩ :=
    outerLoop hMul hpre hc rfl (L - 0) 0 u₆ rfl (by omega) {
      pc := b8000825c_pc h₆
      x2 := hsp₆
      x19 := by rw [b8000825c_x19 h₆]; rfl
      x26 := by
        rw [k₆ .x26 (by decide), k₅ .x26 (by decide), k₄ .x26 (by decide), hregs .x26 (by decide),
          h.x26]; simp
      x24 := fun h1 ↦ by
        have hHb := ValidMemRange.bounds hpre.heights.range (by omega)
        have e144 : u₅.getMem (u₅.getReg .x2 + 144) = s.getReg .x13 := by
          rw [hsp₅, hm₅, show s.getReg .x2 - 496 + 144 = s.getReg .x2 - 352 by addr_omega [hb1]]
          exact hAv.heights
        rw [b8000825c_x24 h₆, hx11₅ h1 hh32, e144]
        addr_omega [hHb, hn32, hh32, h1]
      veq := Nat.zero_le _
      cursor := by
        have e := b8000825c_m_x2_168 h₆
        rw [hsp₅, hm₅] at e; rv_eval [] at e
        rw [e, hKv.point]; simp
      frame := DFrame.refl _ _
      elems := fun j hj ↦ by
        rw [hvW j hj]
        simp [twPre, hj] }
  swap
  · exact ⟨t, hrv.trans (hr₄.trans (hr₅.trans (hr₆.trans hrt))), Or.inr hd⟩
  have hx := hpre.stack.next
  simp only [stack_eq] at hx
  -- what the point loop writes misses all but the weights
  have hWb := hc.wb
  have ow (a : Word) (ha : OW s W (s.getReg .x12).toNat a) :
      ¬ Within a (s.getReg .x2 - 488) 56 ∧ ¬ Within a (s.getReg .x2 - 432) 40 ∧
      ¬ Within a (s.getReg .x2 - 360) 16 ∧ ¬ Within a (s.getReg .x2 - 392) 16 ∧
      ¬ Within a (s.getReg .x2 - 320) 24 ∧ ¬ Within a (s.getReg .x2 - 104) 104 ∧
      ¬ Within a nextAddr 8 := by
    rcases ha with (ha | ha | ha) | ha <;>
      exact ⟨by addr_omega [ha, hb1, hWb], by addr_omega [ha, hb1, hWb],
        by addr_omega [ha, hb1, hWb], by addr_omega [ha, hb1, hWb], by addr_omega [ha, hb1, hWb],
        by addr_omega [ha, hb1, hWb, hs₂], by addr_omega [ha, hb1, hWb, hx]⟩
  have hnt : heapNext t = heapNext u₆ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hft nextAddr fun i hi hw ↦ (ow _ hw).2.2.2.2.2.2
      (by addr_omega [hi]))
  have hHt : HeapOk t := ⟨hnt ▸ I₆.heap.lo, hnt ▸ I₆.heap.hi⟩
  have hfresh (a : Word) (ha : Within a W (24 * (s.getReg .x12).toNat)) :
      heapNext u ≤ a.toNat ∧ a.toNat < heapNext t := by
    rw [hnt, hn₆]
    simp only [heapNext] at hW1 ⊢
    rcases hW1 with h0 | h0
    · simp only [Within] at ha; omega
    · simp only [Within] at ha; omega
  have It : Inv s t := I₆.step hpre hft (fun a ha ↦ by
    refine ⟨?_, (ow a ha).2.2.2.2.2.1⟩
    rcases ha with (ha | ha | ha) | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨le_trans hsle (hfresh a ha).1, (hfresh a ha).2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha, hb1])))))
    hHt hnt.ge (hx2t.trans hsp₆.symm)
  -- `u₆`'s arguments: `0x8000825c` writes around them
  have hA₆ : Args s u₆ := {
    formPowers := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans hAv.formPowers
    forms := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans hAv.forms
    constraintPowers := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans
      hAv.constraintPowers
    constraintLen := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans hAv.constraintLen
    tables := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans hAv.tables
    equalityPoint := by
      rw [h₆.frame _ (by rv_eval [hsp₅]; and_intros <;> addr_omega [hb1]), hm₅]
      exact hAv.equalityPoint
    heights := by
      rw [h₆.frame _ (by rv_eval [hsp₅]; and_intros <;> addr_omega [hb1]), hm₅]
      exact hAv.heights }
  have keep6 (a : Word) (ha : Apart a 8 (s.getReg .x2 - 376) 56) (hab : a.toNat + 8 ≤ 2 ^ 64)
      (hw : ∀ i < 8, ¬ OW s W (s.getReg .x12).toNat (a + BitVec.ofNat 64 i)) :
      t.getMem a = v.getMem a := (hft a hw).trans (slot a ha hab)
  have hfut : DFrame u t (Loc s u t) := by
    refine ((hfv.mono fun a ha ↦ ?_).trans hfv₆ fun a ha ↦ Or.inl (by addr_omega [ha, hb1])).trans
      hft fun a ha ↦ ?_
    · rcases ha with ha | ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨h1, by rw [hnt, hn₆]; exact h2⟩)
    · rcases ha with (ha | ha | ha) | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inr (hfresh a ha))
      · exact Or.inl (by addr_omega [ha, hb1])
  have owk (a : Word) (hA : ¬ Within a (s.getReg .x2 - 200) 72 ∧ ¬ Within a (s.getReg .x2 - 2128) 1632 ∧
      ¬ Within a (s.getReg .x2 - 328) 8 ∧ ¬ Within a W (24 * (s.getReg .x12).toNat)) :
      ¬ OW s W (s.getReg .x12).toNat a := by
    rintro ((h0 | h0 | h0) | h0)
    · exact hA.1 h0
    · exact hA.2.1 h0
    · exact hA.2.2.2 h0
    · exact hA.2.2.1 h0
  refine ⟨t, hrv.trans (hr₄.trans (hr₅.trans (hr₆.trans hrt))), Or.inl ⟨W, hpct, {
    inv := It
    kept := (hKv.step hfv₆ (fun a ha ↦ by addr_omega [ha, hb1]) hb1).step hft
      (fun a ha ↦ (ow a ha).1) hb1
    args := hA₆.step hft (fun a ha ↦ ⟨(ow a ha).2.1, (ow a ha).2.2.1⟩) hb1
    tablesLen := by
      rw [keep6 _ (by addr_omega [hb1]) (by addr_omega [hb1]) fun i hi hw ↦
        (ow _ hw).2.2.2.1 (by addr_omega [hi, hb1])]
      exact m392
    pointLen := by
      rw [keep6 _ (by addr_omega [hb1]) (by addr_omega [hb1]) fun i hi hw ↦
        (ow _ hw).2.2.2.1 (by addr_omega [hi, hb1]), m384, hx9]
    x26 := by rw [hx26t]; simp
    wptr := by
      rw [vecPtr, keep6 _ (by addr_omega [hb1]) (by addr_omega [hb1]) fun i hi hw ↦
        (ow _ hw).2.2.2.2.1 (by addr_omega [hi, hb1])]
      rfl
    wlen := by
      rw [vecLen, keep6 _ (by addr_omega [hb1]) (by addr_omega [hb1]) fun i hi hw ↦
        (ow _ hw).2.2.2.2.1 (by addr_omega [hi, hb1])]
      exact hlenv
    wbuf := by
      simp only [NewBuf] at hbv ⊢
      rw [hnt, hn₆]
      omega
    weights := by
      rw [weightsOf, ← twPre_length_eq _ _ _ _, hpt]
      apply List.ext_getElem (by rw [eListAt_length, twPre_length])
      intro j h1 h2
      rw [eListAt_getElem, ← List.getD_eq_getElem _ 0 h2]
      exact helt j (by rw [eListAt_length] at h1; exact h1)
    buf := by
      simp only [NewBuf] at hPb ⊢
      rw [hnt, hn₆]
      simp only [heapNext] at hPb hmv huv ⊢
      omega
    point := by
      rw [← hptv]
      simp only [heapNext] at hPb hhu hW1
      rw [hft.eListAt fun i hi hw ↦ by
        rcases hPb.2 with h0 | h0
        · omega
        · rcases hw with (hw | hw | hw) | hw
          · addr_omega [hw, hi, h0, hhu, hs₂, hb1]
          · addr_omega [hw, hi, h0, hhu, hs₂, hb1]
          · rcases hW1 with h1 | h1
            · simp only [Within] at hw; omega
            · addr_omega [hw, hi, h0, h1]
          · addr_omega [hw, hi, h0, hhu, hs₂, hb1]]
      exact hfv₆.eListAt fun i hi hw ↦ by
        rcases hPb.2 with h0 | h0
        · omega
        · addr_omega [hw, hi, h0, hhu, hs₂, hb1]
    run := fun T hT ↦ by
      obtain ⟨T', e, hT'⟩ := h.run T hT
      exact ⟨T', e, h.inv.transcript hpre hHt hfut hT'⟩ }⟩⟩
