import Rv64Verifier.Proofs.Bus.TsRows

/-!
# `table_sumcheck`: the rows loop's iteration

From `0x80008484`, `next_scalars(TABLE_WIDTHS[opcode])` into `S - 152` (`rowsScalars`); an `Err`
returns through `0x800084f8` (`rowsErr`). Then the pair is stored at the rows' end
(`0x800083f4`) and the loop goes on at `0x80008428` or leaves for `0x80008508` (`rowsIter`,
`rowsLoop`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The table and the height of item `i`, as the code reads them. -/
theorem readRows_drop (s : MachineState) (p : List E) (rows : List (List E × List E)) {i : ℕ}
    (hi : i < min (s.getReg .x12).toNat (s.getReg .x14).toNat) (T : TState) :
    (readRowsM p ((rowItems s).drop i) rows).run T =
      ((TM.nextScalars (tables.getD (s.getMem (s.getReg .x11 +
        BitVec.ofNat 64 (80 * i + 72))).toNat default).width).run T).bind fun r ↦
        (readRowsM p ((rowItems s).drop (i + 1)) (rows ++
          [(p.take (s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i))).toNat, r.1)])).run r.2 := by
  rw [List.drop_eq_getElem_cons (by rw [rowItems_length]; exact hi), rowItems_getElem,
    readRowsM_cons]

/-- `next_scalars`' arguments: `S - 152` and the transcript. -/
theorem scalarsPre {s v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s v)
    (h10 : v.getReg .x10 = s.getReg .x2 - 152) (h11 : v.getReg .x11 = tsSelf s) :
    NextScalarsPre v := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hsl : stackLo v nextScalarsStack = s.getReg .x2 - 1760 := by
    show v.getReg .x2 - BitVec.ofNat 64 1264 = _
    rw [h.sp]; addr_omega [hb1]
  have hm := h.mono
  have hn := h.heap.hi
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  have hr := hpre.stack.rodata
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have ps := hpre.proofStack
  have pf := hpre.proofFree
  have bf := hpre.streamFree
  have hrb : rodataBase.toNat = 2684354560 := rfl
  simp only [stack_eq] at ha hx hr ss ps
  simp only [ProofApart] at ps
  simp only [Outside, heapNext, heapEnd] at sf pf bf hm hn ha
  have hs8 : (tsSelf s).toNat + 368 ≤ 2 ^ 64 := by addr_omega [hS]
  exact {
    heap := h.heap
    out := by rw [h10]; addr_omega [hb1, hb2, hb3]
    self := h11 ▸ h.tok hpre
    stack := hpre.stack.sub 496 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [h10, hsl]; addr_omega [hb1]
    selfStack := by rw [h11, hsl]; addr_omega [hb1, ss]
    outSelf := by rw [h10, h11]; addr_omega [hb1, ss, hs8]
    proofStack := by
      simp only [ProofApart, h11, hsl, e0, e1, e2]
      exact ⟨by addr_omega [hb1, ps.1], by addr_omega [hb1, ps.2]⟩
    proofOut := by
      simp only [ProofApart, h10, h11, e0, e1, e2]
      exact ⟨by addr_omega [hb1, ps.1], by addr_omega [hb1, ps.2]⟩
    outFree := by rw [h10]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    selfFree := by rw [h11]; simp only [Outside, heapNext, heapEnd]; addr_omega [sf, hm]
    proofFree := by rw [h11, e0]; simp only [Outside, heapNext, heapEnd]; addr_omega [pf, hm]
    streamFree := by rw [h11, e1, e2]; simp only [Outside, heapNext, heapEnd]; addr_omega [bf, hm]
    rodata := h.rodata hpre
    outRodata := by rw [h10]; addr_omega [hb1, hr, hrb]
    selfRodata := h11 ▸ hpre.selfRodata }

/-- `Err` from `next_scalars`: `0x800084f8` stores it in the result, then `0x80008928`. -/
theorem rowsErr {s v : MachineState} {cl : E} {P : Word} (hpre : TableSumcheckPre s)
    (I : Inv s v) (hK : Kept s v cl P) (hpc : v.pc = 0x800084f8)
    (hnone : ∀ T, TranscriptAt s (tsSelf s) T → (mirror s).run T = none) :
    ∃ t, Reaches Image.code v t ∧ Done s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have ho := hpre.out
  have os := hpre.outStack
  have ox := hpre.outFree.2
  simp only [stack_eq] at os
  have h40 : v.getMem (v.getReg .x2 + 40) = s.getReg .x10 := by
    rw [I.sp, show s.getReg .x2 - 496 + 40 = s.getReg .x2 - 456 by addr_omega [hb1]]; exact hK.out
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b800084f8_spec hpc (by
    rv_eval [h40]
    and_intros
    · exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho]) (by addr_omega [ho])
    · rw [I.sp]; valid_access hval [hb1])
  have hf : DFrame v t (Within · (s.getReg .x10) 24) := fun a ha ↦
    ht.frame a (by
      rv_eval [h40]
      have h0 := ha 0 (by decide)
      rw [add_ofNat_zero] at h0
      exact fun e ↦ h0 (by rw [e]; addr_omega [ho]))
  have hn : heapNext t = heapNext v := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf nextAddr fun i hi hw ↦ by addr_omega [hw, hi, ox])
  have I' : Inv s t := I.step hpre hf (fun a ha ↦ ⟨Or.inl ha, by addr_omega [ha, os, hb1]⟩)
    ⟨hn ▸ I.heap.lo, hn ▸ I.heap.hi⟩ hn.ge (b800084f8_keeps ht .x2 (by decide))
  obtain ⟨t', hr', ht'⟩ := err928 hpre I' (b800084f8_pc ht)
    (by rw [hf _ fun i hi hw ↦ by addr_omega [hw, hi, os, hb1]]; exact hK.out)
    (Or.inr (b800084f8_x10 ht)) hnone
  exact ⟨t', hr.trans hr', ht'⟩

/-- What `next_scalars` writes: its stack, `S - 152`, the transcript's sponge and offsets,
`NEXT`, the heap allocated. -/
def NW (s v t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2128) 1632 ∨ Within a (s.getReg .x2 - 152) 24 ∨
    Within a (tsSelf s + 8) 344 ∨ Within a nextAddr 8 ∨ Fresh v t a

theorem NW.miss {s v t : MachineState} (hpre : TableSumcheckPre s) (ht : HeapOk t) {a : Word}
    (ha : NW s v t a) :
    ¬ Within a (s.getReg .x2 - 488) 208 ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hs := hpre.stack.above
  have ss := hpre.selfStack
  have hS := hpre.self.self
  have hh := ht.hi
  simp only [stack_eq] at hs ss
  simp only [heapEnd, heapNext] at hh hs
  rcases ha with ha | ha | ha | ha | ⟨-, h2⟩
  all_goals first
    | exact ⟨by addr_omega [ha, hb1, hs, ss, hS], by addr_omega [ha, hb1, hs, ss, hS]⟩
    | (simp only [heapNext] at h2
       exact ⟨by addr_omega [h2, hb1, hs, hh], by addr_omega [h2, hb1, hs, hh]⟩)

theorem AW.nw {s v t : MachineState} {a : Word} (ha : AW s v t a) : NW s v t a := by
  rcases ha with ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))

/-- From `0x80008484` to `0x800084c4`: the opcode checked, `next_scalars(TABLE_WIDTHS[opcode])`
into `S - 152`, its `Vec` in `s10`, `s2`, `s7`; an `Err` returns. -/
theorem rowsScalars (hNS : NextScalarsSpec) {s u r v v₃ : MachineState} {ch : List E} {cl : E}
    {P W R : Word} {n i : ℕ} {rows : List (List E × List E)} (hpre : TableSumcheckPre s)
    (hc : RowsCtx s u r ch cl P W R n) (h : RowsHead s u r v ch cl R n i rows) (hi : i < n)
    (hpc : v₃.pc = 0x80008484) (I₃ : Inv s v₃) (hf₃ : DFrame v v₃ (AW s v v₃))
    (h22 : v₃.getReg .x22 = v.getReg .x22)
    (hT₃ : ∀ T, TranscriptAt v (tsSelf s) T → TranscriptAt v₃ (tsSelf s) T) :
    ∃ v₇, Reaches Image.code v₃ v₇ ∧ ((v₇.pc = 0x800084c4 ∧ Inv s v₇ ∧ DFrame v₃ v₇ (NW s v₃ v₇) ∧
      heapNext v₃ ≤ heapNext v₇ ∧
      (∀ r ∈ ([.x8, .x9, .x19, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg),
        v₇.getReg r = v₃.getReg r) ∧
      v₇.getReg .x26 = vecCap v₇ (s.getReg .x2 - 152) ∧
      v₇.getReg .x18 = vecPtr v₇ (s.getReg .x2 - 152) ∧
      v₇.getReg .x23 = vecLen v₇ (s.getReg .x2 - 152) ∧
      ∃ xs, NewVecE v₃ v₇ (s.getReg .x2 - 152) xs ∧ ∀ T, TranscriptAt v₃ (tsSelf s) T → ∃ T',
        (TM.nextScalars (tables.getD (s.getMem (s.getReg .x11 +
          BitVec.ofNat 64 (80 * i + 72))).toNat default).width).run T = some (xs, T') ∧
        TranscriptAt v₇ (tsSelf s) T') ∨ Done s v₇) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hsp₃ := I₃.sp
  have hn := hc.n
  have hTr : RO s tableSumcheckStack (tsWrites s) (tsSelf s) (s.getReg .x11)
      (8 * (10 * (s.getReg .x12).toNat)) := by
    rw [show 8 * (10 * (s.getReg .x12).toNat) = 80 * (s.getReg .x12).toNat by ring]
    exact hpre.tables
  have hTv := hTr.range
  have hTb := ValidMemRange.bounds hTv (by omega)
  have hx22 : v₃.getReg .x22 = s.getReg .x11 + BitVec.ofNat 64 (80 * i + 72) := h22.trans h.x22
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008484_spec hpc (by
    rv_eval [hx22]; valid_access hTv [hTb, hi, hn])
  have hm₄ := b80008484_mem_same h₄
  have k₄ := b80008484_keeps h₄
  set op := s.getMem (s.getReg .x11 + BitVec.ofNat 64 (80 * i + 72)) with hop_def
  have hop : v₃.getMem (v₃.getReg .x22) = op := by
    rw [hx22]; exact I₃.word hpre.tables (by addr_omega [hTb, hi, hn]) (by addr_omega [hTb, hi, hn])
  by_cases h6 : 6 ≤ op.toNat
  · exact ⟨v₄, hr₄, Or.inr (Or.inr (trap (b80008484_pc_taken h₄ (by rw [hop]; exact h6))))⟩
  have hsp₄ : v₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hsp₃
  have hh₃ := I₃.heap.hi
  have e168 : v₄.getMem (s.getReg .x2 - 328) = 0xa0000460 := by
    rw [hm₄, hf₃ _ fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, h2⟩
      · addr_omega [hw, hj, hb1]
      · addr_omega [hw, hj, hb1]
      · addr_omega [hw, hj, hb1]
      · have ha := hpre.stack.above
        simp only [stack_eq, heapNext, heapEnd] at ha h2 hh₃
        addr_omega [h2, hj, hb1, ha, hh₃]]
    exact h.widths
  have hwr : ValidMemRange 0xa0000460 6 := region_range ⟨Or.inr ⟨by decide, by decide⟩, by decide⟩
  have h10₄ : v₄.getReg .x10 = op := (b80008484_x10 h₄).trans hop
  have hA := hpre.args.region
  have h6' : op.toNat < 6 := by omega
  have hmul : (0xa0000460 : Word) + op * 8 = 0xa0000460 + BitVec.ofNat 64 (8 * op.toNat) := by
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
    simp only [Sym.wordToNatLit]
    omega
  obtain ⟨v₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80008490_spec
    (b80008484_pc_not_taken h₄ (by rw [hop]; simp only [Sym.wordToNatLit]; omega)) (by
      rv_eval [hsp₄, e168, h10₄]
      and_intros
      · rcases hA with h0 | h0
        · omega
        · exact Region.valid h0 (by addr_omega [h0]) (by addr_omega [h0]) (by addr_omega [h0])
      · rw [hmul]; valid_access hwr [h6']
      · valid_access hval [hb1])
  have hm₅ := b80008490_mem_same h₅
  have k₅ := b80008490_keeps h₅
  have hsp₅ : v₅.getReg .x2 = s.getReg .x2 - 496 := (k₅ .x2 (by decide)).trans hsp₄
  have h10₅ : v₅.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b80008490_x10 h₅, hsp₄]; addr_omega [hb1]
  have h11₅ : v₅.getReg .x11 = tsSelf s := by
    rw [b80008490_x11 h₅, hsp₄, show s.getReg .x2 - 496 + 512 = s.getReg .x2 + 16 by
      addr_omega [hb1, hb2], hm₄]
    exact I₃.word hpre.args (by addr_omega [hb1, hb2]) (by addr_omega [hb1, hb2])
  have hro₄ : RodataOk v₄ := fun p hp ↦ (hm₄ _).trans (I₃.rodata hpre p hp)
  have h12₅ : (v₅.getReg .x12).toNat = (tables.getD op.toNat default).width := by
    rw [b80008490_x12 h₅, hsp₄, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by
      addr_omega [hb1], e168, h10₄]
    exact width_at hro₄ h6'
  have I₅ : Inv s v₅ := (I₃.same hpre hm₄ (k₄ .x2 (by decide))).same hpre hm₅ (k₅ .x2 (by decide))
  obtain ⟨v₆, hr₆, ⟨hpc₆, hp₆, post₆⟩ | hd⟩ :=
    hNS.call hr₅ (b80008490_pc h₅) (scalarsPre hpre I₅ h10₅ h11₅)
  swap
  · exact ⟨v₆, hr₄.trans hr₆, Or.inr (Or.inr hd)⟩
  have hsl : stackLo v₅ nextScalarsStack = s.getReg .x2 - 1760 := by
    show v₅.getReg .x2 - BitVec.ofNat 64 1264 = _
    rw [hsp₅]; addr_omega [hb1]
  have hf₆ := post₆.frame
  simp only [TFrame] at hf₆
  rw [h10₅, h11₅, hsl] at hf₆
  have I₆ : Inv s v₆ := I₅.locT hpre (hf₆.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr ha)
      · exact Or.inl (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inl (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inr ha))) post₆.heap post₆.mono (hp₆.reg .x2)
  have hsp₆ : v₆.getReg .x2 = s.getReg .x2 - 496 := (hp₆.reg .x2).trans hsp₅
  obtain ⟨v₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800084b0_spec
    (by rw [hpc₆, returnAddress_eq, b80008490_x1 h₅]; decide) (by
      rv_eval [hsp₆]; and_intros <;> valid_access hval [hb1])
  have hm₇ := b800084b0_mem_same h₇
  have k₇ := b800084b0_keeps h₇
  have I₇ : Inv s v₇ := I₆.same hpre hm₇ (k₇ .x2 (by decide))
  have hcap : v₆.getMem (v₆.getReg .x2 + 344) = vecCap v₆ (s.getReg .x2 - 152) := by
    rw [hsp₆]; simp only [vecCap]; congr 1; addr_omega [hb1]
  -- the transcripts the entry's stands for, at `v₅`
  have hT₅ (T : TState) (hT : TranscriptAt v₃ (tsSelf s) T) :
      TranscriptAt v₅ (v₅.getReg .x11) T :=
    h11₅ ▸ (I₃.same hpre hm₄ (k₄ .x2 (by decide))).transcript hpre I₅.heap
      (DFrame.of_same hm₅ _) (I₃.transcript hpre (I₃.same hpre hm₄ (k₄ .x2 (by decide))).heap
        (DFrame.of_same hm₄ _) hT)
  have hfN : DFrame v₃ v₇ (NW s v₃ v₇) := (((DFrame.of_same (fun a ↦ (hm₅ a).trans (hm₄ a))
    (NW s v₃ v₇)).trans hf₆ fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))
        · simp only [heapNext, hm₅, hm₄] at h1 ⊢; exact h1
        · simp only [heapNext, hm₇] at h2 ⊢; exact h2).trans
    (DFrame.of_same hm₇ fun _ ↦ False) fun _ h ↦ h.elim)
  have hn₇ : heapNext v₃ ≤ heapNext v₇ := by
    have := post₆.mono
    simp only [heapNext, hm₇, hm₅, hm₄] at this ⊢
    exact this
  have hR (r : Reg) (hr : r ∈ ([.x8, .x9, .x19, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg)) :
      v₇.getReg r = v₃.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₇ _ (by decide), hp₆ _ (by decide), k₅ _ (by decide), k₄ _ (by decide)]
  by_cases herr : vecCap v₆ (s.getReg .x2 - 152) = errNiche
  · -- `Err`
    have hpc₇ := b800084b0_pc_taken h₇ (by rw [hcap]; exact herr)
    have hK : Kept s v₇ cl P := ((h.kept hpre hc).step hf₃ (fun a ha hw ↦
      (NW.miss hpre I₃.heap ha.nw).1 (by addr_omega [hw, hb1])) hb1).step hfN
        (fun a ha hw ↦ (NW.miss hpre I₇.heap ha).1 (by addr_omega [hw, hb1])) hb1
    obtain ⟨t, hrt, ht⟩ := rowsErr hpre I₇ hK hpc₇ fun T hT ↦ by
      obtain ⟨T₁, T₂, e1, e2, hT₂⟩ := h.run T hT
      have hv := post₆.value T₂ (hT₅ T₂ (hT₃ T₂ hT₂))
      rw [h12₅, h10₅] at hv
      rcases e : (TM.nextScalars (tables.getD op.toNat default).width).run T₂ with _ | ⟨xs, T₃⟩
      · refine mirror_run_none s e1 (e2.trans ?_)
        rw [readRows_drop s _ _ (hn ▸ hi), e]
        rfl
      · rw [e] at hv; exact absurd herr hv.1
    exact ⟨t, hr₄.trans (hr₆.trans (hr₇.trans hrt)), Or.inr ht⟩
  -- `Ok`: the values, fixed by any transcript
  have hpc₇ := b800084b0_pc_not_taken h₇ (by rw [hcap]; exact herr)
  obtain ⟨T₀, hT₀⟩ := exists_transcriptAt v₃ (tsSelf s)
  have hv₀ := post₆.value T₀ (hT₅ T₀ hT₀)
  rw [h12₅, h10₅] at hv₀
  rcases e₀ : (TM.nextScalars (tables.getD op.toNat default).width).run T₀ with _ | ⟨xs, T₀'⟩
  · rw [e₀] at hv₀; exact absurd hv₀ herr
  rw [e₀] at hv₀
  obtain ⟨-, hvec, -⟩ := hv₀
  refine ⟨v₇, hr₄.trans (hr₆.trans hr₇), Or.inl ⟨hpc₇, I₇, hfN, hn₇, hR, ?_, ?_, ?_, xs,
    (hvec.of_same hm₇).weaken (by simp only [heapNext, hm₅, hm₄]; exact le_refl _),
    fun T hT ↦ ?_⟩⟩
  · rw [b800084b0_x26 h₇, hcap]; simp only [vecCap, hm₇]
  · rw [b800084b0_x18 h₇, hsp₆]; simp only [vecPtr, hm₇]; congr 1; addr_omega [hb1]
  · rw [b800084b0_x23 h₇, hsp₆]; simp only [vecLen, hm₇]; congr 1; addr_omega [hb1]
  · have hv := post₆.value T (hT₅ T hT)
    rw [h12₅, h10₅] at hv
    rcases e : (TM.nextScalars (tables.getD op.toNat default).width).run T with _ | ⟨xs', T'⟩
    · rw [e] at hv; exact absurd hv herr
    rw [e] at hv
    obtain ⟨-, hvec', hT'⟩ := hv
    have exs : xs' = xs := hvec'.elems.symm.trans hvec.elems
    subst exs
    exact ⟨T', rfl, I₆.transcript hpre I₇.heap (DFrame.of_same hm₇ _) (h11₅ ▸ hT')⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
