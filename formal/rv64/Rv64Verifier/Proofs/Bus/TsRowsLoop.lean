import Rv64Verifier.Proofs.Bus.TsRowsIter

/-!
# `table_sumcheck`: the rows loop

`0x800084c4` skips `grow_one` (the rows' capacity is `tables.len()`, past the loop's count) and
`0x800083f4` stores the pair at the rows' end; `rowsIter` is one iteration from the head,
`rowsLoop` all of them, to `0x80008508`.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The stack below the saved registers, `NEXT` and the heap allocated since the entry. -/
def LocS (s v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2128) 2024 ∨ Within a nextAddr 8 ∨ Fresh s v a

/-- `Inv.transcript` for a step writing the heap allocated since the entry. -/
theorem Inv.transcriptS {s u v : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hv : HeapOk v) (hf : DFrame u v (LocS s v)) {T : TState}
    (hT : TranscriptAt u (tsSelf s) T) : TranscriptAt v (tsSelf s) T := by
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have ps := hpre.proofStack
  have pf := hpre.proofFree
  have bf := hpre.streamFree
  have hn := hv.hi
  rw [stackLo_eq, stack_eq] at ss ps
  simp only [ProofApart] at ps
  simp only [Outside, heapNext, heapEnd] at pf bf sf hn
  have loc (lo : Word) (n : Nat) (h1 : Apart lo n (s.getReg .x2 - 2128) 2128)
      (h2 : Apart lo n nextAddr 8) (h3 : lo.toNat + n ≤ (s.getMem nextAddr).toNat ∨
        0x78000000 ≤ lo.toNat) : Misses (LocS s v) lo n := fun y hy hl ↦ by
    simp only [LocS, Fresh, heapNext] at hl
    rcases hl with hl | hl | hl
    · addr_omega [hy, hl, h1]
    · addr_omega [hy, hl, h2]
    · addr_omega [hy, hl, h3, hn]
  refine hf.transcriptAt hT (h.tok hpre) (loc _ _ (by addr_omega [ss, hS])
    (by addr_omega [sf.2, hS]) (by addr_omega [sf.1, hS])) ?_ ?_
    (loc _ _ (by addr_omega [ss, hS]) (by addr_omega [sf.2, hS]) (by addr_omega [sf.1, hS]))
  · rw [e0]; exact loc _ _ ps.1 pf.2 pf.1
  · rw [e1, e2]; exact loc _ _ ps.2 bf.2 bf.1

/-- What an iteration from `v` writes: `next_scalars`' and the others' (`NW`), the rows' length
and the pair at `q`. -/
def IterW (s v t : MachineState) (q : Word) (a : Word) : Prop :=
  NW s v t a ∨ Within a (s.getReg .x2 - 280) 8 ∨ Within a q 48

theorem IterW.miss {s v t : MachineState} {q : Word} (hpre : TableSumcheckPre s) (ht : HeapOk t)
    (hq : q.toNat + 48 ≤ heapNext t) {a : Word} (ha : IterW s v t q a) :
    ¬ Within a (s.getReg .x2 - 488) 208 ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hs := hpre.stack.above
  have hh := ht.hi
  simp only [stack_eq] at hs
  simp only [heapEnd, heapNext] at hh hs hq
  rcases ha with ha | ha | ha
  · have := NW.miss hpre ht ha
    exact ⟨fun hw ↦ this.1 (by addr_omega [hw, hb1]), this.2⟩
  · exact ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1]⟩
  · exact ⟨by addr_omega [ha, hb1, hs, hh, hq], by addr_omega [ha, hb1, hs, hh, hq]⟩

/-- A heap range allocated before `v`, apart from `q`, misses what the iteration writes. -/
theorem IterW.heap {s v t : MachineState} {q p : Word} {m : ℕ} (hpre : TableSumcheckPre s)
    (hv : HeapOk v) (hp : m = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + m ≤ heapNext v ∧
      Apart p m q 48) : ∀ k < m, ¬ IterW s v t q (p + BitVec.ofNat 64 k) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hs := hpre.stack.above
  have sf := hpre.selfFree
  have hS := hpre.self.self
  have hh := hv.hi
  have hl := hpre.heap.lo
  simp only [stack_eq] at hs
  simp only [Outside, heapEnd, heapNext, heapStart] at hh hs sf hl hp
  intro k hk hw
  rcases hp with h0 | ⟨h1, h2, h3⟩
  · omega
  rcases hw with (hw | hw | hw | hw | ⟨hw, -⟩) | hw | hw
  all_goals first
    | addr_omega [hw, hk, h1, h2, h3, hb1, hs, hh, hl]
    | addr_omega [hw, hk, h1, h2, sf, hS, hh, hl]

theorem LocS.w {s v : MachineState} (hpre : TableSumcheckPre s) (hv : HeapOk v) {a : Word}
    (ha : LocS s v a) : W s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := hv.hi
  have hs := hpre.stack.above
  simp only [stack_eq] at hs
  rcases ha with ha | ha | ⟨h1, h2⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by rw [stackLo_eq]; addr_omega [ha])))),
      by addr_omega [ha, hb1]⟩
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))), by addr_omega [ha, hb1]⟩
  · refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))), ?_⟩
    simp only [heapEnd, heapNext] at hh h2 hs
    addr_omega [hh, h2, hb1, hs]

/-- A `Vec<E>` whose header is copied to `b`, its elements kept. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.move {s t t' : MachineState} {a b : Word}
    {xs : List E} (h : NewVecE s t a xs) (h0 : t'.getMem b = vecCap t a)
    (h1 : t'.getMem (b + 8) = vecPtr t a) (h2 : t'.getMem (b + 16) = vecLen t a)
    (he : eListAt t' (vecPtr t a) (vecLen t a).toNat = eListAt t (vecPtr t a) (vecLen t a).toNat)
    (hn : heapNext t ≤ heapNext t') : NewVecE s t' b xs := by
  have e0 : vecCap t' b = vecCap t a := h0
  have e1 : vecPtr t' b = vecPtr t a := h1
  have e2 : vecLen t' b = vecLen t a := h2
  obtain ⟨⟨hr, hl⟩, hb', he'⟩ := h
  simp only [RawVecOk, Buf, NewBuf, heapStart] at hr hb'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [RawVecOk, Buf, heapStart, e0, e1]; omega
  · rw [e0, e2]; exact hl
  · simp only [NewBuf, e0, e1]; omega
  · simp only [vecEs] at he' ⊢; rw [e1, e2, he]; exact he'

/-- One iteration from the head: the pair `(point[..height], evaluations)` pushed. -/
theorem rowsIter (hTA : TryAllocZeroedSpec) (hMC : MemcpySpec 0x800126e4)
    (hNS : NextScalarsSpec) {s u r v : MachineState} {ch : List E} {cl : E} {P W R : Word}
    {n i : ℕ} {rows : List (List E × List E)} (hpre : TableSumcheckPre s)
    (hc : RowsCtx s u r ch cl P W R n) (h : RowsHead s u r v ch cl R n i rows)
    (hpc : v.pc = 0x80008428) (hi : i < n) :
    ∃ t, Reaches Image.code v t ∧ ((∃ row, t.pc = (if i + 1 = n then 0x80008508 else 0x80008428) ∧
      RowsHead s u r t ch cl R n (i + 1) (rows ++ [row])) ∨ Done s t) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := h.inv
  obtain ⟨v₃, hr₃, ⟨hpc₃, I₃, hf₃, hn₃, k₃, h24₃, h8₃, h27₃, hle, hQb, hel₃⟩ | hd⟩ :=
    rowsAlloc hTA hMC hpre hc h hpc hi
  swap
  · exact ⟨v₃, hr₃, Or.inr (Or.inr hd)⟩
  have hT₃ (T : TState) (hT : TranscriptAt v (tsSelf s) T) : TranscriptAt v₃ (tsSelf s) T :=
    I.transcript hpre I₃.heap (hf₃.mono fun a ha ↦ AW.loc hb1 ha) hT
  obtain ⟨v₇, hr₇, ⟨hpc₇, I₇, hf₇, hn₇, k₇, h26₇, h18₇, h23₇, xs, hvec, hrun⟩ | hd⟩ :=
    rowsScalars hNS hpre hc h hi hpc₃ I₃ hf₃ (k₃ .x22 (by decide)) hT₃
  swap
  · exact ⟨v₇, hr₃.trans hr₇, Or.inr hd⟩
  have hn := hc.n
  set hw := s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i)) with hhw
  set nt := (s.getReg .x12).toNat with hnt
  -- the bounds
  have hRb := hc.rbuf
  have hur := hc.ur
  have hrv := h.rv
  have hmu := hc.atr.inv.mono
  have hhv := I₇.heap.hi
  have hlo := hpre.heap.lo
  have ha := hpre.stack.above
  simp only [stack_eq] at ha
  simp only [NewBuf] at hRb
  simp only [heapEnd] at hhv ha
  simp only [heapStart] at hlo
  have hvt7 : heapNext v ≤ heapNext v₇ := hn₃.trans hn₇
  have hR : heapNext u ≤ R.toNat ∧ R.toNat + 48 * nt ≤ heapNext r := by
    rcases hRb.2 with h0 | h0
    · omega
    · exact h0
  have hnt32 : nt < 2 ^ 32 := by omega
  have hRv : ValidMemRange R (6 * nt) := heap_range (by omega) (by omega) hRb.1
  have hsp₇ := I₇.sp
  have h9₇ : v₇.getReg .x9 = R := by rw [k₇ .x9 (by decide), k₃ .x9 (by decide), h.x9]
  have h19₇ : v₇.getReg .x19 = BitVec.ofNat 64 n := by
    rw [k₇ .x19 (by decide), k₃ .x19 (by decide), h.x19]
  have h20₇ : v₇.getReg .x20 = BitVec.ofNat 64 i := by
    rw [k₇ .x20 (by decide), k₃ .x20 (by decide), h.x20]
  have h21₇ : v₇.getReg .x21 = BitVec.ofNat 64 (48 * i) := by
    rw [k₇ .x21 (by decide), k₃ .x21 (by decide), h.x21]
  have h22₇ : v₇.getReg .x22 = s.getReg .x11 + BitVec.ofNat 64 (80 * i + 72) := by
    rw [k₇ .x22 (by decide), k₃ .x22 (by decide), h.x22]
  have h24₇ : v₇.getReg .x24 = s.getReg .x13 + BitVec.ofNat 64 (8 * i) := by
    rw [k₇ .x24 (by decide), h24₃, h.x11]
  have h8₇ : v₇.getReg .x8 = hw := by rw [k₇ .x8 (by decide), h8₃]
  have h27₇ : v₇.getReg .x27 = hw := by rw [k₇ .x27 (by decide), h27₃, h8₃]
  -- the frame from `v` to `v₇`
  have hf₀₇ : DFrame v v₇ (NW s v v₇) := (hf₃.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩)))).trans hf₇ fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ⟨h1, h2⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))
  -- `0x800084c4`: `rows.len() ≠ rows.capacity()`
  obtain ⟨v₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b800084c4_spec hpc₇ (by
    rv_eval [hsp₇]; valid_access hval [hb1])
  have hm₈ := b800084c4_mem_same h₈
  have k₈ := b800084c4_keeps h₈
  have e200 : v₇.getMem (v₇.getReg .x2 + 200) = s.getReg .x12 := by
    rw [hsp₇, show s.getReg .x2 - 496 + 200 = s.getReg .x2 - 296 by addr_omega [hb1],
      hf₀₇ _ fun j hj hw' ↦ (NW.miss hpre I₇.heap hw').1 (by addr_omega [hj, hb1])]
    exact h.cap
  have hpc₈ := b800084c4_pc_taken h₈ (by
    rw [e200, h20₇]
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    omega)
  have hsp₈ : v₈.getReg .x2 = s.getReg .x2 - 496 := (k₈ .x2 (by decide)).trans hsp₇
  have h9₈ : v₈.getReg .x9 = R := (k₈ .x9 (by decide)).trans h9₇
  have h21₈ : v₈.getReg .x21 = BitVec.ofNat 64 (48 * i) := (k₈ .x21 (by decide)).trans h21₇
  -- `0x800083f4`: the pair at `R + 48 i`
  obtain ⟨t, hrt, h₉⟩ := Sym.BlockSpec.reaches b800083f4_spec hpc₈ (by
    rv_eval [hsp₈, h9₈, h21₈]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hRv [hR, hi, hn, hrv, hur, hvt7, hhv]
      | addr_omega [hR, hi, hn, hrv, hur, hvt7, hhv, ha, hb1])
  have k₉ := b800083f4_keeps h₉
  have hRi : (R + BitVec.ofNat 64 (48 * i)).toNat = R.toNat + 48 * i := by
    addr_omega [hR, hi, hn, hrv, hur, hvt7, hhv]
  have hf₉ : DFrame v₈ t fun a ↦ Within a (s.getReg .x2 - 280) 8 ∨
      Within a (R + BitVec.ofNat 64 (48 * i)) 48 := fun a ha' ↦ h₉.frame a (by
    have h0 := ha' 0 (by decide)
    rw [add_ofNat_zero] at h0
    rv_eval [hsp₈, h9₈, h21₈]
    and_intros <;> intro e <;> exact h0 (by
      rw [e]
      first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hRi, hR, hi, hn, hrv, hur, hvt7, hhv])))
  have hx := hpre.stack.next
  simp only [stack_eq] at hx
  have hRi' : R.toNat + 48 * i + 48 ≤ heapNext r := by omega
  have hn₉ : heapNext t = heapNext v₇ := by
    simp only [heapNext]
    refine congrArg BitVec.toNat ((hf₉ nextAddr fun j hj hw' ↦ ?_).trans (hm₈ _))
    rcases hw' with hw' | hw'
    · addr_omega [hw', hj, hb1, hx]
    · addr_omega [hw', hj, hRi, hRi', hrv, hvt7, hhv]
  have hvt : heapNext v ≤ heapNext t := by rw [hn₉]; exact hvt7
  have Ht : HeapOk t := ⟨hn₉ ▸ I₇.heap.lo, hn₉ ▸ I₇.heap.hi⟩
  have hsp₉ : t.getReg .x2 = s.getReg .x2 - 496 := (k₉ .x2 (by decide)).trans hsp₈
  have hsu : heapNext s ≤ heapNext u := hmu
  have hfL : DFrame v₇ t (LocS s t) := (DFrame.of_same hm₈ _).trans hf₉ fun a ha' ↦ by
    rcases ha' with ha' | ha'
    · exact Or.inl (by addr_omega [ha', hb1])
    · refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> addr_omega [ha', hRi, hR, hsu, hRi', hrv, hvt]
  have It : Inv s t := I₇.step hpre hfL (fun a ha' ↦ LocS.w hpre Ht ha') Ht
    (by rw [hn₉]) (hsp₉.trans hsp₇.symm)
  set q := R + BitVec.ofNat 64 (48 * i) with hq
  have hfI : DFrame v t (IterW s v t q) := ((hf₀₇.mono fun a ha' ↦ by
      rcases ha' with ha' | ha' | ha' | ha' | ⟨h1, h2⟩
      · exact Or.inl (Or.inl ha')
      · exact Or.inl (Or.inr (Or.inl ha'))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ha')))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ha'))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by rw [hn₉]; exact h2⟩))))).trans
    (DFrame.of_same hm₈ fun _ ↦ False) fun _ h ↦ h.elim).trans hf₉ fun a ha' ↦ by
      rcases ha' with ha' | ha'
      · exact Or.inr (Or.inl ha')
      · exact Or.inr (Or.inr ha')
  have hqt : q.toNat + 48 ≤ heapNext t := by rw [hRi]; omega
  have miss (a : Word) (ha1 : (s.getReg .x2).toNat - 488 ≤ a.toNat)
      (ha2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 280) : t.getMem a = v.getMem a :=
    hfI a fun j hj hw' ↦ (IterW.miss hpre Ht hqt hw').1 (by addr_omega [hj, hb1, hb2, ha1, ha2])
  have hsr : heapNext s ≤ heapNext r := hsu.trans hur
  -- the pairs read before keep their buffers
  have old (a : Word) (xs' : List E) (p : NewVecE r v a xs') (ha1 : heapNext s ≤ a.toNat)
      (ha2 : a.toNat + 24 ≤ heapNext v) (ha3 : Apart a 24 q 48) : NewVecE r t a xs' := by
    have hl := p.vec.len
    have hbf := p.buf
    simp only [NewBuf] at hbf
    refine p.dframe hfI hvt (IterW.heap hpre I.heap (Or.inr ⟨ha1, ha2, ha3⟩))
      (IterW.heap hpre I.heap ?_)
    rcases hbf.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega, by addr_omega [h0, hRi, hR, hRi', hl]⟩
  -- the new pair: the point's prefix
  have m1 := b800083f4_m1 h₉
  have m2 := b800083f4_m2 h₉
  have m3 := b800083f4_m3 h₉
  have m4 := b800083f4_m4 h₉
  have m5 := b800083f4_m5 h₉
  have m6 := b800083f4_m6 h₉
  rw [h9₈, h21₈] at m1 m2 m3 m4 m5 m6
  rw [h8₃] at hQb hel₃
  simp only [NewBuf] at hQb
  have hp1 : NewVecE r t q (ch.reverse.take hw.toNat) := by
    have e0 : vecCap t q = hw := by rw [vecCap, m6, k₈ .x27 (by decide), h27₇]
    have e1 : vecPtr t q = v₃.getReg .x25 := by
      rw [vecPtr, m5, k₈ .x25 (by decide), k₇ .x25 (by decide)]
    have e2 : vecLen t q = hw := by rw [vecLen, m4, k₈ .x8 (by decide), h8₇]
    have hf₃₉ : DFrame v₃ t (IterW s v₃ t q) := ((hf₇.mono fun a ha' ↦ by
        rcases ha' with ha' | ha' | ha' | ha' | ⟨h1, h2⟩
        · exact Or.inl (Or.inl ha')
        · exact Or.inl (Or.inr (Or.inl ha'))
        · exact Or.inl (Or.inr (Or.inr (Or.inl ha')))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ha'))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by rw [hn₉]; exact h2⟩))))).trans
      (DFrame.of_same hm₈ fun _ ↦ False) fun _ h ↦ h.elim).trans hf₉ fun a ha' ↦ by
        rcases ha' with ha' | ha'
        · exact Or.inr (Or.inl ha')
        · exact Or.inr (Or.inr ha')
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [RawVecOk, Buf, e0, e1, heapStart]
      rcases hQb.2 with h0 | h0
      · exact ⟨hQb.1, Or.inl h0⟩
      · exact ⟨hQb.1, Or.inr ⟨by omega, by omega⟩⟩
    · rw [e0, e2]
    · simp only [NewBuf, e0, e1]
      rcases hQb.2 with h0 | h0
      · exact ⟨hQb.1, Or.inl h0⟩
      · exact ⟨hQb.1, Or.inr ⟨by omega, by omega⟩⟩
    · simp only [vecEs, e1, e2]
      rw [← hel₃]
      refine hf₃₉.eListAt (IterW.heap hpre I₃.heap ?_)
      rcases hQb.2 with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega, by addr_omega [h0, hRi, hRi', hrv]⟩
  -- the evaluations, their header copied from `S - 152`
  have hp2 : NewVecE r t (R + BitVec.ofNat 64 (48 * i + 24)) xs := by
    have hb24 : R + BitVec.ofNat 64 (48 * i + 24) = q + 24 := (add_ofNat_add _ _ _).symm
    have hbuf := hvec.buf
    have hl := hvec.vec.len
    simp only [NewBuf] at hbuf
    rw [hb24]
    refine (hvec.move ?_ ?_ ?_ ?_ ?_).weaken (by omega)
    · rw [m3, k₈ .x26 (by decide), h26₇]
    · rw [show q + 24 + 8 = q + 32 by rw [BitVec.add_assoc]; rfl, m2, k₈ .x18 (by decide), h18₇]
    · rw [show q + 24 + 16 = q + 40 by rw [BitVec.add_assoc]; rfl, m1, k₈ .x23 (by decide), h23₇]
    · refine ((DFrame.of_same hm₈ fun a ↦ Within a (s.getReg .x2 - 280) 8 ∨ Within a q 48).trans
        hf₉ fun _ h ↦ h).eListAt fun j hj hw' ↦ ?_
      rcases hbuf.2 with h0 | h0
      · omega
      · rcases hw' with hw' | hw'
        · addr_omega [hw', hj, h0, hb1, ha, hhv, hl]
        · addr_omega [hw', hj, h0, hRi, hRi', hrv, hn₃, hl]
    · rw [hn₉]
  -- the loop's branch
  have e19 : v₈.getReg .x19 = BitVec.ofNat 64 n := (k₈ .x19 (by decide)).trans h19₇
  have e20 : v₈.getReg .x20 = BitVec.ofNat 64 i := (k₈ .x20 (by decide)).trans h20₇
  have hpct : t.pc = if i + 1 = n then 0x80008508 else 0x80008428 := by
    by_cases hl : i + 1 = n
    · simp only [hl, ↓reduceIte]
      exact b800083f4_pc_taken h₉ (by rw [e19, e20, ← hl, BitVec.ofNat_add]; rfl)
    · simp only [hl, ↓reduceIte]
      refine b800083f4_pc_not_taken h₉ fun e ↦ hl ?_
      rw [e19, e20] at e
      have e' : BitVec.ofNat 64 n = BitVec.ofNat 64 (i + 1) :=
        e.trans (by rw [BitVec.ofNat_add]; rfl)
      have := congrArg BitVec.toNat e'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at this
      omega
  refine ⟨t, hr₃.trans (hr₇.trans (hr₈.trans hrt)), Or.inl ⟨(ch.reverse.take hw.toNat, xs), hpct, {
    inv := It
    x9 := (k₉ .x9 (by decide)).trans h9₈
    x11 := by
      rw [b800083f4_x11 h₉, k₈ .x24 (by decide), h24₇, show (8 : Word) = BitVec.ofNat 64 8 from rfl,
        add_ofNat_add, show 8 * i + 8 = 8 * (i + 1) by ring]
    x19 := (k₉ .x19 (by decide)).trans e19
    x20 := by rw [b800083f4_x20 h₉, e20, BitVec.ofNat_add]; rfl
    x21 := by
      rw [b800083f4_x21 h₉, h21₈, show 48 * (i + 1) = 48 * i + 48 by ring, BitVec.ofNat_add]; rfl
    x22 := by
      rw [b800083f4_x22 h₉, k₈ .x22 (by decide), h22₇,
        show (80 : Word) = BitVec.ofNat 64 80 from rfl, add_ofNat_add,
        show 80 * i + 72 + 80 = 80 * (i + 1) + 72 by ring]
    frame := (h.frame.mono fun a ha' ↦ by
        rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ⟨h1, h2⟩
        · exact Or.inl ha'
        · exact Or.inr (Or.inl ha')
        · exact Or.inr (Or.inr (Or.inl ha'))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha')))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩)))))).trans hfI
      fun a ha' ↦ by
        rcases ha' with (ha' | ha' | ha' | ha' | ⟨h1, h2⟩) | ha' | ha'
        · exact Or.inl ha'
        · exact Or.inr (Or.inl ha')
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha')))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha', hb1]))))
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))) <;>
            addr_omega [ha', hRi, hR, hRi', hrv, hvt]
    rv := hrv.trans hvt
    cap := (miss _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans h.cap
    ptr := (miss _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans h.ptr
    len := by
      have := b800083f4_m_x2_216 h₉
      rw [hsp₈, show s.getReg .x2 - 496 + 216 = s.getReg .x2 - 280 by addr_omega [hb1], e20] at this
      rw [BitVec.ofNat_add]
      exact this
    widths := (miss _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans h.widths
    rowsLen := by rw [List.length_append, List.length_singleton, h.rowsLen]
    pairs := fun j hj ↦ by
      have hj' : j < i + 1 := by
        rw [List.length_append, List.length_singleton, h.rowsLen] at hj; exact hj
      by_cases hji : j < rows.length
      · rw [List.getElem_append_left hji]
        have hj2 : j < i := h.rowsLen ▸ hji
        obtain ⟨p1, p2⟩ := h.pairs j hji
        exact ⟨old _ _ p1 (by addr_omega [hR, hsu, hRi', hj2]) (by addr_omega [hR, hRi', hrv, hj2])
            (by addr_omega [hR, hRi, hRi', hj2]),
          old _ _ p2 (by addr_omega [hR, hsu, hRi', hj2]) (by addr_omega [hR, hRi', hrv, hj2])
            (by addr_omega [hR, hRi, hRi', hj2])⟩
      · have hj2 : j = rows.length := by have := h.rowsLen; omega
        subst hj2
        rw [List.getElem_concat_length rfl, h.rowsLen]
        exact ⟨hp1, hp2⟩
    run := fun T hT ↦ by
      obtain ⟨T₁, T₂, e1, e2, hT₂⟩ := h.run T hT
      obtain ⟨T₃, e3, hT₃'⟩ := hrun T₂ (hT₃ T₂ hT₂)
      refine ⟨T₁, T₃, e1, ?_, I₇.transcriptS hpre Ht hfL hT₃'⟩
      rw [e2, readRows_drop s _ _ (hn ▸ hi), e3]
      rfl }⟩⟩

/-- The loop: from the head with `i` rows read, all `n` are, at `0x80008508`. -/
theorem rowsLoop (hTA : TryAllocZeroedSpec) (hMC : MemcpySpec 0x800126e4)
    (hNS : NextScalarsSpec) {s u r : MachineState} {ch : List E} {cl : E} {P W R : Word} {n : ℕ}
    (hpre : TableSumcheckPre s) (hc : RowsCtx s u r ch cl P W R n) :
    ∀ k i (v : MachineState) (rows : List (List E × List E)), n - i = k → i < n →
      v.pc = 0x80008428 → RowsHead s u r v ch cl R n i rows →
      ∃ t, Reaches Image.code v t ∧
        ((∃ rows', t.pc = 0x80008508 ∧ RowsHead s u r t ch cl R n n rows') ∨ Done s t) := by
  intro k
  induction k with
  | zero => intro i v rows hk hi; omega
  | succ k ih =>
    intro i v rows hk hi hpc h
    obtain ⟨t, hr, ⟨row, hpct, ht⟩ | hd⟩ := rowsIter hTA hMC hNS hpre hc h hpc hi
    · by_cases hl : i + 1 = n
      · simp only [hl, ↓reduceIte] at hpct
        exact ⟨t, hr, Or.inl ⟨rows ++ [row], hpct, hl ▸ ht⟩⟩
      · simp only [hl, ↓reduceIte] at hpct
        obtain ⟨t', hr', ht'⟩ := ih (i + 1) t (rows ++ [row]) (by omega) (by omega) hpct ht
        exact ⟨t', hr.trans hr', ht'⟩
    · exact ⟨t, hr, Or.inr hd⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
