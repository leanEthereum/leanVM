import Rv64Verifier.Proofs.Bus.TsStages

/-!
# `table_sumcheck`: the rows loop's state

```rust
let mut rows = Vec::with_capacity(tables.len());
for (table, &height) in tables.iter().zip(table_log_heights) {
    rows.push((point[..height].to_vec(), transcript.next_scalars(table.width())?));
}
```

The loop's head is `0x80008428` (`RowsHead`), its memory `RowsMem`, what it writes from
`0x80008384` on `RowsW`. An iteration first allocates the point's prefix and copies it
(`rowsAlloc`, to `0x80008484`). `TABLE_WIDTHS` is read from `.rodata` (`width_at`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The mirror, a table at a time -/

theorem readRowsM_cons (p : List E) (it : Table × ℕ) (rest : List (Table × ℕ))
    (rows : List (List E × List E)) (T : TState) :
    (readRowsM p (it :: rest) rows).run T =
      ((TM.nextScalars it.1.width).run T).bind fun r ↦
        (readRowsM p rest (rows ++ [(p.take it.2, r.1)])).run r.2 := by
  simp only [readRowsM, StateT.run_bind]
  rfl

theorem rowItems_length (s : MachineState) :
    (rowItems s).length = min (s.getReg .x12).toNat (s.getReg .x14).toNat := by
  simp only [rowItems, List.length_zip, tablesAt_length, natsAt_length]

theorem rowItems_getElem (s : MachineState) (i : ℕ) (h : i < (rowItems s).length) :
    (rowItems s)[i] = (tables.getD (s.getMem (s.getReg .x11 + BitVec.ofNat 64 (80 * i + 72))).toNat
      default, (s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i))).toNat) := by
  simp [rowItems, tablesAt, natsAt, readWords_eq_map]

theorem tables_width (i : ℕ) (hi : i < 6) :
    (tables.getD i default).width = LayoutMirror.tableWidthsRust.getD i 0 := by
  have hl : tables.length = 6 := by
    have := congrArg List.length LayoutMirror.tableWidthsRust_eq
    rw [List.length_map] at this
    rw [this]
    rfl
  rw [← LayoutMirror.tableWidthsRust_eq, List.getD_eq_getElem _ _ (by rw [hl]; exact hi),
    List.getD_eq_getElem _ _ (by rw [List.length_map, hl]; exact hi), List.getElem_map]

/-- `TABLE_WIDTHS[opcode]`, in `.rodata` at `0xa0000460`. -/
theorem width_at {u : MachineState} (h : RodataOk u) {op : Word} (hop : op.toNat < 6) :
    (u.getMem (0xa0000460 + op * 8)).toNat = (tables.getD op.toNat default).width := by
  rw [tables_width _ hop]
  have e : op = BitVec.ofNat 64 op.toNat := by simp
  generalize op.toNat = k at e hop
  subst e
  interval_cases k
  · rw [h.word (a := 2684355680 + 0#64 * 8) (v := 0xf)]; decide +kernel
  · rw [h.word (a := 2684355680 + 1#64 * 8) (v := 0xf)]; decide +kernel
  · rw [h.word (a := 2684355680 + 2#64 * 8) (v := 0x8)]; decide +kernel
  · rw [h.word (a := 2684355680 + 3#64 * 8) (v := 0xf)]; decide +kernel
  · rw [h.word (a := 2684355680 + 4#64 * 8) (v := 0xe)]; decide +kernel
  · rw [h.word (a := 2684355680 + 5#64 * 8) (v := 0x5c)]; decide +kernel

/-! ## The loop's state -/

/-- What the loop writes from `0x80008384` on: the callees' stack, `S - 152`, the widths' address
at `S - 328`, the rows' `Vec`, the transcript's sponge and offsets, `NEXT`, the heap allocated. -/
def RowsW (s u v : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2128) 1632 ∨ Within a (s.getReg .x2 - 152) 24 ∨
    Within a (s.getReg .x2 - 328) 8 ∨ Within a (s.getReg .x2 - 296) 24 ∨
    Within a (tsSelf s + 8) 344 ∨ Within a nextAddr 8 ∨ Fresh u v a

theorem RowsW.miss {s u v : MachineState} (hpre : TableSumcheckPre s) (hv : HeapOk v) {a : Word}
    (ha : RowsW s u v a) : ¬ Within a (s.getReg .x2 - 488) 160 ∧
      ¬ Within a (s.getReg .x2 - 320) 24 ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hs := hpre.stack.above
  have ss := hpre.selfStack
  have hS := hpre.self.self
  have hh := hv.hi
  simp only [stack_eq] at hs ss
  simp only [heapEnd, heapNext] at hh hs
  rcases ha with ha | ha | ha | ha | ha | ha | ⟨-, h2⟩
  all_goals first
    | exact ⟨by addr_omega [ha, hb1, hs, ss, hS], by addr_omega [ha, hb1, hs, ss, hS],
        by addr_omega [ha, hb1, hs, ss, hS]⟩
    | (simp only [heapNext] at h2
       exact ⟨by addr_omega [h2, hb1, hs, hh], by addr_omega [h2, hb1, hs, hh],
        by addr_omega [h2, hb1, hs, hh]⟩)

/-- A buffer allocated before `u` misses what the loop writes. -/
theorem RowsW.old {s u v : MachineState} (hpre : TableSumcheckPre s) (hu : HeapOk u) {p : Word}
    {m : ℕ} (hp : m = 0 ∨ heapNext s ≤ p.toNat ∧ p.toNat + m ≤ heapNext u) :
    ∀ i < m, ¬ RowsW s u v (p + BitVec.ofNat 64 i) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hs := hpre.stack.above
  have sf := hpre.selfFree
  have hS := hpre.self.self
  have hh := hu.hi
  have hl := hpre.heap.lo
  simp only [stack_eq] at hs
  simp only [Outside, heapEnd, heapNext, heapStart] at hh hs sf hl hp
  intro i hi hw
  rcases hp with h0 | h0
  · omega
  rcases hw with hw | hw | hw | hw | hw | hw | ⟨h1, -⟩
  all_goals first
    | addr_omega [hw, hi, h0, hb1, hs, hh, hl]
    | addr_omega [hw, hi, h0, sf, hS, hh, hl]
    | (simp only [heapNext] at h1; addr_omega [h1, hi, h0, hh, hl])

/-- Fixed through the loop: the state at `0x80008384`, the rows' buffer `R` allocated by `r`, the
loop's count `n`. -/
structure RowsCtx (s u r : MachineState) (ch : List E) (cl : E) (P W R : Word) (n : ℕ) :
    Prop where
  atr : AtRows s u ch cl P W
  ur : heapNext u ≤ heapNext r
  rbuf : NewBuf u r R (48 * (s.getReg .x12).toNat) 8
  n : n = min (s.getReg .x12).toNat (s.getReg .x14).toNat

/-- The loop's memory after `i` rows: the rows' `Vec` at `S - 296` holds `rows` (capacity
`tables.len()`, buffer `R`); `run` says the mirror's rows are
those of the remaining items read after `rows`. -/
structure RowsMem (s u r v : MachineState) (ch : List E) (cl : E) (R : Word) (i : ℕ)
    (rows : List (List E × List E)) : Prop where
  inv : Inv s v
  frame : DFrame u v (RowsW s u v)
  rv : heapNext r ≤ heapNext v
  cap : v.getMem (s.getReg .x2 - 296) = s.getReg .x12
  ptr : v.getMem (s.getReg .x2 - 288) = R
  len : v.getMem (s.getReg .x2 - 280) = BitVec.ofNat 64 i
  rowsLen : rows.length = i
  pairs : ∀ j (hj : j < rows.length), NewVecE r v (R + BitVec.ofNat 64 (48 * j)) rows[j].1 ∧
    NewVecE r v (R + BitVec.ofNat 64 (48 * j + 24)) rows[j].2
  run : ∀ T, TranscriptAt s (tsSelf s) T → ∃ T₁ T₂,
    (TM.sumcheck (eAt s (tsTarget s)) 4 (List.replicate (nRounds s) none)).run T =
      some ((ch, cl), T₁) ∧
    (readRowsM ch.reverse (rowItems s) []).run T₁ =
      (readRowsM ch.reverse ((rowItems s).drop i) rows).run T₂ ∧ TranscriptAt v (tsSelf s) T₂

/-- The loop's head, `0x80008428`, `i` of `n` rows read, the widths' address at `S - 328`. -/
structure RowsHead (s u r v : MachineState) (ch : List E) (cl : E) (R : Word) (n i : ℕ)
    (rows : List (List E × List E)) : Prop extends RowsMem s u r v ch cl R i rows where
  x9 : v.getReg .x9 = R
  x11 : v.getReg .x11 = s.getReg .x13 + BitVec.ofNat 64 (8 * i)
  x19 : v.getReg .x19 = BitVec.ofNat 64 n
  x20 : v.getReg .x20 = BitVec.ofNat 64 i
  x21 : v.getReg .x21 = BitVec.ofNat 64 (48 * i)
  x22 : v.getReg .x22 = s.getReg .x11 + BitVec.ofNat 64 (80 * i + 72)
  widths : v.getMem (s.getReg .x2 - 328) = 0xa0000460

section
variable {s u r v : MachineState} {ch : List E} {cl : E} {P W R : Word} {n i : ℕ}
  {rows : List (List E × List E)}

theorem RowsMem.kept (hpre : TableSumcheckPre s) (hc : RowsCtx s u r ch cl P W R n)
    (h : RowsMem s u r v ch cl R i rows) : Kept s v cl P := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact hc.atr.kept.step h.frame (fun a ha hw ↦ (RowsW.miss hpre h.inv.heap ha).1
    (by addr_omega [hw, hb1])) hb1

theorem RowsMem.args (hpre : TableSumcheckPre s) (hc : RowsCtx s u r ch cl P W R n)
    (h : RowsMem s u r v ch cl R i rows) : Args s v := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact hc.atr.args.step h.frame (fun a ha ↦ ⟨fun hw ↦ (RowsW.miss hpre h.inv.heap ha).1
    (by addr_omega [hw, hb1]), fun hw ↦ (RowsW.miss hpre h.inv.heap ha).1
    (by addr_omega [hw, hb1])⟩) hb1

/-- A slot of the frame between `S - 488` and `S - 328` is as at `0x80008384`. -/
theorem RowsMem.slot (hpre : TableSumcheckPre s) (h : RowsMem s u r v ch cl R i rows)
    {a : Word} (ha1 : (s.getReg .x2).toNat - 488 ≤ a.toNat)
    (ha2 : a.toNat + 8 ≤ (s.getReg .x2).toNat - 328) : v.getMem a = u.getMem a := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  exact h.frame a fun j hj hw ↦ (RowsW.miss hpre h.inv.heap hw).1
    (by addr_omega [hj, hb1, hb2, ha1, ha2])

theorem RowsMem.point (hpre : TableSumcheckPre s) (hc : RowsCtx s u r ch cl P W R n)
    (h : RowsMem s u r v ch cl R i rows) : eListAt v P ch.length = ch.reverse := by
  have hb := hc.atr.buf
  simp only [NewBuf] at hb
  rw [← hc.atr.point]
  exact h.frame.eListAt (RowsW.old hpre hc.atr.inv.heap (by omega))

end

/-! ## An iteration -/

/-- What an iteration from `v` writes before the rows' `Vec`: the callees' stack, `S - 152`,
`NEXT`, the heap allocated since `v`. -/
def AW (s v t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2128) 1632 ∨ Within a (s.getReg .x2 - 152) 24 ∨
    Within a nextAddr 8 ∨ Fresh v t a

theorem AW.loc {s v t : MachineState} (hb1 : 0xa0000f38 + 2128 ≤ (s.getReg .x2).toNat) {a : Word}
    (ha : AW s v t a) : Loc s v t a := by
  rcases ha with ha | ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr ha)

theorem mul24_toNat (x : Word) (h : x.toNat < 2 ^ 32) : (x * 16 + x * 8).toNat = 24 * x.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul]
  simp only [Sym.wordToNatLit]
  omega

/-- From the head to `0x80008484`: the height checked against `point.len()`, its buffer allocated
(`try_allocate_in`) and `point[..height]` copied into it (`memcpy`). -/
theorem rowsAlloc (hTA : TryAllocZeroedSpec) (hMC : MemcpySpec 0x800126e4)
    {s u r v : MachineState} {ch : List E} {cl : E} {P W R : Word} {n i : ℕ}
    {rows : List (List E × List E)} (hpre : TableSumcheckPre s) (hc : RowsCtx s u r ch cl P W R n)
    (h : RowsHead s u r v ch cl R n i rows) (hpc : v.pc = 0x80008428) (hi : i < n) :
    ∃ v₃, Reaches Image.code v v₃ ∧ ((v₃.pc = 0x80008484 ∧ Inv s v₃ ∧ DFrame v v₃ (AW s v v₃) ∧
      heapNext v ≤ heapNext v₃ ∧
      (∀ r ∈ ([.x9, .x19, .x20, .x21, .x22] : List Reg), v₃.getReg r = v.getReg r) ∧
      v₃.getReg .x24 = v.getReg .x11 ∧
      v₃.getReg .x8 = s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i)) ∧
      v₃.getReg .x27 = v₃.getReg .x8 ∧ (v₃.getReg .x8).toNat ≤ ch.length ∧
      NewBuf v v₃ (v₃.getReg .x25) ((v₃.getReg .x8).toNat * 24) 8 ∧
      eListAt v₃ (v₃.getReg .x25) (v₃.getReg .x8).toNat = ch.reverse.take (v₃.getReg .x8).toNat) ∨
      Dead Image.code v₃) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := h.inv
  have hsp := I.sp
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  simp only [stack_eq] at ha hx
  have hn := hc.n
  have hHr : ValidMemRange (s.getReg .x13) (s.getReg .x14).toNat := hpre.heights.range
  have hHb := ValidMemRange.bounds hHr (by omega)
  -- `0x80008428`: the height against `point.len()`
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008428_spec hpc (by
    rv_eval [hsp, h.x11]
    and_intros
    · valid_access hval [hb1]
    · valid_access hHr [hHb, hi, hn])
  have hm₁ := b80008428_mem_same h₁
  have k₁ := b80008428_keeps h₁
  set hw := s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i)) with hhw
  have hgt : v.getMem (v.getReg .x11) = hw := by
    rw [h.x11]
    exact I.word hpre.heights (by addr_omega [hHb, hi, hn]) (by addr_omega [hHb, hi, hn])
  have e112 : (v.getMem (v.getReg .x2 + 112)).toNat = ch.length := by
    rw [hsp, show s.getReg .x2 - 496 + 112 = s.getReg .x2 - 384 by addr_omega [hb1],
      h.slot hpre (by addr_omega [hb1]) (by addr_omega [hb1])]
    exact hc.atr.pointLen
  by_cases hlt : ch.length < hw.toNat
  · exact ⟨v₁, hr₁, Or.inr (trap (b80008428_pc_taken h₁ (by rw [hgt, e112]; exact hlt)))⟩
  have hle : hw.toNat ≤ ch.length := by omega
  -- `try_allocate_in(height, 8, 24)` into `S - 152`
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008434_spec
    (b80008428_pc_not_taken h₁ (by rw [hgt, e112]; exact hle)) trivial
  have k₂ := b80008434_keeps h₂
  have hm₂ := b80008434_mem_same h₂
  have hsp₂ : v₂.getReg .x2 = s.getReg .x2 - 496 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  have h10₂ : v₂.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b80008434_x10 h₂, k₁ .x2 (by decide), hsp]; rv_eval []
  have h11₂ : v₂.getReg .x11 = hw := by rw [b80008434_x11 h₂, b80008428_x8 h₁, hgt]
  have hn₂ : heapNext v₂ = heapNext v := by simp only [heapNext, hm₂, hm₁]
  have hpre₃ : TryAllocPre .x13 .x14 v₂ := {
    heap := ⟨hn₂ ▸ I.heap.lo, hn₂ ▸ I.heap.hi⟩
    out := by rw [h10₂]; valid_sub hval [hb1]
    align := by rw [b80008434_x13 h₂]; decide
    size := by rw [b80008434_x14 h₂]; decide
    stack := hpre.stack.sub 496 hsp₂ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [h10₂]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    outStack := by rw [h10₂]; simp only [stackLo, tryAllocStack, hsp₂]; addr_omega [hb1] }
  obtain ⟨v₃, hr₃, ⟨hpc₃, hp₃, post₃, -⟩ | hd⟩ := hTA.call hr₂ (b80008434_pc h₂) hpre₃
  swap
  · exact ⟨v₃, hr₁.trans hr₃, Or.inr hd⟩
  have hsp₃ : v₃.getReg .x2 = s.getReg .x2 - 496 := (hp₃.reg .x2).trans hsp₂
  have hf₃ := DFrame.of_byteFrame post₃.frame
  simp only [h10₂, stackLo, tryAllocStack, hsp₂] at hf₃
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008454_spec
    (by rw [hpc₃, returnAddress_eq, b80008434_x1 h₂]; decide) (by
      rv_eval [hsp₃]; valid_access hval [hb1])
  have e344 : v₃.getMem (v₃.getReg .x2 + 344) = v₃.getMem (v₂.getReg .x10) := by
    rw [hsp₃, h10₂]; congr 1; addr_omega [hb1]
  by_cases hok : v₃.getMem (v₂.getReg .x10) = 0
  swap
  · exact ⟨v₄, hr₁.trans (hr₃.trans hr₄),
      Or.inr (trap (b80008454_pc_taken h₄ (by rw [e344]; exact hok)))⟩
  obtain ⟨hcap₃, hbuf₃⟩ := post₃.ok hok
  rw [h10₂, h11₂] at hcap₃
  rw [h10₂, h11₂, b80008434_x14 h₂, b80008434_x13 h₂] at hbuf₃
  simp only [Sym.wordToNatLit] at hbuf₃
  have k₄ := b80008454_keeps h₄
  have hm₄ := b80008454_mem_same h₄
  have hsp₄ : v₄.getReg .x2 = s.getReg .x2 - 496 := (k₄ .x2 (by decide)).trans hsp₃
  obtain ⟨v₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000845c_spec
    (b80008454_pc_not_taken h₄ (by rw [e344]; exact hok)) (by
      rv_eval [hsp₄]; and_intros <;> valid_access hval [hb1])
  have k₅ := b8000845c_keeps h₅
  have hm₅ := b8000845c_mem_same h₅
  set Q := v₃.getMem (s.getReg .x2 - 152 + 16) with hQ
  have h25₅ : v₅.getReg .x25 = Q := by
    rw [b8000845c_x25 h₅, hsp₄, hm₄]; congr 1; addr_omega [hb1]
  have h27₅ : v₅.getReg .x27 = hw := by
    rw [b8000845c_x27 h₅, hsp₄, hm₄, ← hcap₃]; congr 1; addr_omega [hb1]
  have h8₄ : v₄.getReg .x8 = hw := by
    rw [k₄ .x8 (by decide), hp₃.reg .x8, k₂ .x8 (by decide), b80008428_x8 h₁, hgt]
  have hsp₅ : v₅.getReg .x2 = s.getReg .x2 - 496 := (k₅ .x2 (by decide)).trans hsp₄
  have hn₃ := post₃.mono
  have hh₃ := post₃.heap.hi
  have hPb := hc.atr.buf
  have hlo := hpre.heap.lo
  have hmu := hc.atr.inv.mono
  have hmv := h.inv.mono
  have huv : heapNext u ≤ heapNext v := hc.ur.trans h.rv
  have hn₂' : heapNext v₂ = heapNext v := hn₂
  have hH₃ := post₃.heap
  simp only [NewBuf, heapNext, heapEnd, heapStart] at hPb hbuf₃ hn₃ hh₃ hlo hmu hmv huv hn₂
  have hL32 : ch.length < 2 ^ 32 := by
    have := h.inv.heap.hi
    simp only [heapNext, heapEnd] at this
    rcases hPb.2 with h0 | h0 <;> omega
  -- `memcpy(Q, point, 24 height)`, unless the height is zero
  obtain ⟨v₇, hr₇, ⟨hpc₇, hf₇, k₇, hel₇⟩ | hd⟩ : ∃ v₇, Reaches Image.code v₅ v₇ ∧
      ((v₇.pc = 0x80008484 ∧
      DFrame v₅ v₇ (fun a ↦ Within a Q (24 * hw.toNat) ∨ Within a (s.getReg .x2 - 512) 16) ∧
      (∀ r ∈ calleeSaved, v₇.getReg r = v₅.getReg r) ∧
      eListAt v₇ Q hw.toNat = eListAt v₅ P hw.toNat) ∨ Dead Image.code v₇) := by
    by_cases hz : hw = 0
    · refine ⟨v₅, Reaches.refl _, Or.inl ⟨b8000845c_pc_taken h₅ (by rw [h8₄]; exact hz),
        DFrame.refl _ _, fun _ _ ↦ rfl, by rw [hz]; rfl⟩⟩
    have hz' : hw.toNat ≠ 0 := fun e ↦ hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    obtain ⟨v₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80008468_spec
      (b8000845c_pc_not_taken h₅ (by rw [h8₄]; exact hz)) (by
        rv_eval [hsp₅]; valid_access hval [hb1])
    have hsp₆ : v₆.getReg .x2 = s.getReg .x2 - 496 :=
      ((b80008468_keeps h₆) .x2 (by decide)).trans hsp₅
    have h10₆ : v₆.getReg .x10 = Q := by rw [b80008468_x10 h₆, h25₅]
    have h11₆ : v₆.getReg .x11 = P := by
      rw [b80008468_x11 h₆, hsp₅, hm₅, hm₄, show s.getReg .x2 - 496 + 56 = s.getReg .x2 - 440 by
        addr_omega [hb1]]
      have hK := h.kept hpre hc
      rw [hf₃ _ fun j hj hw' ↦ by
        rcases hw' with hw' | hw' | hw' | ⟨h1, h2⟩
        · addr_omega [hw', hj, hb1]
        · addr_omega [hw', hj, hb1]
        · addr_omega [hw', hj, hb1, hx]
        · simp only [heapNext] at h1 h2; addr_omega [h1, h2, hj, hb1, hh₃, ha], hm₂, hm₁]
      exact hK.point
    have h12₆ : (v₆.getReg .x12).toNat = 24 * hw.toNat := by
      rw [b80008468_x12 h₆, k₅ .x8 (by decide), h8₄]; exact mul24_toNat _ (by omega)
    have hQb : heapNext v ≤ Q.toNat ∧ Q.toNat + hw.toNat * 24 ≤ heapNext v₃ := by
      simp only [heapNext]; rcases hbuf₃.2 with h0 | h0
      · omega
      · omega
    simp only [heapNext] at hQb
    have hpre₇ : MemcpyPre v₆ := {
      dst := by rw [h10₆, h12₆]; addr_omega [hQb, hh₃, hlo, hmv, hmu]
      src := by
        rw [h11₆, h12₆]; rcases hPb.2 with h0 | h0
        · omega
        · addr_omega [h0, hle, hmu, hlo, huv, hn₂, hn₃, hh₃]
      apart := by
        rw [h10₆, h11₆, h12₆]; rcases hPb.2 with h0 | h0
        · omega
        · addr_omega [h0, hle, hQb, huv, hn₂]
      stack := ⟨by simp only [stackLo, memcpyStack, hsp₆]; valid_sub hval [hb1],
        by rw [hsp₆]; addr_omega [hb1, hb3]⟩
      dstStack := by
        rw [h10₆, h12₆]; simp only [stackLo, memcpyStack, hsp₆]; addr_omega [hQb, hh₃, ha, hb1]
      srcStack := by
        rw [h11₆, h12₆]; simp only [stackLo, memcpyStack, hsp₆]; rcases hPb.2 with h0 | h0
        · omega
        · addr_omega [h0, hle, huv, hn₂, hn₃, hh₃, ha, hb1] }
    obtain ⟨v₇, hr₇, ⟨hpc₇, hp₇, post₇⟩ | hd⟩ := hMC.call hr₆ (b80008468_pc h₆) hpre₇
    swap
    · exact ⟨v₇, hr₇, Or.inr hd⟩
    have hm₆ := b80008468_mem_same h₆
    have hf₇ := DFrame.of_byteFrame post₇.frame
    simp only [h10₆, h12₆, stackLo, memcpyStack, hsp₆] at hf₇
    have hby := post₇.bytes
    rw [h10₆, h11₆, h12₆] at hby
    refine ⟨v₇, hr₇, Or.inl ⟨by rw [hpc₇, returnAddress_eq, b80008468_x1 h₆]; decide,
      (DFrame.of_same hm₆ _).trans hf₇ fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (by addr_omega [ha, hb1]),
      fun r hr ↦ by rw [hp₇ r hr, (b80008468_keeps h₆) r (mem_of_calleeSaved hr _)], ?_⟩⟩
    rw [eListAt_eq_of_bytesAt hby hbuf₃.1 hPb.1]
    exact (DFrame.of_same hm₆ fun _ ↦ False).eListAt fun _ _ h ↦ h
  swap
  · exact ⟨v₇, hr₁.trans (hr₃.trans (hr₄.trans hr₅ |>.trans hr₇)), Or.inr hd⟩
  have hreach : Reaches Image.code v v₇ := hr₁.trans (hr₃.trans ((hr₄.trans hr₅).trans hr₇))
  -- what the steps from `v` to `v₇` write
  have hn₇ : heapNext v₇ = heapNext v₃ := by
    simp only [heapNext]
    refine congrArg BitVec.toNat ((hf₇ nextAddr fun j hj hw' ↦ ?_).trans ((hm₅ _).trans (hm₄ _)))
    rcases hw' with hw' | hw'
    · rcases Nat.eq_zero_or_pos hw.toNat with h0 | h0
      · simp only [Within] at hw'; omega
      · rcases hbuf₃.2 with h1 | h1
        · omega
        · addr_omega [hw', hj, h1, hh₃]
    · addr_omega [hw', hj, hb1, hx]
  have hfr₅ : DFrame v v₅ (AW s v v₃) := ((DFrame.of_same (fun a ↦ (hm₂ a).trans (hm₁ a))
    (AW s v v₃)).trans hf₃ fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ha)
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext] at h1 ⊢; omega, h2⟩))).trans
    (DFrame.of_same (fun a ↦ (hm₅ a).trans (hm₄ a)) fun _ ↦ False) fun _ h ↦ h.elim
  have hQb : hw.toNat = 0 ∨ heapNext v ≤ Q.toNat ∧ Q.toNat + hw.toNat * 24 ≤ heapNext v₃ := by
    simp only [heapNext]; rcases hbuf₃.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hfr : DFrame v v₇ (AW s v v₇) := (hfr₅.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨h1, by rw [hn₇]; exact h2⟩))).trans hf₇ fun a ha ↦ by
    rcases ha with ha | ha
    · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;> rcases hQb with h0 | h0
      · simp only [Within] at ha; omega
      · simp only [Within] at ha; omega
      · simp only [Within] at ha; omega
      · rw [hn₇]; simp only [Within] at ha; omega
    · exact Or.inl (by addr_omega [ha, hb1])
  have hvv : heapNext v ≤ heapNext v₇ := by rw [hn₇, ← hn₂']; exact post₃.mono
  have hsp₇ : v₇.getReg .x2 = s.getReg .x2 - 496 := (k₇ .x2 (by decide)).trans hsp₅
  have I₇ : Inv s v₇ := I.loc hpre (hfr.mono fun a ha ↦ AW.loc hb1 ha)
    ⟨hn₇ ▸ hH₃.lo, hn₇ ▸ hH₃.hi⟩ hvv (hsp₇.trans hsp.symm)
  have R7 (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x21, .x22] : List Reg)) :
      v₇.getReg r = v.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [k₇ _ (by decide), k₅ _ (by decide), k₄ _ (by decide), hp₃ _ (by decide),
        k₂ _ (by decide), k₁ _ (by decide)]
  have hx8 : v₇.getReg .x8 = hw := (k₇ .x8 (by decide)).trans ((k₅ .x8 (by decide)).trans h8₄)
  have hx25 : v₇.getReg .x25 = Q := (k₇ .x25 (by decide)).trans h25₅
  refine ⟨v₇, hreach, Or.inl ⟨hpc₇, I₇, hfr, hvv, fun r hr ↦ ?_, ?_, hx8, ?_,
    by rw [hx8]; exact hle, ?_, ?_⟩⟩
  · exact R7 r hr
  · rw [k₇ .x24 (by decide), k₅ .x24 (by decide), k₄ .x24 (by decide), hp₃ .x24 (by decide),
      b80008434_x24 h₂, k₁ .x11 (by decide)]
  · rw [hx8, k₇ .x27 (by decide), h27₅]
  · rw [hx8, hx25]
    simp only [NewBuf, heapNext] at hbuf₃ hn₇ ⊢
    omega
  · rw [hx8, hx25, hel₇, hfr₅.eListAt fun j hj hw' ↦ ?_, ← eListAt_take _ _ hle, h.point hpre hc]
    rcases hPb.2 with h0 | h0
    · omega
    · rcases hw' with hw' | hw' | hw' | ⟨h1, -⟩
      · addr_omega [hw', hj, h0, hle, huv, hn₂, hn₃, hh₃, ha, hb1]
      · addr_omega [hw', hj, h0, hle, huv, hn₂, hn₃, hh₃, ha, hb1]
      · addr_omega [hw', hj, h0, hle, huv, hn₂, hn₃, hh₃, hx]
      · simp only [heapNext] at h1; addr_omega [h1, hj, h0, hle, huv, hn₂, hn₃, hh₃]

end Rv64Verifier.Proofs.Bus.TableSumcheck
