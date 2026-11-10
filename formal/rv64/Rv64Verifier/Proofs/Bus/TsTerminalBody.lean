import Rv64Verifier.Proofs.Bus.TsStages

/-!
# `table_sumcheck`: the terminal's loop head

```rust
for (((table, (_, evaluations)), forms), &weight) in
    tables.iter().zip(&rows).zip(bus_forms).zip(&weights)
{
    let n_constraints = table.n_constraints();
    let summand = dot(&constraint_powers[cursor..cursor + n_constraints], ..);
```

The loop's head at `0x80008600` (`LoopAt`, from the loop's start `u₀`, `Ctx`) copies the weight to
`sp + 224`, reads the table's opcode (trapping past six) and `N_CONSTRAINTS[opcode]` from
`.rodata`, and traps where the slice of `constraint_powers` overflows or runs past it; it reaches
`0x80008694` for JUMP and `0x800087f4` otherwise (`AtSum`). The loop writes only `TW`.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the terminal loop writes from `u₀` on: `sp + 136` and `sp + 144`, `sp + 224` up to the
saved registers, the callees' stacks, `NEXT` and the heap it allocates. -/
def TW (s u₀ u : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 360) 16 ∨ Within a (s.getReg .x2 - 272) 168 ∨
    Within a (s.getReg .x2 - 2128) 1632 ∨ Within a nextAddr 8 ∨ Fresh u₀ u a

theorem TW.mono {s u₀ u v : MachineState} (h : heapNext u ≤ heapNext v) {a : Word}
    (ha : TW s u₀ u a) : TW s u₀ v a := by
  rcases ha with ha | ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩)))

theorem TW.loc {s u₀ u : MachineState} (hpre : TableSumcheckPre s) {a : Word}
    (ha : TW s u₀ u a) : Loc s u₀ u a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases ha with ha | ha | ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr ha)

/-- A frame slot the loop does not write. -/
theorem tw_slot {s u₀ u : MachineState} (hpre : TableSumcheckPre s) (hu : HeapOk u) {a : Word}
    (h1 : (s.getReg .x2 - 496).toNat ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ (s.getReg .x2 - 360).toNat ∨
      ((s.getReg .x2 - 344).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2 - 272).toNat)) :
    ∀ i < 8, ¬ TW s u₀ u (a + BitVec.ofNat 64 i) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := hu.hi
  simp only [heapEnd] at hh
  intro i hi hw
  rcases h2 with h2 | h2 <;>
    rcases hw with hw | hw | hw | hw | ⟨-, hw⟩ <;> addr_omega [hw, h1, h2, hi, hb1, hb2, hh]

/-- The heap below the loop's start. -/
theorem tw_old {s u₀ u : MachineState} (hpre : TableSumcheckPre s) (h0 : HeapOk u₀) {a : Word}
    {m : Nat} (h1 : heapStart ≤ a.toNat) (h2 : a.toNat + m ≤ heapNext u₀) :
    ∀ i < m, ¬ TW s u₀ u (a + BitVec.ofNat 64 i) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := h0.hi
  simp only [heapEnd, heapStart] at hh h1
  intro i hi hw
  rcases hw with hw | hw | hw | hw | ⟨hw, -⟩ <;> addr_omega [hw, h1, h2, hi, hb1, hh]

/-! ## The mirror, an item at a time -/

/-- `constraint_powers` and `form_powers` on the entry's arguments. -/
def cpOf (s : MachineState) : List E := eListAt s (s.getReg .x17) (s.getReg .x28).toNat
def fpOf (s : MachineState) : List E := eListAt s (s.getReg .x29) (s.getReg .x30).toNat

/-- The terminal's items: each table, its row, its forms and its weight. -/
def tItems (s : MachineState) (rows : List (List E × List E)) (ws : List E) :
    List (((Table × (List E × List E)) × List Form) × E) :=
  (((tablesAt s (s.getReg .x11) (s.getReg .x12).toNat).zip rows).zip
    (formRowsAt s (s.getReg .x15) (s.getReg .x16).toNat)).zip ws

/-- The terminal and the cursor after the first `k` items. -/
def tAcc (s : MachineState) (rows : List (List E × List E)) (ws : List E) (k : ℕ) : E × ℕ :=
  ((tItems s rows ws).take k).foldl (terminalStep (cpOf s) (fpOf s)) (0, 0)

/-- The `i`-th table's opcode. -/
def opAt (s : MachineState) (i : ℕ) : ℕ :=
  (s.getMem (s.getReg .x11 + BitVec.ofNat 64 (80 * i + 72))).toNat

theorem formRowsAt_length (s : MachineState) (a : Word) (n : Nat) :
    (formRowsAt s a n).length = n := by
  simp [formRowsAt]

theorem tItems_length (s : MachineState) (rows : List (List E × List E)) (ws : List E) :
    (tItems s rows ws).length =
      min (min (min (s.getReg .x12).toNat rows.length) (s.getReg .x16).toNat) ws.length := by
  simp only [tItems, List.length_zip, tablesAt_length, formRowsAt_length]

theorem tItems_getElem {s : MachineState} {rows : List (List E × List E)} {ws : List E} {k : ℕ}
    (hk : k < (tItems s rows ws).length) :
    ∃ (hr : k < rows.length) (hw : k < ws.length), (tItems s rows ws)[k] =
      (((tables.getD (opAt s k) default, rows[k]),
        formVecAt s (s.getReg .x15 + BitVec.ofNat 64 (24 * k))), ws[k]) := by
  have hk' := hk
  rw [tItems_length] at hk'
  refine ⟨by omega, by omega, ?_⟩
  simp [tItems, List.getElem_zip, tablesAt, formRowsAt, opAt]

theorem tAcc_succ (s : MachineState) (rows : List (List E × List E)) (ws : List E) (k : ℕ)
    (hk : k < (tItems s rows ws).length) :
    tAcc s rows ws (k + 1) =
      terminalStep (cpOf s) (fpOf s) (tAcc s rows ws k) (tItems s rows ws)[k] := by
  simp only [tAcc, List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hk,
    Option.toList_some, List.foldl_cons, List.foldl_nil]

theorem terminalOf_eq (s : MachineState) (rows : List (List E × List E)) (ws : List E) :
    terminalOf s rows ws = (tAcc s rows ws (tItems s rows ws).length).1 := by
  simp only [terminalOf, tAcc, List.take_length, terminalRust, tItems, cpOf, fpOf]

theorem eListAt_drop_take (s : MachineState) (p : Word) {L c n : ℕ} (h : c + n ≤ L) :
    ((eListAt s p L).drop c).take n = eListAt s (p + BitVec.ofNat 64 (24 * c)) n := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, eListAt_length]; omega
  · intro j h1 h2
    simp only [List.getElem_take, List.getElem_drop, eListAt_getElem, add_ofNat_add]
    congr 3
    ring

theorem mul48 (v : ℕ) :
    BitVec.ofNat 64 v * 32 + BitVec.ofNat 64 v * 16 = BitVec.ofNat 64 (48 * v) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Sym.wordToNatLit]
  omega

/-! ## `N_CONSTRAINTS` -/

theorem nc_valid : ValidMemRange 0xa0000080 6 := by
  intro i hi
  interval_cases i <;> decide

theorem nc_at {u : MachineState} (h : RodataOk u) {x : Word} (hx : x.toNat < 6) :
    u.getMem (0xa0000080 + x * 8) =
      BitVec.ofNat 64 (tables.getD x.toNat default).nConstraints := by
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < 6 ∧ x = BitVec.ofNat 64 k := ⟨x.toNat, hx, by simp⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  interval_cases k <;> exact h.word

theorem nc_le {op : ℕ} (h : op < 6) : (tables.getD op default).nConstraints ≤ 2 := by
  interval_cases op <;> decide

theorem nc_jump : (tables.getD 4 default).nConstraints = 2 := by decide

theorem nc_other {op : ℕ} (h6 : op < 6) (h4 : op ≠ 4) :
    (tables.getD op default).nConstraints = 0 := by
  interval_cases op <;> first | decide | exact absurd rfl h4

theorem constraints_jump : (tables.getD 4 default).constraints = jumpConstraints := rfl

/-! ## The loop's context and head -/

/-- The loop's context, fixed from its start `u₀`. -/
structure Ctx (s u₀ : MachineState) (rows : List (List E × List E)) (ws : List E) (W : Word)
    (n : ℕ) : Prop where
  inv : Inv s u₀
  args : Args s u₀
  formLen : u₀.getMem (s.getReg .x2 - 448) = s.getReg .x30
  count : u₀.getMem (s.getReg .x2 - 392) = BitVec.ofNat 64 n
  rowsPtr : u₀.getMem (s.getReg .x2 - 344) = vecPtr u₀ (s.getReg .x2 - 296)
  nc : u₀.getMem (s.getReg .x2 - 336) = 0xa0000080
  wptr : u₀.getMem (s.getReg .x2 - 328) = W
  rowsAt : RowsAt s u₀ (s.getReg .x2 - 296) rows
  wbuf : NewBuf s u₀ W (24 * (s.getReg .x12).toNat) 8
  weights : eListAt u₀ W (s.getReg .x12).toNat = ws
  len : (tItems s rows ws).length = n

/-- At the loop's head, `i` items done: the terminal's limbs in `s9`, `s8`, `s11`. -/
structure LoopAt (s u₀ u : MachineState) (rows : List (List E × List E)) (ws : List E) (i : ℕ) :
    Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 496
  heap : HeapOk u
  mono : heapNext u₀ ≤ heapNext u
  frame : DFrame u₀ u (TW s u₀ u)
  x18 : u.getReg .x18 = BitVec.ofNat 64 i
  x10 : u.getReg .x10 = BitVec.ofNat 64 (tAcc s rows ws i).2
  x22 : u.getReg .x22 = s.getReg .x30
  acc : Model.limbs (tAcc s rows ws i).1 = (u.getReg .x25, u.getReg .x24, u.getReg .x27)
  cur : (tAcc s rows ws i).2 ≤ (s.getReg .x28).toNat

/-- Past the head: the weight at `sp + 224`, `s3` the row, `a1` the slice of `constraint_powers`,
`s0` its length, `s5` the next cursor. -/
structure AtSum (s u₀ v : MachineState) (rows : List (List E × List E)) (ws : List E) (i : ℕ) :
    Prop where
  sp : v.getReg .x2 = s.getReg .x2 - 496
  heap : HeapOk v
  mono : heapNext u₀ ≤ heapNext v
  frame : DFrame u₀ v (TW s u₀ v)
  x18 : v.getReg .x18 = BitVec.ofNat 64 i
  x19 : v.getReg .x19 = vecPtr u₀ (s.getReg .x2 - 296) + BitVec.ofNat 64 (48 * i)
  x11 : v.getReg .x11 = s.getReg .x17 + BitVec.ofNat 64 (24 * (tAcc s rows ws i).2)
  x8 : v.getReg .x8 = BitVec.ofNat 64 (tables.getD (opAt s i) default).nConstraints
  x21 : v.getReg .x21 =
    BitVec.ofNat 64 ((tAcc s rows ws i).2 + (tables.getD (opAt s i) default).nConstraints)
  x9 : v.getReg .x9 = BitVec.ofNat 64 (24 * i)
  x22 : v.getReg .x22 = s.getReg .x30
  acc : Model.limbs (tAcc s rows ws i).1 = (v.getReg .x25, v.getReg .x24, v.getReg .x27)
  weight : eAt v (s.getReg .x2 - 272) = ws.getD i 0
  op6 : opAt s i < 6
  cur : (tAcc s rows ws i).2 + (tables.getD (opAt s i) default).nConstraints ≤
    (s.getReg .x28).toNat

theorem Ctx.lens {s u₀ : MachineState} {rows : List (List E × List E)} {ws : List E} {W : Word}
    {n : ℕ} (C : Ctx s u₀ rows ws W n) :
    ws.length = (s.getReg .x12).toNat ∧ n ≤ (s.getReg .x12).toNat ∧ n ≤ rows.length ∧
      n ≤ (s.getReg .x16).toNat := by
  have hw : ws.length = (s.getReg .x12).toNat := by rw [← C.weights, eListAt_length]
  have hl := C.len
  rw [tItems_length, hw] at hl
  omega

/-- The weights' buffer, below the loop's start. -/
theorem Ctx.wbounds {s u₀ : MachineState} {rows : List (List E × List E)} {ws : List E} {W : Word}
    {n : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) (hn : 0 < n) :
    heapStart ≤ W.toNat ∧ W.toNat + 24 * (s.getReg .x12).toNat ≤ heapNext u₀ ∧
      W.toNat % 8 = 0 := by
  have hb := C.wbuf
  have hl := hpre.heap.lo
  have hx := C.lens
  simp only [NewBuf] at hb
  refine ⟨?_, ?_, hb.1⟩ <;> rcases hb.2 with h0 | h0 <;> omega

/-- The head, from `0x80008600` to `0x80008694` (JUMP) or `0x800087f4`. -/
theorem headStep {s u₀ u : MachineState} {rows : List (List E × List E)} {ws : List E} {W : Word}
    {n i : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) (L : LoopAt s u₀ u rows ws i)
    (hpc : u.pc = 0x80008600) (hi : i < n) :
    ∃ v, Reaches Image.code u v ∧ ((AtSum s u₀ v rows ws i ∧
      ((opAt s i = 4 ∧ v.pc = 0x80008694) ∨ (opAt s i ≠ 4 ∧ v.pc = 0x800087f4))) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hsp := L.sp
  have I : Inv s u := C.inv.loc hpre (L.frame.mono fun _ ha ↦ TW.loc hpre ha) L.heap L.mono
    (hsp.trans C.inv.sp.symm)
  have sl (a : Word) (h1 : (s.getReg .x2 - 496).toNat ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2 - 360).toNat ∨
        ((s.getReg .x2 - 344).toNat ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2 - 272).toNat)) :
      u.getMem a = u₀.getMem a := L.frame a (tw_slot hpre L.heap h1 h2)
  have e400 : u.getMem (s.getReg .x2 - 400) = s.getReg .x11 :=
    (sl _ (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1]))).trans C.args.tables
  have e408 : u.getMem (s.getReg .x2 - 408) = s.getReg .x28 :=
    (sl _ (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1]))).trans C.args.constraintLen
  have e416 : u.getMem (s.getReg .x2 - 416) = s.getReg .x17 :=
    (sl _ (by addr_omega [hb1]) (Or.inl (by addr_omega [hb1]))).trans C.args.constraintPowers
  have e344 : u.getMem (s.getReg .x2 - 344) = vecPtr u₀ (s.getReg .x2 - 296) :=
    (sl _ (by addr_omega [hb1]) (Or.inr ⟨by addr_omega [hb1], by addr_omega [hb1]⟩)).trans
      C.rowsPtr
  have e336 : u.getMem (s.getReg .x2 - 336) = 0xa0000080 :=
    (sl _ (by addr_omega [hb1]) (Or.inr ⟨by addr_omega [hb1], by addr_omega [hb1]⟩)).trans C.nc
  have e328 : u.getMem (s.getReg .x2 - 328) = W :=
    (sl _ (by addr_omega [hb1]) (Or.inr ⟨by addr_omega [hb1], by addr_omega [hb1]⟩)).trans C.wptr
  obtain ⟨hwl, hn12, -, -⟩ := C.lens
  have hiT : i < (s.getReg .x12).toNat := by omega
  obtain ⟨hW1, hW2, hW3⟩ := C.wbounds hpre (by omega)
  have hh0 := C.inv.heap.hi
  simp only [heapStart, heapEnd] at hW1 hh0
  have hWv : ValidMemRange W (3 * (s.getReg .x12).toNat) := heap_range (by omega) (by omega) hW3
  have hTv : ValidMemRange (s.getReg .x11) (10 * (s.getReg .x12).toNat) :=
    RO.range (by rw [show 8 * (10 * (s.getReg .x12).toNat) = 80 * (s.getReg .x12).toNat by ring]
                 exact hpre.tables)
  have hTb := hpre.tables.bound
  -- `0x80008600`: the weight to `sp + 224`, the opcode
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008600_spec hpc (by
    rv_eval [hsp, L.x18, e400, e328]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hTv [hTb, hiT]
      | valid_access hWv [hW1, hW2, hiT])
  have k₁ := b80008600_keeps h₁
  have hf₁ := DFrame.of_memFrame (b80008600_frame h₁ (by rw [hsp]; addr_omega [hb1]))
  rw [hsp, show s.getReg .x2 - 496 + 224 = s.getReg .x2 - 272 by addr_omega [hb1]] at hf₁
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  have hop : u₁.getReg .x12 = s.getMem (s.getReg .x11 + BitVec.ofNat 64 (80 * i + 72)) := by
    have e := b80008600_x12 h₁
    rw [hsp, L.x18] at e
    rv_eval [e400] at e
    rw [e, ← I.word hpre.tables (by addr_omega [hTb, hiT]) (by addr_omega [hTb, hiT])]
    exact congrArg _ (by addr_omega [hTb, hiT])
  have hopn : (u₁.getReg .x12).toNat = opAt s i := by rw [hop]; rfl
  by_cases h6 : 6 ≤ opAt s i
  · refine ⟨u₁, hr₁, Or.inr (trap (b80008600_pc_taken h₁ ?_))⟩
    rw [← b80008600_x12 h₁, hopn]
    simp only [Sym.wordToNatLit]
    exact h6
  have hop6 : opAt s i < 6 := by omega
  have hpc₁ := b80008600_pc_not_taken h₁ (by
    rw [← b80008600_x12 h₁, hopn]; simp only [Sym.wordToNatLit]; exact hop6)
  have hweight : eAt u₁ (s.getReg .x2 - 272) = ws.getD i 0 := by
    have m0 := b80008600_m_x2_224 h₁
    have m1 := b80008600_m_x2_232 h₁
    have m2 := b80008600_m_x2_240 h₁
    rw [hsp, L.x18] at m0 m1 m2
    rv_eval [e328] at m0 m1 m2
    rw [eAt_congr (s := u) (b := W + BitVec.ofNat 64 (24 * i))
      (by rw [m0]; exact congrArg _ (by addr_omega [hW1, hW2, hiT]))
      (by rw [show s.getReg .x2 - 272 + 8 = s.getReg .x2 - 264 by addr_omega [hb1], m1]
          exact congrArg _ (by addr_omega [hW1, hW2, hiT]))
      (by rw [show s.getReg .x2 - 272 + 16 = s.getReg .x2 - 256 by addr_omega [hb1], m2]
          exact congrArg _ (by addr_omega [hW1, hW2, hiT])),
      L.frame.eAt fun j hj ↦ tw_old hpre C.inv.heap (a := W + BitVec.ofNat 64 (24 * i)) (m := 24)
        (by simp only [heapStart]; addr_omega [hW1, hW2, hiT]) (by addr_omega [hW1, hW2, hiT]) j hj,
      ← C.weights, eListAt_getD _ _ hiT]
  -- `0x80008648`: `N_CONSTRAINTS[opcode]`, the cursor's overflow
  have e336₁ : u₁.getMem (s.getReg .x2 - 336) = 0xa0000080 :=
    (hf₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]).trans e336
  have hop6' : (u₁.getReg .x12).toNat < 6 := by rw [hopn]; exact hop6
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008648_spec hpc₁ (by
    rv_eval [hsp₁, e336₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access nc_valid [hop6'])
  set c := (tAcc s rows ws i).2 with hc
  set nC := (tables.getD (opAt s i) default).nConstraints with hnC
  have hnC2 : nC ≤ 2 := nc_le hop6
  have hnc : u₁.getMem (0xa0000080 + u₁.getReg .x12 * 8) = BitVec.ofNat 64 nC := by
    rw [hf₁ _ (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hop6']), hnC, ← hopn]
    exact nc_at (I.rodata hpre) hop6'
  have hx8₂ : u₂.getReg .x8 = BitVec.ofNat 64 nC := by
    have e := b80008648_x8 h₂
    rw [hsp₁] at e
    rv_eval [e336₁] at e
    rw [e]
    exact (congrArg _ (by addr_omega [hop6'])).trans hnc
  have hx21₂ : u₂.getReg .x21 = BitVec.ofNat 64 nC + BitVec.ofNat 64 c := by
    rw [b80008648_x21 h₂, ← b80008648_x8 h₂, hx8₂, k₁ .x10 (by decide), L.x10]
  have hcur := L.cur
  have h28 := (s.getReg .x28).isLt
  by_cases hov : c + nC < 2 ^ 64
  swap
  · refine ⟨u₂, hr₁.trans hr₂, Or.inr (trap (b80008648_pc_taken h₂ ?_))⟩
    rw [← b80008648_x21 h₂, ← b80008648_x8 h₂, hx21₂, hx8₂, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := nC) (by omega), Nat.mod_eq_of_lt (a := c) (by omega)]
    omega
  have hx21n : u₂.getReg .x21 = BitVec.ofNat 64 (c + nC) := by
    rw [hx21₂]; addr_omega [hov]
  have hpc₂ := b80008648_pc_not_taken h₂ (by
    rw [← b80008648_x21 h₂, ← b80008648_x8 h₂, hx21n, hx8₂, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := nC) (by omega), Nat.mod_eq_of_lt hov]
    omega)
  have k₂ := b80008648_keeps h₂
  have hm₂ := b80008648_mem_same h₂
  have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 496 := (k₂ .x2 (by decide)).trans hsp₁
  -- `0x80008660`: the slice ends within `constraint_powers`
  have e408₂ : u₂.getMem (s.getReg .x2 - 408) = s.getReg .x28 := by
    rw [hm₂, hf₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]]; exact e408
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008660_spec hpc₂ (by
    rv_eval [hsp₂]; valid_access hval [hb1])
  by_cases hend : (s.getReg .x28).toNat < c + nC
  · refine ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inr (trap (b80008660_pc_taken h₃ ?_))⟩
    rw [hsp₂]; rv_eval [e408₂]
    rw [hx21n, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hov]
    exact hend
  have hpc₃ := b80008660_pc_not_taken h₃ (by
    rw [hsp₂]; rv_eval [e408₂]
    rw [hx21n, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hov]
    omega)
  have k₃ := b80008660_keeps h₃
  have hm₃ := b80008660_mem_same h₃
  have hsp₃ : u₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  -- `0x80008668`: the slice's start, the row
  have e416₃ : u₃.getMem (s.getReg .x2 - 416) = s.getReg .x17 := by
    rw [hm₃, hm₂, hf₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]]; exact e416
  have e344₃ : u₃.getMem (s.getReg .x2 - 344) = vecPtr u₀ (s.getReg .x2 - 296) := by
    rw [hm₃, hm₂, hf₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]]; exact e344
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80008668_spec hpc₃ (by
    rv_eval [hsp₃]; and_intros <;> valid_access hval [hb1])
  have k₄ := b80008668_keeps h₄
  have hm₄ := b80008668_mem_same h₄
  have R1 (r : Reg) (h1 : r ∈ ([.x2, .x18, .x22, .x24, .x25, .x27] : List Reg)) :
      u₄.getReg r = u.getReg r := by
    rw [k₄ r (mem_of_mem h1 _), k₃ r (mem_of_mem h1 _), k₂ r (mem_of_mem h1 _),
      k₁ r (mem_of_mem h1 _)]
  have hx12₃ : u₃.getReg .x12 = u₁.getReg .x12 := by
    rw [k₃ .x12 (by decide), k₂ .x12 (by decide)]
  have hfr : DFrame u₀ u₄ (TW s u₀ u₄) := by
    have hn : heapNext u₄ = heapNext u := by
      simp only [heapNext]
      rw [hm₄, hm₃, hm₂, hf₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
    exact (L.frame.mono fun a ha ↦ TW.mono hn.ge ha).trans
      (hf₁.trans (DFrame.of_same (fun a ↦ (hm₄ a).trans ((hm₃ a).trans (hm₂ a))) _)
        fun _ h ↦ h) fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb1]))
  have hn₄ : heapNext u₄ = heapNext u := by
    simp only [heapNext]
    rw [hm₄, hm₃, hm₂, hf₁ _ fun j hj hw ↦ by addr_omega [hw, hj, hb1]]
  have hAt : AtSum s u₀ u₄ rows ws i := {
    sp := (R1 .x2 (by decide)).trans hsp
    heap := ⟨hn₄ ▸ L.heap.lo, hn₄ ▸ L.heap.hi⟩
    mono := hn₄ ▸ L.mono
    frame := hfr
    x18 := (R1 .x18 (by decide)).trans L.x18
    x19 := by
      rw [b80008668_x19 h₄, hsp₃, k₃ .x11 (by decide), k₂ .x11 (by decide), b80008600_x11 h₁,
        k₃ .x18 (by decide), k₂ .x18 (by decide), k₁ .x18 (by decide), L.x18]
      rv_eval [e344₃]
      rw [← mul48]
    x11 := by
      rw [b80008668_x11 h₄, hsp₃, k₃ .x10 (by decide), k₂ .x10 (by decide), k₁ .x10 (by decide),
        L.x10]
      rv_eval [e416₃]
      rw [← mul24]
    x8 := by rw [k₄ .x8 (by decide), k₃ .x8 (by decide)]; exact hx8₂
    x21 := by rw [k₄ .x21 (by decide), k₃ .x21 (by decide)]; exact hx21n
    x9 := by
      rw [k₄ .x9 (by decide), k₃ .x9 (by decide), k₂ .x9 (by decide), b80008600_x9 h₁, L.x18,
        mul24]
    x22 := (R1 .x22 (by decide)).trans L.x22
    acc := by rw [R1 .x25 (by decide), R1 .x24 (by decide), R1 .x27 (by decide)]; exact L.acc
    weight := by
      rw [← hweight]
      exact (DFrame.of_same (fun a ↦ (hm₄ a).trans ((hm₃ a).trans (hm₂ a))) fun _ ↦ False).eAt
        fun _ _ h ↦ h
    op6 := hop6
    cur := by omega }
  have hx12₄ : u₃.getReg .x12 = BitVec.ofNat 64 (opAt s i) := by
    rw [hx12₃, ← hopn]; simp
  by_cases h4 : opAt s i = 4
  · exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl ⟨hAt, Or.inl ⟨h4,
      b80008668_pc_not_taken h₄ (by rw [hx12₄, h4]; rfl)⟩⟩⟩
  · exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl ⟨hAt, Or.inr ⟨h4,
      b80008668_pc_taken h₄ (by
        rw [hx12₄]; intro e; apply h4
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this)⟩⟩⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
