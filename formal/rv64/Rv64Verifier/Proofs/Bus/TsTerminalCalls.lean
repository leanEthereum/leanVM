import Rv64Verifier.Proofs.Bus.TsTerminalBody

/-!
# `table_sumcheck`: the terminal's calls, and the summand of a table without constraints

`mul` and `dot` into the frame (`mulCall`, `dotCall`), the `i`-th row's evaluations (`Ctx.row`),
and the summand of a table other than JUMP: `0x800087f4` calls `dot` on an empty slice into
`sp + 248` and returns to `0x8000880c` (`AtForms`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
  Rv64Verifier.MultilinearContracts Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem TW.trans {s u₀ v w : MachineState} (hm : heapNext u₀ ≤ heapNext v) {a : Word}
    (ha : TW s v w a) : TW s u₀ w a := by
  rcases ha with ha | ha | ha | ha | ⟨h1, h2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩)))

theorem tw_comp {s u₀ v w : MachineState} (h₁ : DFrame u₀ v (TW s u₀ v))
    (h₂ : DFrame v w (TW s v w)) (hm₁ : heapNext u₀ ≤ heapNext v) (hm₂ : heapNext v ≤ heapNext w) :
    DFrame u₀ w (TW s u₀ w) :=
  (h₁.mono fun _ ha ↦ TW.mono hm₂ ha).trans h₂ fun _ ha ↦ TW.trans hm₁ ha

theorem Ctx.invAt {s u₀ v : MachineState} {rows : List (List E × List E)} {ws : List E}
    {W : Word} {n : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n)
    (hf : DFrame u₀ v (TW s u₀ v)) (hv : HeapOk v) (hm : heapNext u₀ ≤ heapNext v)
    (hsp : v.getReg .x2 = s.getReg .x2 - 496) : Inv s v :=
  C.inv.loc hpre (hf.mono fun _ ha ↦ TW.loc hpre ha) hv hm (hsp.trans C.inv.sp.symm)

/-- The `i`-th row: its evaluations' `Vec` at `R + 48 i + 24`, all below the loop's start. -/
theorem Ctx.row {s u₀ : MachineState} {rows : List (List E × List E)} {ws : List E} {W : Word}
    {n i : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n) (hi : i < n) :
    ∃ R, vecPtr u₀ (s.getReg .x2 - 296) = R ∧ heapStart ≤ R.toNat ∧
      R.toNat + 48 * n ≤ heapNext u₀ ∧ R.toNat % 8 = 0 ∧
      ∃ EP EL : Word, vecPtr u₀ (R + BitVec.ofNat 64 (48 * i + 24)) = EP ∧
        vecLen u₀ (R + BitVec.ofNat 64 (48 * i + 24)) = EL ∧ EP.toNat % 8 = 0 ∧
        (EL.toNat = 0 ∨ heapStart ≤ EP.toNat ∧ EP.toNat + 24 * EL.toNat ≤ heapNext u₀) ∧
        eListAt u₀ EP EL.toNat = (rows.getD i ([], [])).2 := by
  have hR := C.rowsAt
  obtain ⟨-, -, hnr, -⟩ := C.lens
  have hl := hpre.heap.lo
  have hc := hR.vec.len
  have hb := hR.vec.raw
  have hlen := hR.len
  simp only [RawVecOk, Buf] at hb
  have hir : i < rows.length := by omega
  obtain ⟨-, hp2⟩ := hR.pairs i hir
  have hbb := hp2.buf
  simp only [NewBuf] at hbb
  refine ⟨_, rfl, ?_, ?_, hb.1, _, _, rfl, rfl, hbb.1, ?_, ?_⟩
  · rcases hb.2 with h0 | h0 <;> omega
  · rcases hb.2 with h0 | h0 <;> omega
  · simp only [heapStart] at hl ⊢
    have hv2 := hp2.vec.len
    rcases hbb.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · rw [List.getD_eq_getElem _ _ hir, ← hp2.elems]; rfl

/-- `mul` of two `E`s of the frame into a third. -/
theorem mulCall (hMul : MulSpec) {s v v' : MachineState} (hpre : TableSumcheckPre s)
    (hr : Reaches Image.code v v') (hpc : v'.pc = 0x80008c48)
    (hsp : v'.getReg .x2 = s.getReg .x2 - 496) (hro : RodataOk v') {o l r : Word}
    (h10 : v'.getReg .x10 = s.getReg .x2 - o) (h11 : v'.getReg .x11 = s.getReg .x2 - l)
    (h12 : v'.getReg .x12 = s.getReg .x2 - r)
    (ho : 128 ≤ o.toNat ∧ o.toNat ≤ 472 ∧ o.toNat % 8 = 0)
    (hl : 128 ≤ l.toNat ∧ l.toNat ≤ 472 ∧ l.toNat % 8 = 0)
    (hr' : 128 ≤ r.toNat ∧ r.toNat ≤ 472 ∧ r.toNat % 8 = 0)
    (hol : o.toNat + 24 ≤ l.toNat ∨ l.toNat + 24 ≤ o.toNat)
    (hor : o.toNat + 24 ≤ r.toNat ∨ r.toNat + 24 ≤ o.toNat) :
    ∃ t, Reaches Image.code v t ∧ ((t.pc = returnAddress v' ∧ Preserves v' t ∧
      eAt t (s.getReg .x2 - o) = eAt v' (s.getReg .x2 - l) * eAt v' (s.getReg .x2 - r) ∧
      DFrame v' t fun a ↦ Within a (s.getReg .x2 - o) 24 ∨ Within a (s.getReg .x2 - 2128) 1632) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hrs := hpre.stack.rodata
  simp only [stack_eq] at hrs
  have hsl : stackLo v' mulStack = s.getReg .x2 - 1520 := by
    simp only [stackLo, mulStack, hsp]; addr_omega [hb1]
  have pre : MulPre v' := {
    out := by rw [h10]; valid_sub hval [hb1, ho]
    lhs := by rw [h11]; valid_sub hval [hb1, hl]
    rhs := by rw [h12]; valid_sub hval [hb1, hr']
    stack := ⟨by rw [hsl]; valid_sub hval [hb1], by rw [hsp]; addr_omega [hb1, hb3]⟩
    outLhs := by rw [h10, h11]; addr_omega [hb1, ho, hl, hol]
    outRhs := by rw [h10, h12]; addr_omega [hb1, ho, hr', hor]
    outStack := by rw [h10, hsl]; addr_omega [hb1, ho]
    lhsStack := by rw [h11, hsl]; addr_omega [hb1, hl]
    rhsStack := by rw [h12, hsl]; addr_omega [hb1, hr']
    rodata := hro
    stackRodata := by rw [hsl]; addr_omega [hrs, hb1] }
  obtain ⟨t, hrt, ⟨hpct, hpt, post⟩ | hd⟩ := hMul.call hr hpc pre
  · refine ⟨t, hrt, Or.inl ⟨hpct, hpt, by rw [← h10, ← h11, ← h12]; exact post.value, ?_⟩⟩
    refine (DFrame.of_two fun a h1 h2 ↦ post.frame a h1 h2).mono fun a ha ↦ ?_
    rw [h10, hsl] at ha
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by addr_omega [ha, hb1])
  · exact ⟨t, hrt, Or.inr hd⟩

/-- `dot` into the frame, of slices apart from the stack. -/
theorem dotCall (hDot : DotSpec) {s v v' : MachineState} (hpre : TableSumcheckPre s)
    (hr : Reaches Image.code v v') (hpc : v'.pc = 0x80007f3c)
    (hsp : v'.getReg .x2 = s.getReg .x2 - 496) (hro : RodataOk v') {o : Word}
    (h10 : v'.getReg .x10 = s.getReg .x2 - o)
    (ho : 128 ≤ o.toNat ∧ o.toNat ≤ 472 ∧ o.toNat % 8 = 0)
    (hl : ValidMemRange (v'.getReg .x11) (3 * (v'.getReg .x12).toNat))
    (hr' : ValidMemRange (v'.getReg .x13) (3 * (v'.getReg .x14).toNat))
    (hla : Apart (v'.getReg .x11) (24 * (v'.getReg .x12).toNat) (s.getReg .x2 - 2128) 2128)
    (hra : Apart (v'.getReg .x13) (24 * (v'.getReg .x14).toNat) (s.getReg .x2 - 2128) 2128) :
    ∃ t, Reaches Image.code v t ∧ ((t.pc = returnAddress v' ∧ Preserves v' t ∧
      v'.getReg .x12 = v'.getReg .x14 ∧
      eAt t (s.getReg .x2 - o) = dotRust (eListAt v' (v'.getReg .x11) (v'.getReg .x12).toNat)
        (eListAt v' (v'.getReg .x13) (v'.getReg .x12).toNat) ∧
      DFrame v' t fun a ↦ Within a (s.getReg .x2 - o) 24 ∨ Within a (s.getReg .x2 - 2128) 1632) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hrs := hpre.stack.rodata
  simp only [stack_eq] at hrs
  have hsl : stackLo v' dotStack = s.getReg .x2 - 1616 := by
    simp only [stackLo, dotStack, mulStack, Nat.reduceAdd, hsp]; addr_omega [hb1]
  have pre : DotPre v' := {
    ret := by rw [h10]; valid_sub hval [hb1, ho]
    left := hl
    right := hr'
    stack := ⟨by rw [hsl]; valid_sub hval [hb1], by rw [hsp]; addr_omega [hb1, hb3]⟩
    retLeft := by rw [h10]; addr_omega [hb1, ho, hla]
    retRight := by rw [h10]; addr_omega [hb1, ho, hra]
    retStack := by rw [h10, hsl]; addr_omega [hb1, ho]
    leftStack := by rw [hsl]; addr_omega [hb1, hla]
    rightStack := by rw [hsl]; addr_omega [hb1, hra]
    rodata := hro
    retRodata := by rw [h10]; addr_omega [hrs, hb1, ho]
    stackRodata := by rw [hsl]; addr_omega [hrs, hb1] }
  obtain ⟨t, hrt, ⟨hpct, hpt, post⟩ | hd⟩ := hDot.call hr hpc pre
  · refine ⟨t, hrt, Or.inl ⟨hpct, hpt, post.len, by rw [← h10]; exact post.value, ?_⟩⟩
    refine (DFrame.of_two fun a h1 h2 ↦ post.frame a h1 h2).mono fun a ha ↦ ?_
    rw [h10, hsl] at ha
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (by addr_omega [ha, hb1])
  · exact ⟨t, hrt, Or.inr hd⟩

/-! ## The summand -/

/-- The summand of the `i`-th item. -/
def sumOf (s : MachineState) (rows : List (List E × List E)) (ws : List E) (i : ℕ) : E :=
  dotRust (((cpOf s).drop (tAcc s rows ws i).2).take (tables.getD (opAt s i) default).nConstraints)
    ((tables.getD (opAt s i) default).constraints (rows.getD i ([], [])).2)

/-- At `0x8000880c`: the summand at `sp + 248`. -/
structure AtForms (s u₀ v : MachineState) (rows : List (List E × List E)) (ws : List E) (i : ℕ) :
    Prop where
  sp : v.getReg .x2 = s.getReg .x2 - 496
  heap : HeapOk v
  mono : heapNext u₀ ≤ heapNext v
  frame : DFrame u₀ v (TW s u₀ v)
  x18 : v.getReg .x18 = BitVec.ofNat 64 i
  x19 : v.getReg .x19 = vecPtr u₀ (s.getReg .x2 - 296) + BitVec.ofNat 64 (48 * i)
  x21 : v.getReg .x21 =
    BitVec.ofNat 64 ((tAcc s rows ws i).2 + (tables.getD (opAt s i) default).nConstraints)
  x9 : v.getReg .x9 = BitVec.ofNat 64 (24 * i)
  x22 : v.getReg .x22 = s.getReg .x30
  acc : Model.limbs (tAcc s rows ws i).1 = (v.getReg .x25, v.getReg .x24, v.getReg .x27)
  weight : eAt v (s.getReg .x2 - 272) = ws.getD i 0
  summand : eAt v (s.getReg .x2 - 248) = sumOf s rows ws i
  cur : (tAcc s rows ws i).2 + (tables.getD (opAt s i) default).nConstraints ≤
    (s.getReg .x28).toNat

/-- A table other than JUMP: `dot` of empty slices, `0`. -/
theorem otherSum (hDot : DotSpec) {s u₀ v : MachineState} {rows : List (List E × List E)}
    {ws : List E} {W : Word} {n i : ℕ} (hpre : TableSumcheckPre s) (C : Ctx s u₀ rows ws W n)
    (h : AtSum s u₀ v rows ws i) (h4 : opAt s i ≠ 4) (hpc : v.pc = 0x800087f4) :
    ∃ w, Reaches Image.code v w ∧
      ((w.pc = 0x8000880c ∧ AtForms s u₀ w rows ws i) ∨ Dead Image.code w) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn0 : (tables.getD (opAt s i) default).nConstraints = 0 := nc_other h.op6 h4
  have I := C.invAt hpre h.frame h.heap h.mono h.sp
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800087f4_spec hpc trivial
  have k₁ := b800087f4_keeps h₁
  have hm₁ := b800087f4_mem_same h₁
  have hsp₁ : v₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans h.sp
  have I₁ : Inv s v₁ := I.same hpre hm₁ (k₁ .x2 (by decide))
  have h12 : v₁.getReg .x12 = 0 := by rw [b800087f4_x12 h₁, h.x8, hn0]; rfl
  have h14 := b800087f4_x14 h₁
  obtain ⟨v₂, hr₂, ⟨hpc₂, hp₂, -, hv₂, hf₂⟩ | hd⟩ := dotCall hDot hpre hr₁ (b800087f4_pc h₁) hsp₁
    (I₁.rodata hpre) (o := 248) (by rw [b800087f4_x10 h₁, h.sp]; addr_omega [hb1]) (by decide)
    (by rw [h12]; intro j hj; simp at hj) (by rw [h14]; intro j hj; simp at hj)
    (by rw [h12]; simp [Apart]) (by rw [h14]; simp [Apart])
  swap
  · exact ⟨v₂, hr₂, Or.inr hd⟩
  have hn₂ : heapNext v₂ = heapNext v := by
    simp only [heapNext]
    rw [hf₂ _ fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1], hm₁]
  have hR (r : Reg) (hr : r ∈ ([.x2, .x9, .x18, .x19, .x21, .x22, .x24, .x25, .x27] : List Reg)) :
      v₂.getReg r = v.getReg r := by
    rw [hp₂ r (by unfold calleeSaved; exact mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  refine ⟨v₂, hr₂, Or.inl ⟨by rw [hpc₂, returnAddress_eq, b800087f4_x1 h₁]; decide, {
    sp := (hR .x2 (by decide)).trans h.sp
    heap := ⟨hn₂ ▸ h.heap.lo, hn₂ ▸ h.heap.hi⟩
    mono := hn₂ ▸ h.mono
    frame := (h.frame.mono fun a ha ↦ TW.mono hn₂.ge ha).trans
      ((DFrame.of_same hm₁ fun a ↦ Within a (s.getReg .x2 - 248) 24 ∨
        Within a (s.getReg .x2 - 2128) 1632).trans hf₂ fun _ h ↦ h) fun a ha ↦ by
        rcases ha with ha | ha
        · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
        · exact Or.inr (Or.inr (Or.inl ha))
    x18 := (hR .x18 (by decide)).trans h.x18
    x19 := (hR .x19 (by decide)).trans h.x19
    x21 := (hR .x21 (by decide)).trans h.x21
    x9 := (hR .x9 (by decide)).trans h.x9
    x22 := (hR .x22 (by decide)).trans h.x22
    acc := by rw [hR .x25 (by decide), hR .x24 (by decide), hR .x27 (by decide)]; exact h.acc
    weight := by
      rw [hf₂.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb1],
        (DFrame.of_same hm₁ fun _ ↦ False).eAt fun _ _ h ↦ h]
      exact h.weight
    summand := by
      rw [hv₂, h12]
      simp only [sumOf, hn0, List.take_zero]
      simp [dotRust, eListAt]
    cur := h.cur }⟩⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
