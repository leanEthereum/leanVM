import Rv64Verifier.Proofs.Bus.TsRowsLoop

/-!
# `table_sumcheck`: the rows, from `0x80008384` to `0x80008520`

`0x80008384` allocates the rows' buffer for `tables.len()` pairs (`try_allocate_in`) and leaves
`min(tables.len(), table_log_heights.len())` in `s3` (`rowsStart`); the loop (`rowsLoop`) reads
the rows, and `0x80008508` leaves the terminal loop's count in `a1` (`rowsEnd`). `stageE` is all
of it: the rows at `S - 296`, those of the mirror (`AtTerminal`).
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section
variable {s u r v : MachineState} {ch : List E} {cl : E} {P W R : Word} {n i : ℕ}
  {rows : List (List E × List E)}

/-- A step that writes nothing keeps the loop's memory. -/
theorem RowsMem.same (hpre : TableSumcheckPre s) (h : RowsMem s u r v ch cl R i rows)
    {t : MachineState} (hm : ∀ a, t.getMem a = v.getMem a) (hsp : t.getReg .x2 = v.getReg .x2) :
    RowsMem s u r t ch cl R i rows := by
  have hn : heapNext t = heapNext v := by simp only [heapNext, hm]
  have It : Inv s t := h.inv.same hpre hm hsp
  exact {
    inv := It
    frame := (h.frame.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha | ha | ha | ⟨h1, h2⟩
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by rw [hn]; exact h2⟩))))))
      |>.trans (DFrame.of_same hm fun _ ↦ False) fun _ h ↦ h.elim
    rv := by rw [hn]; exact h.rv
    cap := (hm _).trans h.cap
    ptr := (hm _).trans h.ptr
    len := (hm _).trans h.len
    rowsLen := h.rowsLen
    pairs := fun j hj ↦ ⟨(h.pairs j hj).1.of_same hm, (h.pairs j hj).2.of_same hm⟩
    run := fun T hT ↦ by
      obtain ⟨T₁, T₂, e1, e2, hT₂⟩ := h.run T hT
      exact ⟨T₁, T₂, e1, e2, h.inv.transcript hpre It.heap (DFrame.of_same hm _) hT₂⟩ }

/-- The rows read, the terminal's count in `a1`: `AtTerminal`. -/
theorem atTerminal_of (hpre : TableSumcheckPre s) (hc : RowsCtx s u r ch cl P W R n)
    (h : RowsMem s u r v ch cl R n rows)
    (hx11 : v.getReg .x11 = BitVec.ofNat 64
      (min (min (s.getReg .x12).toNat rows.length) (s.getReg .x16).toNat)) :
    AtTerminal s v ch cl P W rows := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn := hc.n
  have hWb := hc.atr.wbuf
  have hRb := hc.rbuf
  have hur := hc.ur
  have hrv := h.rv
  have hmu := hc.atr.inv.mono
  have hlo := hpre.heap.lo
  simp only [NewBuf] at hWb hRb
  simp only [heapStart] at hlo
  have hut : heapNext u ≤ heapNext v := hur.trans hrv
  have hsr : heapNext s ≤ heapNext r := hmu.trans hur
  have w320 (k : ℕ) (hk : k ≤ 16) : v.getMem (s.getReg .x2 - 320 + BitVec.ofNat 64 k) =
      u.getMem (s.getReg .x2 - 320 + BitVec.ofNat 64 k) :=
    h.frame _ fun j hj hw ↦ (RowsW.miss hpre h.inv.heap hw).2.1 (by addr_omega [hj, hb1, hk])
  have eC : vecCap v (s.getReg .x2 - 296) = s.getReg .x12 := h.cap
  have eP : vecPtr v (s.getReg .x2 - 296) = R := by
    rw [vecPtr, show s.getReg .x2 - 296 + 8 = s.getReg .x2 - 288 by addr_omega [hb1]]; exact h.ptr
  have eL : vecLen v (s.getReg .x2 - 296) = BitVec.ofNat 64 n := by
    rw [vecLen, show s.getReg .x2 - 296 + 16 = s.getReg .x2 - 280 by addr_omega [hb1]]; exact h.len
  have hnt : n ≤ (s.getReg .x12).toNat := by omega
  have hnL : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.getReg .x12).isLt; omega)]
  exact {
    inv := h.inv
    kept := h.kept hpre hc
    args := h.args hpre hc
    tablesLen := (h.slot hpre (by addr_omega [hb1]) (by addr_omega [hb1])).trans hc.atr.tablesLen
    wptr := by
      rw [vecPtr, show s.getReg .x2 - 320 + 8 = s.getReg .x2 - 320 + BitVec.ofNat 64 8 from rfl,
        w320 8 (by omega)]
      exact hc.atr.wptr
    wlen := by
      rw [vecLen, show s.getReg .x2 - 320 + 16 = s.getReg .x2 - 320 + BitVec.ofNat 64 16 from rfl,
        w320 16 (by omega)]
      exact hc.atr.wlen
    wbuf := by simp only [NewBuf]; omega
    weights := by
      rw [h.frame.eListAt (RowsW.old hpre hc.atr.inv.heap (by omega))]
      exact hc.atr.weights
    rowsAt := {
      vec := ⟨by simp only [RawVecOk, Buf, eC, eP, heapStart]; omega,
        by rw [eL, eC, hnL]; exact hnt⟩
      fresh := by simp only [NewBuf, eC, eP]; omega
      len := by rw [eL, hnL, h.rowsLen]
      pairs := fun j hj ↦ by
        rw [eP]; exact ⟨(h.pairs j hj).1.weaken hsr, (h.pairs j hj).2.weaken hsr⟩ }
    rowsLen := h.rowsLen.trans hn
    x11 := hx11
    run := fun T hT ↦ by
      obtain ⟨T₁, T₂, e1, e2, hT₂⟩ := h.run T hT
      refine ⟨T₁, T₂, e1, ?_, hT₂⟩
      rw [e2, List.drop_eq_nil_of_le (by rw [rowItems_length, ← hn])]
      rfl }

/-- `0x80008508` to `0x80008520`: `a1 = min(min(tables.len(), rows.len()), bus_forms.len())`. -/
theorem rowsEnd (hpre : TableSumcheckPre s) (hc : RowsCtx s u r ch cl P W R n)
    (h : RowsHead s u r v ch cl R n n rows) (hpc : v.pc = 0x80008508) :
    ∃ t, Reaches Image.code v t ∧ t.pc = 0x80008520 ∧ AtTerminal s t ch cl P W rows := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have hsp := h.inv.sp
  have hn := hc.n
  have e104 : v.getMem (v.getReg .x2 + 104) = s.getReg .x12 := by
    rw [hsp, show s.getReg .x2 - 496 + 104 = s.getReg .x2 - 392 by addr_omega [hb1],
      h.slot hpre (by addr_omega [hb1]) (by addr_omega [hb1])]
    exact hc.atr.tablesLen
  have e24 : v.getMem (v.getReg .x2 + 24) = s.getReg .x16 := by
    rw [hsp, show s.getReg .x2 - 496 + 24 = s.getReg .x2 - 472 by addr_omega [hb1]]
    exact (h.kept hpre hc).forms
  have hnt : n ≤ (s.getReg .x12).toNat := by omega
  have hnL : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (s.getReg .x12).isLt; omega)]
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008508_spec hpc (by
    rv_eval [hsp]; valid_access hval [hb1])
  have hm₁ := b80008508_mem_same h₁
  have k₁ := b80008508_keeps h₁
  -- `min(tables.len(), rows.len())`
  obtain ⟨v₂, hr₂, hpc₂, hm₂, hx₂, k₂⟩ : ∃ v₂, Reaches Image.code v₁ v₂ ∧ v₂.pc = 0x80008514 ∧
      (∀ a, v₂.getMem a = v₁.getMem a) ∧
      v₂.getReg .x11 = BitVec.ofNat 64 (min (s.getReg .x12).toNat n) ∧
      v₂.getReg .x2 = v₁.getReg .x2 := by
    by_cases hlt : (s.getReg .x12).toNat < n
    · refine ⟨v₁, Reaches.refl _, b80008508_pc_taken h₁ (by rw [e104, h.x20, hnL]; exact hlt),
        fun _ ↦ rfl, ?_, rfl⟩
      rw [b80008508_x11 h₁, e104, Nat.min_eq_left hlt.le]; simp
    · obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80008510_spec
        (b80008508_pc_not_taken h₁ (by rw [e104, h.x20, hnL]; omega)) trivial
      refine ⟨v₂, hr₂, b80008510_pc h₂, b80008510_mem_same h₂, ?_,
        b80008510_keeps h₂ .x2 (by decide)⟩
      rw [b80008510_x11 h₂, k₁ .x20 (by decide), h.x20, Nat.min_eq_right (by omega)]
  have hsp₂ : v₂.getReg .x2 = s.getReg .x2 - 496 := by rw [k₂, k₁ .x2 (by decide), hsp]
  have e24₂ : v₂.getMem (v₂.getReg .x2 + 24) = s.getReg .x16 := by
    rw [k₂, k₁ .x2 (by decide), hm₂, hm₁, e24]
  have hm32 : min (s.getReg .x12).toNat n < 2 ^ 64 := by
    have := (s.getReg .x12).isLt; omega
  have hxL : (v₂.getReg .x11).toNat = min (s.getReg .x12).toNat n := by
    rw [hx₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm32]
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80008514_spec hpc₂ (by
    rv_eval [hsp₂]; valid_access hval [hb1])
  have hm₃ := b80008514_mem_same h₃
  have k₃ := b80008514_keeps h₃
  -- then with `bus_forms.len()`
  obtain ⟨t, hr₄, hpct, hm₄, hx₄, k₄⟩ : ∃ t, Reaches Image.code v₃ t ∧ t.pc = 0x80008520 ∧
      (∀ a, t.getMem a = v₃.getMem a) ∧
      t.getReg .x11 = BitVec.ofNat 64 (min (min (s.getReg .x12).toNat n) (s.getReg .x16).toNat) ∧
      t.getReg .x2 = v₃.getReg .x2 := by
    by_cases hlt : min (s.getReg .x12).toNat n < (s.getReg .x16).toNat
    · refine ⟨v₃, Reaches.refl _, b80008514_pc_taken h₃ (by rw [e24₂, hxL]; exact hlt),
        fun _ ↦ rfl, ?_, rfl⟩
      rw [k₃ .x11 (by decide), hx₂, Nat.min_eq_left hlt.le]
    · obtain ⟨t, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000851c_spec
        (b80008514_pc_not_taken h₃ (by rw [e24₂, hxL]; omega)) trivial
      refine ⟨t, hr₄, b8000851c_pc h₄, b8000851c_mem_same h₄, ?_,
        b8000851c_keeps h₄ .x2 (by decide)⟩
      rw [b8000851c_x11 h₄, b80008514_x10 h₃, e24₂, Nat.min_eq_right (by omega)]; simp
  have hm (a : Word) : t.getMem a = v.getMem a := by rw [hm₄, hm₃, hm₂, hm₁]
  have hspt : t.getReg .x2 = v.getReg .x2 := by
    rw [k₄, k₃ .x2 (by decide), k₂, k₁ .x2 (by decide)]
  refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), hpct,
    atTerminal_of hpre hc (h.toRowsMem.same hpre hm hspt) ?_⟩
  rw [hx₄, h.rowsLen]

end

/-- What `0x80008384` to the loop's head writes. -/
def StartW (s u t : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2128) 1632 ∨ Within a (s.getReg .x2 - 152) 24 ∨
    Within a (s.getReg .x2 - 328) 8 ∨ Within a (s.getReg .x2 - 296) 24 ∨ Within a nextAddr 8 ∨
    Fresh u t a

/-- From `0x80008384`: the rows' buffer allocated, and either no rows (`0x80008520`) or the
loop's head with none read yet. -/
theorem rowsStart (hTA : TryAllocZeroedSpec) {s u : MachineState} {ch : List E} {cl : E}
    {P W : Word} (hpre : TableSumcheckPre s) (h : AtRows s u ch cl P W) (hpc : u.pc = 0x80008384) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80008520 ∧ AtTerminal s t ch cl P W []) ∨
      (∃ r R, t.pc = 0x80008428 ∧ 1 ≤ min (s.getReg .x12).toNat (s.getReg .x14).toNat ∧
        RowsCtx s u r ch cl P W R (min (s.getReg .x12).toNat (s.getReg .x14).toNat) ∧
        RowsHead s u r t ch cl R (min (s.getReg .x12).toNat (s.getReg .x14).toNat) 0 []) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  have I := h.inv
  have hsp := I.sp
  have ha := hpre.stack.above
  have hx := hpre.stack.next
  simp only [stack_eq] at ha hx
  have e104 : u.getMem (u.getReg .x2 + 104) = s.getReg .x12 := by
    rw [hsp, show s.getReg .x2 - 496 + 104 = s.getReg .x2 - 392 by addr_omega [hb1]]
    exact h.tablesLen
  -- `try_allocate_in(tables.len(), 8, 48)` into `S - 152`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80008384_spec hpc (by
    rv_eval [hsp]; valid_access hval [hb1])
  have k₁ := b80008384_keeps h₁
  have hm₁ := b80008384_mem_same h₁
  have hsp₁ : u₁.getReg .x2 = s.getReg .x2 - 496 := (k₁ .x2 (by decide)).trans hsp
  have h10₁ : u₁.getReg .x10 = s.getReg .x2 - 152 := by
    rw [b80008384_x10 h₁, hsp]; rv_eval []
  have h11₁ : u₁.getReg .x11 = s.getReg .x12 := by rw [b80008384_x11 h₁, e104]
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, hm₁]
  have hpre₂ : TryAllocPre .x13 .x14 u₁ := {
    heap := ⟨hn₁ ▸ I.heap.lo, hn₁ ▸ I.heap.hi⟩
    out := by rw [h10₁]; valid_sub hval [hb1]
    align := by rw [b80008384_x13 h₁]; decide
    size := by rw [b80008384_x14 h₁]; decide
    stack := hpre.stack.sub 496 hsp₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [h10₁]; simp only [Outside, heapEnd]; addr_omega [hb1, ha, hx]
    outStack := by rw [h10₁]; simp only [stackLo, tryAllocStack, hsp₁]; addr_omega [hb1] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post₂, -⟩ | hd⟩ := hTA.call hr₁ (b80008384_pc h₁) hpre₂
  swap
  · exact ⟨u₂, hr₂, Or.inr (Or.inr hd)⟩
  have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 496 := (hp₂.reg .x2).trans hsp₁
  have hf₂ := DFrame.of_byteFrame post₂.frame
  simp only [h10₁, stackLo, tryAllocStack, hsp₁] at hf₂
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800083a4_spec
    (by rw [hpc₂, returnAddress_eq, b80008384_x1 h₁]; decide) (by
      rv_eval [hsp₂]; valid_access hval [hb1])
  have e344 : u₂.getMem (u₂.getReg .x2 + 344) = u₂.getMem (u₁.getReg .x10) := by
    rw [hsp₂, h10₁]; congr 1; addr_omega [hb1]
  by_cases hok : u₂.getMem (u₁.getReg .x10) = 0
  swap
  · exact ⟨u₃, hr₂.trans hr₃,
      Or.inr (Or.inr (trap (b800083a4_pc_taken h₃ (by rw [e344]; exact hok))))⟩
  obtain ⟨hcap₂, hbuf₂⟩ := post₂.ok hok
  rw [h10₁, h11₁] at hcap₂
  rw [h10₁, h11₁, b80008384_x14 h₁, b80008384_x13 h₁] at hbuf₂
  simp only [Sym.wordToNatLit] at hbuf₂
  set R := u₂.getMem (s.getReg .x2 - 152 + 16) with hR
  have k₃ := b800083a4_keeps h₃
  have hm₃ := b800083a4_mem_same h₃
  have hsp₃ : u₃.getReg .x2 = s.getReg .x2 - 496 := (k₃ .x2 (by decide)).trans hsp₂
  -- `0x800083ac`: the rows' `Vec` at `S - 296`
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800083ac_spec
    (b800083a4_pc_not_taken h₃ (by rw [e344]; exact hok)) (by
      rv_eval [hsp₃]; and_intros <;> valid_access hval [hb1])
  have k₄ := b800083ac_keeps h₄
  have hf₄ := DFrame.of_memFrame (b800083ac_frame h₄ (by rw [hsp₃]; addr_omega [hb1]))
  rw [hsp₃, show s.getReg .x2 - 496 + 200 = s.getReg .x2 - 296 by addr_omega [hb1]] at hf₄
  have h9₄ : u₄.getReg .x9 = R := by
    rw [b800083ac_x9 h₄, hsp₃, hm₃]; congr 1; addr_omega [hb1]
  have m200 : u₄.getMem (s.getReg .x2 - 296) = s.getReg .x12 := by
    have := b800083ac_m_x2_200 h₄
    rw [hsp₃, hm₃] at this; rv_eval [] at this
    rw [this, ← hcap₂]; congr 1; addr_omega [hb1]
  have m208 : u₄.getMem (s.getReg .x2 - 288) = R := by
    have := b800083ac_m_x2_208 h₄
    rw [hsp₃, hm₃] at this; rv_eval [] at this
    rw [this]; congr 1; addr_omega [hb1]
  have m216 : u₄.getMem (s.getReg .x2 - 280) = 0 := by
    have := b800083ac_m_x2_216 h₄
    rw [hsp₃] at this; rv_eval [] at this; exact this
  set nt := (s.getReg .x12).toNat with hnt
  set nh := (s.getReg .x14).toNat with hnh
  -- `s3 = min(tables.len(), heights.len())`
  have h8₃ : u₃.getReg .x8 = s.getReg .x12 := by
    rw [k₃ .x8 (by decide), hp₂ .x8 (by decide), b80008384_x8 h₁, e104]
  have h26₃ : u₃.getReg .x26 = s.getReg .x14 := by
    rw [k₃ .x26 (by decide), hp₂ .x26 (by decide), k₁ .x26 (by decide), h.x26]
  obtain ⟨u₅, hr₅, hpc₅, hm₅, hx19₅, k₅⟩ : ∃ u₅, Reaches Image.code u₄ u₅ ∧
      u₅.pc = 0x800083cc ∧ (∀ a, u₅.getMem a = u₄.getMem a) ∧
      u₅.getReg .x19 = BitVec.ofNat 64 (min nt nh) ∧
      ∀ r, r ≠ .x19 → u₅.getReg r = u₄.getReg r := by
    by_cases hlt : nt < nh
    · refine ⟨u₄, Reaches.refl _, b800083ac_pc_taken h₄ (by rw [h8₃, h26₃]; exact hlt),
        fun _ ↦ rfl, ?_, fun _ _ ↦ rfl⟩
      rw [b800083ac_x19 h₄, h8₃, Nat.min_eq_left hlt.le]; simp [hnt]
    · obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800083c8_spec
        (b800083ac_pc_not_taken h₄ (by rw [h8₃, h26₃]; omega)) trivial
      refine ⟨u₅, hr₅, b800083c8_pc h₅, b800083c8_mem_same h₅, ?_, fun r hr ↦ ?_⟩
      · rw [b800083c8_x19 h₅, k₄ .x26 (by decide), h26₃, Nat.min_eq_right (by omega)]; simp [hnh]
      · have := b800083c8_keeps h₅
        rcases r <;> first | (exfalso; exact hr rfl) | exact this _ (by decide) | rfl
  have hsp₅ : u₅.getReg .x2 = s.getReg .x2 - 496 := by
    rw [k₅ .x2 (by decide), k₄ .x2 (by decide), hsp₃]
  -- the frame so far
  have hn₄ : heapNext u₄ = heapNext u₂ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat ((hf₄ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hx]).trans
      (hm₃ _))
  have hn₅ : heapNext u₅ = heapNext u₂ := by simp only [heapNext, hm₅] at hn₄ ⊢; exact hn₄
  have hm₂ := post₂.mono
  have hH₂ := post₂.heap
  have hf₅ : DFrame u u₅ (StartW s u u₅) := (((DFrame.of_same hm₁ (StartW s u u₅)).trans hf₂
    fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ha)
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [← hn₁]; exact h1,
          by rw [hn₅]; exact h2⟩))))).trans
    (DFrame.of_same hm₃ fun _ ↦ False) fun _ h ↦ h.elim).trans
    ((hf₄.trans (DFrame.of_same hm₅ fun _ ↦ False) fun _ h ↦ h.elim))
    fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inl ha)))
  have hc : RowsCtx s u u₂ ch cl P W R (min nt nh) := {
    atr := h
    ur := by rw [← hn₁]; exact hm₂
    rbuf := by
      simp only [NewBuf] at hbuf₂ ⊢
      rw [← hn₁]
      rcases hbuf₂.2 with h0 | h0
      · exact ⟨hbuf₂.1, Or.inl (by omega)⟩
      · exact ⟨hbuf₂.1, Or.inr ⟨h0.1, by omega⟩⟩
    n := rfl }
  -- the loop's memory once `0x80008428` or `0x80008520` is reached
  have mk (t : MachineState) (hf : DFrame u₅ t (Within · (s.getReg .x2 - 328) 8))
      (hspt : t.getReg .x2 = s.getReg .x2 - 496) : RowsMem s u u₂ t ch cl R 0 [] := by
    have hnt' : heapNext t = heapNext u₅ := by
      simp only [heapNext]
      exact congrArg BitVec.toNat (hf nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hx])
    have hfS : DFrame u t (StartW s u t) := (hf₅.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha | ha | ⟨h1, h2⟩
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by rw [hnt']; exact h2⟩))))).trans
      hf fun a ha ↦ Or.inr (Or.inr (Or.inl ha))
    have hL : DFrame u t (Loc s u t) := hfS.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)
    have hHt : HeapOk t := ⟨by rw [hnt', hn₅]; exact hH₂.lo, by rw [hnt', hn₅]; exact hH₂.hi⟩
    have It : Inv s t := I.loc hpre hL hHt (by rw [hnt', hn₅, ← hn₁]; exact hm₂)
      (hspt.trans hsp.symm)
    have slot (a : Word) (ha : Apart a 8 (s.getReg .x2 - 328) 8) (hab : a.toNat + 8 ≤ 2 ^ 64) :
        t.getMem a = u₄.getMem a :=
      (hf a fun j hj hw ↦ by addr_omega [hw, hj, ha, hab]).trans (hm₅ a)
    exact {
      inv := It
      frame := hfS.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha)))))
      rv := by rw [hnt', hn₅]
      cap := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans m200
      ptr := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans m208
      len := (slot _ (by addr_omega [hb1]) (by addr_omega [hb1])).trans m216
      rowsLen := rfl
      pairs := fun j hj ↦ absurd hj (Nat.not_lt_zero _)
      run := fun T hT ↦ by
        obtain ⟨T', e, hT'⟩ := h.run T hT
        exact ⟨T', T', e, by rw [List.drop_zero], I.transcript hpre hHt hL hT'⟩ }
  -- `0x800083cc`: no rows, or the loop
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800083cc_spec hpc₅ (by
    rv_eval [hsp₅]; valid_access hval [hb1])
  have hm₆ := b800083cc_mem_same h₆
  have k₆ := b800083cc_keeps h₆
  have hsp₆ : u₆.getReg .x2 = s.getReg .x2 - 496 := (k₆ .x2 (by decide)).trans hsp₅
  have hn32 : min nt nh < 2 ^ 64 := by have := (s.getReg .x12).isLt; omega
  by_cases hz : min nt nh = 0
  · obtain ⟨u₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800084f0_spec
      (b800083cc_pc_taken h₆ (by rw [hx19₅, hz]; rfl)) trivial
    have hm₇ (a : Word) : u₇.getMem a = u₅.getMem a := (b800084f0_mem_same h₇ a).trans (hm₆ a)
    have hsp₇ : u₇.getReg .x2 = s.getReg .x2 - 496 :=
      ((b800084f0_keeps h₇) .x2 (by decide)).trans hsp₆
    have hmem := mk u₇ (DFrame.of_same hm₇ _) hsp₇
    have hmem' : RowsMem s u u₂ u₇ ch cl R (min nt nh) [] := by rw [hz]; exact hmem
    refine ⟨u₇, hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₇)))),
      Or.inl ⟨b800084f0_pc h₇, atTerminal_of hpre hc hmem' ?_⟩⟩
    rw [b800084f0_x11 h₇]; simp
  -- `0x800083d4`: the loop's head
  have hA₅ := (mk u₅ (DFrame.refl _ _) hsp₅).args hpre hc
  obtain ⟨u₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800083d4_spec
    (b800083cc_pc_not_taken h₆ (by
      rw [hx19₅]; intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32] at this
      exact hz this)) (by
      rv_eval [hsp₆]; and_intros <;> valid_access hval [hb1])
  have k₇ := b800083d4_keeps h₇
  have hf₇ := DFrame.of_memFrame (b800083d4_frame h₇ (by rw [hsp₆]; addr_omega [hb1]))
  rw [hsp₆, show s.getReg .x2 - 496 + 168 = s.getReg .x2 - 328 by addr_omega [hb1]] at hf₇
  have hsp₇ : u₇.getReg .x2 = s.getReg .x2 - 496 := (k₇ .x2 (by decide)).trans hsp₆
  have hmem := mk u₇ ((DFrame.of_same hm₆ _).trans hf₇ fun _ h ↦ h) hsp₇
  have e96 : u₆.getMem (u₆.getReg .x2 + 96) = s.getReg .x11 := by
    rw [hsp₆, hm₆, show s.getReg .x2 - 496 + 96 = s.getReg .x2 - 400 by addr_omega [hb1]]
    exact hA₅.tables
  refine ⟨u₇, hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₇)))),
    Or.inr (Or.inl ⟨u₂, R, b800083d4_pc h₇, by omega, hc, { hmem with
      x9 := by rw [k₇ .x9 (by decide), k₆ .x9 (by decide), k₅ .x9 (by decide), h9₄]
      x11 := by
        rw [k₇ .x11 (by decide), b800083cc_x11 h₆, hsp₅, show s.getReg .x2 - 496 + 144 =
          s.getReg .x2 - 352 by addr_omega [hb1], hA₅.heights]
        simp
      x19 := by rw [k₇ .x19 (by decide), k₆ .x19 (by decide), hx19₅]
      x20 := by rw [b800083d4_x20 h₇]; rfl
      x21 := by rw [b800083d4_x21 h₇]; rfl
      x22 := by rw [b800083d4_x22 h₇, e96]; rfl
      widths := by
        have := b800083d4_m_x2_168 h₇
        rw [hsp₆] at this; rv_eval [] at this; exact this }⟩)⟩

/-- The rows, from `0x80008384` to `0x80008520`. The rows' capacity is `tables.len()`, so
`grow_one` is never called. -/
theorem stageE (hTA : TryAllocZeroedSpec) (hMC : MemcpySpec 0x800126e4) (hNS : NextScalarsSpec)
    {s u : MachineState} {ch : List E} {cl : E}
    {P W : Word} (hpre : TableSumcheckPre s) (h : AtRows s u ch cl P W) (hpc : u.pc = 0x80008384) :
    ∃ t, Reaches Image.code u t ∧
      ((∃ rows, t.pc = 0x80008520 ∧ AtTerminal s t ch cl P W rows) ∨ Done s t) := by
  obtain ⟨t, hr, ⟨hpct, ht⟩ | ⟨r, R, hpct, h1, hc, hh⟩ | hd⟩ := rowsStart hTA hpre h hpc
  · exact ⟨t, hr, Or.inl ⟨[], hpct, ht⟩⟩
  · obtain ⟨t', hr', ⟨rows, hpc', ht'⟩ | hd⟩ :=
      rowsLoop hTA hMC hNS hpre hc _ 0 t [] rfl h1 hpct hh
    · obtain ⟨t'', hr'', hpc'', ht''⟩ := rowsEnd hpre hc ht' hpc'
      exact ⟨t'', hr.trans (hr'.trans hr''), Or.inl ⟨rows, hpc'', ht''⟩⟩
    · exact ⟨t', hr.trans hr', Or.inr hd⟩
  · exact ⟨t, hr, Or.inr (Or.inr hd)⟩

end Rv64Verifier.Proofs.Bus.TableSumcheck
