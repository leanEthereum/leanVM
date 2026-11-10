import Rv64Verifier.Proofs.Bus.VbbTail63

/-!
# `verify_bus_balance`'s side loop: the selectors' sum

From `0x80007b24` to `0x80007bbc`: `E::sum` over the framework selectors chained with the tables'
(`sideSums`), as two loops each skipped when empty (`sumE_append`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem NewBuf.heapArr {h t : MachineState} {q : Word} {n : Nat} (hb : NewBuf h t q (24 * n) 8)
    (hn : 0 < n) (hlo : heapStart ≤ heapNext h) (hhi : heapNext t ≤ heapEnd) : HeapArr q n := by
  obtain ⟨b8, hb⟩ := hb
  rcases hb with h0 | ⟨b1, b2⟩
  · omega
  · exact ⟨b8, by omega, by omega⟩

theorem NewBuf.lt {h t : MachineState} {q : Word} {n : Nat} (hb : NewBuf h t q (24 * n) 8)
    (hhi : heapNext t ≤ heapEnd) : n < 2 ^ 60 := by
  obtain ⟨-, hb⟩ := hb
  simp only [heapEnd] at hhi
  rcases hb with h0 | ⟨-, b2⟩ <;> omega

theorem ofNat_ne_zero {n : Nat} (h : n < 2 ^ 60) (hn : n ≠ 0) : BitVec.ofNat 64 n ≠ 0 := by
  intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  exact hn this

/-- The tables' selectors' sum, from `0x80007b8c`. -/
theorem sumTb {t t₁ : MachineState} {q : Word} {n : Nat} {a : E} {T : List E} (hq : HeapArr q n)
    (hl : eListAt t q n = T) (hn : 0 < n) (hpc : t₁.pc = 0x80007b8c)
    (mem : ∀ x, t₁.getMem x = t.getMem x)
    (regs : ∀ r ∈ ([.x2, .x15, .x16, .x17, .x22, .x25] : List Reg), t₁.getReg r = t.getReg r)
    (x20 : t₁.getReg .x20 = q) (x11 : t₁.getReg .x11 = BitVec.ofNat 64 n)
    (sum : eOf3 (t₁.getReg .x19) (t₁.getReg .x23) (t₁.getReg .x18) = a) (hT : T.length = n) :
    ∃ t', Reaches Image.code t₁ t' ∧ t'.pc = 0x80007bbc ∧ (∀ x, t'.getMem x = t.getMem x) ∧
      (∀ r ∈ ([.x2, .x15, .x16, .x17, .x22, .x25] : List Reg), t'.getReg r = t.getReg r) ∧
      eOf3 (t'.getReg .x19) (t'.getReg .x23) (t'.getReg .x18) = sumLeft a T := by
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007b8c_spec hpc trivial
  have k₂ := b80007b8c_keeps h₂
  have S : SumB t t₂ q n a T 0 := by
    refine ⟨fun x ↦ (b80007b8c_mem_same h₂ x).trans (mem x),
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (regs r hr), ?_, ?_, ?_⟩
    · rw [k₂ .x20 (by decide), x20]; simp
    · rw [b80007b8c_x10 h₂, x20, x11, mul24]
    · rw [k₂ .x19 (by decide), k₂ .x23 (by decide), k₂ .x18 (by decide), sum]; rfl
  obtain ⟨t', hr, S', hpc'⟩ := sumLoopB hq hl (n - 1) 0 t₂ (by omega) S (b80007b8c_pc h₂)
  refine ⟨t', hr₂.trans hr, hpc', S'.mem, S'.regs, ?_⟩
  rw [S'.sum, ← hT, List.take_length]

set_option maxRecDepth 8192 in
/-- From `0x80007b24` to `0x80007bbc`: the selectors' sum in `s3`, `s7`, `s2`. -/
theorem sideSums {s z h t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    (hpre : BusBalancePre s) (Ih : Inv s h) (Ct : Cur s z h t) (X : Ex s h t i sd point)
    (tb : eListAt t (t.getReg .x20) sd.2.1.tables.length = tbSel sd point)
    (tbBuf : NewBuf h t (t.getReg .x20) (24 * sd.2.1.tables.length) 8) (hpc : t.pc = 0x80007b24) :
    ∃ t', Reaches Image.code t t' ∧ t'.pc = 0x80007bbc ∧ (∀ x, t'.getMem x = t.getMem x) ∧
      (∀ r ∈ ([.x2, .x15, .x16, .x17, .x22, .x25] : List Reg), t'.getReg r = t.getReg r) ∧
      eOf3 (t'.getReg .x19) (t'.getReg .x23) (t'.getReg .x18) =
        sumE (sd.2.1.framework.map (·.eqAbove point) ++ tbSel sd point) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp : t.getReg .x2 = s.getReg .x2 - 1344 := Ct.inv.sp
  have htE := Ct.inv.heap.hi
  have hlo := Ih.heap.lo
  have hhl : heapStart ≤ heapNext h := le_trans hpre.heap.lo Ih.mono
  have a56 : t.getReg .x2 + 56 = s.getReg .x2 - 1288 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a48 : t.getReg .x2 + 48 = s.getReg .x2 - 1296 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a40 : t.getReg .x2 + 40 = s.getReg .x2 - 1304 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hfl := NewBuf.lt X.fwBuf htE
  have htl := NewBuf.lt tbBuf htE
  have hFl : (sd.2.1.framework.map (·.eqAbove point)).length = sd.2.1.framework.length :=
    List.length_map _
  have hTl : (tbSel sd point).length = sd.2.1.tables.length := List.length_map _
  rw [sumE_append]
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007b24_spec hpc (by
    rv_eval [sp]; valid_access hval [hb1])
  have k₁ := b80007b24_keeps h₁
  have m₁ := b80007b24_mem_same h₁
  have r56 : t.getMem (t.getReg .x2 + 56) = BitVec.ofNat 64 sd.2.1.framework.length := by
    rw [a56]; exact X.m1288
  -- the tables' part, from `0x80007b8c` or past it
  have tail (t₂ : MachineState) (hr : Reaches Image.code t t₂) (hpc₂ :
      (t₂.pc = 0x80007b8c ∧ 0 < sd.2.1.tables.length) ∨
      (t₂.pc = 0x80007bbc ∧ sd.2.1.tables.length = 0))
      (mem : ∀ x, t₂.getMem x = t.getMem x)
      (regs : ∀ r ∈ ([.x2, .x15, .x16, .x17, .x20, .x22, .x25] : List Reg),
        t₂.getReg r = t.getReg r)
      (x11 : t₂.getReg .x11 = BitVec.ofNat 64 sd.2.1.tables.length)
      (sum : eOf3 (t₂.getReg .x19) (t₂.getReg .x23) (t₂.getReg .x18) =
        sumLeft 0 (sd.2.1.framework.map (·.eqAbove point))) :
      ∃ t', Reaches Image.code t t' ∧ t'.pc = 0x80007bbc ∧ (∀ x, t'.getMem x = t.getMem x) ∧
        (∀ r ∈ ([.x2, .x15, .x16, .x17, .x22, .x25] : List Reg), t'.getReg r = t.getReg r) ∧
        eOf3 (t'.getReg .x19) (t'.getReg .x23) (t'.getReg .x18) =
          sumLeft (sumLeft 0 (sd.2.1.framework.map (·.eqAbove point))) (tbSel sd point) := by
    rcases hpc₂ with ⟨hpc₂, h0⟩ | ⟨hpc₂, h0⟩
    · obtain ⟨t', hr', hpc', mem', regs', sum'⟩ :=
        sumTb (NewBuf.heapArr tbBuf (by omega) hhl htE)
        tb (by omega) hpc₂ mem (fun r hr ↦ regs r (mem_of_mem hr _))
        (regs .x20 (by decide)) x11 sum hTl
      exact ⟨t', hr.trans hr', hpc', mem', regs', sum'⟩
    · have hT : tbSel sd point = [] := List.length_eq_zero_iff.mp (hTl.trans h0)
      refine ⟨t₂, hr, hpc₂, mem, fun r hr ↦ regs r (mem_of_mem hr _), ?_⟩
      rw [sum, hT]; rfl
  by_cases hf0 : sd.2.1.framework.length = 0
  · -- no framework selector: `0x80007b78`
    have pc₁ := b80007b24_pc_taken h₁ (by rw [r56, hf0]; rfl)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007b78_spec pc₁ (by
      rv_eval [k₁ .x2 (by decide), sp]; valid_access hval [hb1])
    have k₂ := b80007b78_keeps h₂
    have r48 : t₁.getMem (t₁.getReg .x2 + 48) = BitVec.ofNat 64 sd.2.1.tables.length := by
      rw [k₁ .x2 (by decide), a48, m₁]; exact X.m1296
    have hF : sd.2.1.framework.map (·.eqAbove point) = [] :=
      List.length_eq_zero_iff.mp (hFl.trans hf0)
    refine tail t₂ (hr₁.trans hr₂) ?_ (fun x ↦ (b80007b78_mem_same h₂ x).trans (m₁ x))
      (fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)))
      (by rw [b80007b78_x11 h₂, r48]) (by
        rw [b80007b78_x19 h₂, b80007b78_x23 h₂, b80007b78_x18 h₂, hF]; exact eOf3_zero)
    by_cases ht0 : sd.2.1.tables.length = 0
    · exact Or.inr ⟨b80007b78_pc_taken h₂ (by rw [r48, ht0]; rfl), ht0⟩
    · exact Or.inl ⟨b80007b78_pc_not_taken h₂ (by rw [r48]; exact ofNat_ne_zero htl ht0),
        by omega⟩
  · -- the framework selectors' loop
    have pc₁ := b80007b24_pc_not_taken h₁ (by rw [r56]; exact ofNat_ne_zero hfl hf0)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007b2c_spec pc₁ (by
      rv_eval [k₁ .x2 (by decide), sp]; valid_access hval [hb1])
    have k₂ := b80007b2c_keeps h₂
    have m₂ (x : Word) : t₂.getMem x = t.getMem x := (b80007b2c_mem_same h₂ x).trans (m₁ x)
    have r40 : t₁.getMem (t₁.getReg .x2 + 40) = t.getMem (s.getReg .x2 - 1304) := by
      rw [k₁ .x2 (by decide), a40, m₁]
    have x11₁ : t₁.getReg .x11 = BitVec.ofNat 64 sd.2.1.framework.length := by
      rw [b80007b24_x11 h₁, r56]
    have S : SumA t t₂ (t.getMem (s.getReg .x2 - 1304)) sd.2.1.framework.length 0
        (sd.2.1.framework.map (·.eqAbove point)) 0 := by
      refine ⟨m₂, fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)), ?_, ?_, ?_⟩
      · rw [b80007b2c_x14 h₂, r40]; simp
      · rw [b80007b2c_x10 h₂, r40, x11₁, mul24]
      · rw [b80007b2c_x19 h₂, b80007b2c_x23 h₂, b80007b2c_x18 h₂]; exact eOf3_zero
    obtain ⟨t₃, hr₃, S', pc₃⟩ := sumLoopA (NewBuf.heapArr X.fwBuf (by omega) hhl htE) X.fw
      (sd.2.1.framework.length - 1) 0 t₂ (by omega) S (b80007b2c_pc h₂)
    have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1344 := (S'.regs .x2 (by decide)).trans sp
    obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80007b6c_spec pc₃ (by
      rv_eval [sp₃]; valid_access hval [hb1])
    have k₄ := b80007b6c_keeps h₄
    have m₄ (x : Word) : t₄.getMem x = t.getMem x := (b80007b6c_mem_same h₄ x).trans (S'.mem x)
    have r48 : t₃.getMem (t₃.getReg .x2 + 48) = BitVec.ofNat 64 sd.2.1.tables.length := by
      rw [sp₃, ← sp, a48, S'.mem]; exact X.m1296
    have sum₄ : eOf3 (t₄.getReg .x19) (t₄.getReg .x23) (t₄.getReg .x18) =
        sumLeft 0 (sd.2.1.framework.map (·.eqAbove point)) := by
      rw [k₄ .x19 (by decide), k₄ .x23 (by decide), k₄ .x18 (by decide), S'.sum, ← hFl,
        List.take_length]
    have regs₄ : ∀ r ∈ ([.x2, .x15, .x16, .x17, .x20, .x22, .x25] : List Reg),
        t₄.getReg r = t.getReg r := fun r hr ↦ (k₄ r (mem_of_mem hr _)).trans (S'.regs r hr)
    by_cases ht0 : sd.2.1.tables.length = 0
    · have pc₄ := b80007b6c_pc_not_taken h₄ (by rw [r48, ht0]; rfl)
      obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80007b74_spec pc₄ trivial
      have k₅ := b80007b74_keeps h₅
      exact tail t₅ (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))))
        (Or.inr ⟨b80007b74_pc h₅, ht0⟩) (fun x ↦ (b80007b74_mem_same h₅ x).trans (m₄ x))
        (fun r hr ↦ (k₅ r (mem_of_mem hr _)).trans (regs₄ r hr))
        (by rw [k₅ .x11 (by decide), b80007b6c_x11 h₄, r48])
        (by rw [k₅ .x19 (by decide), k₅ .x23 (by decide), k₅ .x18 (by decide)]; exact sum₄)
    · exact tail t₄ (hr₁.trans (hr₂.trans (hr₃.trans hr₄)))
        (Or.inl ⟨b80007b6c_pc_taken h₄ (by rw [r48]; exact ofNat_ne_zero htl ht0), by omega⟩) m₄
        regs₄
        (by rw [b80007b6c_x11 h₄, r48]) sum₄

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
