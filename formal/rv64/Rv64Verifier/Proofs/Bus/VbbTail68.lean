import Rv64Verifier.Proofs.Bus.VbbTail67

/-!
# `verify_bus_balance`'s side loop: a side's tail

From the sums' entry `0x80007b24` (`Tl`): the selectors' sum (`sideSums`), `0x80007bbc` reading the
tree's value, `known` and the totals, room for one more total (`toPush`), the push (`pushTot`), to
the next side's head with the invariant, or past the last side (`sideTail`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem ofNat_24 {i : Nat} (hi : i < 3) :
    BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (8 * i) = BitVec.ofNat 64 (24 * i) := by
  interval_cases i <;> decide

/-- The side's total. -/
def sideTot (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point treeValues : List E)
    (i : Nat) (rows : E) : E :=
  treeValues.getD i 0 + dotRust (sd.2.1.framework.map (·.eqAbove point))
    (sd.2.2.1.map (sd.2.2.2.2 + ·)) +
    (sumE (sd.2.1.framework.map (·.eqAbove point) ++ tbSel sd point) + 1) + rows

set_option maxRecDepth 8192 in
theorem sideTail (hG : GrowOneFreshSpec 0x80011c78 24 8)
    {bev : MachineState → Word → List E → Option E} {s z w v h₀ h e t : MachineState}
    {k : Start} {state : GkrState} {mem : List E} {mf bf bv : E}
    {acc : List (List Form) × List E} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E}
    (hpre : BusBalancePre s) (C : SCtx bev s z w v h₀ k state mem mf bf bv)
    (Sd : Sides s z h₀ h (w.getReg .x23) (w.getReg .x25).toNat acc) (hi : i < 3)
    (T : Tl s z h e t i sd state.point (w.getReg .x23) (w.getReg .x25).toNat acc.1 acc.2)
    (hpc : t.pc = 0x80007b24) :
    ∃ h', Reaches Image.code t h' ∧ (Dead Image.code h' ∨
      Sides s z h₀ h' (w.getReg .x23) (w.getReg .x25).toNat
        ((blkFold state.point i sd acc.1 (min sd.2.1.tables.length sd.1.length)).1,
          acc.2 ++ [sideTot sd state.point state.values i
            (blkFold state.point i sd acc.1 (min sd.2.1.tables.length sd.1.length)).2]) ∧
      ((i + 1 < 3 ∧ h'.pc = 0x800074e0 ∧ h'.getReg .x22 = BitVec.ofNat 64 (i + 1)) ∨
        (i + 1 = 3 ∧ h'.pc = 0x80007c2c))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hsz : heapNext s ≤ heapNext z := C.fps.inv.mono
  have Ih := Sd.inv
  have M := T.mm
  have Ct := M.cur
  have sp : t.getReg .x2 = s.getReg .x2 - 1344 := Ct.inv.sp
  -- the selectors' sum
  obtain ⟨t₁, hr₁, pc₁, m₁, k₁, sum₁⟩ := sideSums hpre Ih Ct T.ex T.tb T.tbBuf hpc
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1344 := (k₁ .x2 (by decide)).trans sp
  have C₁ : Cur s z h t₁ := Ct.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₁ Ct.inv.heap (k₁ .x2 (by decide))) fun _ h ↦ h.elim
  obtain ⟨tp, tA, tz, tv⟩ := treeAt (i := i) hpre C Sd C₁ hi
  obtain ⟨T8, Tl, Th⟩ := tA
  simp only [heapStart, heapEnd] at Tl Th
  have hvT : ValidMemRange (vecPtr z (s.getReg .x2 - 176)) (3 * 3) :=
    heapRange T8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have a64 : t₁.getMem (s.getReg .x2 - 1280) = vecPtr z (s.getReg .x2 - 176) := tp
  have a160 : t₁.getMem (s.getReg .x2 - 1184) = BitVec.ofNat 64 (16 * i) := (m₁ _).trans T.m1184
  have a168 : t₁.getMem (s.getReg .x2 - 1176) = BitVec.ofNat 64 (8 * i) := (m₁ _).trans T.m1176
  have h24 := ofNat_24 hi
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007bbc_spec pc₁ (by
    rv_eval [sp₁, a64, a160, a168, h24]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hvT [Tl, Th, hi])
  have kk := b80007bbc_keeps h₂
  have m₂ (x : Word) : t₂.getMem x = t.getMem x := (b80007bbc_mem_same h₂ x).trans (m₁ x)
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1344 := (kk .x2 (by decide)).trans sp₁
  have St : StepS s t t₂ fun _ ↦ False := StepS.same m₂ Ct.inv.heap (sp₂.trans sp.symm)
  have C₂ : Cur s z h t₂ := Ct.next hpre hsz St fun _ h ↦ h.elim
  have M₂ := M.keep hpre hsz (hPb_of C) (DFrame.of_same m₂ _) St.heap St.mono (sp₂.trans sp.symm)
  -- the totals' length and capacity
  have a712 : t₁.getReg .x2 + 712 = s.getReg .x2 - 632 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a728 : t₁.getReg .x2 + 728 = s.getReg .x2 - 632 + 16 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x21₂ : t₂.getReg .x21 = vecLen t₂ (s.getReg .x2 - 632) := by
    rw [b80007bbc_x21 h₂, a728]; exact (m₁ _).trans (m₂ _).symm
  have hlen : t₁.getMem (t₁.getReg .x2 + 728) = vecLen t₂ (s.getReg .x2 - 632) := by
    rw [a728]; exact (m₁ _).trans (m₂ _).symm
  have hcap : t₁.getMem (t₁.getReg .x2 + 712) = vecCap t₂ (s.getReg .x2 - 632) := by
    rw [a712]; exact (m₁ _).trans (m₂ _).symm
  have hpc₂ : (t₂.pc = 0x80007480 ∧ vecLen t₂ (s.getReg .x2 - 632) ≠
      vecCap t₂ (s.getReg .x2 - 632)) ∨ (t₂.pc = 0x80007bf4 ∧
      vecLen t₂ (s.getReg .x2 - 632) = vecCap t₂ (s.getReg .x2 - 632)) := by
    by_cases he : vecLen t₂ (s.getReg .x2 - 632) = vecCap t₂ (s.getReg .x2 - 632)
    · exact Or.inr ⟨b80007bbc_pc_not_taken h₂ (by rw [hlen, hcap]; exact he), he⟩
    · exact Or.inl ⟨b80007bbc_pc_taken h₂ (by rw [hlen, hcap]; exact he), he⟩
  obtain ⟨q, hrq, hd | ⟨pcq, Q⟩⟩ := toPush hG hpre hsz C₂ M₂.mat.mono M₂.totals hpc₂
  · exact ⟨q, hr₁.trans (hr₂.trans hrq), Or.inl hd⟩
  -- the total
  have x22₂ : t₂.getReg .x22 = BitVec.ofNat 64 i :=
    (kk .x22 (by decide)).trans ((k₁ .x22 (by decide)).trans T.x22)
  have e320 : t₁.getReg .x2 + 1024 = s.getReg .x2 - 320 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e312 : t₁.getReg .x2 + 1032 = s.getReg .x2 - 320 + 8 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e304 : t₁.getReg .x2 + 1040 = s.getReg .x2 - 320 + 16 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have eT : t₁.getMem (t₁.getReg .x2 + 64) + (t₁.getMem (t₁.getReg .x2 + 160) +
      t₁.getMem (t₁.getReg .x2 + 168)) =
      vecPtr z (s.getReg .x2 - 176) + BitVec.ofNat 64 (24 * i) := by
    have b64 : t₁.getReg .x2 + 64 = s.getReg .x2 - 1280 := by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    have b160 : t₁.getReg .x2 + 160 = s.getReg .x2 - 1184 := by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    have b168 : t₁.getReg .x2 + 168 = s.getReg .x2 - 1176 := by
      rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [b64, b160, b168, a64, a160, a168, h24]
  have htot : eOf3 ((((t₂.getReg .x17 ^^^ t₂.getReg .x19) ^^^ t₂.getReg .x28) ^^^
      t₂.getReg .x24) ^^^ 1)
      (((t₂.getReg .x23 ^^^ t₂.getReg .x16) ^^^ t₂.getReg .x8) ^^^ t₂.getReg .x26)
      (((t₂.getReg .x18 ^^^ t₂.getReg .x15) ^^^ t₂.getReg .x30) ^^^ t₂.getReg .x27) =
      sideTot sd state.point state.values i
        (blkFold state.point i sd acc.1 (min sd.2.1.tables.length sd.1.length)).2 := by
    simp only [sideTot]
    rw [total_eq, ← T.acc, ← sum₁, ← T.ex.known, ← tv, eAt_eq_eOf3 t, eAt_eq_eOf3 t₁]
    rw [kk .x17 (by decide), kk .x16 (by decide), kk .x15 (by decide), kk .x19 (by decide),
      kk .x23 (by decide), kk .x18 (by decide), k₁ .x17 (by decide), k₁ .x16 (by decide),
      k₁ .x15 (by decide), b80007bbc_x28 h₂, b80007bbc_x8 h₂, b80007bbc_x30 h₂,
      b80007bbc_x24 h₂, b80007bbc_x26 h₂, b80007bbc_x27 h₂, e320, e312, e304, eT]
    simp only [m₁]
  obtain ⟨h', hr', Ch, Mh, below, forms, totals, tbuf, x25, x27, hpc'⟩ :=
    pushTot hpre hsz M₂ Q pcq x21₂ x22₂ hi htot
  have hq1256 : q.getMem (s.getReg .x2 - BitVec.ofNat 64 1256) =
      h.getMem (s.getReg .x2 - BitVec.ofNat 64 1256) :=
    Q.cur.slot hpre (by omega) (by omega) fun y hy hy' ↦ by
      simp only [SlotW] at hy'
      rcases hy' with hy' | hy' | hy' | hy' | hy' | hy' | hy' <;> addr_omega [hy, hy', hb1]
  have W := headWords hpre C Sd
  refine ⟨h', hr₁.trans (hr₂.trans (hrq.trans hr')), Or.inr ⟨⟨Ch.inv,
    (Sd.step.trans Ch.step).weaken fun a ha ↦ ha.elim id (SideW.loopW Ch.inv.heap), Mh, below,
    forms, totals, ?_, ?_, tbuf⟩, hpc'⟩⟩
  · rw [x25, kk .x25 (by decide), k₁ .x25 (by decide), T.ex.x25]; exact Sd.x25
  · rw [x27]; exact (hq1256.trans W.2.2.2).trans Sd.x27

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
