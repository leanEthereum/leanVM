module

public import NativeRustcVmArm.Bus.AccumulateSide.LoopKit

/-!
# `accumulate_side`: the table and form for `add_scaled`
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- The owner's form after one turn. -/
theorem slot_next (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) :
    slotOf (sta SL m0 (BA L rows bl) Fm (j + 1)).1 (blk (BA L rows bl) j).owner m0.regs.X2.toNat =
      (slotOf (sta SL m0 (BA L rows bl) Fm j).1 (blk (BA L rows bl) j).owner m0.regs.X2.toNat).addScaled
        (gf m0 (BA L rows bl) j) (tsl SL m0 j) := by
  have ho : (blk (BA L rows bl) j).owner < 6 := by
    rw [blk_eq hj]
    exact (h.bown bl[j] (List.getElem_mem hj)).1
  obtain ⟨hs, hr⟩ := sta_shape h j
  have ho' : (blk (BA L rows bl) j).owner < (sta SL m0 (BA L rows bl) Fm j).1.size := by omega
  have hrow : ((sta SL m0 (BA L rows bl) Fm j).1.getD (blk (BA L rows bl) j).owner #[]).size = 3 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ho', Option.getD_some]
    exact hr _ ho'
  change slotOf (stAt Fm m0.regs.X2.toNat (BA L rows bl) SL (wA m0) (betaA m0) (ptA m0) (j + 1)).1 _ _ = _
  rw [stAt_succ]
  change slotOf ((sta SL m0 (BA L rows bl) Fm j).1.modify (blk (BA L rows bl) j).owner
    fun row ↦ row.modify m0.regs.X2.toNat fun f ↦ f.addScaled (gf m0 (BA L rows bl) j) (tsl SL m0 j)) _ _ = _
  rw [slotOf_modify, ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl, ho', by rw [hrow]; exact h.side⟩)]

/-- The form update fits because the final accumulated forms fit. -/
theorem add_scaled_fits (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) :
    ((slotOf (sta SL m0 (BA L rows bl) Fm j).1 (blk (BA L rows bl) j).owner m0.regs.X2.toNat).addScaled
      (gf m0 (BA L rows bl) j) (tsl SL m0 j)).size ≤ formCap := by
  rw [← slot_next h hj]
  refine slot_fits h (by omega) ?_ h.side
  rw [blk_eq hj]
  exact (h.bown bl[j] (List.getElem_mem hj)).1

/-- `TABLES` is a readable region apart from this call's frame. -/
theorem tables_ok (h : Pre L rows bl Fm SL m0) :
    ROk m0 0 (NativeRustcVmArm.rodataAddr .tables, 240) := by
  have hi := (ro_ok h .tables).1
  have hn : (NativeRustcVm.Data.Item.bytes .tables).length = 240 := by
    rw [NativeRustcVmArm.Tables.TableTerms.tables_bytes,
      NativeRustcVm.Transcript.length_flatMap_wordBytes, NativeRustcVmArm.Tables.TableTerms.tablesWords_length]
  rw [hn] at hi
  exact ⟨by change 0 < 240; decide, hi.1, hi.2, by omega⟩

/-- A table word read through the second symbolic region. -/
theorem table_load (h : Pre L rows bl Fm SL m0) {m : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) m) {o c : Nat} (ho : o < 6) (hc : c < 5) :
    (Sym.load 1 (40 * o + 8 * c) 8).eval
      (Env.ofMachine m [(base m0 F, F + 0), (NativeRustcVmArm.rodataAddr .tables, 240)]) =
      (NativeRustcVmArm.Tables.TableTerms.tablesWords.getD (5 * o + c) 0).toBitVec := by
  rw [load_rk rfl]
  have he : 40 * o + 8 * c = 8 * (5 * o + c) := by omega
  rw [word_in h hfr (ro_ok h .tables).1 (ro_ok h .tables).2 (by
    rw [NativeRustcVmArm.Tables.TableTerms.tables_bytes,
      NativeRustcVm.Transcript.length_flatMap_wordBytes, NativeRustcVmArm.Tables.TableTerms.tablesWords_length]
    omega), he]
  have hb := (h.rodata .tables).1
  rw [NativeRustcVmArm.Tables.TableTerms.tables_bytes] at hb
  have hw : NativeRustcVm.WordsAt m0.dmem (NativeRustcVmArm.rodataAddr .tables)
      NativeRustcVmArm.Tables.TableTerms.tablesWords := hb
  have hi : 5 * o + c < NativeRustcVmArm.Tables.TableTerms.tablesWords.length := by
    rw [NativeRustcVmArm.Tables.TableTerms.tablesWords_length]
    omega
  rw [NativeRustcVm.wordOf_of_wordAt (hw.getElem hi), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

/-- The bounded owner and table label at `b31`. -/
theorem matchT (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) {m : MachineData}
    (hst : St m0 (TT SL m0 L rows bl Fm j) L31 m) :
    Match (Env.ofMachine m [(base m0 F, F + 0), (NativeRustcVmArm.rodataAddr .tables, 240)]) sT m := by
  have hh := St.lift (D := L31) hst (by decide) 0 [(NativeRustcVmArm.rodataAddr .tables, 240)]
  refine match_ofMachine (sregions := [(F + 0, true), (240, false)])
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, rfl, nofun, trivial⟩
    (sp_eval hst.fr.sp _ _) trivial ⟨rfl, trivial⟩ ⟨?_, trivial⟩ trivial
  dsimp only
  rw [Holds.evc hh (s := .reg .X20) (i := 96) (by decide)]
  change (blk (BA L rows bl) j).owner.toUInt64.toNat < 6
  rw [blk_eq hj]
  change bl[j].owner.toUInt64.toNat < 6
  have hb := (h.bown bl[j] (List.getElem_mem hj)).1
  change bl[j].owner < 6 at hb
  rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
  exact hb

/-- The selected form's complete buffer is inside the forms allocation. -/
theorem slot_ok (h : Pre L rows bl Fm SL m0) {o : Nat} (ho : o < 6) :
    InOk m0 (m0.regs.X1.toBitVec + BitVec.ofNat 64 (formBufBytes * (3 * o + m0.regs.X2.toNat)))
      formBufBytes N := by
  have hs := h.side
  exact InOk.sub h.formsOk (by change 5928 * (3 * o + m0.regs.X2.toNat) + 5928 ≤ 106704; omega)
    (by decide)

/-- A byte written to the selected form is in the accumulator's output footprint. -/
theorem slot_out (h : Pre L rows bl Fm SL m0) {o : Nat} (ho : o < 6) {q : BitVec 64}
    (hq : InRange (m0.regs.X1.toBitVec + BitVec.ofNat 64 (formBufBytes * (3 * o + m0.regs.X2.toNat)))
      formBufBytes q) : outs m0 q := by
  have hs := h.side
  have hn := h.formsOk.1.2
  change m0.regs.X1.toBitVec.toNat + 106704 ≤ 2 ^ 64 at hn
  rw [Sym.inRange_iff (slot_ok h ho).1.2,
    NativeRustcVm.toNat_add_ofNat (by change m0.regs.X1.toBitVec.toNat +
      5928 * (3 * o + m0.regs.X2.toNat) < 2 ^ 64; omega)] at hq
  change InRange m0.regs.X1.toBitVec formsBytes q
  rw [Sym.inRange_iff h.formsOk.1.2]
  change m0.regs.X1.toBitVec.toNat ≤ q.toNat ∧ q.toNat < m0.regs.X1.toBitVec.toNat + 106704
  change m0.regs.X1.toBitVec.toNat + 5928 * (3 * o + m0.regs.X2.toNat) ≤ q.toNat ∧
    q.toNat < m0.regs.X1.toBitVec.toNat + 5928 * (3 * o + m0.regs.X2.toNat) + 5928 at hq
  omega

end

end NativeRustcVmArm.Bus.AccumulateSide
