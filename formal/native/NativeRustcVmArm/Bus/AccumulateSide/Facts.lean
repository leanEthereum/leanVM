module

public import NativeRustcVmArm.Bus.AccumulateSide.Calls

/-!
# `accumulate_side`: the inputs' words

An input's word in a state of the body is the entry's (`word_in`). The entry's words: the
framework's count and placements (`fw_word`, `fw_p`), the table blocks' placements (`tb_p`), the
fingerprints (`fp_c0`, `fp_c1`), the blocks (`bl_owner`, `bl_tuple`), the layout's heights and
rows (`ht_word`, `rw_word`), `TABLES` (`tab_word`). The table's values below `30` are the entry's
arguments (`T_sv`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm (wordOf)
open LeanVM.Protocol.Verifier (Placement)

public section

theorem addr_eq (a : BitVec 64) {x y : Nat} (h : x = y) :
    a + BitVec.ofNat 64 x = a + BitVec.ofNat 64 y := by rw [h]

theorem T_sv [Labels] (SL : BusLayoutW) (m0 : MachineData) (B : Array BusBlockW)
    (Fm : Array (Array FormW)) (j : Nat) {i : Nat} (hi : i < 30) :
    T SL m0 B Fm j i = sv m0 i := by
  simp only [T, T0, hi, ite_true, show ¬190 ≤ i by omega, ite_false]

variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- **An input's word** in a state of the body is the entry's. -/
theorem word_in (h : Pre L rows bl Fm SL m0) {st : MachineData}
    (hfr : Fr m0 F N slots keep (outs m0) st) {a : BitVec 64} {n o : Nat}
    (hok : InOk m0 a n N) (hap : Apart a n m0.regs.X1.toBitVec formsBytes) (ho : o + 8 ≤ n) :
    wordOf st.dmem (a + BitVec.ofNat 64 o) = wordOf m0.dmem (a + BitVec.ofNat 64 o) :=
  NativeRustcVm.wordOf_congr fun i hi ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact Bus.Fr.bytes_eq hfr h.stack hok.1.2 hok.2
      (fun j hj ↦ NativeRustcVm.Apart.not_inRange_add hap hok.1.2 h.formsOk.1.2 hj) _
      (by omega)

/-- A read-only item: readable, apart from the stack and the forms. -/
theorem ro_ok (h : Pre L rows bl Fm SL m0) (t : NativeRustcVm.Data.Item) :
    InOk m0 (NativeRustcVmArm.rodataAddr t) t.bytes.length N ∧
      Apart (NativeRustcVmArm.rodataAddr t) t.bytes.length m0.regs.X1.toBitVec formsBytes :=
  ⟨⟨⟨(h.rodata t).1.mapped, (h.rodata t).2.1⟩, (h.rodata t).2.2⟩,
    NativeRustcVm.Apart.symm (h.formsRo t)⟩

/-! ## The side layout -/

theorem fw_word (h : Pre L rows bl Fm SL m0) :
    wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8) = SL.framework.size.toUInt64 :=
  NativeRustcVm.wordOf_of_wordAt h.sl.framework.2.1

theorem fw_le (h : Pre L rows bl Fm SL m0) : SL.framework.size ≤ 3 := h.sl.framework.1

theorem sv17 (h : Pre L rows bl Fm SL m0) : (sv m0 17).toNat = SL.framework.size := by
  show (wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8)).toNat = _
  rw [fw_word h, Nat.toUInt64,
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (fw_le h) (by decide))]

theorem sv19 (h : Pre L rows bl Fm SL m0) : (sv m0 19).toNat = cK SL m0 := by
  show (if (stackArg m0 0).toNat <
      (wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8)).toNat
      then stackArg m0 0 else wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8)).toNat = _
  have e := sv17 h
  change (wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 8)).toNat = _ at e
  unfold cK nA
  split <;> omega

/-- Framework placement `i`'s words. -/
theorem fw_p (h : Pre L rows bl Fm SL m0) {i : Nat} (hi : i < SL.framework.size) :
    SL.framework[i].variableCount < 2 ^ 64 ∧ SL.framework[i].index < 2 ^ 64 ∧
      wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 (16 + 16 * i)) =
        SL.framework[i].variableCount.toUInt64 ∧
      wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 (24 + 16 * i)) =
        SL.framework[i].index.toUInt64 := by
  obtain ⟨h1, h2, h3, h4⟩ := h.sl.framework.2.2 i hi
  simp only [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] at h3 h4
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [addr_eq _ (show 16 + 16 * i = 8 + (8 + NativeRustcVm.Bus.placementBytes * i) by
      unfold NativeRustcVm.Bus.placementBytes; omega)]
    exact NativeRustcVm.wordOf_of_wordAt h3
  · rw [addr_eq _ (show 24 + 16 * i = 8 + (8 + NativeRustcVm.Bus.placementBytes * i + 8) by
      unfold NativeRustcVm.Bus.placementBytes; omega)]
    exact NativeRustcVm.wordOf_of_wordAt h4

/-- The table blocks' count. -/
theorem tb_word (h : Pre L rows bl Fm SL m0) :
    wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 64) = bl.length.toUInt64 := by
  rw [← h.sl_size]
  exact NativeRustcVm.wordOf_of_wordAt h.sl.tables.2.1

/-- Table placement `j`'s words. -/
theorem tb_p (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < SL.tables.size) :
    SL.tables[j].variableCount < 2 ^ 64 ∧ SL.tables[j].index < 2 ^ 64 ∧
      wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 (72 + 16 * j)) =
        SL.tables[j].variableCount.toUInt64 ∧
      wordOf m0.dmem (m0.regs.X6.toBitVec + BitVec.ofNat 64 (80 + 16 * j)) =
        SL.tables[j].index.toUInt64 := by
  obtain ⟨h1, h2, h3, h4⟩ := h.sl.tables.2.2 j hj
  simp only [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] at h3 h4
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [addr_eq _ (show 72 + 16 * j = 64 + (8 + NativeRustcVm.Bus.placementBytes * j) by
      unfold NativeRustcVm.Bus.placementBytes; omega)]
    exact NativeRustcVm.wordOf_of_wordAt h3
  · rw [addr_eq _ (show 80 + 16 * j = 64 + (8 + NativeRustcVm.Bus.placementBytes * j + 8) by
      unfold NativeRustcVm.Bus.placementBytes; omega)]
    exact NativeRustcVm.wordOf_of_wordAt h4

/-! ## The fingerprints -/

omit [Labels] in
theorem fp_c0 {i : Nat} (hi : i < nA m0) :
    wordOf m0.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i)) = (fpv m0 i).c0 := by
  simp [fpv, fpsA, NativeRustcVm.ewsOf, Array.getD_eq_getD_getElem?, hi, NativeRustcVm.ewOf]

omit [Labels] in
theorem fp_c1 {i : Nat} (hi : i < nA m0) :
    wordOf m0.dmem (m0.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i + 8)) = (fpv m0 i).c1 := by
  simp [fpv, fpsA, NativeRustcVm.ewsOf, Array.getD_eq_getD_getElem?, hi, NativeRustcVm.ewOf,
    ← NativeRustcVm.addr_add_add]

/-! ## The blocks -/

theorem bl_words (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) :
    wordOf m0.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j)) = bl[j].owner.toUInt64 ∧
      wordOf m0.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j + 8)) =
        bl[j].tuple.toUInt64 := by
  have hb := NativeRustcVm.BytesAt.flatMap_getElem (f := NativeRustcVm.Data.Block.bytes) (k := 16)
    (fun x ↦ by simp [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes,
      NativeRustcVm.length_wordBytes]) h.blocks hj
  rw [NativeRustcVm.Data.Block.bytes, NativeRustcVm.bytesAt_append] at hb
  obtain ⟨h1, h2⟩ := hb
  rw [show (NativeRustcVm.Data.natBytes bl[j].owner).length = 8 by
    simp [NativeRustcVm.Data.natBytes, NativeRustcVm.length_wordBytes],
    NativeRustcVm.addr_add_add] at h2
  exact ⟨NativeRustcVm.wordOf_of_wordAt h1, NativeRustcVm.wordOf_of_wordAt h2⟩

/-! ## The layout -/

theorem ht_word (h : Pre L rows bl Fm SL m0) {o : Nat} (ho : o < nTables) :
    wordOf m0.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 (24 + 8 * o)) =
      (L.tableLogHeights.getD o 0).toUInt64 := by
  have hs := h.lay.heights_size
  have hw := NativeRustcVm.WordsAt.getElem h.lay.heights
    (i := o) (by simp [hs]; exact ho)
  simp only [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] at hw
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  simp [Array.getD_eq_getD_getElem?, show o < L.tableLogHeights.size by omega]

theorem ht_le (h : Pre L rows bl Fm SL m0) (o : Nat) : L.tableLogHeights.getD o 0 ≤ 30 := by
  rw [Array.getD_eq_getD_getElem?]
  cases hx : L.tableLogHeights[o]? with
  | none => simp
  | some x => exact h.lay.heights_le x (Array.mem_of_getElem? hx)

theorem rw_word (h : Pre L rows bl Fm SL m0) {o : Nat} (ho : o < nTables) :
    wordOf m0.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 (72 + 8 * o)) =
      (rows.getD o 0).toUInt64 := by
  have hs := h.rows_size
  have hw := NativeRustcVm.WordsAt.getElem h.rowsW (i := o) (by simp [hs]; exact ho)
  simp only [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] at hw
  rw [NativeRustcVm.wordOf_of_wordAt hw]
  simp [Array.getD_eq_getD_getElem?, show o < rows.size by omega]

/-! ## `TABLES` -/

theorem tab_word (h : Pre L rows bl Fm SL m0) {i : Nat} (hi : i < 30) :
    wordOf m0.dmem (NativeRustcVmArm.rodataAddr .tables + BitVec.ofNat 64 (8 * i)) =
      NativeRustcVmArm.Tables.TableTerms.tablesWords.getD i 0 := by
  have hb := (h.rodata .tables).1
  rw [NativeRustcVmArm.Tables.TableTerms.tables_bytes] at hb
  have hl : i < NativeRustcVmArm.Tables.TableTerms.tablesWords.length := by
    rw [NativeRustcVmArm.Tables.TableTerms.tablesWords_length]; exact hi
  have hw := NativeRustcVm.WordsAt.getElem (ws := NativeRustcVmArm.Tables.TableTerms.tablesWords)
    hb (i := i) hl
  rw [NativeRustcVm.wordOf_of_wordAt hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

end

end NativeRustcVmArm.Bus.AccumulateSide
