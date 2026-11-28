module

public import NativeRustcVmX64.Bus.AccumulateSide.Zero
public import NativeRustcVmX64.Bus.AccumulateSide.FactsT

/-!
# `accumulate_side`: what the table loop's turn needs (x86-64)

Memory: the forms and the frame's `FormBuf` kept by a block writing the frame below its offset
`6056` (`forms_run`, `fbuf_run`) and by a callee changing its stack, a part of the frame below
`6056` and outputs apart from the frame (`forms_call`, `fbuf_call`). The data: block `j`'s words
(`block_words`), `TABLES`' and `PADDING`'s (`tables_word`, `padding_slice`), `padding_weight`
of the rows modulo `2 ^ 64` (`paddingWeight_mod64`). The model: block `j` (`BA_getD`), its form
(`blockForm_coords`), the forms' shape and fit (`sta_shape`, `slot_fits`).
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-! ## The model -/

theorem blockForm_coords {b b' : BusBlockW} (h : b.coordinates = b'.coordinates) (w : Array EW)
    (beta : EW) : blockForm b w beta = blockForm b' w beta := by
  unfold blockForm; rw [h]

theorem BA_size (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) :
    (BA L rows bl).size = bl.length := by simp [BA]

theorem BA_getD (L : LayoutW) (rows : Array Nat) (bl : List NativeRustcVm.Data.Block) {j : Nat}
    (hj : j < bl.length) :
    (BA L rows bl).getD j default = blockW L.tableLogHeights rows (bl[j]'hj) := by
  simp [BA, Array.getD_eq_getD_getElem?, hj]

theorem slotOf_eq {G : Array (Array FormW)} {o s : Nat} (ho : o < G.size) (hs : s < G[o].size) :
    slotOf G o s = G[o][s] := by
  simp [slotOf, Array.getD_eq_getD_getElem?, ho, hs]

private theorem lowBit_mod64 (n k : Nat) (hk : k < 64) :
    ((n % 2 ^ 64) >>> k) % 2 = (n >>> k) % 2 := by
  have hd : 2 ^ k * 2 ∣ 2 ^ 64 := by
    rw [← Nat.pow_succ]
    exact Nat.pow_dvd_pow 2 (by omega)
  simp only [Nat.shiftRight_eq_div_pow]
  rw [← Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd n hd, Nat.mod_mul_right_div_self]

/-- `paddingWeight` reads only the low 64 bits when the point has fewer than 64 coordinates. -/
theorem paddingWeight_mod64 (point : Array EW) (n : Nat) (hp : point.size < 64) :
    paddingWeight point (n % 2 ^ 64) = paddingWeight point n := by
  have fold_eq (xs : List (EW × Nat)) (hx : ∀ x ∈ xs, x.2 < 64) (acc : EW) :
      xs.foldl (fun pad (r, k) ↦
        let b := EW.ofNat (((n % 2 ^ 64) >>> k) % 2)
        (1 + b) * r + (1 + b + r) * pad) acc =
      xs.foldl (fun pad (r, k) ↦
        let b := EW.ofNat ((n >>> k) % 2)
        (1 + b) * r + (1 + b + r) * pad) acc := by
    induction xs generalizing acc with
    | nil => rfl
    | cons x xs ih =>
      rcases x with ⟨r, k⟩
      simp only [List.foldl_cons]
      rw [lowBit_mod64 n k (hx (r, k) (List.mem_cons_self))]
      exact ih (fun x hx' ↦ hx x (List.mem_cons_of_mem _ hx')) _
  unfold paddingWeight
  rw [lowBit_mod64 n point.size hp]
  congr 1
  simp only [← Array.foldl_toList]
  apply fold_eq
  intro x hx
  have hm : x ∈ point.zipIdx := Array.mem_toList_iff.mp hx
  have hb := Array.mem_zipIdx hm
  omega

section
variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

theorem fm_shape (h : Pre L rows bl Fm SL m0) : Fm.size = 6 ∧ ∀ o (ho : o < Fm.size),
    Fm[o].size = 3 :=
  ⟨h.forms.size, h.forms.row_size⟩

theorem sta_shape (h : Pre L rows bl Fm SL m0) (j : Nat) :
    (stA L rows bl Fm SL m0 j).1.size = 6 ∧ ∀ o (ho : o < (stA L rows bl Fm SL m0 j).1.size),
      (stA L rows bl Fm SL m0 j).1[o].size = 3 := by
  obtain ⟨h1, h2⟩ := stAt_size Fm (reg m0 .rdx).toNat (BA L rows bl) SL (wA m0) (betaA m0)
    (ptA m0) j
  obtain ⟨s1, s2⟩ := fm_shape h
  refine ⟨h1.trans s1, fun o ho ↦ ?_⟩
  rw [h2 o (by rw [h1] at ho; exact ho) ho]
  exact s2 o (by rw [h1] at ho; exact ho)

/-- **The owner's form of the side fits** after any turn. -/
theorem slot_fits (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j ≤ bl.length) {o s : Nat}
    (ho : o < 6) (hs : s < 3) :
    (slotOf (stA L rows bl Fm SL m0 j).1 o s).size ≤ formCap := by
  have hjk : j ≤ (BA L rows bl).size := by rw [BA_size]; exact hj
  have hmono := slot_size_mono Fm (reg m0 .rdx).toNat (BA L rows bl) SL (wA m0) (betaA m0)
    (ptA m0) o s (j := j) (k := (BA L rows bl).size) hjk
  refine Nat.le_trans hmono ?_
  obtain ⟨g1, g2⟩ := sta_shape h (BA L rows bl).size
  have ho' : o < (stA L rows bl Fm SL m0 (BA L rows bl).size).1.size := by rw [g1]; exact ho
  have hs' : s < (stA L rows bl Fm SL m0 (BA L rows bl).size).1[o].size := by
    rw [g2 o ho']; exact hs
  have hfit := h.fits.2
  rw [accumulateSide_eq _ _ _ _ _ _ _ _ _ (by rw [h.sl_size, BA_size])] at hfit
  rw [slotOf_eq ho' hs']
  exact hfit _ (Array.getElem_mem ho') _ (Array.getElem_mem hs')

/-- Block `j`'s form fits. -/
theorem form_fits (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) :
    (blockForm ((BA L rows bl).getD j default) (wA m0) (betaA m0)).size ≤ formCap := by
  refine h.fits.1 _ ?_
  rw [BA_getD L rows bl hj]
  simp [BA]
  exact ⟨bl[j], List.getElem_mem hj, rfl⟩

/-- Block `j`'s words: its owner, its tuple. -/
theorem block_words (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < bl.length) :
    NativeRustcVm.WordAt m0.dmem (off (reg m0 .rcx) (16 * j)) (bl[j].owner).toUInt64 ∧
      NativeRustcVm.WordAt m0.dmem (off (reg m0 .rcx) (16 * j + 8)) (bl[j].tuple).toUInt64 := by
  have hb := NativeRustcVm.BytesAt.flatMap_getElem (k := 16) (fun b ↦ by
    simp [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes,
      NativeRustcVm.length_wordBytes]) h.blocks hj
  unfold NativeRustcVm.Data.Block.bytes NativeRustcVm.Data.natBytes at hb
  refine ⟨hb.left, ?_⟩
  have := hb.right
  rw [NativeRustcVm.length_wordBytes, NativeRustcVm.addr_add_add] at this
  exact this

end

/-! ## `TABLES` and `PADDING` -/

section
variable [Labels]

omit [Labels] in
/-- `TABLES`' bytes. -/
theorem tables_len : (NativeRustcVm.Data.Item.bytes .tables).length = 240 := by
  rw [NativeRustcVmX64.Tables.TableTerms.tables_bytes, NativeRustcVm.Transcript.length_flatMap_wordBytes,
    NativeRustcVmX64.Tables.TableTerms.tablesWords_length]

/-- `TABLES`' word `i`. -/
theorem tables_word {m : MachineData} {n : Nat} (hr : RodataAt m n) {i : Nat} (hi : i < 30) :
    NativeRustcVm.WordAt m.dmem (off (rodataAddr .tables) (8 * i))
      (NativeRustcVmX64.Tables.TableTerms.tablesWords.getD i 0) := by
  have hb := hr.bytesAt .tables
  rw [NativeRustcVmX64.Tables.TableTerms.tables_bytes] at hb
  have := NativeRustcVm.BytesAt.flatMap_getElem (k := 8) NativeRustcVm.length_wordBytes hb
    (i := i) (by rw [NativeRustcVmX64.Tables.TableTerms.tablesWords_length]; exact hi)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
    rw [NativeRustcVmX64.Tables.TableTerms.tablesWords_length]; exact hi), Option.getD_some]
  exact this

/-- The span selected from `TABLES` is a readable padding row. -/
theorem padding_slice {m : MachineData} {s o : Nat} (hr : RodataAt m s) (ho : o < 6)
    {p n : BitVec 64}
    (hp : p = rodataAddr .padding + BitVec.ofNat 64 (16 *
      (NativeRustcVmX64.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toNat))
    (hn : n.toNat = (NativeRustcVmX64.Tables.TableTerms.tablesWords.getD (5 * o + 4) 0).toNat) :
    SliceOk m p n s ∧ slice m p n = (tablesW.getD o default).padding := by
  let start := (NativeRustcVmX64.Tables.TableTerms.tablesWords.getD (5 * o + 3) 0).toNat
  let len := (NativeRustcVmX64.Tables.TableTerms.tablesWords.getD (5 * o + 4) 0).toNat
  obtain ⟨hbound, hdata⟩ := padding_read ho
  change start + len < 154 at hbound
  have hpositive : ∀ o : Fin 6, 0 <
      (NativeRustcVmX64.Tables.TableTerms.tablesWords.getD (5 * o.val + 4) 0).toNat := by
    decide +kernel
  have hpos : 0 < len := hpositive ⟨o, ho⟩
  change (NativeRustcVm.Data.padding.drop start).take len =
    (tablesW.getD o default).padding.toList at hdata
  have hlen : len = (tablesW.getD o default).padding.size := by
    have hlen := congrArg List.length hdata
    simp only [List.length_take, List.length_drop, padding_length, Array.length_toList] at hlen
    omega
  have bytes : NativeRustcVm.Data.Item.padding.bytes.length = 2448 := by decide +kernel
  have hpad : NativeRustcVm.EWsAt m.dmem (rodataAddr .padding) NativeRustcVm.Data.padding :=
    hr.bytesAt .padding
  have hw := (hpad.drop start).take len
  rw [hdata] at hw
  have hsize := hr.noWrap .padding
  rw [bytes] at hsize
  unfold NativeRustcVm.NoWrap at hsize
  have haddr : (rodataAddr .padding + BitVec.ofNat 64 (16 * start)).toNat =
      (rodataAddr .padding).toNat + 16 * start :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  constructor
  · unfold SliceOk
    rw [hp, hn]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hm := hw.mapped
      rw [Array.length_toList, ← hlen] at hm
      exact hm
    · unfold NoWrap
      rw [haddr]
      omega
    · have hap := hr.apart .padding
      rw [bytes] at hap
      unfold OffStack Apart
      unfold NativeRustcVm.Apart at hap
      rw [haddr]
      omega
  · unfold slice
    rw [hp, hn]
    change (NativeRustcVm.ewsOf m.dmem
      (rodataAddr .padding + BitVec.ofNat 64 (16 * start)) len).toArray = _
    rw [hlen, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hw]

end

end

end NativeRustcVmX64.Bus.AccumulateSide
