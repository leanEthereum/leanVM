module

public import NativeRustcVmArm.Bus.BusLayout.Common

/-!
# `bus_layout`: the sizes

From the entry to `.LBusLayout_8` (`sizes_run`): the prologue `b0`, `memset` of the sizes, the
framework's sizes (`b1`-`b4`, `fw_write`), then the blocks' heights (`b5`, the loop `b7`, `b6`:
`LInv`, `loop_step`). Afterwards the sizes' first `n = |framework| + |blocks|` words are
`S` (`SizesAt`).
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- The sizes' first `k` words. -/
def SizesAt (d : Mem 64) (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (k : Nat) : Prop :=
  ∀ j < k, WordAt d (fa m0 (8 + 8 * j)) ((S L bl m0).getD j 0).toUInt64

/-- The registers `b0` sets for the whole function. -/
structure Regs (m0 st : MachineData) : Prop where
  x19 : st.regs.getXReg .X19 = m0.regs.X0
  x20 : st.regs.getXReg .X20 = m0.regs.X2
  x24 : st.regs.getXReg .X24 = m0.regs.X5
  x25 : st.regs.getXReg .X25 = m0.regs.X1
  x26 : (st.regs.getXReg .X26).toBitVec = fa m0 8

theorem Regs.keep {m0 st st' : MachineData} (h : Regs m0 st)
    (hk : Bus.KeepRegs [.X19, .X20, .X24, .X25, .X26] st st') : Regs m0 st' :=
  ⟨(hk .X19 (by simp)).trans h.x19, (hk .X20 (by simp)).trans h.x20,
    (hk .X24 (by simp)).trans h.x24, (hk .X25 (by simp)).trans h.x25,
    by rw [hk .X26 (by simp)]; exact h.x26⟩

theorem S_getD_fw {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData} {j : Nat}
    (hj : j < nf m0) :
    (S L bl m0).getD j 0 = (wordOf m0.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * j))).toNat := by
  simp only [S, szs, List.getD_eq_getElem?_getD, List.getElem?_append_left
    (show j < (fws m0).toList.length by simpa [fws_size] using hj)]
  simp only [fws, natsOf, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by rw [NativeRustcVm.length_wordsOf]; exact hj)]
  simp

theorem S_getD_bl {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData} {i : Nat}
    (hi : i < bl.length) :
    (S L bl m0).getD (nf m0 + i) 0 = L.tableLogHeights.getD bl[i].owner 0 := by
  simp only [S, szs, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [fws_size])]
  simp [fws_size, List.getElem?_eq_getElem hi]

/-- The loop's head `.LBusLayout_6`, `i` blocks' heights written. -/
structure LInv (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (i : Nat)
    (st : MachineData) : Prop where
  fr : Frm m0 st
  regs : Regs m0 st
  lt : i < bl.length
  sizes : SizesAt st.dmem L bl m0 (nf m0 + i)
  x21 : (st.regs.getXReg .X21).toNat = nf m0 + bl.length
  x22 : (st.regs.getXReg .X22).toNat = bl.length - i
  x23 : (st.regs.getXReg .X23).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i)
  x8 : (st.regs.getXReg .X8).toNat = 8 * (nf m0 + i)
  x9 : (st.regs.getXReg .X9).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 24

theorem frame_wf {m0 st : MachineData} {N : Nat} (hS : StackOk m0 N) (hF : 1840 ≤ N)
    (hk : Kept m0.dmem st.dmem) : (Env.ofMachine st [(fb m0, 1840)]).WF :=
  Bus.wf_frame hS hF hk

variable [Host] {k : Nat}

/-- Where the sizes are done: `.LBusLayout_8`. -/
abbrev Done (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (k : Nat)
    (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b9Offset) ∧ Frm m0 st.data ∧ Regs m0 st.data ∧
    (st.data.regs.getXReg .X21).toNat = nf m0 + bl.length ∧
    SizesAt st.data.dmem L bl m0 (nf m0 + bl.length)



/-- A framework size written by `b2`, `b3` or `b4`: the frame, the sizes. -/
theorem fw_write {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 st st' : MachineData} {j : Nat}
    (hpre : BusLayoutPre L bl m0) (hfr : Frm m0 st) (hsz : SizesAt st.dmem L bl m0 j)
    (hj : j < nf m0) {S S' : SState}
    (hm : Match (Env.ofMachine st [(fb m0, 1840), (m0.regs.X1.toBitVec, 8 * (j + 1))]) S st)
    (hm' : Match (Env.ofMachine st [(fb m0, 1840), (m0.regs.X1.toBitVec, 8 * (j + 1))]) S' st')
    (hwf : (Env.ofMachine st [(fb m0, 1840), (m0.regs.X1.toBitVec, 8 * (j + 1))]).WF)
    (hsp : S.sp = .ptr 0 0) (hsp' : S'.sp = .ptr 0 0)
    (hkeep : ∀ r ∈ keep, ∃ v, S.reg r = some v ∧ S'.reg r = some v)
    (hw : ∀ t < 8, findWrite 0 (8 + 8 * j + t) S'.mem = some (.load 1 (8 * j) 8, t))
    (hall : (S'.mem.all fun w ↦ w.r == 0 && decide (8 + 8 * j ≤ w.off) &&
      decide (w.off + w.n ≤ 16 + 8 * j)) = true) :
    Frm m0 st' ∧ SizesAt st'.dmem L bl m0 (j + 1) := by
  obtain ⟨hS, hnf, -, hF, -, -, -, -, -, -, -, -, hO, hOF, -⟩ := hpre
  have hnfe : nf m0 = m0.regs.X2.toNat := rfl
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF1 : 1840 ≤ busLayoutStack := by decide
  have hj3 : j < 3 := by have : nf m0 ≤ 3 := hnf; omega
  have hb := base_toNat (m0 := m0) (F := 1840) (by omega)
  have hlt := m0.regs.SP.toNat_lt
  have hfb : (fb m0).toNat + 1840 ≤ 2 ^ 64 := by rw [hb]; omega
  have hW : ∀ w ∈ S'.mem, w.r = 0 ∧ 8 + 8 * j ≤ w.off ∧ w.off + w.n ≤ 16 + 8 * j := fun w hw' ↦ by
    have := List.all_eq_true.mp hall w hw'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hfr' : Frm m0 st' := by
    refine Fr.ofBlockW hfr hm hm' hwf rfl (hsp'.trans hsp.symm) hkeep rfl hF1 hN slots_le
      fun w hw' ↦ .inl ⟨(hW w hw').1, by have := hW w hw'; omega, fun p hp ↦ ?_⟩
    have := hW w hw'
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (left; simp; omega)
  have hsame := same_of_writes_in hm' hwf (r := 0) rfl hfb (lo := 8 + 8 * j) (hi := 16 + 8 * j)
    (by omega) (by omega) (by
      refine List.all_eq_true.mpr fun w hw' ↦ ?_
      obtain ⟨h1, h2, h3⟩ := hW w hw'
      simp [h1, h2, h3])
  refine ⟨hfr', fun j' hj' ↦ ?_⟩
  by_cases hjj : j' = j
  · subst hjj
    have h := Bus.wordAt_write hm' (r := 0) (o := 8 + 8 * j') rfl (by omega) hw
    rw [Bus.load_r1] at h
    rw [S_getD_fw hj]
    have hfw : wordOf st.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * j')) =
        wordOf m0.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * j')) := by
      apply NativeRustcVm.wordOf_congr
      intro i hi
      rw [NativeRustcVm.addr_add_add]
      exact Bus.Fr.bytes_eq hfr hS hF.1.2 hF.2 (fun i' hi' h ↦
        (NativeRustcVm.Apart.symm hOF).not_inRange_add hF.1.2 hO.1.2 hi' h) _
        (by have : nf m0 ≤ 3 := hnf; omega)
    rw [hfw] at h
    simpa [UInt64.ofNat_toNat] using h
  · have hold := hsz j' (by omega)
    exact wordAt_keep_out (sz := 1840) hfb hsame (by omega) (by omega) (by omega) (by omega)
      (by simpa using hold)

omit [Host] in
/-- Block `i`'s owner, read in the frame. -/
theorem owner_word {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 st : MachineData}
    (hpre : BusLayoutPre L bl m0) (hfr : Frm m0 st) {i : Nat} (hi : i < bl.length) :
    wordOf st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i)) = bl[i].owner.toUInt64 := by
  obtain ⟨hS, -, -, -, -, -, -, -, hB, hBok, -, -, hO, -, hOB, -⟩ := hpre
  have hb := hB.flatMap_getElem (k := 16)
    (fun x ↦ by simp [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes,
      NativeRustcVm.length_wordBytes]) hi
  simp only [NativeRustcVm.Data.Block.bytes, NativeRustcVm.Data.natBytes] at hb
  rw [← NativeRustcVm.wordOf_of_wordAt hb.left]
  apply NativeRustcVm.wordOf_congr
  intro t ht
  rw [NativeRustcVm.addr_add_add]
  exact Bus.Fr.bytes_eq hfr hS hBok.1.2 hBok.2
    (fun j hj h ↦ (NativeRustcVm.Apart.symm hOB).not_inRange_add hBok.1.2 hO.1.2 hj h) _
    (by omega)

omit [Host] in
/-- Height `o` of the layout, read in the frame. -/
theorem height_word {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 st : MachineData}
    (hpre : BusLayoutPre L bl m0) (hfr : Frm m0 st) {o : Nat} (ho : o < 6) :
    wordOf st.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * o)) =
      (L.tableLogHeights.getD o 0).toUInt64 := by
  obtain ⟨hS, -, -, -, -, -, -, -, -, -, hL, hLok, hO, -, -, hOL⟩ := hpre
  have hsz : L.tableLogHeights.size = 6 := hL.heights_size
  have hw := NativeRustcVm.WordsAt.getElem hL.heights (i := o) (by simp [hsz, ho])
  simp only [List.getElem_map, Array.getElem_toList] at hw
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
    ← NativeRustcVm.wordOf_of_wordAt hw]
  apply NativeRustcVm.wordOf_congr
  intro t ht
  simp only [NativeRustcVm.addr_add_add]
  exact Bus.Fr.bytes_eq hfr hS hLok.1.2 hLok.2
    (fun j hj h ↦ (NativeRustcVm.Apart.symm hOL).not_inRange_add hLok.1.2 hO.1.2 hj h) _
    (by unfold layoutBytes NativeRustcVm.Layout.placementBytes columnCountW; omega)

end

end NativeRustcVmArm.Bus.BusLayout
