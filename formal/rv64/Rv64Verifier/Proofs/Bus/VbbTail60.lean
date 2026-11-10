import Rv64Verifier.Proofs.Bus.VbbTail59

/-!
# `verify_bus_balance`'s side loop: the block loop's count

From `known` (`Dotted`, `0x8000779c`) through `0x800077ac` and `0x800077b0`: the number of blocks the
loop runs, `min(tables, blocks)`, in `s5`, the framework selectors' pointer at `S - 1304`, `8 i` and
`16 i` at `S - 1176` and `S - 1184` (`At3`, `enterHead`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Past `0x800077b0` at `t`, from `Front` at `u`. -/
structure At3 (s z h u t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) : Prop where
  cur : Cur s z h t
  fr : DFrame u t (EW s u t)
  mono : heapNext u ≤ heapNext t
  ex : Ex s h t i sd point
  tb : eListAt t (t.getReg .x20) sd.2.1.tables.length = tbSel sd point
  tbBuf : NewBuf h t (t.getReg .x20) (24 * sd.2.1.tables.length) 8
  x21 : (t.getReg .x21).toNat = min sd.2.1.tables.length sd.1.length
  x22 : t.getReg .x22 = BitVec.ofNat 64 i
  x9 : t.getReg .x9 = sideWord s h i 72
  x18 : t.getReg .x18 = sideWord s h i 80
  x20 : t.getReg .x20 = u.getReg .x20
  x26 : t.getReg .x26 = sideWord s h i 64
  m1176 : t.getMem (s.getReg .x2 - 1176) = BitVec.ofNat 64 (8 * i)
  m1184 : t.getMem (s.getReg .x2 - 1184) = BitVec.ofNat 64 (16 * i)

/-- `0x8000779c` and `0x800077ac`: `s5` is the number of blocks the loop runs. -/
theorem enterMin {s z h u t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    (hpre : BusBalancePre s) (SO : SideOk s z h i sd) (F : Front s z h u i sd point)
    (D : Dotted s z h u t i sd point) (hpc : t.pc = 0x8000779c) :
    ∃ t₂, Reaches Image.code t t₂ ∧ t₂.pc = 0x800077b0 ∧
      (t₂.getReg .x21).toNat = min sd.2.1.tables.length sd.1.length ∧
      t₂.getReg .x22 = BitVec.ofNat 64 i ∧
      (∀ r ∈ ([.x2, .x9, .x18, .x20, .x24, .x25, .x26] : List Reg), t₂.getReg r = t.getReg r) ∧
      ∀ a, t₂.getMem a = t.getMem a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have Ct := D.cur
  have spt : t.getReg .x2 = s.getReg .x2 - 1344 := Ct.inv.sp
  have htE := Ct.inv.heap.hi
  have ut (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h5 : j ≤ 104 ∨ 328 ≤ j) :
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    D.fr _ fun q hq hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hq, hb1, hj, hj2, h5]
      · addr_omega [hw, hq, hb1, hj, hj2]
      · addr_omega [hw, hq, hb1, hj, hj2, hnx]
      · simp only [heapNext, heapEnd] at a2 htE; addr_omega [a2, hq, hb1, hj, hj2, htE]
  have m1296 : t.getMem (s.getReg .x2 - 1296) = BitVec.ofNat 64 sd.2.1.tables.length :=
    (ut 1296 (by omega) (by omega) (by omega)).trans F.m1296
  have m1152 : t.getMem (s.getReg .x2 - 1152) = BitVec.ofNat 64 i :=
    (ut 1152 (by omega) (by omega) (by omega)).trans F.m1152
  have x8 : t.getReg .x8 = vecLen s (blkVec s i) :=
    (D.regs .x8 (by decide)).trans (F.x8.trans SO.blen)
  have hbl : (vecLen s (blkVec s i)).toNat = sd.1.length := by
    rw [← SO.blocks, blocksAt, List.length_map, List.length_range]; rfl
  have htl : sd.2.1.tables.length < 2 ^ 64 := by
    have hb := F.tbBuf
    have hu := F.cur.inv.heap.hi
    simp only [NewBuf, heapNext, heapEnd] at hb hu
    rcases hb.2 with h0 | ⟨-, b2⟩ <;> omega
  have htl' : (BitVec.ofNat 64 sd.2.1.tables.length).toNat = sd.2.1.tables.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl]
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000779c_spec hpc (by
    rv_eval [spt]; and_intros <;> valid_access hval [hb1])
  have k₁ := b8000779c_keeps h₁
  have m₁ := b8000779c_mem_same h₁
  have r48 : t.getMem (t.getReg .x2 + 48) = BitVec.ofNat 64 sd.2.1.tables.length := by
    rw [spt]; rv_eval []; exact m1296
  have x22₁ : t₁.getReg .x22 = BitVec.ofNat 64 i := by
    rw [b8000779c_x22 h₁, spt]; rv_eval []; exact m1152
  by_cases hlt : sd.2.1.tables.length < sd.1.length
  · refine ⟨t₁, hr₁, b8000779c_pc_taken h₁ (by rw [r48, x8, htl', hbl]; exact hlt), ?_, x22₁,
      fun r hr ↦ k₁ r (mem_of_mem hr _), m₁⟩
    rw [b8000779c_x21 h₁, r48, htl']; omega
  · have pc₁ := b8000779c_pc_not_taken h₁ (by rw [r48, x8, htl', hbl]; omega)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800077ac_spec pc₁ trivial
    have k₂ := b800077ac_keeps h₂
    refine ⟨t₂, hr₁.trans hr₂, b800077ac_pc h₂, ?_, (k₂ .x22 (by decide)).trans x22₁,
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)),
      fun a ↦ (b800077ac_mem_same h₂ a).trans (m₁ a)⟩
    rw [b800077ac_x21 h₂, k₁ .x8 (by decide), x8, hbl]; omega

theorem ofNat_mul8 {i : Nat} (hi : i < 3) : BitVec.ofNat 64 i * 8 = BitVec.ofNat 64 (8 * i) := by
  interval_cases i <;> decide

theorem ofNat_mul16 {i : Nat} (hi : i < 3) : BitVec.ofNat 64 i * 16 = BitVec.ofNat 64 (16 * i) := by
  interval_cases i <;> decide

set_option maxRecDepth 8192 in
/-- From `known` past `0x800077b0`. -/
theorem enterHead {s z h u t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (SO : SideOk s z h i sd) (F : Front s z h u i sd point) (D : Dotted s z h u t i sd point)
    (hi : i < 3) (hpc : t.pc = 0x8000779c) :
    ∃ t₃, Reaches Image.code t t₃ ∧ At3 s z h u t₃ i sd point ∧
      ((t₃.getReg .x21 = 0 ∧ t₃.pc = 0x80007b18) ∨ (t₃.getReg .x21 ≠ 0 ∧ t₃.pc = 0x800077c8)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have Ct := D.cur
  have spt : t.getReg .x2 = s.getReg .x2 - 1344 := Ct.inv.sp
  have hut := D.mono
  have hlo := Ih.heap.lo
  have huE := F.cur.inv.heap.hi
  obtain ⟨t₂, hr₂, pc₂, x21₂, x22₂, k₂, m₂⟩ := enterMin hpre SO F D hpc
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1344 := (k₂ .x2 (by decide)).trans spt
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800077b0_spec pc₂ (by
    rv_eval [sp₂]; and_intros <;> valid_access hval [hb1])
  have k₃ := b800077b0_keeps h₃
  have ft : DFrame t t₃ fun a ↦ Within a (s.getReg .x2 - 1304) 8 ∨
      Within a (s.getReg .x2 - 1184) 16 := fun a ha ↦ (h₃.frame a (by
    rv_eval [sp₂]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]
      first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hb1])))).trans (m₂ a)
  have hn₃ : heapNext t₃ = heapNext t := by
    simp only [heapNext]; rw [ft nextAddr fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb1, hnx]]
  have st : StepS s t t₃ fun a ↦ Within a (s.getReg .x2 - 1304) 8 ∨
      Within a (s.getReg .x2 - 1184) 16 :=
    StepS.ofDFrame Ct.inv.heap ft (fun _ h ↦ h) (fun j hj hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hj, hb1, hnx])
      ((k₃ .x2 (by decide)).trans (k₂ .x2 (by decide)))
  have C₃ : Cur s z h t₃ := Ct.next hpre hsz st fun a ha ↦ Or.inl (by
    simp only [SlotW]
    rcases ha with ha | ha
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))
  have fr : DFrame u t₃ (EW s u t₃) :=
    (D.fr.mono fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (by
      rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨a1, by rw [hn₃]; exact a2⟩))))))).trans ft fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  have hu₃ : heapNext u ≤ heapNext t₃ := by rw [hn₃]; exact hut
  have ut (j : Nat) (h1 : 1288 ≤ j) (h2 : j ≤ 1296) :
      t₃.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    fr _ fun q hq hw ↦ by
      have hE := C₃.inv.heap.hi
      rcases hw with hw | hw | hw | hw | hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2, hnx]
      · simp only [heapNext, heapEnd] at a2 hE; addr_omega [a2, hq, hb1, h1, h2, hE]
  have tt (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≠ 1304) (h2 : j ≤ 1168 ∨ 1192 ≤ j)
      (h8 : j % 8 = 0) :
      t₃.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    ft _ fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1, hj, hj2, h1, h2, h8]
  have e1304 : t₃.getMem (s.getReg .x2 - 1304) = u.getReg .x24 := by
    have e := b800077b0_m_x2_40 h₃
    have a : t₂.getReg .x2 + 40 = s.getReg .x2 - 1304 := by
      rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [a] at e
    rw [e, k₂ .x24 (by decide), D.regs .x24 (by decide)]
  have hfb := F.fwBuf
  have hev := F.cur.inv.heap
  have ex : Ex s h t₃ i sd point := by
    refine ⟨?_, ?_, (ut 1288 (by omega) (by omega)).trans F.m1288,
      (ut 1296 (by omega) (by omega)).trans F.m1296, ?_, ?_⟩
    · rw [e1304, DFrame.eListNew fr hfb (le_refl _) hlo huE fun a h1 h2 ↦ EW.low hpre hev h1 h2]
      exact F.fw
    · rw [e1304]; exact ⟨hfb.1, hfb.2.imp_right fun h ↦ ⟨h.1, le_trans h.2 hu₃⟩⟩
    · rw [← D.known]
      have e8 : s.getReg .x2 - 320 + 8 = s.getReg .x2 - BitVec.ofNat 64 312 :=
        slot_add (S := s.getReg .x2) (j := 320) (k := 8) (by addr_omega [hb1]) (by omega)
      have e16 : s.getReg .x2 - 320 + 16 = s.getReg .x2 - BitVec.ofNat 64 304 :=
        slot_add (S := s.getReg .x2) (j := 320) (k := 16) (by addr_omega [hb1]) (by omega)
      refine eAt_congr (tt 320 (by omega) (by omega) (by omega) (by omega) rfl) ?_ ?_
      · rw [e8]; exact tt 312 (by omega) (by omega) (by omega) (by omega) rfl
      · rw [e16]; exact tt 304 (by omega) (by omega) (by omega) (by omega) rfl
    · rw [k₃ .x25 (by decide), k₂ .x25 (by decide), D.regs .x25 (by decide), F.x25]
  have x20 : t₃.getReg .x20 = u.getReg .x20 := by
    rw [k₃ .x20 (by decide), k₂ .x20 (by decide), D.regs .x20 (by decide)]
  have htb := F.tbBuf
  have x21₃ : t₃.getReg .x21 = t₂.getReg .x21 := k₃ .x21 (by decide)
  refine ⟨t₃, hr₂.trans hr₃, ⟨C₃, fr, hu₃, ex, ?_, ?_, x21₃ ▸ x21₂, (k₃ .x22 (by decide)).trans x22₂,
    ?_, ?_, x20, ?_, ?_, ?_⟩, ?_⟩
  · rw [x20, DFrame.eListNew fr htb (le_refl _) hlo huE fun a h1 h2 ↦ EW.low hpre hev h1 h2]
    exact F.tb
  · rw [x20]; exact ⟨htb.1, htb.2.imp_right fun h ↦ ⟨h.1, le_trans h.2 hu₃⟩⟩
  · rw [k₃ .x9 (by decide), k₂ .x9 (by decide)]; exact D.x9
  · rw [k₃ .x18 (by decide), k₂ .x18 (by decide)]; exact D.x18
  · rw [k₃ .x26 (by decide), k₂ .x26 (by decide), D.regs .x26 (by decide)]; exact F.x26
  · have e := b800077b0_m_x2_168 h₃
    have a : t₂.getReg .x2 + 168 = s.getReg .x2 - 1176 := by
      rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [a, x22₂, ofNat_mul8 hi] at e
    exact e
  · have e := b800077b0_m_x2_160 h₃
    have a : t₂.getReg .x2 + 160 = s.getReg .x2 - 1184 := by
      rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [a, x22₂, ofNat_mul16 hi] at e
    exact e
  · by_cases h0 : t₂.getReg .x21 = 0
    · exact Or.inl ⟨x21₃.trans h0, b800077b0_pc_taken h₃ h0⟩
    · exact Or.inr ⟨x21₃ ▸ h0, b800077b0_pc_not_taken h₃ h0⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
