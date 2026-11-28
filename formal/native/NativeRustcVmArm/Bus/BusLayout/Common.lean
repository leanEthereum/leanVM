module

public import NativeRustcVmArm.Code.Vm.BusLayout.Names
public import NativeRustcVmArm.Bus.BusLayout.Exec
public import NativeRustcVmArm.Bus.BusLayout.Model
public import NativeRustcVmArm.Bus.Frame

/-!
# `bus_layout`: the frame, the layout under construction, the epilogue

The frame (`fb`, 1840 bytes) holds the sizes at `8`, the offsets at `440`, the layout under
construction at `872` (`Part`: the depth, the tables' count at `936`, the placements pushed so
far). `built`: once every placement is pushed and the framework's count stored at `880`, it is
`busLayout`'s `BusLayoutWAt`; `busLayoutWAt_transfer` moves it to the output. `finish` runs
`b20`-`b22`: the count, `memcpy` to the output, its tag, the epilogue.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Verifier (Placement)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(1760, .X29), (1768, .X30), (1776, .X26), (1784, .X25), (1792, .X24), (1800, .X23),
    (1808, .X22), (1816, .X21), (1824, .X20), (1832, .X19)]

/-- The callee-saved registers it does not save. -/
abbrev keep : List XReg := [.X27, .X28]

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1840 := by decide

/-- The output's bytes. -/
abbrev outs (m0 : MachineData) : BitVec 64 → Prop :=
  InRange m0.regs.X0.toBitVec optBusLayoutBytes

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 1840
/-- Frame byte `o`. -/
abbrev fa (m0 : MachineData) (o : Nat) : BitVec 64 := fb m0 + BitVec.ofNat 64 o
/-- The framework's count. -/
abbrev nf (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- The framework's sizes. -/
abbrev fws (m0 : MachineData) : Array Nat := natsOf m0 m0.regs.X1 m0.regs.X2.toNat
/-- The sizes. -/
abbrev S (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) : List Nat :=
  szs (fws m0) L.tableLogHeights bl
/-- The offsets and the depth. -/
abbrev O (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) :
    Array Nat × Nat :=
  so (fws m0) L.tableLogHeights bl
/-- Placement `j`. -/
abbrev P (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (j : Nat) :
    Placement :=
  pl (fws m0) L.tableLogHeights bl j

/-- Between the prologue and the epilogue. -/
abbrev Frm (m0 st : MachineData) : Prop :=
  Fr m0 1840 busLayoutStack slots keep (outs m0) st

/-- `bus_layout`'s postcondition, reached. -/
abbrev Post (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ BusLayoutPost L bl m0 st.data

/-- **The layout under construction** at `872` after `i` placements. -/
structure Part (d : Mem 64) (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (i : Nat) : Prop where
  depth : WordAt d (fa m0 872) (O L bl m0).2.toUInt64
  tlen : WordAt d (fa m0 936) (i - nf m0).toUInt64
  fw : ∀ j < min i (nf m0), PlacementAt d (fa m0 (888 + 16 * j)) (P L bl m0 j)
  tb : ∀ j < i - nf m0, PlacementAt d (fa m0 (944 + 16 * j)) (P L bl m0 (nf m0 + j))

theorem fws_size (m0 : MachineData) : (fws m0).size = nf m0 := by simp [natsOf]

theorem S_length (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) :
    (S L bl m0).length = nf m0 + bl.length := by
  rw [length_szs, fws_size]

/-! ## The pre's facts -/

section
variable {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}

theorem pre_S_le [Labels] (hpre : BusLayoutPre L bl m0) : ∀ s ∈ S L bl m0, s ≤ 30 :=
  szs_le hpre.2.2.1 hpre.2.2.2.2.2.2.2.2.2.2.1.heights_le

theorem pre_n [Labels] (hpre : BusLayoutPre L bl m0) : nf m0 + bl.length ≤ 54 := by
  have h1 : nf m0 ≤ 3 := hpre.2.1
  have h2 := hpre.2.2.2.2.2.1
  unfold maxBlocks at h2
  omega

theorem pre_O_lt [Labels] (hpre : BusLayoutPre L bl m0) (j : Nat) :
    (O L bl m0).1.getD j 0 < 2 ^ 64 := by
  show (stackOffsets (S L bl m0).toArray).1.getD j 0 < 2 ^ 64
  have h1 := offset_le (l := S L bl m0) j
  have h2 := sum_pow_le (pre_S_le hpre)
  have h3 : (S L bl m0).length * 2 ^ 30 ≤ 54 * 2 ^ 30 :=
    Nat.mul_le_mul_right _ (by rw [S_length]; exact pre_n hpre)
  omega

theorem pre_depth_lt [Labels] (hpre : BusLayoutPre L bl m0) : (O L bl m0).2 < 2 ^ 64 := by
  show (stackOffsets (S L bl m0).toArray).2 < 2 ^ 64
  have := depth_le (pre_S_le hpre) (by rw [S_length]; exact pre_n hpre)
  omega

theorem pre_S_getD_le [Labels] (hpre : BusLayoutPre L bl m0) (j : Nat) :
    (S L bl m0).getD j 0 ≤ 30 := by
  rw [List.getD_eq_getElem?_getD]
  cases e : (S L bl m0)[j]? with
  | none => simp
  | some x => exact pre_S_le hpre x (List.mem_of_getElem? e)

theorem pre_P_ok [Labels] (hpre : BusLayoutPre L bl m0) (j : Nat) :
    (P L bl m0 j).variableCount < 2 ^ 64 ∧ (P L bl m0 j).index < 2 ^ 64 :=
  ⟨by have := pre_S_getD_le hpre j; show (S L bl m0).getD j 0 < 2 ^ 64; omega, pre_O_lt hpre j⟩

/-- The output is apart from the frame. -/
theorem outs_frame [Labels] (hpre : BusLayoutPre L bl m0) :
    ∀ q, outs m0 q → ¬InRange (fb m0) 1840 q := by
  intro q hq hq'
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hpre.1.2.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hO := hpre.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hA := apart_frame hN hF hO.2
  change InRange m0.regs.X0.toBitVec optBusLayoutBytes q at hq
  rw [Sym.inRange_iff hO.1.2] at hq
  rw [Sym.inRange_iff (Bus.frame_mapped hpre.1 hF).2] at hq'
  unfold Apart at hA
  omega

end

/-! ## The layout built -/

theorem placementAt_transfer {d d' : Mem 64} {a b : BitVec 64} {n o : Nat} {p : Placement}
    (htr : ∀ i < n, ∀ x, d.get? (a + BitVec.ofNat 64 i) = some x →
      d'.get? (b + BitVec.ofNat 64 i) = some x)
    (ho : o + 16 ≤ n) (h : PlacementAt d (a + BitVec.ofNat 64 o) p) :
    PlacementAt d' (b + BitVec.ofNat 64 o) p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, wordAt_transfer htr (by omega) h3, ?_⟩
  simp only [off, NativeRustcVm.addr_add_add] at h4 ⊢
  exact wordAt_transfer htr (by omega) h4

/-- **A side's layout moved** with its 888 bytes. -/
theorem busLayoutWAt_transfer {d d' : Mem 64} {a b : BitVec 64} {BL : BusLayoutW}
    (htr : ∀ i < 888, ∀ x, d.get? (a + BitVec.ofNat 64 i) = some x →
      d'.get? (b + BitVec.ofNat 64 i) = some x)
    (h : BusLayoutWAt d a BL) : BusLayoutWAt d' b BL := by
  obtain ⟨hdl, hd, ⟨hfs, hfl, hfi⟩, ⟨hts, htl, hti⟩⟩ := h
  refine ⟨hdl, ?_, ⟨hfs, ?_, fun i hi ↦ ?_⟩, ⟨hts, ?_, fun i hi ↦ ?_⟩⟩
  · have := wordAt_transfer (o := 0) htr (by omega) (by rw [add_zero']; exact hd)
    rwa [add_zero'] at this
  · exact wordAt_transfer htr (by omega) hfl
  · have := hfi i hi
    simp only [off, NativeRustcVm.addr_add_add] at this ⊢
    exact placementAt_transfer htr (by unfold NativeRustcVm.Bus.placementBytes; omega) this
  · exact wordAt_transfer htr (by omega) htl
  · have := hti i hi
    unfold maxBlocks at hts
    simp only [off, NativeRustcVm.addr_add_add] at this ⊢
    exact placementAt_transfer htr (by unfold NativeRustcVm.Bus.placementBytes; omega) this

/-- **The layout built**: every placement pushed, the framework's count at `880`. -/
theorem built [Labels] {d : Mem 64} {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) (rows : Array Nat)
    (hp : Part d L bl m0 (nf m0 + bl.length)) (h880 : WordAt d (fa m0 880) (nf m0).toUInt64) :
    BusLayoutWAt d (fa m0 872)
      (busLayout (fws m0) (bl.map (blockW L.tableLogHeights rows)).toArray) := by
  have hnf : nf m0 ≤ 3 := hpre.2.1
  have hbl : bl.length ≤ 51 := hpre.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [busLayout_depth]; exact pre_depth_lt hpre
  · rw [busLayout_depth]; exact hp.depth
  · rw [busLayout_framework]
    refine ⟨by simp [fws_size, hnf], ?_, fun j hj ↦ ?_⟩
    · simp only [List.size_toArray, List.length_map, List.length_range, fws_size]
      simp only [off, fa, NativeRustcVm.addr_add_add] at h880 ⊢
      exact h880
    · simp only [List.size_toArray, List.length_map, List.length_range, fws_size] at hj
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
      have := hp.fw j (by omega)
      simp only [off, fa, NativeRustcVm.addr_add_add, NativeRustcVm.Bus.placementBytes] at this ⊢
      rwa [show 872 + 8 + (8 + 16 * j) = 888 + 16 * j by omega]
  · rw [busLayout_tables]
    refine ⟨by simp [hbl, maxBlocks], ?_, fun j hj ↦ ?_⟩
    · simp only [List.size_toArray, List.length_map, List.length_range]
      have := hp.tlen
      simp only [off, fa, NativeRustcVm.addr_add_add, Nat.add_sub_cancel_left] at this ⊢
      exact this
    · simp only [List.size_toArray, List.length_map, List.length_range] at hj
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, fws_size]
      have := hp.tb j (by omega)
      simp only [off, fa, NativeRustcVm.addr_add_add, NativeRustcVm.Bus.placementBytes] at this ⊢
      rwa [show 872 + 64 + (8 + 16 * j) = 944 + 16 * j by omega]

/-! ## The labels -/

section
variable [Host] {k : Nat}

theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b5Offset) NativeRustcVmArm.Vm.BusLayout.label_4_at
theorem lbl_5 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b6Offset) NativeRustcVmArm.Vm.BusLayout.label_5_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b7Offset) NativeRustcVmArm.Vm.BusLayout.label_6_at
theorem lbl_8 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b9Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b9Offset) NativeRustcVmArm.Vm.BusLayout.label_8_at
theorem lbl_10 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b13Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b13Offset) NativeRustcVmArm.Vm.BusLayout.label_10_at
theorem lbl_11 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b14Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b14Offset) NativeRustcVmArm.Vm.BusLayout.label_11_at
theorem lbl_14 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b17Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b17Offset) NativeRustcVmArm.Vm.BusLayout.label_14_at
theorem lbl_17 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.BusLayout.label_17 = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b20Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.BusLayout.b20Offset) NativeRustcVmArm.Vm.BusLayout.label_17_at

end

end

end NativeRustcVmArm.Bus.BusLayout
