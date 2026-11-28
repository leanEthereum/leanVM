module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.StackOffsets.Names
public import NativeRustcVmArm.Bus.BusLayout.Keep

/-!
# `bus_layout`: the offsets and the layout's start

From `.LBusLayout_8` (`offsets_run`): `b9` and `memset` clear the offsets; `b10` calls
`stack_offsets` on the sizes (`natsOf_S`; they fit, `offsetsFit`), which succeeds with the depth
and the offsets (`OffsAt`); `b11` checks it; `b12` stores the depth and clears the layout, to the
placements' loop (`PInv` at `0`).
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)

public section

section
variable {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}

/-- The sizes `stack_offsets` reads. -/
theorem natsOf_S [Labels] (hpre : BusLayoutPre L bl m0) {m : MachineData}
    (hs : SizesAt m.dmem L bl m0 (nf m0 + bl.length)) (h0 : m.regs.X0.toBitVec = fa m0 8)
    (h1 : m.regs.X1.toNat = nf m0 + bl.length) :
    natsOf m m.regs.X0 m.regs.X1.toNat = (S L bl m0).toArray := by
  unfold natsOf
  rw [h0, h1]
  congr 1
  apply List.ext_getElem (by simp [S_length])
  intro i hi1 hi2
  simp only [List.length_map, NativeRustcVm.length_wordsOf] at hi1
  simp only [List.getElem_map, NativeRustcVm.wordsOf, List.getElem_range]
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.wordOf_of_wordAt (hs i hi1),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some, Nat.toUInt64_eq,
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (pre_S_le hpre _ (List.getElem_mem hi2))
      (by decide))]

/-- The offsets `stack_offsets` wrote. -/
theorem offsAt_of [Labels] {d : Mem 64} (h : WordsAt d (fa m0 440) (natWords (O L bl m0).1)) :
    OffsAt d L bl m0 := fun j hj ↦ by
  have hsz : (O L bl m0).1.size = nf m0 + bl.length := by rw [size_so, fws_size]
  have h' := NativeRustcVm.WordsAt.getElem h (i := j) (by simp [natWords, hsz, hj])
  rw [NativeRustcVm.addr_add_add] at h'
  simp only [natWords, List.getElem_map, Array.getElem_toList] at h'
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some]

end

variable [Host] {k : Nat}

/-- **The offsets, the layout's start**: from `.LBusLayout_8` to the placements' loop. -/
theorem offsets_run (hp : Placed code k)
    (hms : Spec (Labels.label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost)
    (hso : Spec (Labels.label NativeRustcVmArm.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost)
    {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    (hpre : BusLayoutPre L bl m0) {st : MachineState} (hD : Done L bl m0 k st) :
    Eventually (step1 Host.exe) (fun st' ↦
      st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BusLayout.b14Offset) ∧ PInv L bl m0 0 st'.data) st := by
  obtain ⟨hpc, hfr, hregs, hx21, hsz⟩ := hD
  have hS := hpre.1
  have hN : busLayoutStack ≤ m0.regs.SP.toNat := hS.2.1
  have hF : 1840 ≤ busLayoutStack := by decide
  have hF' : 1840 ≤ m0.regs.SP.toNat := by omega
  have hn := pre_n hpre
  have hle : 1840 + stackOffsetsStack ≤ busLayoutStack := le_refl _
  -- `b9`: `memset` of the offsets.
  have hwf := Bus.wf_frame (F := 1840) hS hF hfr.kept
  have hm := Bus.match_frame (m := st.data) hS hF rfl hfr.sp
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 st1.data := Fr.ofBlock hfr hm hm1 hwf rfl rfl rfl (ofBlock_keep (by decide))
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have K1 : Bus.KeepRegs [.X19, .X20, .X21] st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
  have e0 : st1.data.regs.X0.toBitVec = fa m0 440 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]; rfl
  have e2 : st1.data.regs.X2.toNat = 432 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      hm1.regs .X2 _ rfl]; rfl
  have e22 : (st1.data.regs.getXReg .X22).toBitVec = fa m0 440 := by rw [hm1.regs .X22 _ rfl]; rfl
  have hfb : (fb m0).toNat = m0.regs.SP.toNat - 1840 := base_toNat hF'
  have hlt := m0.regs.SP.toNat_lt
  have h440 : (fa m0 440).toNat = (fb m0).toNat + 440 := NativeRustcVm.toNat_add_ofNat (by omega)
  refine Fr.callW hfr1 keep_callee hms (W := InRange (fa m0 440) 432)
    (fun m' h ↦ ⟨by rw [← e0, ← e2]; exact h.2.2.1, h.2.2.2⟩)
    (fun q hq ↦ .inl (inRange_local hN hF (by omega) hq))
    (fun p hp' i hi ↦ slot_not_local hF' (by revert p; decide) (by
      have := slots_le p hp'; omega))
    hpc1 ⟨fun t ht ↦ by
        rw [e0, NativeRustcVm.addr_add_add]
        exact hfr1.kept _ ((Bus.frame_mapped hS hF).1 _ (by omega)),
      by unfold NoWrap; rw [e0, e2, h440]; omega⟩ fun m2 hfr2 hq2 hcs2 ↦ ?_
  have K2 : Bus.KeepRegs [.X19, .X20, .X21, .X22] st1.data m2 := Bus.KeepRegs.of_call hcs2 rfl
  have hs2 : SameOutside st1.data.dmem m2.dmem (InRange (fa m0 440) 432) := by
    rw [← e0, ← e2]; exact hq2.2.2.1
  have hsz2 : SizesAt m2.dmem L bl m0 (nf m0 + bl.length) := fun j hj ↦
    word_keep hs2 (fun i hi ↦ frame_out hF' (by omega) (by omega) (.inl (by omega)))
      (by rw [hd1]; exact hsz j hj)
  -- `b10`: `stack_offsets` of the sizes.
  have hwf2 := Bus.wf_frame (F := 1840) hS hF hfr2.kept
  have hm2 := Bus.match_frame (m := m2) hS hF rfl hfr2.sp
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf2 rfl hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hfr3 : Frm m0 st3.data := Fr.ofBlock hfr2 hm2 hm3 hwf2 rfl rfl rfl (ofBlock_keep (by decide))
  have hd3 : st3.data.dmem = m2.dmem := hm3.dmem_eq hwf2 rfl
  have K3 : Bus.KeepRegs [.X19, .X20, .X21, .X22] m2 st3.data := Bus.KeepRegs.of_block hm3 rfl
  have e3x0 : st3.data.regs.X0.toBitVec = fa m0 8 := by
    rw [show st3.data.regs.X0 = st3.data.regs.getXReg .X0 from rfl, hm3.regs .X0 _ rfl]; rfl
  have e3x1 : st3.data.regs.X1.toNat = nf m0 + bl.length := by
    rw [show st3.data.regs.X1 = st3.data.regs.getXReg .X1 from rfl, mov_reg (r' := .X21) hm3 rfl,
      K2 .X21 (by simp), K1 .X21 (by simp), hx21]
  have e3x2 : st3.data.regs.X2.toBitVec = fa m0 440 := by
    rw [show st3.data.regs.X2 = st3.data.regs.getXReg .X2 from rfl, hm3.regs .X2 _ rfl]; rfl
  have e3x3 : st3.data.regs.X3.toNat = 54 := by
    rw [show st3.data.regs.X3 = st3.data.regs.getXReg .X3 from rfl, ← UInt64.toNat_toBitVec,
      hm3.regs .X3 _ rfl]; rfl
  have e3x23 : (st3.data.regs.getXReg .X23).toBitVec = fa m0 8 := by rw [hm3.regs .X23 _ rfl]; rfl
  have hl8 := Bus.local_ok (F := 1840) (N' := stackOffsetsStack) (o := 8)
    (n := 8 * (nf m0 + bl.length)) hS hle (by omega) hfr3.kept hfr3.sp
  have hl440 := Bus.local_ok (F := 1840) (N' := stackOffsetsStack) (o := 440) (n := 432) hS hle
    (by omega) hfr3.kept hfr3.sp
  have hpre3 : StackOffsetsPre st3.data := by
    simp only [StackOffsetsPre, e3x0, e3x1, e3x2, e3x3]
    refine ⟨hfr3.stackOk hS rfl hle, by unfold columnCountW; omega, hl8.1, hl8.2, hl440.1, hl440.2,
      ?_⟩
    unfold Apart
    have h8 : (fa m0 8).toNat = (fb m0).toNat + 8 := NativeRustcVm.toNat_add_ofNat (by omega)
    rw [h8, h440]
    omega
  refine Fr.leafIn hfr3 hN hle (by omega : 440 + 432 ≤ 1840) keep_callee
    (fun p hp' ↦ ⟨slots_le p hp', .inr (by revert p; decide)⟩) (outs_frame hpre) hso hpc3 hpre3
    (fun m' h ↦ ⟨NativeRustcVm.SameOutside.mono h.2.1 fun q hq ↦ hq.elim
      (fun h' ↦ .inr (.inl (by rw [e3x2, e3x3] at h'; exact h'))) .inl, h.2.2⟩)
    fun m4 hfr4 hq4 hcs4 ↦ ?_
  have hsizes3 : SizesAt st3.data.dmem L bl m0 (nf m0 + bl.length) := by rw [hd3]; exact hsz2
  have hnats := natsOf_S hpre hsizes3 e3x0 e3x1
  obtain ⟨hres, hch4, -⟩ := hq4
  rw [hnats] at hres
  simp only [e3x1, e3x3, e3x2] at hres hch4
  have hfit : nf m0 + bl.length ≤ 54 ∧ OffsetsFit (S L bl m0).toArray :=
    ⟨hn, offsetsFit (pre_S_le hpre) (by rw [S_length]; exact hn)⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true hfit)] at hres
  obtain ⟨hx0, hx1, hoffs⟩ := hres
  have K4 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X23] st3.data m4 :=
    Bus.KeepRegs.of_call hcs4 rfl
  have hsz4 : SizesAt m4.dmem L bl m0 (nf m0 + bl.length) := fun j hj ↦
    word_keep hch4 (fun i hi h ↦ h.elim (frame_out hF' (by omega) (by omega) (.inl (by omega)))
      (slot_not_callee (by omega) hfr3.sp (by omega))) (hsizes3 j hj)
  have hoffs4 : OffsAt m4.dmem L bl m0 := offsAt_of hoffs
  -- `b11`: `stack_offsets` succeeded.
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 (Env.wf_nil _) rfl
    (match_nil _) fun st5 hm5 hpc5 ↦ ?_
  have hfr5 : Frm m0 st5.data := Fr.ofBlock hfr4 (match_nil _) hm5 (Env.wf_nil _) rfl rfl rfl
    (ofBlock_keep (by decide))
  have hd5 : st5.data.dmem = m4.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  have K5 : Bus.KeepRegs [.X1, .X19, .X20, .X21, .X22, .X23] m4 st5.data :=
    Bus.KeepRegs.of_block hm5 rfl
  have hpc5' := (pc_of_cond hpc5).2 (by
    show (!(SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).eval _) = false
    rw [eval_eq_lit _ _ _ .X0 (by decide), show m4.regs.getXReg .X0 = 1 from hx0]
    rfl)
  -- `b12`: the depth, the layout cleared.
  have hwf6 := Bus.wf_frame (F := 1840) hS hF hfr5.kept
  have hm6 := Bus.match_frame (m := st5.data) hS hF rfl hfr5.sp
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf6 hpc5' hm6
    fun st6 hm6' hpc6 ↦ ?_
  have hall := b12_mem
  have hdep := b12_depth
  have hct := b12_count
  rw [Bus.after_eq run_b12] at hall hdep hct
  have hfr6 : Frm m0 st6.data :=
    frm_block hN hfr5 hm6 hm6' hwf6 rfl (ofBlock_keep (by decide)) (by decide) hall
  have K6 : Bus.KeepRegs [.X19, .X20, .X21, .X22, .X23] st5.data st6.data :=
    Bus.KeepRegs.of_block hm6' rfl
  have hko : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 872 → WordAt m4.dmem (fa m0 o) w →
      WordAt st6.data.dmem (fa m0 o) w :=
    fun ho h ↦ keep_out hm6' hwf6 rfl hF' (by decide) (by decide) hall (by omega) (.inl ho)
      (by rw [Env.ofMachine_mem0, hd5]; exact h)
  have hpart : Part st6.data.dmem L bl m0 0 := by
    refine ⟨?_, ?_, fun j hj ↦ absurd hj (by omega), fun j hj ↦ absurd hj (by omega)⟩
    · have h := Bus.wordAt_write hm6' (r := 0) (o := 872) rfl (by omega) hdep
      rw [show UInt64.ofBitVec ((Sym.reg .X1).eval (Env.ofMachine st5.data [(fb m0, 1840)])) =
          (O L bl m0).2.toUInt64 by
        apply UInt64.toNat_inj.mp
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (pre_depth_lt hpre)]
        show (st5.data.regs.getXReg .X1).toBitVec.toNat = _
        rw [UInt64.toNat_toBitVec, K5 .X1 (by simp)]
        exact hx1] at h
      exact h
    · have h := Bus.wordAt_write hm6' (r := 0) (o := 936) rfl (by omega) hct
      rw [Nat.zero_sub]
      exact h
  simp only [PcOk] at hpc6
  rw [lbl_11 hp] at hpc6
  have hx19 : st6.data.regs.getXReg .X19 = st.data.regs.getXReg .X19 := by
    rw [K6 .X19 (by simp), K5 .X19 (by simp), K4 .X19 (by simp), K3 .X19 (by simp),
      K2 .X19 (by simp), K1 .X19 (by simp)]
  have hx20 : st6.data.regs.getXReg .X20 = st.data.regs.getXReg .X20 := by
    rw [K6 .X20 (by simp), K5 .X20 (by simp), K4 .X20 (by simp), K3 .X20 (by simp),
      K2 .X20 (by simp), K1 .X20 (by simp)]
  have hx21s : st6.data.regs.getXReg .X21 = st.data.regs.getXReg .X21 := by
    rw [K6 .X21 (by simp), K5 .X21 (by simp), K4 .X21 (by simp), K3 .X21 (by simp),
      K2 .X21 (by simp), K1 .X21 (by simp)]
  refine .done _ ⟨hpc6, hfr6, by have : 1 ≤ bl.length := hpre.2.2.2.2.1; omega,
    fun j hj ↦ hko (by omega) (hsz4 j hj), fun j hj ↦ hko (by omega) (hoffs4 j hj), hpart,
    by rw [hx19, hregs.x19], ?_, ?_, ?_, ?_, by rw [hx20, hregs.x20], by rw [hx21s, hx21], ?_, ?_⟩
  · rw [← UInt64.toNat_toBitVec, hm6'.regs .X8 _ rfl]; rfl
  · rw [← UInt64.toNat_toBitVec, hm6'.regs .X9 _ rfl, Nat.zero_min]; rfl
  · rw [hm6'.regs .X10 _ rfl]; rfl
  · rw [hm6'.regs .X11 _ rfl]; rfl
  · rw [K6 .X22 (by simp), K5 .X22 (by simp), K4 .X22 (by simp), K3 .X22 (by simp),
      K2 .X22 (by simp), e22]
  · rw [K6 .X23 (by simp), K5 .X23 (by simp), K4 .X23 (by simp), e3x23]

end

end NativeRustcVmArm.Bus.BusLayout
