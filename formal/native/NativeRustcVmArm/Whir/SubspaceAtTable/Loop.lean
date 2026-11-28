module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Whir.SubspaceAtTable.Exec
public import NativeRustcVm.Whir.MathSubspace

/-!
# `subspace_at_table`'s loop

At the loop's head (`b3`) after `i` table entries (`Inv`): `W` (X22) is `atAfter`'s, the `What`s
so far in the frame from byte 8, X21 the next slot, X25 the next pair (plus 8), X26 the entries
left. A turn (`step`): `b3` loads the pair and calls `kmul` (`What_i`), `b4` stores it and calls
`kmul` (`W²`), `b5` calls `kmul` (`root·W`), `b6` takes the sum as the next `W` and counts; after
the last entry it falls through to `b7` (`Done`).
-/

namespace NativeRustcVmArm.Whir.SubspaceAtTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceAtTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 336
/-- The table's entries. -/
def nOf (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- The table. -/
def tbOf (m0 : MachineData) : Array (UInt64 × UInt64) :=
  (pairsOf m0.dmem m0.regs.X1.toBitVec (nOf m0)).toArray
/-- The output. -/
def outsOf (m0 : MachineData) : List Region := [⟨m0.regs.X0.toBitVec, whatBytes⟩]

/-- The loop's head after `i` entries. -/
structure Inv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  fr : Frame m0 336 subspaceAtTableStack slots (outsOf m0) st
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X2
  x21 : st.regs.X21.toBitVec = fbOf m0 + BitVec.ofNat 64 (8 * i + 8)
  x22 : st.regs.X22 = (atAfter (tbOf m0) m0.regs.X3 i).2
  x25 : st.regs.X25.toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * i + 8)
  x26 : st.regs.X26.toNat = nOf m0 - i
  what : NativeRustcVm.WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 8)
    (atAfter (tbOf m0) m0.regs.X3 i).1.toList

/-- After the loop. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : Frame m0 336 subspaceAtTableStack slots (outsOf m0) st
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X2
  what : NativeRustcVm.WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 8)
    (subspaceAtTable (tbOf m0) m0.regs.X3).toList

end

public section

theorem stack_eq : subspaceAtTableStack = 448 := rfl

theorem tbOf_size (m0 : MachineData) : (tbOf m0).size = nOf m0 := by simp [tbOf, pairsOf]

theorem tbOf_get (m0 : MachineData) {i : Nat} (hi : i < (tbOf m0).size) :
    (tbOf m0)[i] = (wordOf m0.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * i)),
      wordOf m0.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * i) + 8#64)) := by
  simp [tbOf, pairsOf, ewOf]

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 336 := by decide

theorem x30_mem : XReg.X30 ∈ slots.map (·.2) := List.mem_map.mpr ⟨(264, .X30), by simp [slots], rfl⟩

/-- The slots are at 256 and above. -/
theorem slots_ge : ∀ p ∈ slots, 256 ≤ p.1 := by decide

theorem ofNat_eq {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by rw [h]

variable [Host] {k : Nat}

/-- **A turn of the loop.** -/
theorem step (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : SubspaceAtTablePre m0) {i : Nat} (hi : i < nOf m0)
    {st : MachineData} (hI : Inv m0 i st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b7Offset)) ∨
        (Inv m0 (i + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b3Offset) ∧ i + 1 < nOf m0))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b3Offset)⟩ := by
  obtain ⟨hS, hn31, htin, houtin, hap⟩ := hpre
  have hS448 := stack_eq
  have hn : nOf m0 ≤ 31 := hn31
  have hnn : nOf m0 = m0.regs.X2.toNat := rfl
  have hF : 336 ≤ subspaceAtTableStack := by decide
  have hkle : 336 + kmulStack ≤ subspaceAtTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hsize := tbOf_size m0
  have hi' : i < (tbOf m0).size := by omega
  let tbl := m0.regs.X1.toBitVec
  let w := (atAfter (tbOf m0) m0.regs.X3 i).2
  -- `b3`: load the pair, call `kmul`
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hrd : Readable st (tbl + BitVec.ofNat 64 (16 * i)) 16 :=
    hfr.readable (Readable.sub htin.1 (by omega))
  let env3 := Env.ofMachine st [(tbl + BitVec.ofNat 64 (16 * i), 16)]
  have hwf3 : env3.WF := wf_one hrd.1 hrd.2
  have hm3 : Match env3 ldS st := match_one <| by
    show st.regs.X25.toBitVec = _
    rw [hI.x25, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add]
  refine exec_then hk3 run_b3 hwf3 hm3 fun s1 hm1 hpc1 ↦ ?_
  have hb3 := after_eq run_b3 ▸ b3_keeps
  have hfr1 := hfr.of_regs hm3 hm1 hwf3 rfl hb3.1 hb3.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq hwf3 hb3.2
  have harg := hfr.get?_arg hS htin fun r hr ↦ by
    simp only [outsOf, List.mem_singleton] at hr
    subst hr
    exact ⟨hap.symm, houtin.1.2⟩
  have hb30 : env3.base 0 = tbl + BitVec.ofNat 64 (16 * i) := rfl
  have hroot : (s1.data.regs.getXReg .X23).toBitVec = ((tbOf m0)[i]'hi').1.toBitVec := by
    refine (hm1.regs .X23 _ rfl).trans ?_
    simp only [Sym.eval]
    rw [load8_eq, hb30, NativeRustcVm.addr_add_zero, tbOf_get m0 hi']
    refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
    rw [addr_add]
    refine harg _ ?_
    omega
  have hinv : (s1.data.regs.getXReg .X1).toBitVec = ((tbOf m0)[i]'hi').2.toBitVec := by
    refine (hm1.regs .X1 _ rfl).trans ?_
    simp only [Sym.eval]
    rw [load8_eq, hb30, tbOf_get m0 hi', show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
    refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun j hj ↦ ?_)
    rw [addr_add, addr_add]
    refine harg _ ?_
    omega
  have hw1 : (s1.data.regs.getXReg .X0).toBitVec = w.toBitVec := by
    refine (hm1.regs .X0 _ rfl).trans ?_
    show st.regs.X22.toBitVec = _
    rw [hI.x22]
  refine call_then hpc1 hkmul (hfr1.stackOk hS rfl hkle) fun s2 hpc2 ⟨hx0, hsame2, hsv2⟩ ↦ ?_
  have hfr2 := hfr1.call hS hkle slots_le hsame2 hsv2
  have hwlen : ((atAfter (tbOf m0) m0.regs.X3 i).1.toList.flatMap NativeRustcVm.wordBytes).length =
      8 * i := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, atAfter_size _ _ _ hi'.le]
  have hwhat2 : NativeRustcVm.WordsAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 8)
      (atAfter (tbOf m0) m0.regs.X3 i).1.toList :=
    hfr1.bytes_call hS hkle hsame2 (by rw [hwlen]; omega) (hd1 ▸ hI.what)
  -- `b4`: store `What_i`, call `kmul`
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b4Offset) := hpc2
  have hslot : Readable s2.data (fbOf m0 + BitVec.ofNat 64 (8 * i + 8)) 8 :=
    hfr2.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env4 := Env.ofMachine s2.data [(fbOf m0 + BitVec.ofNat 64 (8 * i + 8), 8)]
  have hwf4 : env4.WF := wf_one hslot.1 hslot.2
  have e21 : s2.data.regs.getXReg .X21 = st.regs.getXReg .X21 :=
    (hsv2.1 .X21 rfl).trans (Match.reg_eq hm3 hm1 rfl rfl)
  have hm4 : Match env4 stS s2.data := match_one <| by
    rw [e21]
    show st.regs.X21.toBitVec = _
    rw [hI.x21]
    simp
  refine exec_at hk4 run_b4 hwf4 hpc2' hm4 fun s3 hm5 hpc3 ↦ ?_
  have hb4 := after_eq run_b4 ▸ b4_keeps
  have hsame3 := same_region hm5 hwf4 (r := 0) rfl hb4.2
  have hfr3 := hfr2.of_block hm4 hm5 hwf4 rfl hb4.1 (r := 0) rfl le_rfl hb4.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (by omega) h))
    (fun q hq j hj ↦ not_inRange_slot hS hF (by omega) (slots_le q hq) hj
      (.inl (by have := slots_ge q hq; omega)))
  have hv : NativeRustcVm.WordAt s3.data.dmem (fbOf m0 + BitVec.ofNat 64 (8 * i + 8))
      (kmul w ((tbOf m0)[i]'hi').2) := by
    have := Match.wordAt_write hm5 (r := 0) (o := 0) rfl (by decide) (v := .reg .X0) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    convert this using 1
    show _ = UInt64.ofBitVec (s2.data.regs.X0.toBitVec)
    have h0 : s1.data.regs.X0 = w := UInt64.toBitVec_inj.mp hw1
    have h1 : s1.data.regs.X1 = ((tbOf m0)[i]'hi').2 := UInt64.toBitVec_inj.mp hinv
    rw [hx0, h0, h1]
  have hwhat3 : NativeRustcVm.WordsAt s3.data.dmem (fbOf m0 + BitVec.ofNat 64 8)
      (atAfter (tbOf m0) m0.regs.X3 (i + 1)).1.toList := by
    rw [atAfter_succ _ _ hi', atStep, Array.toList_push, NativeRustcVm.wordsAt_append,
      NativeRustcVm.wordsAt_singleton, Array.length_toList, atAfter_size _ _ _ hi'.le, addr_add]
    refine ⟨NativeRustcVm.BytesAt.of_sameOutside_apart hwhat2 hsame3 ?_ ?_ hslot.2,
      by rw [show 8 + 8 * i = 8 * i + 8 by omega]; exact hv⟩
    · rw [hwlen]
      have h1 := toNat_add_ofNat' (a := fbOf m0) (i := 8) (by unfold fbOf; omega)
      have h2 := toNat_add_ofNat' (a := fbOf m0) (i := 8 * i + 8) (by unfold fbOf; omega)
      unfold NativeRustcVm.Apart
      rw [h1, h2]
      omega
    · rw [hwlen]
      exact NativeRustcVm.NoWrap.sub hfnw (by omega)
  have hpc3' := hpc3
  refine call_then hpc3 hkmul (hfr3.stackOk hS rfl hkle) fun s4 hpc4 ⟨hx0', hsame4, hsv4⟩ ↦ ?_
  have hfr4 := hfr3.call hS hkle slots_le hsame4 hsv4
  have hwhat4 : NativeRustcVm.WordsAt s4.data.dmem (fbOf m0 + BitVec.ofNat 64 8)
      (atAfter (tbOf m0) m0.regs.X3 (i + 1)).1.toList := by
    refine hfr3.bytes_call hS hkle hsame4 ?_ hwhat3
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, atAfter_size _ _ _ (by omega)]
    omega
  have hlen' : ((atAfter (tbOf m0) m0.regs.X3 (i + 1)).1.toList.flatMap
      NativeRustcVm.wordBytes).length = 8 * (i + 1) := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList, atAfter_size _ _ _ (by omega)]
  -- `b5`: call `kmul` for `root·W`
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b5Offset) := hpc4
  refine exec_at hk5 run_b5 (Env.wf_nil _) hpc4' (match_nil _) fun s5 hm6 hpc5 ↦ ?_
  have hb5 := after_eq run_b5 ▸ b5_keeps
  have hfr5 := hfr4.of_regs (match_nil _) hm6 (Env.wf_nil _) rfl hb5.1 hb5.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm6.dmem_eq (Env.wf_nil _) hb5.2
  refine call_then hpc5 hkmul (hfr5.stackOk hS rfl hkle) fun s6 hpc6 ⟨hx0'', hsame6, hsv6⟩ ↦ ?_
  have hfr6 := hfr5.call hS hkle slots_le hsame6 hsv6
  have hwhat6 : NativeRustcVm.WordsAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 8)
      (atAfter (tbOf m0) m0.regs.X3 (i + 1)).1.toList :=
    hfr5.bytes_call hS hkle hsame6 (by rw [hlen']; omega) (hd5 ▸ hwhat4)
  -- `b6`: the next `W`, the counters
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceAtTable.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b6Offset) := hpc6
  refine exec_at hk6 run_b6 (Env.wf_nil _) hpc6' (match_nil _) fun s7 hm7 hpc7 ↦ ?_
  have hb6 := after_eq run_b6 ▸ b6_keeps
  have hfr7 := hfr6.of_regs (match_nil _) hm7 (Env.wf_nil _) rfl hb6.1 hb6.2
  have hd7 : s7.data.dmem = s6.data.dmem := hm7.dmem_eq (Env.wf_nil _) hb6.2
  -- the registers kept
  have e7 : ∀ r ∈ [XReg.X19, .X20], s7.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;>
    exact (Match.reg_eq (match_nil _) hm7 rfl rfl).trans ((hsv6.1 _ rfl).trans
      ((Match.reg_eq (match_nil _) hm6 rfl rfl).trans ((hsv4.1 _ rfl).trans
        ((Match.reg_eq hm4 hm5 rfl rfl).trans ((hsv2.1 _ rfl).trans
          (Match.reg_eq hm3 hm1 rfl rfl))))))
  have e6 : ∀ r ∈ [XReg.X25, .X26], s6.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;>
    exact (hsv6.1 _ rfl).trans
      ((Match.reg_eq (match_nil _) hm6 rfl rfl).trans ((hsv4.1 _ rfl).trans
        ((Match.reg_eq hm4 hm5 rfl rfl).trans ((hsv2.1 _ rfl).trans
          (Match.reg_eq hm3 hm1 rfl rfl)))))
  have e21 : (s7.data.regs.getXReg .X21).toBitVec = fbOf m0 + BitVec.ofNat 64 (8 * (i + 1) + 8) := by
    rw [Match.reg_eq (match_nil _) hm7 rfl rfl, hsv6.1 _ rfl,
      Match.reg_eq (match_nil _) hm6 rfl rfl, hsv4.1 _ rfl, hm5.regs .X21 _ rfl]
    simp only [Sym.eval, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
    show fbOf m0 + BitVec.ofNat 64 (8 * i + 8) + BitVec.ofNat 64 8 = _
    rw [addr_add, show 8 * i + 8 + 8 = 8 * (i + 1) + 8 by omega]
  have e25 : (s7.data.regs.getXReg .X25).toBitVec =
      m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * (i + 1) + 8) := by
    rw [hm7.regs .X25 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, e6 .X25 (by simp)]
    show st.regs.X25.toBitVec + BitVec.ofNat 64 16 = _
    rw [hI.x25, addr_add, show 16 * i + 8 + 16 = 16 * (i + 1) + 8 by omega]
  have e22 : s4.data.regs.X22 = w :=
    (hsv4.1 .X22 rfl).trans ((Match.reg_eq hm4 hm5 rfl rfl).trans ((hsv2.1 .X22 rfl).trans
      ((Match.reg_eq hm3 hm1 rfl rfl).trans hI.x22)))
  have e23 : s4.data.regs.X23 = ((tbOf m0)[i]'hi').1 :=
    (hsv4.1 .X23 rfl).trans ((Match.reg_eq hm4 hm5 rfl rfl).trans ((hsv2.1 .X23 rfl).trans
      (UInt64.toBitVec_inj.mp hroot)))
  have hroot' : s6.data.regs.X0 = kmul ((tbOf m0)[i]'hi').1 w := by
    have h0 : s5.data.regs.X0 = s4.data.regs.X23 := UInt64.toBitVec_inj.mp (hm6.regs .X0 _ rfl)
    have h1 : s5.data.regs.X1 = s4.data.regs.X22 := UInt64.toBitVec_inj.mp (hm6.regs .X1 _ rfl)
    rw [hx0'', h0, h1, e23, e22]
  have hww : s6.data.regs.X24 = kmul w w := by
    have h24 : s6.data.regs.X24 = s5.data.regs.X24 := hsv6.1 .X24 rfl
    have h24' : s5.data.regs.X24 = s4.data.regs.X0 := UInt64.toBitVec_inj.mp (hm6.regs .X24 _ rfl)
    have h0 : s3.data.regs.X0 = s2.data.regs.X22 := UInt64.toBitVec_inj.mp (hm5.regs .X0 _ rfl)
    have h1 : s3.data.regs.X1 = s2.data.regs.X22 := UInt64.toBitVec_inj.mp (hm5.regs .X1 _ rfl)
    have h22 : s2.data.regs.X22 = s4.data.regs.X22 :=
      ((hsv4.1 .X22 rfl).trans (Match.reg_eq hm4 hm5 rfl rfl)).symm
    rw [h24, h24', hx0', h0, h1, h22, e22]
  have e22' : s7.data.regs.X22 = (atAfter (tbOf m0) m0.regs.X3 (i + 1)).2 := by
    apply UInt64.toBitVec_inj.mp
    rw [atAfter_succ _ _ hi', atStep]
    refine (hm7.regs .X22 _ rfl).trans ?_
    sym_simp
    simp only [Env.ofMachine_regs]
    show s6.data.regs.X0.toBitVec ^^^ s6.data.regs.X24.toBitVec = _
    rw [hroot', hww, ← UInt64.toBitVec_xor, UInt64.xor_comm]
  have e26 : (s7.data.regs.getXReg .X26).toBitVec = st.regs.X26.toBitVec - 1#64 := by
    refine (hm7.regs .X26 _ rfl).trans ?_
    sym_simp
    rw [Env.ofMachine_regs, e6 .X26 (by simp)]
    rfl
  simp only [PcOk] at hpc7
  sym_simp at hpc7
  simp only [Env.ofMachine_regs] at hpc7
  simp only [e6 .X26 (by simp)] at hpc7
  have hl2 : Labels.label NativeRustcVmArm.Vm.SubspaceAtTable.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceAtTable.b3Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceAtTable.b3Offset) NativeRustcVmArm.Vm.SubspaceAtTable.label_2_at
  have hwhat7 : NativeRustcVm.WordsAt s7.data.dmem (fbOf m0 + BitVec.ofNat 64 8)
      (atAfter (tbOf m0) m0.regs.X3 (i + 1)).1.toList := hd7 ▸ hwhat6
  have x19' : s7.data.regs.X19 = m0.regs.X0 := (e7 .X19 (by simp)).trans hI.x19
  have x20' : s7.data.regs.X20 = m0.regs.X2 := (e7 .X20 (by simp)).trans hI.x20
  have h26 : st.regs.X26.toBitVec.toNat = nOf m0 - i := hI.x26
  by_cases hlast : nOf m0 - i = 1
  · have hx26 : (st.regs.getXReg .X26).toBitVec = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      show st.regs.X26.toBitVec.toNat = _
      rw [h26, hlast]
      rfl
    simp only [hx26, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc7
    refine .done _ (.inl ⟨⟨hfr7, x19', x20', ?_⟩, hpc7⟩)
    rw [subspaceAtTable_eq, hsize, show nOf m0 = i + 1 by omega]
    exact hwhat7
  · have hb : ((st.regs.getXReg .X26).toBitVec == 1#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      apply hlast
      rw [← h26]
      exact congrArg BitVec.toNat h
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc7
    refine .done _ (.inr ⟨⟨hfr7, x19', x20', e21, e22', e25, ?_, hwhat7⟩, hpc7.trans hl2,
      by omega⟩)
    show (s7.data.regs.getXReg .X26).toBitVec.toNat = _
    rw [e26, BitVec.toNat_sub, h26]
    simp only [BitVec.toNat_ofNat]
    omega

end

end NativeRustcVmArm.Whir.SubspaceAtTable
