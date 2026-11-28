module

public import NativeRustcVmArm.Code.Vm.Kinv.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.SubspaceTable.Inner

/-!
# `subspace_table`'s turns

At the turns' head (`b14`) after `t` turns (`OInv t`): `b14` starts the layer's loop at word `t`
(`Inner.inner_step`, by `Sym.loop`); `b18` loads the new root (word `t`) and calls `kinv`; `b19`
leaves for `None` when this was the table's 31st root (`t = 30`, so `μ = 31`, `Full`); `b20`
pushes the pair and counts, back to `b14` (`OInv (t + 1)`) or on to the copy (`Done`).
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region WordAt WordsAt)

@[expose] public section

/-- The table full at `b23`: `μ = 31`. -/
structure Full (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0
  hmu : muOf m0 = 31

end

public section

/-- A left shift of a small value. -/
theorem shl_ofNat {x : BitVec 64} {n i : Nat} (hx : x.toNat = i) :
    x <<< n = BitVec.ofNat 64 (i * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx, BitVec.toNat_ofNat]

/-- `[x, lsl #3]` of a small value. -/
theorem memExt3_ofNat {x : BitVec 64} {i : Nat} (hx : x.toNat = i) :
    BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E3⟩) = BitVec.ofNat 64 (i * 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.apply_mem_extend, BitVec.unsigned, BitVec.toNat_ofInt, Int.shiftLeft_eq,
    BitVec.toNat_ofNat]
  rw [hx]
  omega

variable [Host] {k : Nat}

/-- **A turn.** -/
theorem outer_step (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hkinv : Spec (label NativeRustcVmArm.Vm.Kinv.entryLabel) KinvPre KinvPost)
    {m0 : MachineData} (hS : StackOk m0 subspaceTableStack) {t : Nat} {st : MachineData}
    (hO : OInv m0 t st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (OInv m0 (t + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset) ∧ t + 1 < muOf m0) ∨
        (Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b21Offset)) ∨
        (Full m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b23Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset)⟩ := by
  have hF : 864 ≤ subspaceTableStack := by decide
  have hkle : 864 + kinvStack ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have hT := hO.turn
  have ht := hT.ht
  have hmu := hT.hmu
  -- `b14`: the layer's loop from word `t`
  have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk14 run_b14 (Env.wf_nil _) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have hb14 := after_eq run_b14 ▸ b14_keeps
  have hfr1 := hT.fr.of_regs (match_nil _) hm1 (Env.wf_nil _) rfl hb14.1 hb14.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq (Env.wf_nil _) hb14.2
  have hT1 : Turn m0 t s1.data := hT.store (o := 16) (n := 0) hS hfr1 (fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Match.reg_eq (match_nil _) hm1 rfl rfl)
    (fun p _ ↦ by rw [hd1]) le_rfl (by omega)
  have h26 : st.regs.X26.toBitVec.toNat = t := hT.x26
  have h20 : st.regs.X20.toBitVec.toNat = muOf m0 := by rw [hT.x20]; rfl
  have hI0 : IInv m0 t t s1.data := by
    refine ⟨hT1, (Match.reg_eq (r := .X21) (match_nil _) hm1 rfl rfl).trans hO.x21, ?_, ?_, ?_,
      le_rfl, ht⟩
    · rw [hd1, innerL_start (by rw [layerAt_length]; omega)]
      exact hO.layer
    · show (s1.data.regs.getXReg .X19).toBitVec = _
      rw [hm1.regs .X19 _ rfl]
      sym_simp
      show st.regs.X28.toBitVec + st.regs.X26.toBitVec <<< 3 = _
      rw [hT.x28, shl_ofNat h26, addr_add]
      congr 2
      omega
    · show (s1.data.regs.getXReg .X29).toBitVec.toNat = _
      rw [hm1.regs .X29 _ rfl]
      sym_simp
      show (st.regs.X24.toBitVec - (if st.regs.X20.toBitVec.ult st.regs.X26.toBitVec then
        st.regs.X20.toBitVec else st.regs.X26.toBitVec) <<< 3).toNat = _
      rw [bv_ult_toNat, h20, h26, decide_eq_false (by omega)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [shl_ofNat h26, toNat_sub_ofNat (by
        rw [show st.regs.X24.toBitVec.toNat = _ from hT.x24]; omega)]
      rw [show st.regs.X24.toBitVec.toNat = _ from hT.x24]
      omega
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b15Offset) := hpc1
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ Turned m0 t s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b18Offset))
    (fun n s ↦ ∃ j, n = muOf m0 - j ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b15Offset) ∧ IInv m0 t j s.data)
    (fun n s ⟨j, hn, hpc, hI⟩ ↦ by
      obtain ⟨d, pc⟩ := s
      simp only at hpc
      subst hpc
      refine (inner_step hp hkmul hS hI).mono fun s' h ↦ ?_
      rcases h with ⟨hI', hpc'⟩ | h
      · exact .inr ⟨muOf m0 - (j + 1), by have := hI.hj; omega, j + 1, rfl, hpc', hI'⟩
      · exact .inl h)
    (n := muOf m0 - t) ⟨t, rfl, hpc1', hI0⟩
  refine hloop.bind fun s2 ⟨hTd, hpc2⟩ ↦ ?_
  -- `b18`: the new root, `kinv`
  have hT2 := hTd.turn
  have hlayT := hTd.layer
  obtain ⟨L, hLd⟩ : ∃ L, layerAt (muOf m0) (t + 1) = L := ⟨_, rfl⟩
  rw [hLd] at hlayT
  have hL : L.length = muOf m0 := hLd ▸ layerAt_length _ _
  have htL : t < L.length := by omega
  obtain ⟨root, hrootd⟩ : ∃ r, L[t]'htL = r := ⟨_, rfl⟩
  let a := fbOf m0 + BitVec.ofNat 64 (16 + 8 * t)
  have hroot : WordAt s2.data.dmem a root := by
    have := hlayT.getElem (i := t) (by omega)
    rw [addr_add, hrootd] at this
    exact this
  have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hrd : Readable s2.data a 8 := hT2.fr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env3 := Env.ofMachine s2.data [(a, 8)]
  have hwf3 : env3.WF := wf_one hrd.1 hrd.2
  have hm3 : Match env3 rootS s2.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl trivial trivial trivial
      ⟨by
        simp only [rAddr]
        sym_simp
        show s2.data.regs.X28.toBitVec +
          BitVec.ofInt 64 (s2.data.regs.X26.toBitVec.apply_mem_extend ⟨.UXTX, .E3⟩) =
            a + BitVec.ofInt 64 0
        rw [hT2.x28, memExt3_ofNat (show s2.data.regs.X26.toBitVec.toNat = t from hT2.x26),
          addr_add]
        simp only [a, BitVec.ofInt_ofNat, BitVec.add_zero]
        congr 2
        omega, trivial⟩
  obtain ⟨d2, pc2⟩ := s2
  simp only at hpc2
  subst hpc2
  refine exec_then hk18 run_b18 hwf3 hm3 fun s3 hm4 hpc3 ↦ ?_
  have hb18 := after_eq run_b18 ▸ b18_keeps
  have hfr3 := hT2.fr.of_regs hm3 hm4 hwf3 rfl hb18.1 hb18.2
  have hd3 : s3.data.dmem = d2.dmem := hm4.dmem_eq hwf3 hb18.2
  have hT3 : Turn m0 t s3.data := hT2.store (o := 16) (n := 0) hS hfr3 (fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm3 hm4 rfl rfl)
    (fun p _ ↦ by rw [hd3]) le_rfl (by omega)
  have hld : env3.load 0 0 8 = root.toBitVec :=
    load_word (show WordAt d2.dmem (a + BitVec.ofNat 64 0) _ by
      rw [NativeRustcVm.addr_add_zero]; exact hroot)
  have hx0 : s3.data.regs.X0 = root := UInt64.toBitVec_inj.mp ((hm4.regs .X0 _ rfl).trans hld)
  have hx21 : s3.data.regs.X21 = root := UInt64.toBitVec_inj.mp ((hm4.regs .X21 _ rfl).trans hld)
  have hlay3 : WordsAt s3.data.dmem (fbOf m0 + BitVec.ofNat 64 16) L := hd3 ▸ hlayT
  refine call_then hpc3 hkinv (hfr3.stackOk hS rfl hkle) fun s4 hpc4 ⟨hk4, hsame4, hsv4⟩ ↦ ?_
  have hT4 := hT3.call hS hkle hsame4 hsv4
  have hLb : (L.flatMap NativeRustcVm.wordBytes).length = 8 * muOf m0 := by
    rw [NativeRustcVm.length_wordsBytes, hL]
  have hlay4 : WordsAt s4.data.dmem (fbOf m0 + BitVec.ofNat 64 16) L :=
    hfr3.bytes_call hS hkle hsame4 (o := 16) (by rw [hLb]; omega) hlay3
  have hinv : s4.data.regs.X0 = kinv root := by rw [hk4, hx0]
  have e21 : s4.data.regs.X21 = root := (hsv4.1 .X21 rfl).trans hx21
  -- `b19`: the 31st root
  have hk19 : b19.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b19Offset) := b19_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b19Offset) := hpc4
  refine exec_at hk19 run_b19 (Env.wf_nil _) hpc4' (match_nil _) fun s5 hm5 hpc5 ↦ ?_
  have hb19 := after_eq run_b19 ▸ b19_keeps
  have hfr5 := hT4.fr.of_regs (match_nil _) hm5 (Env.wf_nil _) rfl hb19.1 hb19.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm5.dmem_eq (Env.wf_nil _) hb19.2
  have hT5 : Turn m0 t s5.data := hT4.store (o := 16) (n := 0) hS hfr5 (fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Match.reg_eq (match_nil _) hm5 rfl rfl)
    (fun p _ ↦ by rw [hd5]) le_rfl (by omega)
  have e0 : s5.data.regs.X0 = kinv root :=
    (Match.reg_eq (r := .X0) (match_nil _) hm5 rfl rfl).trans hinv
  have e21' : s5.data.regs.X21 = root :=
    (Match.reg_eq (r := .X21) (match_nil _) hm5 rfl rfl).trans e21
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  simp only [Env.ofMachine_regs, bv_beq_toNat] at hpc5
  have h26' : (s4.data.regs.getXReg .X26).toBitVec.toNat = t := hT4.x26
  rw [h26'] at hpc5
  by_cases h30 : t = 30
  · simp only [h30, BitVec.toNat_ofNat, show 30 % 2 ^ 64 = 30 from rfl, decide_true,
      ↓reduceIte] at hpc5
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_17 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b23Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b23Offset) NativeRustcVmArm.Vm.SubspaceTable.label_17_at
    exact .done _ (.inr (.inr ⟨⟨hT5.fr, hT5.out, by omega⟩, hpc5.trans hl⟩))
  have hne : decide (t = (BitVec.ofNat 64 30).toNat) = false := by
    rw [decide_eq_false_iff_not, BitVec.toNat_ofNat]
    omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpc5
  -- `b20`: push the pair, count
  have ht29 : t ≤ 29 := by omega
  have hk20 : b20.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b20Offset) := b20_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc5' : s5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b20Offset) := hpc5
  let pa := fbOf m0 + BitVec.ofNat 64 (272 + 16 * (t + 1))
  have hrd5 : Readable s5.data pa 16 := hT5.fr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env6 := Env.ofMachine s5.data [(pa, 16)]
  have hwf6 : env6.WF := wf_one hrd5.1 hrd5.2
  have hm6 : Match env6 pushS s5.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl trivial trivial trivial
      ⟨by
        simp only [pAddr]
        sym_simp
        show s5.data.regs.X27.toBitVec + s5.data.regs.X25.toBitVec <<< 4 = pa + BitVec.ofInt 64 0
        rw [hT5.x27, shl_ofNat (show s5.data.regs.X25.toBitVec.toNat = t + 1 from hT5.x25),
          addr_add]
        simp only [pa, BitVec.ofInt_ofNat, BitVec.add_zero]
        congr 2
        omega, trivial⟩
  refine exec_at hk20 run_b20 hwf6 hpc5' hm6 fun s6 hm7 hpc6 ↦ ?_
  have hb20 := after_eq run_b20 ▸ b20_keeps
  have hsame6 := same_region hm7 hwf6 (r := 0) rfl hb20.2
  have hfr6 := hT5.fr.of_block hm6 hm7 hwf6 rfl hb20.1 (r := 0) rfl le_rfl hb20.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 272 + 16 * (t + 1)) (n := 16) (by omega) h))
    (fun q hq i hi ↦ not_inRange_slot hS hF (o := 272 + 16 * (t + 1)) (n := 16) (by omega)
      (slots_le q hq) hi (.inl (by have := slots_ge q hq; omega)))
  have hpnw : NativeRustcVm.NoWrap pa 16 := NativeRustcVm.NoWrap.sub hfnw (by omega)
  have hap : ∀ o' len, o' + len ≤ 272 + 16 * (t + 1) →
      NativeRustcVm.Apart (fbOf m0 + BitVec.ofNat 64 o') len pa 16 := by
    intro o' len h1
    unfold NativeRustcVm.Apart
    rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  have hkeep : ∀ {o' : Nat} {bs : List UInt8}, o' + bs.length ≤ 272 + 16 * (t + 1) →
      NativeRustcVm.BytesAt s5.data.dmem (fbOf m0 + BitVec.ofNat 64 o') bs →
      NativeRustcVm.BytesAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 o') bs := by
    intro o' bs hle h
    exact NativeRustcVm.BytesAt.of_sameOutside_apart h hsame6 (hap o' _ hle)
      (NativeRustcVm.NoWrap.sub hfnw (by omega)) hpnw
  have hw0 : WordAt s6.data.dmem pa root := by
    have := Match.wordAt_write hm7 (r := 0) (o := 0) rfl (by decide) (v := .reg .X21) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    convert this using 1
    exact e21'.symm
  have hw8 : WordAt s6.data.dmem (pa + BitVec.ofNat 64 8) (kinv root) := by
    have := Match.wordAt_write hm7 (r := 0) (o := 8) rfl (by decide) (v := .reg .X0) (by decide)
    convert this using 1
    exact e0.symm
  have htab : WordsAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 272)
      (pairWords (tableAt (muOf m0) (t + 1))) := by
    have hlen := table_len (m0 := m0) (t := t) (by omega)
    have hr : ∀ h, (layerAt (muOf m0) (t + 1))[t]'h = root := fun h ↦ by
      subst hLd; exact hrootd
    rw [tableAt_succ ht, hr, show rootPair root = (root, kinv root) from rfl, pairWords_concat,
      NativeRustcVm.wordsAt_append_iff, pairWords_length', tableAt_length (by omega)]
    refine ⟨hkeep (by rw [hlen]) (hd5 ▸ hT4.table), ?_⟩
    rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_singleton_iff, addr_add,
      show 272 + 8 * (2 * (t + 1)) = 272 + 16 * (t + 1) by omega]
    dsimp only
    exact ⟨hw0, hw8⟩
  have hout : WordAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0 :=
    hkeep (bs := NativeRustcVm.wordBytes m0.regs.X0)
      (by rw [NativeRustcVm.length_wordBytes]; omega) (hd5 ▸ hT4.out)
  have hlay6 : WordsAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 16) L :=
    hkeep (by rw [hLb]; omega) (hd5 ▸ hlay4)
  have ekeep : ∀ r ∈ [XReg.X20, .X24, .X27, .X28],
      s6.data.regs.getXReg r = s4.data.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (Match.reg_eq hm6 hm7 rfl rfl).trans (Match.reg_eq (match_nil _) hm5 rfl rfl)
  have e26 : s6.data.regs.X26.toNat = t + 1 := by
    show (s6.data.regs.getXReg .X26).toBitVec.toNat = _
    rw [hm7.regs .X26 _ rfl]
    sym_simp
    show (s5.data.regs.X26.toBitVec + _).toNat = _
    have h5 : s5.data.regs.getXReg .X26 = s4.data.regs.getXReg .X26 :=
      Match.reg_eq (match_nil _) hm5 rfl rfl
    have h4 : s4.data.regs.X26.toBitVec.toNat = t := hT4.x26
    rw [show s5.data.regs.X26 = s4.data.regs.X26 from h5, toNat_add_ofNat' (by omega), h4]
  have e25 : s6.data.regs.X25.toNat = t + 1 + 1 := by
    show (s6.data.regs.getXReg .X25).toBitVec.toNat = _
    rw [hm7.regs .X25 _ rfl]
    sym_simp
    show (s5.data.regs.X25.toBitVec + _).toNat = _
    have h5 : s5.data.regs.getXReg .X25 = s4.data.regs.getXReg .X25 :=
      Match.reg_eq (match_nil _) hm5 rfl rfl
    have h4 : s4.data.regs.X25.toBitVec.toNat = t + 1 := hT4.x25
    rw [show s5.data.regs.X25 = s4.data.regs.X25 from h5, toNat_add_ofNat' (by omega), h4]
  have e21'' : s6.data.regs.X21 = lastAt (layerAt (muOf m0) (t + 1)) (t + 1) := by
    rw [hLd, lastAt_succ htL, hrootd]
    exact (Match.reg_eq (r := .X21) hm6 hm7 rfl rfl).trans e21'
  have hTn : t + 1 < muOf m0 → Turn m0 (t + 1) s6.data := fun hlt ↦
    { fr := hfr6, out := hout, table := htab
      x20 := (ekeep .X20 (.head _)).trans hT4.x20
      x24 := by
        rw [show s6.data.regs.X24 = s4.data.regs.X24 from ekeep .X24 (.tail _ (.head _))]
        exact hT4.x24
      x25 := e25
      x26 := e26
      x27 := by
        rw [show s6.data.regs.X27 = s4.data.regs.X27 from
          ekeep .X27 (.tail _ (.tail _ (.head _)))]
        exact hT4.x27
      x28 := by
        rw [show s6.data.regs.X28 = s4.data.regs.X28 from
          ekeep .X28 (.tail _ (.tail _ (.tail _ (.head _))))]
        exact hT4.x28
      ht := hlt
      hmu := hmu }
  simp only [PcOk] at hpc6
  sym_simp at hpc6
  simp only [bv_beq_toNat] at hpc6
  have h26n : (env6.regs .X26).toNat = t := by
    show (s5.data.regs.getXReg .X26).toBitVec.toNat = t
    rw [Match.reg_eq (r := .X26) (match_nil _) hm5 rfl rfl]; exact hT4.x26
  have h20n : (env6.regs .X20).toNat = muOf m0 := by
    show (s5.data.regs.getXReg .X20).toBitVec.toNat = _
    rw [Match.reg_eq (r := .X20) (match_nil _) hm5 rfl rfl]
    show s4.data.regs.X20.toNat = _
    rw [hT4.x20]; rfl
  rw [toNat_add_ofNat' (by rw [h26n]; omega), h26n, h20n] at hpc6
  by_cases hlast : t + 1 = muOf m0
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc6
    refine .done _ (.inr (.inl ⟨⟨hfr6, hout, ?_, ?_, by omega⟩, hpc6⟩))
    · have := htab; rwa [hlast] at this
    · rw [e25, hlast]
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc6
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_12 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b14Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b14Offset) NativeRustcVmArm.Vm.SubspaceTable.label_12_at
    have hlay6' : WordsAt s6.data.dmem (fbOf m0 + BitVec.ofNat 64 16)
        (layerAt (muOf m0) (t + 1)) := by rw [hLd]; exact hlay6
    exact .done _ (.inl ⟨⟨hTn (by omega), e21'', hlay6'⟩, hpc6.trans hl, by omega⟩)

end

end NativeRustcVmArm.Whir.SubspaceTable
