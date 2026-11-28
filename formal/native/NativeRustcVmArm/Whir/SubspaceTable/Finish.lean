module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.SubspaceTable.Outer

/-!
# `subspace_table`'s exits

- `epilogue` (`b24`): the callee-saved registers restored, memory as it was;
- `finish_done` (`b21`, `b22`): the count stored in the table's `Buf`, the `Buf` copied to the
  output after its tag `1` (`memcpy`), the tag;
- `finish_full` (`b23`): tag `0` for `μ = 31` (the table's 32nd root does not fit);
- `finish_big` (`b5`): tag `0` for `μ > 31`.
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region WordAt WordsAt)

public section

theorem outsOf_size : 8 + tableBytes = 512 := rfl

/-- The output apart from the frame. -/
theorem out_apart {m0 : MachineData} (hpre : SubspaceTablePre m0) :
    NativeRustcVm.Apart m0.regs.X0.toBitVec 512 (fbOf m0) 864 :=
  apart_frame hpre.2.2 (by decide) hpre.1.2.1

/-- A byte of the output's first `n` is one of the output's. -/
theorem inAny_out {m0 : MachineData} (hpre : SubspaceTablePre m0) {o n : Nat} (hon : o + n ≤ 512)
    {p : BitVec 64} (h : NativeRustcVm.InRange (m0.regs.X0.toBitVec + BitVec.ofNat 64 o) n p) :
    NativeRustcVm.InAny (outsOf m0) p :=
  ⟨_, List.mem_singleton_self _, NativeRustcVm.InRange.of_sub h hpre.2.1.2 hon⟩

/-- The slots are not the output's. -/
theorem slot_not_out {m0 : MachineData} (hpre : SubspaceTablePre m0) {o n : Nat}
    (hon : o + n ≤ 512) : ∀ q ∈ slots, ∀ i < 8,
      ¬NativeRustcVm.InRange (m0.regs.X0.toBitVec + BitVec.ofNat 64 o) n
        (m0.regs.SP.toBitVec - BitVec.ofNat 64 864 + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i) := by
  intro q hq i hi h
  have hap := out_apart hpre
  have hnw := hpre.2.1.2
  have := slots_le q hq
  rw [addr_add] at h
  exact not_inRange_of_apart hap.symm (frame_ok hpre.1 (by decide)).2.1 hnw
    (by omega : q.1 + i < 864) (NativeRustcVm.InRange.of_sub h hnw hon)

/-- The postcondition after the epilogue, from the body's frame and the output before it. -/
theorem post_of {m0 st s : MachineData} (hfr : Fr m0 st) (hd : s.dmem = st.dmem)
    (hs : Saved m0 s)
    (hv : if m0.regs.X1.toNat ≤ stackCap then
        WordAt st.dmem m0.regs.X0.toBitVec 1 ∧
          BufPairsAt st.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 8) rootCap
            (subspaceTable m0.regs.X1.toNat).toList
      else WordAt st.dmem m0.regs.X0.toBitVec 0) :
    SubspaceTablePost m0 s :=
  ⟨by rw [hd]; exact hv, fun p hp ↦ by rw [hd]; exact hfr.same p hp, hs⟩

variable [Host] {k : Nat}

/-- **The epilogue** (`b24`). -/
theorem epilogue (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 subspaceTableStack)
    {st : MachineData} (hfr : Fr m0 st) :
    Eventually (step1 Host.exe)
      (fun s ↦ s.pc = retOf m0 ∧ s.data.dmem = st.dmem ∧ Saved m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b24Offset)⟩ := by
  have hF : 864 ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, -⟩ := frame_ok hS hF
  have hk : b24.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b24Offset) := b24_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine st [(fbOf m0, 864)]
  have hwf : env.WF := wf_one (hfr.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm : Match env frS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  refine exec_then hk run_b24 hwf hm fun s1 hm1 hpc1 ↦ .done _ ?_
  have hb := after_eq run_b24 ▸ b24_restores
  obtain ⟨hsaved, hx30⟩ := hfr.ret hm1 hwf x30_mem hb.1
  exact ⟨hpc1.trans (by simp only [retOf, hx30]), hm1.dmem_eq hwf hb.2, hsaved⟩

/-- **`μ > 31`** (`b5`): tag `0`. -/
theorem finish_big (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0)
    {st : MachineData} (hfr : Fr m0 st) (hx19 : st.regs.X19 = m0.regs.X0)
    (hmu : 31 < muOf m0) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ SubspaceTablePost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b5Offset)⟩ := by
  have hS := hpre.1
  have hF : 864 ≤ subspaceTableStack := by decide
  have hout := hpre.2.1
  let out := m0.regs.X0.toBitVec
  have hk : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hrd : Readable st out 8 := hfr.readable (Readable.mono hout (by decide))
  let env := Env.ofMachine st [(out, 8)]
  have hwf : env.WF := wf_one hrd.1 hrd.2
  have hm : Match env wordS st := match_one (by
    show st.regs.X19.toBitVec = out + BitVec.ofInt 64 0
    rw [hx19]; simp [out])
  refine exec_then hk run_b5 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb := after_eq run_b5 ▸ b5_keeps
  have hfr1 := hfr.of_block hm hm1 hwf rfl hb.1 (r := 0) rfl le_rfl hb.2
    (fun p h ↦ .inl (inAny_out hpre (o := 0) (n := 8) (by decide)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq i hi h ↦ slot_not_out hpre (o := 0) (n := 8) (by decide) q hq i hi
      (by rw [NativeRustcVm.addr_add_zero]; exact h))
  have hv : WordAt s1.data.dmem out 0 := by
    have := Match.wordAt_write hm1 (r := 0) (o := 0) rfl (by decide) (v := .lit 0) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    exact this
  have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_18 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b24Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b24Offset) NativeRustcVmArm.Vm.SubspaceTable.label_18_at
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b24Offset) := hpc1.trans hl
  obtain ⟨d1, pc1⟩ := s1
  simp only at hpc1'
  subst hpc1'
  refine (epilogue hp hS hfr1).mono fun s ⟨hpc, hd, hs⟩ ↦ ⟨hpc, post_of hfr1 hd hs ?_⟩
  have h : ¬m0.regs.X1.toNat ≤ stackCap := by show ¬muOf m0 ≤ 30; omega
  simp only [h, ↓reduceIte]
  exact hv

/-- **`μ = 31`** (`b23`): tag `0`. -/
theorem finish_full (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0)
    {st : MachineData} (hF : Full m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ SubspaceTablePost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b23Offset)⟩ := by
  have hS := hpre.1
  have hF864 : 864 ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF864
  have hfr := hF.fr
  let out := m0.regs.X0.toBitVec
  let fb := fbOf m0
  have hrd : Readable st out 8 := hfr.readable (Readable.mono hpre.2.1 (by decide))
  have hap : Apart fb 864 out 8 := by
    have := out_apart hpre
    show Apart (fbOf m0) 864 m0.regs.X0.toBitVec 8
    unfold NativeRustcVm.Apart at this
    unfold Apart
    omega
  let env := Env.ofMachine st [(fb, 864), (out, 8)]
  have hwf : env.WF := Env.wf_of ⟨⟨(hfr.readable ⟨hfmap, hfnw⟩).1, hfnw⟩, ⟨hrd.1, hrd.2⟩, trivial⟩
    (List.pairwise_pair.mpr hap)
  have lo : env.load 0 8 8 = out := load_word hF.out
  have hm : Match env noneS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF864 rfl, rfl, fun h ↦ absurd h (by decide),
        trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial
      ⟨by
        show env.load 0 8 8 = out + BitVec.ofInt 64 0
        rw [lo]; simp, trivial⟩
  have hk23 : b23.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b23Offset) := b23_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk24 : b24.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b24Offset) := b24_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk23 run_b23 hwf hm fun s1 hm1 hpc1 ↦ ?_
  refine exec_at hk24 (exec_after run_b23 run_b24') hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ .done _ ?_
  have hb := after_eq run_b24' ▸ b24'_restores
  obtain ⟨hsaved, hx30⟩ := hfr.ret hm2 hwf x30_mem hb.1
  have hsame := same_region hm2 hwf (r := 1) rfl hb.2
  have hv : WordAt s2.data.dmem out 0 := by
    have := Match.wordAt_write hm2 (r := 1) (o := 0) rfl (by decide) (v := .lit 0) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    exact this
  refine ⟨hpc2.trans (by simp only [retOf, hx30]), ?_, fun p hp' ↦ ?_, hsaved⟩
  · have h : ¬m0.regs.X1.toNat ≤ stackCap := by show ¬muOf m0 ≤ 30; rw [hF.hmu]; decide
    simp only [h, ↓reduceIte]
    exact hv
  · rw [hsame p fun h ↦ hp' (.inl (inAny_out hpre (o := 0) (n := 8) (by decide)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))]
    exact hfr.same p hp'

/-- **The table** (`b21`, `b22`): count, copy, tag `1`. -/
theorem finish_done (hp : Placed code k) (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {st : MachineData} (hD : Done m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ SubspaceTablePost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b21Offset)⟩ := by
  have hS := hpre.1
  have hF864 : 864 ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF864
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have hfr := hD.fr
  have hmu := hD.hmu
  let out := m0.regs.X0.toBitVec
  let fb := fbOf m0
  have hapo := out_apart hpre
  have honw : NativeRustcVm.NoWrap m0.regs.X0.toBitVec 512 := hpre.2.1.2
  have htb : tableBytes = 504 := rfl
  -- `b21`: the count, `memcpy`
  have hk21 : b21.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b21Offset) := b21_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine st [(fb, 864)]
  have hwf : env.WF := wf_one (hfr.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm : Match env frS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF864 rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  have lo : env.load 0 8 8 = out := load_word hD.out
  refine exec_then hk21 run_b21 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb21 := after_eq run_b21 ▸ b21_keeps
  have hall : ∀ w ∈ (after b21 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 272 :=
    fun w hw ↦ ⟨(b21_keeps.2 w hw).1, (b21_keeps.2 w hw).2.2⟩
  rw [after_eq run_b21] at hall
  have hfr1 := hfr.of_block hm hm1 hwf rfl hb21.1 (r := 0) rfl (by decide) hall
    (fun p h ↦ .inr (inRange_frame_sub hS hF864 (o := 0) (n := 272) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq i hi ↦ by
      have := not_inRange_slot hS hF864 (o := 0) (n := 272) (by omega) (slots_le q hq) hi
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have h25 : st.regs.X25 = (muOf m0 + 1).toUInt64 :=
    UInt64.toNat.inj (by rw [hD.x25, natCast_toUInt64_toNat (by omega)])
  have hcnt : WordAt s1.data.dmem (fb + BitVec.ofNat 64 264) (muOf m0 + 1).toUInt64 := by
    have := Match.wordAt_write hm1 (r := 0) (o := 264) rfl (by decide) (v := .reg .X25) (by decide)
    convert this using 1
    rw [← h25]
    rfl
  have htl := table_len (m0 := m0) (t := muOf m0) le_rfl
  have htab1 : WordsAt s1.data.dmem (fb + BitVec.ofNat 64 272)
      (pairWords (tableAt (muOf m0) (muOf m0))) :=
    bytesAt_keep hm1 hwf (r := 0) rfl (by rw [htl]; omega)
      (fun w hw ↦ ⟨(hall w hw).1, .inl (hall w hw).2⟩) hD.table
  have hbuf : WordsAt s1.data.dmem (fb + BitVec.ofNat 64 264)
      ((muOf m0 + 1).toUInt64 :: pairWords (tableAt (muOf m0) (muOf m0))) :=
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨hcnt, by rw [addr_add]; exact htab1⟩
  have hx0 : s1.data.regs.X0.toBitVec = out + BitVec.ofNat 64 8 := by
    refine (hm1.regs .X0 _ rfl).trans ?_
    sym_simp
    rw [lo]
  have hx1 : s1.data.regs.X1.toBitVec = fb + BitVec.ofNat 64 264 :=
    (hm1.regs .X1 _ rfl).trans rfl
  have hx2 : s1.data.regs.X2.toNat = 504 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]
    rfl
  have hx19 : s1.data.regs.X19 = m0.regs.X0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans lo)
  have hpre1 : MemcpyPre s1.data := by
    unfold MemcpyPre
    simp only [hx0, hx1, hx2]
    refine ⟨fun i hi ↦ hfr1.kept _ (by rw [addr_add]; exact hpre.2.1.1 _ (by omega)),
      fun i hi ↦ hfr1.kept _ (by rw [addr_add]; exact hfmap _ (by omega)),
      NativeRustcVm.NoWrap.sub honw (by omega), NativeRustcVm.NoWrap.sub hfnw (by omega), ?_⟩
    show Apart (m0.regs.X0.toBitVec + BitVec.ofNat 64 8) 504 (fbOf m0 + BitVec.ofNat 64 264) 504
    unfold NativeRustcVm.Apart at hapo
    unfold NativeRustcVm.NoWrap at honw
    unfold Apart
    rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  refine call_then hpc1 hmemcpy hpre1 fun s2 hpc2 ⟨_, hcopy, hsame2, hsv2⟩ ↦ ?_
  simp only [hx0, hx1, hx2] at hcopy hsame2
  have hfr2 := hfr1.change hsame2 (fun p h ↦ .inl (inAny_out hpre (o := 8) (n := 504) (by decide) h))
    (fun q hq i hi h ↦ slot_not_out hpre (o := 8) (n := 504) (by decide) q hq i hi h)
    (fun r hr _ ↦ hsv2.1 r hr) hsv2.2.1 hsv2.2.2
  -- `b22`: the tag
  have hk22 : b22.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b22Offset) := b22_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b22Offset) := hpc2
  have hrd : Readable s2.data out 8 := hfr2.readable (Readable.mono hpre.2.1 (by decide))
  let env2 := Env.ofMachine s2.data [(out, 8)]
  have hwf2 : env2.WF := wf_one hrd.1 hrd.2
  have hm2 : Match env2 wordS s2.data := match_one (by
    show s2.data.regs.X19.toBitVec = out + BitVec.ofInt 64 0
    rw [show s2.data.regs.X19 = s1.data.regs.X19 from hsv2.1 .X19 rfl, hx19]; simp [out])
  refine exec_at hk22 run_b22 hwf2 hpc2' hm2 fun s3 hm3 hpc3 ↦ ?_
  have hb22 := after_eq run_b22 ▸ b22_keeps
  have hfr3 := hfr2.of_block hm2 hm3 hwf2 rfl hb22.1 (r := 0) rfl le_rfl hb22.2
    (fun p h ↦ .inl (inAny_out hpre (o := 0) (n := 8) (by decide)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq i hi h ↦ slot_not_out hpre (o := 0) (n := 8) (by decide) q hq i hi
      (by rw [NativeRustcVm.addr_add_zero]; exact h))
  have hsame3 := same_region hm3 hwf2 (r := 0) rfl hb22.2
  have hv : WordAt s3.data.dmem out 1 := by
    have := Match.wordAt_write hm3 (r := 0) (o := 0) rfl (by decide) (v := .lit 1) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    exact this
  have hcopy3 : NativeRustcVm.BytesAt s3.data.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 8)
      (bytesOf s1.data.dmem (fbOf m0 + BitVec.ofNat 64 264) 504) := by
    refine NativeRustcVm.BytesAt.of_sameOutside_apart hcopy hsame3 ?_ ?_
      (NativeRustcVm.NoWrap.mono honw (by omega))
    · show NativeRustcVm.Apart _ _ m0.regs.X0.toBitVec 8
      rw [length_bytesOf]
      unfold NativeRustcVm.Apart
      unfold NativeRustcVm.NoWrap at honw
      rw [toNat_add_ofNat' (by omega)]
      omega
    · rw [length_bytesOf]; exact NativeRustcVm.NoWrap.sub honw (by omega)
  have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_18 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b24Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b24Offset) NativeRustcVmArm.Vm.SubspaceTable.label_18_at
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b24Offset) := hpc3.trans hl
  obtain ⟨d3, pc3⟩ := s3
  simp only at hpc3'
  subst hpc3'
  refine (epilogue hp hS hfr3).mono fun s ⟨hpc, hd, hs⟩ ↦ ⟨hpc, post_of hfr3 hd hs ?_⟩
  have h : m0.regs.X1.toNat ≤ stackCap := hmu
  simp only [h, ↓reduceIte]
  refine ⟨hv, ?_⟩
  -- the copied `Buf`
  have hlen : (((muOf m0 + 1).toUInt64 :: pairWords (tableAt (muOf m0) (muOf m0))).flatMap
      NativeRustcVm.wordBytes).length = 8 + 16 * (muOf m0 + 1) := by
    rw [NativeRustcVm.length_wordsBytes, List.length_cons, pairWords_length',
      tableAt_length le_rfl]
    omega
  have hb := NativeRustcVm.BytesAt.take hcopy3 (8 + 16 * (muOf m0 + 1))
  rw [bytesOf_take _ _ (by omega), ← hlen, NativeRustcVmArm.bytesOf_eq hbuf] at hb
  have hw := NativeRustcVm.wordsAt_cons_iff.mp (show WordsAt d3.dmem _ _ from hb)
  have htl' : (subspaceTable (muOf m0)).toList.length = muOf m0 + 1 := by
    rw [subspaceTable_toList, tableAt_length le_rfl]
  refine ⟨by rw [show m0.regs.X1.toNat = muOf m0 from rfl, htl']; show muOf m0 + 1 ≤ 31; omega,
    ?_, ?_⟩
  · rw [show m0.regs.X1.toNat = muOf m0 from rfl, htl']
    exact hw.1
  · rw [show m0.regs.X1.toNat = muOf m0 from rfl, subspaceTable_toList]
    exact hw.2

end

end NativeRustcVmArm.Whir.SubspaceTable
