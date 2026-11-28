module

public import NativeRustcVmX64.Whir.SubspaceTable.Push
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `subspace_table`'s exits (x86-64)

- `epi` (`b24`): the epilogue returns with the entry's callee-saved registers and the body's
  memory, which holds the result (`Res`);
- `big`: `μ ≥ 32` (`b5` stored tag `0`);
- `finish_none` (`b23`): tag `0` at turn `30` (`μ = 31`);
- `finish_done` (`b21`, `b22`): the table's length stored in its `Buf`, the `Buf` copied after the
  output's tag (`memcpy`), tag `1`.
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt wordOf)
open NativeRustcVmX64.Field (midS frameS frameEnv frame_wf match_frame)
open NativeRustcVmX64.Arrays (stackOk_mono load8_eq load_word wordAt_of_write eval_reg eval_lit
  eval_load eval_add apart_symm not_inRange_of_apart written_region0)

@[expose] public section

/-- The result in memory: tag `1` and the table for `μ ≤ 30`, else tag `0`. -/
def Res (m0 : MachineData) (d : DataMem) : Prop :=
  if muOf m0 ≤ 30 then
    WordAt d (reg m0 .rdi) 1 ∧
      BufPairsAt d (reg m0 .rdi + BitVec.ofNat 64 8) rootCap (subspaceTable (muOf m0)).toList
  else WordAt d (reg m0 .rdi) 0

end

public section

/-- `subspace_table`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ SubspaceTablePost m0 s.data

theorem res_none {m0 : MachineData} {d : DataMem} (h : 30 < muOf m0) (hw : WordAt d (reg m0 .rdi) 0) :
    Res m0 d := by
  unfold Res
  simp only [show ¬muOf m0 ≤ 30 by omega, ↓reduceIte]
  exact hw

/-- The output's slot `i` of its first `8` is not a slot of the frame. -/
theorem slot_not_out [Labels] {m0 : MachineData} (hpre : SubspaceTablePre m0) :
    ∀ q ∈ slots, ∀ i < 8, ¬InRange (reg m0 .rdi) 8
      (stackBelow m0 848 + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i) := by
  obtain ⟨hS, hout, _⟩ := hpre
  obtain ⟨hF, -, -, -⟩ := stack_le
  have hsl := slots_ok
  intro q hq i hi
  rw [addr_add]
  exact not_inRange_of_apart (Arrays.apart_mono (apart_symm (apart_frame' hS hF hout.2))
    (n'' := 8) (by omega)) (frame_ok hS hF).2.1
    (NativeRustcVm.NoWrap.mono hout.1.2 (by omega)) (by have := hsl q hq; omega)

/-- The output's first `8` bytes are the output's. -/
theorem out_tag [Labels] {m0 : MachineData} (hpre : SubspaceTablePre m0) :
    ∀ p, InRange (reg m0 .rdi) 8 p →
      NativeRustcVm.InAny (outsOf m0) p ∨ InRange (stackBelow m0 subspaceTableStack)
        subspaceTableStack p :=
  fun _ h ↦ .inl (inAny_one (Arrays.inRange_sub hpre.2.1.1.2 (c := 0) (m := 8) (by decide)
    (by rwa [NativeRustcVm.addr_add_zero])))

variable [Host] {k : Nat}

theorem hb21 (hp : Placed code k) : b21.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b21Offset) :=
  b21_in_code.trans hp.1 (by simp [b21])
theorem hb22 (hp : Placed code k) : b22.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b22Offset) :=
  b22_in_code.trans hp.1 (by simp [b22])
theorem hb24 (hp : Placed code k) : b24.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.SubspaceTable.b24Offset) :=
  b24_in_code.trans hp.1 (by simp [b24])

/-- **The epilogue** (`b24`). -/
theorem epi (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b24Offset)) (hfr : Fr m0 st.data)
    (hv : Res m0 st.data.dmem) : Eventually (step1 Host.exe) (Post m0) st := by
  obtain ⟨hS, hout, _⟩ := hpre
  obtain ⟨hF, -, -, -⟩ := stack_le
  have hwf := hfr.wf (vars := fun _ ↦ 0) (ret := 0) hS hF
  refine exec_at (hb24 hp) run_b24 hwf (by intro l h; cases h) hpc hfr.mid_match
    fun st1 hm1 hpc1 ↦ .done _ ?_
  obtain ⟨hpc', hrsp', hdm, hsaved⟩ := hfr.done hS hF (out_one hout) hm1 hpc1
    (after_eq run_b24 ▸ b24_restores).1 (after_eq run_b24 ▸ b24_restores).2
  exact ⟨hpc', hrsp', by rw [hdm]; exact hv, fun p hp ↦ by rw [hdm]; exact hfr.same p hp, hsaved⟩

/-- **`μ ≥ 32`**: tag `0` stored, the epilogue. -/
theorem big (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b24Offset)) (hfr : Fr m0 st.data)
    (hw : WordAt st.data.dmem (reg m0 .rdi) 0) (hbig : 32 ≤ muOf m0) :
    Eventually (step1 Host.exe) (Post m0) st :=
  epi hp hpre hpc hfr (res_none (by omega) hw)

/-- **Turn `30`** (`b23`): tag `0`. -/
theorem finish_none (hp : Placed code k) {m0 : MachineData} (hpre : SubspaceTablePre m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b23Offset)) (hN : NoneAt m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hpre' := hpre
  obtain ⟨hS, hout, _⟩ := hpre'
  obtain ⟨hF, -, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hN.fr
  have hap : NativeRustcVm.Apart (stackBelow m0 848) 856 (reg m0 .rdi) 512 :=
    apart_symm (apart_frame' hS hF hout.2)
  have hrd0 : Readable st.data (fbOf m0) 16 :=
    Readable.keep (Readable.mono (m := m0) ⟨hfmap, hfnw⟩ (by omega)) hfr.kept
  have hrd1 : Readable st.data (reg m0 .rdi) 8 :=
    Readable.keep (Readable.mono hout.1 (by decide)) hfr.kept
  let env := Env.ofMachine st.data [(fbOf m0, 16), (reg m0 .rdi, 8)] (fun _ ↦ 0) 0
  have hwf : env.WF := Env.wf_of ⟨⟨hrd0.1, hrd0.2⟩, ⟨hrd1.1, hrd1.2⟩, trivial⟩
    (List.pairwise_pair.mpr (by
      show (fbOf m0).toNat + 16 ≤ (reg m0 .rdi).toNat ∨ (reg m0 .rdi).toNat + 8 ≤ (fbOf m0).toNat
      unfold NativeRustcVm.Apart at hap
      unfold fbOf
      omega))
  have hl8 : env.load 0 8 8 = reg m0 .rdi :=
    load_word (show WordAt st.data.dmem (fbOf m0 + BitVec.ofNat 64 8) _ from hN.out)
  have hm : Match env noneS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hfr.rsp, trivial⟩ trivial trivial ⟨by
      show env.load 0 8 8 = reg m0 .rdi + 0#64
      rw [hl8, BitVec.add_zero], trivial⟩
  refine exec_at (hb23 hp) run_b23 hwf (by intro l h; cases h) hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨⟨hk1, hw1⟩, hv1⟩ := after_eq run_b23 ▸ b23_write
  have hfr1 : Fr m0 st1.data := hfr.of_write hm hm1 hwf rfl hk1 (r := 1) rfl le_rfl hw1
    (out_tag hpre) (slot_not_out hpre)
  have htag := wordAt_of_write hm1 (r := 1) (o := 0) rfl (by decide) hv1
  rw [NativeRustcVm.addr_add_zero] at htag
  exact epi hp hpre (show st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b24Offset) from hpc1) hfr1 (res_none hN.hmu htag)

/-- **The table** (`b21`, `b22`): the length, the copy, tag `1`. -/
theorem finish_done (hp : Placed code k) (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 : MachineData} (hpre : SubspaceTablePre m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b21Offset)) (hD : Done m0 st.data) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hpre' := hpre
  obtain ⟨hS, hout, hgot⟩ := hpre'
  obtain ⟨hF, -, -, -⟩ := stack_le
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hsl := slots_ok
  have hfr := hD.fr
  have hmu := hD.hmu
  have htb : tableBytes = 504 := rfl
  have hap : NativeRustcVm.Apart (reg m0 .rdi) 512 (stackBelow m0 848) 856 := apart_frame' hS hF hout.2
  have honw : NativeRustcVm.NoWrap (reg m0 .rdi) 512 := hout.1.2
  unfold NativeRustcVm.Apart at hap
  unfold NativeRustcVm.NoWrap at honw
  have hpl := pairWords_len (tableAt (muOf m0) (muOf m0))
  rw [tableAt_len' le_rfl] at hpl
  -- `b21`: the length, `memcpy`
  have hwf := hfr.got_wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b22Offset)).toBitVec) hS hF hgot (by simp : "memcpy" ∈ _)
  have hmcopy := hfr.got_match (l := "memcpy") (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b22Offset)).toBitVec)
    (fun i hi => hfr.got_byte hS hgot
    (by intro ar har; simp only [List.mem_singleton] at har; subst ar; exact hout.1.2)
    (by intro r hr; simp only [outsOf, List.mem_singleton] at hr; subst r; simp)
    (by simp) hi)
  refine exec_at (hb21 hp) run_b21 hwf (fun _ _ ↦ rfl) hpc hmcopy fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨⟨hk1, hsp1, hw1⟩, hw1', hv48⟩ := after_eq run_b21 ▸ b21_call
  have hrsp1 := rsp_call hm1 hsp1
  have hkept1 : Kept m0.dmem st1.data.dmem := fun p h ↦ hm1.kept hwf p (hfr.kept p h)
  have hl8 : (gotEnv m0 st.data 848 "memcpy" (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b22Offset)).toBitVec).load 0 8 8 =
      reg m0 .rdi :=
    load_word (show WordAt st.data.dmem (stackBelow m0 848 + BitVec.ofNat 64 8) _ from hD.out)
  have hcnt : WordAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 48) (muOf m0 + 1).toUInt64 := by
    have := wordAt_of_write hm1 (r := 0) (o := 48) rfl (by decide) hv48
    rw [eval_reg, gotEnv_regs, hD.r12] at this
    exact this
  have htab1 : WordsAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 56)
      (pairWords (tableAt (muOf m0) (muOf m0))) :=
    bytesAt_block hm1 hwf rfl (by rw [hpl]; omega)
      (fun w hw ↦ ⟨(hw1 w hw).1, by have := hw1' w hw; have := (hw1 w hw).2; omega⟩) hD.table
  have hbuf : WordsAt st1.data.dmem (fbOf m0 + BitVec.ofNat 64 48)
      ((muOf m0 + 1).toUInt64 :: pairWords (tableAt (muOf m0) (muOf m0))) :=
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨hcnt, by rw [addr_add]; exact htab1⟩
  have hrdi : reg st1.data .rdi = reg m0 .rdi + BitVec.ofNat 64 8 := by
    refine (hm1.regs .rdi _ rfl).trans ?_
    rw [eval_add, eval_load, eval_lit, hl8]
  have hrsi : reg st1.data .rsi = fbOf m0 + BitVec.ofNat 64 48 :=
    (hm1.regs .rsi _ rfl).trans (gotEnv_ptr 48)
  have hrdx : (reg st1.data .rdx).toNat = 504 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ rfl]; rfl
  have hrbx : reg st1.data .rbx = reg m0 .rdi := (hm1.regs .rbx _ rfl).trans hl8
  have h8 : (reg m0 .rdi + BitVec.ofNat 64 8).toNat = (reg m0 .rdi).toNat + 8 :=
    toNat_add_ofNat _ _ (by omega)
  have h48 : (fbOf m0 + BitVec.ofNat 64 48).toNat = (rspOf m0).toNat - 848 + 48 :=
    fb_toNat hS hF (by omega)
  have hfb : (stackBelow m0 848).toNat = (rspOf m0).toNat - 848 := hfe
  have hpre1 : MemcpyPre st1.data := by
    unfold MemcpyPre
    simp only [hrdi, hrsi, hrdx]
    refine ⟨stackOk_callee hS hkept1 hrsp1 (by decide), fun i hi ↦ ?_, fun i hi ↦ ?_, ?_, ?_, ?_,
      ?_⟩
    · rw [addr_add]; exact hkept1 _ (hout.1.1 _ (by omega))
    · rw [fbOf, addr_add]; exact hkept1 _ (hfmap _ (by omega))
    · unfold NoWrap; rw [h8]; omega
    · unfold NoWrap; rw [h48]; omega
    · unfold Apart; rw [h8, h48]; omega
    · unfold Apart; rw [h8, hrsp1, hfb]; omega
  refine Frame.call hmemcpy hfr hS (by decide : 848 + 0 ≤ subspaceTableStack) (L := 56)
    (by decide) (fun p hp ↦ ⟨by have := (hsl p hp).1; omega, (hsl p hp).2⟩) (out_one hout) hwf
    hmcopy hm1 hpc1 hk1 hsp1 hw1 hpre1
    (fun m' ⟨_, _, hso, hsv⟩ ↦ ⟨hsv, fun p hp ↦ hso p fun h ↦ hp (.inl (by
      simp only [hrdi, hrdx] at h
      exact inAny_one (Arrays.inRange_sub hout.1.2 (c := 8) (m := 504) (by omega) h)))⟩)
    fun st2 hpc2 hfr2 ⟨_, hcopy, _, hsv2⟩ ↦ ?_
  simp only [hrdi, hrsi, hrdx] at hcopy
  -- `b22`: tag `1`
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SubspaceTable.b22Offset) := hpc2
  have hrbx2 : reg st2.data .rbx = reg m0 .rdi := (hsv2.1 .rbx rfl).trans hrbx
  have hrd : Readable st2.data (reg m0 .rdi) 8 :=
    Readable.keep (Readable.mono hout.1 (by decide)) hfr2.kept
  have hwf2 : (Env.ofMachine st2.data [(reg m0 .rdi, 8)]).WF :=
    Env.wf_of ⟨⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm2 : Match (Env.ofMachine st2.data [(reg m0 .rdi, 8)]) outS st2.data :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show reg st2.data .rbx = reg m0 .rdi + BitVec.ofInt 64 0 by
          rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
          exact hrbx2, trivial⟩
      trivial trivial trivial
  refine exec_at (hb22 hp) run_b22 hwf2 (by intro l h; cases h) hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨⟨hk3, hw3⟩, hv3⟩ := after_eq run_b22 ▸ b22_write
  have hfr3 : Fr m0 st3.data := hfr2.of_write hm2 hm3 hwf2 rfl hk3 (r := 0) rfl le_rfl hw3
    (out_tag hpre) (slot_not_out hpre)
  have htag := wordAt_of_write hm3 (r := 0) (o := 0) rfl (by decide) hv3
  rw [NativeRustcVm.addr_add_zero, eval_lit] at htag
  have hcopy3 : NativeRustcVm.BytesAt st3.data.dmem (reg m0 .rdi + BitVec.ofNat 64 8)
      (bytesOf st1.data.dmem (fbOf m0 + BitVec.ofNat 64 48) 504) := by
    refine NativeRustcVm.BytesAt.of_sameOutside_apart hcopy
      (same_region_le hm3 hwf2 (r := 0) rfl le_rfl hw3) ?_ ?_ ?_
    · rw [length_bytesOf]; unfold NativeRustcVm.Apart; rw [h8]; omega
    · rw [length_bytesOf]; unfold NativeRustcVm.NoWrap; rw [h8]; omega
    · unfold NativeRustcVm.NoWrap; omega
  simp only [PcOk] at hpc3
  refine epi hp hpre (hpc3.trans (hp.label NativeRustcVmX64.Vm.SubspaceTable.label_2_at)) hfr3 ?_
  unfold Res
  simp only [hmu, ↓reduceIte]
  have hlen : (((muOf m0 + 1).toUInt64 :: pairWords (tableAt (muOf m0) (muOf m0))).flatMap
      NativeRustcVm.wordBytes).length = 8 + 16 * (muOf m0 + 1) := by
    rw [NativeRustcVm.length_wordsBytes, List.length_cons, pairWords_length',
      tableAt_length le_rfl]
    omega
  have hb := NativeRustcVm.BytesAt.take hcopy3 (8 + 16 * (muOf m0 + 1))
  rw [bytesOf_take _ _ (by omega), ← hlen, NativeRustcVmX64.bytesOf_eq hbuf] at hb
  have hw := NativeRustcVm.wordsAt_cons_iff.mp (show WordsAt st3.data.dmem
    (reg m0 .rdi + BitVec.ofNat 64 8) _ from hb)
  have htl : (subspaceTable (muOf m0)).toList.length = muOf m0 + 1 := by
    rw [subspaceTable_toList, tableAt_length le_rfl]
  refine ⟨htag, ?_, ?_, ?_⟩
  · rw [htl]; unfold rootCap; omega
  · rw [htl]; exact hw.1
  · rw [subspaceTable_toList]; exact hw.2

end

end NativeRustcVmX64.Whir.SubspaceTable
