module

public import NativeRustcVmX64.Tables.TablePhase.Steps
public import NativeRustcVmX64.Code.Vm.TableSumcheck.Names

/-!
# `table_phase`: the table sumcheck and the exit (x86-64)

From `b6` (the target in RAX, RDX, `ξ`'s powers at the frame's offset `32`): `table_sumcheck`'s
arguments (`b6`, the target's high limb and the evaluations pushed), the call, `b7` and the exit
(`tail6`).
-/

namespace NativeRustcVmX64.Tables.TablePhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Vm.TablePhase
open NativeRustcVmX64.Bus.Gkr (Fr)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)
open NativeRustcVm.Layout (LayoutWAt layoutBytes Same)
open NativeRustcVm.Bus (BusWAt busBytes)
open NativeRustcVm (wordOf)

public section

/-- **Part of an input**: `k` bytes at offset `o`. -/
theorem ReadIn.sub {m : MachineData} {x : BitVec 64} {n N : Nat} {ws : List NativeRustcVm.Region}
    (h : ReadIn m x n N ws) {o k : Nat} (hk : o < n) (hok : o + k ≤ n) :
    ReadIn m (x + BitVec.ofNat 64 o) k N ws := by
  obtain ⟨⟨hm, hnw⟩, hst, hws⟩ := h
  unfold NoWrap at hnw
  have e : (x + BitVec.ofNat 64 o).toNat = x.toNat + o := NativeRustcVm.toNat_add_ofNat (by omega)
  refine ⟨⟨fun i hi ↦ ?_, by unfold NoWrap; rw [e]; omega⟩, ?_, fun w hw ↦ ?_⟩
  · rw [NativeRustcVm.addr_add_add]; exact hm _ (by omega)
  · have := hst; unfold OffStack Apart at this ⊢; rw [e]; omega
  · have := hws w hw; unfold Apart at this ⊢; rw [e]; omega

theorem ewsOf_take {d : DataMem} {x : BitVec 64} {xs : List EW} (h : NativeRustcVm.EWsAt d x xs)
    {j : Nat} (hj : j ≤ xs.length) : NativeRustcVm.ewsOf d x j = xs.take j := by
  have := NativeRustcVm.ewsOf_of_ewsAt (h.take j)
  rwa [List.length_take, Nat.min_eq_left hj] at this

section
variable [Labels] {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} {m0 : MachineData}

/-- **A local of the frame from offset `8`** as an input of a callee at the frame's base. -/
theorem local_in (h : TablePhasePre a s L bus m0) {d : MachineData} (hat : At m0 160 d) {Nc : Nat}
    (hle : 160 + Nc ≤ N) {o n : Nat} (ho : 8 ≤ o) (hon : o + n ≤ 160) :
    ReadIn d (off (stackBelow m0 160) o) n Nc (wsOf m0) := by
  have c := ctx h N_ge
  have hO := c.outOk_frame hat hle ho hon
  refine ⟨⟨hO.1, hO.2.1⟩, hO.2.2.2.2.1, fun w hw ↦ ?_⟩
  simp only [wsOf, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact hO.2.2.1
  · exact Apart.symm' (c.apart_of_stack (pre_parts h).2.2.2.2.2.1.2.2.2.2.1 hon)

/-- A frame byte at offset `j ≥ L` a block writing below `L` did not write. -/
theorem keep_hi {d d' : MachineData} {S : SState} {ret : BitVec 64}
    (hwf : (frameEnv m0 d 160 [] (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 160 [] (fun _ ↦ 0) ret) S d') (hin : writesIn S = true) {L : Nat}
    (hw : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ L) {j : Nat} (hLj : L ≤ j) (hj : j < 168) :
    d'.dmem.get? (off (stackBelow m0 160) j) = d.dmem.get? (off (stackBelow m0 160) j) :=
  hm.get?_mem0 hwf (not_written0 hwf hm hin hj fun w hw' hr ↦ .inl (by have := hw w hw' hr; omega))

end

variable [Host] {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} {m0 : MachineData}
  {k : Nat}

/-- **The table sumcheck and the exit**, from `b6`. -/
theorem tail6 (hp : Placed code k)
    (hsum : ∀ a s heights bus, Spec (Labels.label NativeRustcVmX64.Vm.TableSumcheck.entryLabel)
      (TableSumcheckPre a s heights bus) (TableSumcheckPost a s heights bus))
    (h : TablePhasePre a s L bus m0) {s1 : TState}
    (hg : (grind (grindingBits 4)).run s = some ((), s1)) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b6Offset)) (fr : St m0 24 st.data)
    (r12 : reg st.data .r12 = reg m0 .rdi) (r15 : reg st.data .r15 = reg m0 .rsi)
    (r14 : reg st.data .r14 = reg m0 .rdx) (rbx : reg st.data .rbx = reg m0 .rcx)
    (rbp : reg st.data .rbp = off (stackBelow m0 160) 32)
    (r13 : reg st.data .r13 = off (stackBelow m0 160) 64)
    (hpw : NativeRustcVm.EWsAt st.data.dmem (off (stackBelow m0 160) 32)
      (powers s1.sponge.squeeze.1 5).toList)
    (htg : ewRet st.data = dot ((powers s1.sponge.squeeze.1 5).extract 2 5) bus.totals)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a { s1 with sponge := s1.sponge.squeeze.2 }) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      TablePhasePost a s L bus m0 st'.data) st := by
  have p := pre_parts h
  have hS := p.1
  have c := ctx h N_ge
  set P := powers s1.sponge.squeeze.1 5 with hPdef
  have hP5 : P.size = 5 := size_powers _ _
  set s2 : TState := { s1 with sponge := s1.sponge.squeeze.2 }
  obtain ⟨hmid, h0, hw6, hregs, hw8, hw16⟩ := after_eq run_b6 ▸ ok_b6
  refine blk h fr (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hmid h0 hpc
    fun st1 fr1 hm1 hs1 hpc1 ↦ ?_
  have hwf := wfF h fr (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b6Offset + b6.length)).toBitVec)
  have gr : ∀ r v, (r, v) ∈ ([(.rdi, .reg .r12), (.rsi, .bin .add .W64 (.lit 24) (.reg .r15)),
      (.rdx, .reg .r14), (.rcx, .reg .rbp), (.r8, .reg .r13), (.r9, .reg .rax)] :
        List (Reg64 × Sym)) → reg st1.data r = v.eval (frameEnv m0 st.data 160 [] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b6Offset + b6.length)).toBitVec) := fun r v hr ↦ hm1.regs r v (hregs _ hr)
  have e1di : reg st1.data .rdi = reg m0 .rdi := (gr .rdi (.reg .r12) (by simp)).trans r12
  have e1si : reg st1.data .rsi = reg m0 .rsi + BitVec.ofNat 64 24 := by
    rw [gr .rsi (.bin .add .W64 (.lit 24) (.reg .r15)) (by simp)]
    simp only [Sym.eval, NativeRustcVmX64.Arrays.add_eval]
    show BitVec.ofNat 64 24 + reg st.data .r15 = _
    rw [r15, BitVec.add_comm]
  have e1dx : reg st1.data .rdx = reg m0 .rdx := (gr .rdx (.reg .r14) (by simp)).trans r14
  have e1cx : reg st1.data .rcx = off (stackBelow m0 160) 32 := (gr .rcx (.reg .rbp) (by simp)).trans rbp
  have e18 : reg st1.data .r8 = off (stackBelow m0 160) 64 := (gr .r8 (.reg .r13) (by simp)).trans r13
  have e19 : reg st1.data .r9 = reg st.data .rax := gr .r9 (.reg .rax) (by simp)
  have hsp1 : rspOf st1.data = stackBelow m0 160 := by rw [fr1.frame.sp, off_zero]
  -- the two stack arguments
  have hsa0 : stackArg st1.data 0 = reg st.data .rdx := by
    unfold stackArg; rw [hsp1]
    have := wordAt_write hm1 (r := 0) (o := 8) rfl (by omega) hw8
    rw [show stackBelow m0 160 + BitVec.ofNat 64 (8 + 8 * 0) = off (stackBelow m0 160) 8 from rfl,
      NativeRustcVm.wordOf_of_wordAt this]
    rfl
  have hsa1 : stackArg st1.data 1 = reg m0 .rcx := by
    unfold stackArg; rw [hsp1]
    have := wordAt_write hm1 (r := 0) (o := 16) rfl (by omega) hw16
    rw [show stackBelow m0 160 + BitVec.ofNat 64 (8 + 8 * 1) = off (stackBelow m0 160) 16 from rfl,
      NativeRustcVm.wordOf_of_wordAt this]
    exact rbx
  -- the callee's facts
  have hle_s : 160 - 0 + tableSumcheckStack ≤ N := by decide
  have hat := at_call h fr1 (by omega)
  rw [Nat.sub_zero] at hat
  have hk1 : Kept st.data.dmem st1.data.dmem := hm1.kept hwf
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s2 :=
    tstate_keep h hts hk1 hs1 fun q hq ↦ .inl (frame_in h hq)
  have hloc : ∀ j < 112, 32 ≤ j → st1.data.dmem.get? (off (stackBelow m0 160) j) =
      st.data.dmem.get? (off (stackBelow m0 160) j) := fun j hj hj' ↦
    keep_hi hwf hm1 (writesIn_of_mid hmid) (L := 24) (fun w hw _ ↦ hw6 w hw) (by omega) (by omega)
  have hpw1 : NativeRustcVm.EWsAt st1.data.dmem (off (stackBelow m0 160) 32) P.toList :=
    NativeRustcVmX64.Arrays.ewsAt_congr hpw fun j hj ↦ by
      rw [off_add]; exact hloc _ (by simp [hP5] at hj; omega) (by omega)
  have hcp : arrE st1.data (reg st1.data .rcx) 2 = P.extract 0 2 := by
    unfold arrE; rw [e1cx, ewsOf_take hpw1 (by simp [hP5]), extract_take]
  have hfp : arrE st1.data (reg st1.data .r8) 3 = P.extract 2 5 := by
    unfold arrE
    have hd := hpw1.drop 2
    rw [off_add] at hd
    rw [e18, ewsOf_take hd (by simp [hP5]), List.take_of_length_le (by simp [hP5]),
      extract_drop hP5]
  have htarget : ewArg (reg st1.data .r9) (stackArg st1.data 0) =
      dot (P.extract 2 5) bus.totals := by
    rw [e19, hsa0]; exact htg
  have hrun : (tablePhase L bus).run s = (tableSumcheck L.tableLogHeights bus.forms
      (arrE st1.data (reg st1.data .rcx) 2) (arrE st1.data (reg st1.data .r8) 3) bus.point
      (ewArg (reg st1.data .r9) (stackArg st1.data 0))).run s2 := by
    rw [hcp, hfp, htarget, tablePhase_run, hg]; rfl
  have hL1 : LayoutWAt st1.data.dmem (reg m0 .rsi) L :=
    NativeRustcVm.Tables.LayoutWAt.of_same p.2.2.2.2.2.2.2.2.2.1 (same_in h fr1 p.2.2.2.2.2.2.2.2.1)
  have hB1 : BusWAt st1.data.dmem (reg m0 .rdx) bus :=
    NativeRustcVm.Tables.BusWAt.of_same p.2.2.2.2.2.2.2.2.2.2.2 (same_in h fr1 p.2.2.2.2.2.2.2.2.2.2.1)
  have hpre1 : TableSumcheckPre a s2 L.tableLogHeights bus st1.data := by
    have hfrm := frame_mapped hS N_ge
    have hfnw := frame_noWrap hS N_ge
    unfold NativeRustcVm.NoWrap at hfnw
    have hfb := stackBelow_toNat (m := m0) (n := 160) (by have := hS.1; omega)
    refine ⟨c.stackOk hat (by decide), c.rcAt hat (by decide), rodata_call h fr1 (by omega) hle_s,
      ⟨fun i hi ↦ ?_, ?_⟩, by rw [e1di]; exact hts1, by rw [e1di]; exact c.tstateOk hat (by decide),
      by rw [e1di, hsa1]; exact c.outOk hat (by decide) p.2.2.2.2.2.1, ?_, ?_,
      by rw [e1di]; exact p.2.2.2.2.2.2.1, by rw [hsa1]; exact p.2.2.2.2.2.2.2.1, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [hsp1, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
      exact hk1 _ (fr.frame.kept _ (hfrm (8 + i) (by omega)))
    · rw [hsp1, hfb]; omega
    · rw [e1di, hsp1, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
      exact c.apart_of_stack p.2.2.2.2.1.1 (o := 8) (k := 16) (by omega)
    · rw [hsa1, hsp1, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
      exact c.apart_of_stack p.2.2.2.2.2.1.2.2.2.2.1 (o := 8) (k := 16) (by omega)
    · rw [e1di, hsa1, e1si]
      exact readIn_call h fr1 (by omega) hle_s (ReadIn.sub p.2.2.2.2.2.2.2.2.1 (by decide) (by decide))
    · rw [e1si]
      have := hL1.heightsAt
      rwa [show off (reg m0 .rsi) 24 = reg m0 .rsi + BitVec.ofNat 64 24 from rfl] at this
    · rw [e1di, hsa1, e1dx]; exact readIn_call h fr1 (by omega) hle_s p.2.2.2.2.2.2.2.2.2.2.1
    · rw [e1dx]; exact hB1
    · rw [e1di, hsa1, e1cx]; exact local_in h hat (by decide) (by omega) (by omega)
    · rw [e1di, hsa1, e18]; exact local_in h hat (by decide) (by omega) (by omega)
    · rw [e1di, hsa1, hsp1, e1si, e1dx, e1cx, e18]
      refine got_call h fr1 (by omega) hle_s ?_
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ((got h).1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp)
      · exact ((got h).1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
      · exact ((got h).1 l hl).2.2.2 (reg m0 .rcx, tableEvalsBytes) (by simp)
      · exact got_apart_frame (got h) hS hl (ob := 8) (len := 16) N_ge (by decide)
      · change Apart (gotAddr l) 8 (reg m0 .rsi + BitVec.ofNat 64 24) 48
        have hn : (reg m0 .rsi).toNat + layoutBytes ≤ 2 ^ 64 :=
          p.2.2.2.2.2.2.2.2.1.1.2
        have he : (reg m0 .rsi + BitVec.ofNat 64 24).toNat = (reg m0 .rsi).toNat + 24 :=
          NativeRustcVm.toNat_add_ofNat (by
            have hsize : 24 < layoutBytes := by decide
            omega)
        have hg : Apart (gotAddr l) 8 (reg m0 .rsi) layoutBytes :=
          ((got h).1 l hl).2.2.2 (reg m0 .rsi, layoutBytes) (by simp)
        refine Apart.sub hg ?_ ?_
        · rw [he]; omega
        · rw [he]
          have hsize : 24 + 48 ≤ layoutBytes := by decide
          omega
      · exact ((got h).1 l hl).2.2.2 (reg m0 .rdx, busBytes) (by simp)
      · exact got_apart_frame (got h) hS hl (ob := 32) (len := 32) N_ge (by decide)
      · exact got_apart_frame (got h) hS hl (ob := 64) (len := 48) N_ge (by decide)
      · exact ((got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
      · exact ((got h).1 l hl).2.2.2
          (rodataAddr .tables, NativeRustcVm.Data.Item.tables.bytes.length) (by simp)
  -- the call
  refine Fr.call hS N_ge (c := 0) (lo := 0) (len := 0) (by omega) hle_s
    (fun p hp ↦ by have := slots_le p hp; have := (show ∀ p ∈ slots, 112 ≤ p.1 by decide) p hp; omega)
    (by omega) (fun q hq ↦ outs_not_frame h hq) (X := outs m0) (fun q hq ↦ .inl hq)
    (hsum a s2 L.tableLogHeights bus) fr1 hpc1 hpre1
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ by
      rw [e1di, hsa1] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr hq')
      · exact .inl hq', hq.2.2.2.2⟩)
    fun m2 fr2 hq2 _ _ ↦ ?_
  obtain ⟨q0, q1, q2, -, -⟩ := hq2
  rw [← hrun] at q0 q1 q2
  rw [hsa1] at q1
  rw [e1di] at q2
  -- `b7`, the exit
  obtain ⟨hmid7, hmem7, hr7⟩ := after_eq run_b7 ▸ ok_b7
  refine blk h fr2 (st := ⟨m2, _⟩) (b7_in_code.trans hp.1 (by simp [b7])) run_b7 hmid7
    (by rw [hmem7]; intro w hw; cases hw) rfl fun st3 fr3 hm3 _ hpc3 ↦ ?_
  have hd3 : st3.data.dmem = m2.dmem :=
    hm3.dmem_eq (wfF h fr2 (vars := fun _ ↦ 0) (ret := _)) hmem7
  refine exit8 hp h (by simp only [PcOk, NativeRustcVmX64.Vm.TablePhase.b7_length] at hpc3; exact hpc3) fr3 ?_ (fun x s' hr ↦ by rw [hd3]; exact q1 x s' hr)
    (fun x s' hr ↦ by rw [hd3]; exact q2 x s' hr)
  rw [show reg st3.data .rbp = _ from hm3.regs _ _ (hr7 (.rbp, .un .trunc .W32 (.reg .rax)) (by simp))]
  exact (NativeRustcVmX64.Transcript.trunc32_mod _).trans q0

end

end NativeRustcVmX64.Tables.TablePhase
