module

public import NativeRustcVmX64.Layout.ReadAnnouncedSizes.Body

/-!
# `read_announced_sizes` after `build_layout` (x86-64)

`from12`: `b12` returns `0` (`b14`) on `build_layout`'s `None`; `b13` sets RAX to the stack's
log-size check (the layout's word `16`, `ax13_eval`) and jumps to the epilogue, which returns the
rate (R15) in RDX.
-/

namespace NativeRustcVmX64.Layout.ReadAnnouncedSizes

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReadAnnouncedSizes NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript NativeRustcVmX64.Transcript
open NativeRustcVmX64.Tables.Body NativeRustcVmX64.Sumcheck
open NativeVm.Math.Layout (lmA rowsA rateA ite_true_of ite_false_of)

public section

variable [Host] {k : Nat} {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}

/-- The layout's first 24 bytes, a region beside the frame. -/
theorem wf_lay (h : ReadAnnouncedSizesPre bc a s m0) {d : MachineData} (hk : Kept m0.dmem d.dmem) :
    (frameEnv m0 d 208 [(lA m0, 24)] (fun _ ↦ 0) 0).WF := by
  obtain ⟨-, -, -, -, -, -, -, hlr, hlo, -⟩ := pre_parts h
  have c := ctx h
  have h24 : 24 ≤ layoutBytes := by decide
  have hnw : NativeRustcVm.NoWrap (lA m0) 24 := by
    have := hlr.2; unfold NoWrap at this; unfold NativeRustcVm.NoWrap; omega
  refine frame_wf' c.stack F_le hk (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨fun i hi ↦ hlr.1 i (by omega), hnw⟩
  · have hA := apart_frame hlo c.spN F_le
    show NativeRustcVm.Apart (stackBelow m0 208) (208 + 8) (lA m0) 24
    unfold NativeRustcVm.Apart at hA ⊢
    omega

/-- **After `build_layout`** (`b12`, `b13` or `b14`, `b15`). -/
theorem from12 (hp : Placed code k) (h : ReadAnnouncedSizesPre bc a s m0) {xs : Array EW}
    {s1 : TState} (hrs : (readScalars 8).run s = some (xs, s1)) (hsz : xs.size = 8)
    (hall : (xs.all fun x ↦ x.c1 == 0) = true) (hrate : 1 ≤ rateA xs ∧ rateA xs ≤ 4)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b12Offset)) (hb : Bod m0 8 st.data)
    (hrbx : reg st.data .rbx = lA m0)
    (hr15 : reg st.data .r15 = (xs[7]'(by omega)).c0.toBitVec)
    (hok : OkAl st.data (buildLayout bc (lmA xs) (rowsA xs)).isSome)
    (hL : ∀ L, buildLayout bc (lmA xs) (rowsA xs) = some L → LayoutWAt st.data.dmem (lA m0) L)
    (hts : TStateAt st.data.dmem (tA m0) a s1) :
    Eventually (step1 Host.exe) (Goal bc a s m0) st := by
  have hrun := run_tail bc hrs
  rw [tailP_of bc hall, ite_true_of hrate] at hrun
  have hwf := wf0 h hb.fr.kept 0
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun hpc (match_mid hb 0)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hk1⟩ := ok_b12
  obtain ⟨hb1, hd1⟩ := step0 h hb hwf hm1 hmid1 hmem1
  have g15 : reg st1.data .r15 = (xs[7]'(by omega)).c0.toBitVec :=
    (keeps_reg hm1 hk1 (by simp)).trans hr15
  have gbx : reg st1.data .rbx = lA m0 := (keeps_reg hm1 hk1 (by simp)).trans hrbx
  have hok' : (reg st.data .rax).toNat % 256 =
      (okWord (buildLayout bc (lmA xs) (rowsA xs)).isSome).toNat := hok
  have hc : c12.eval (frameEnv m0 st.data 208 [] (fun _ ↦ 0) 0) =
      !(buildLayout bc (lmA xs) (rowsA xs)).isSome := by
    rw [c12_eval]
    show decide ((reg st.data .rax).toNat % 256 = 0) = _
    rw [hok', okWord_test]
  simp only [PcOk] at hpc1
  cases hbl : buildLayout bc (lmA xs) (rowsA xs) with
  | none =>
    refine fail75 hp h hb1 ((pc_true hpc1 (by rw [hc, hbl]; rfl)).trans (lbl_13 hp)) ?_
    rw [hrun, hbl]; rfl
  | some L =>
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.ReadAnnouncedSizes.b13Offset) :=
    (pc_false hpc1 (by rw [hc, hbl]; rfl)).trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.ReadAnnouncedSizes.b12_next]))
  have hLw : LayoutWAt st1.data.dmem (lA m0) L := by rw [hd1]; exact hL L hbl
  -- `b13`: the stack's log-size, at the layout's byte `16`.
  have hwf2 := wf_lay h hb1.fr.kept
  have hm2 : Match (frameEnv m0 st1.data 208 [(lA m0, 24)] (fun _ ↦ 0) 0) layS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb1.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st1.data .rbx = lA m0 + BitVec.ofInt 64 0
          rw [gbx, ofInt_zero64, BitVec.add_zero], trivial⟩
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf2 nofun hpc1' hm2
    fun st2 hm2' hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hax2, hk2⟩ := ok_b13
  obtain ⟨hb2, hd2⟩ := step0 h hb1 hwf2 hm2' hmid2 hmem2
  have g15' : reg st2.data .r15 = (xs[7]'(by omega)).c0.toBitVec :=
    (keeps_reg hm2' hk2 (by simp)).trans g15
  have hld : (frameEnv m0 st1.data 208 [(lA m0, 24)] (fun _ ↦ 0) 0).load 1 16 8 =
      L.stackLog.toUInt64.toBitVec := load_ofMachine rfl hLw.stack_log
  have hax : reg st2.data .rax = if 16 ≤ L.stackLog ∧ L.stackLog ≤ 30 then 1#64 else 0#64 :=
    (hm2'.regs .rax _ hax2).trans (ax13_eval _ hLw.stack_log_lt hld)
  simp only [PcOk] at hpc2
  refine fin (infix_of ((infix_drop b15 1).trans b15_in_code (by simp [b15])) (by simp [b15]) hp)
    exit_b15d ok_b15d.1 ok_b15d.2.1 ok_b15d.2.2.1 ok_b15d.2.2.2 h hb2
    (hpc2.trans (lbl_22 hp)) ?_ fun L' rate s' hr ↦ ?_
  · by_cases hcnd : 16 ≤ L.stackLog ∧ L.stackLog ≤ 30
    · rw [hax, ite_true_of hcnd, hrun, hbl, Option.bind_some, ite_true_of hcnd]; rfl
    · rw [hax, ite_false_of hcnd, hrun, hbl, Option.bind_some, ite_false_of hcnd]; rfl
  · rw [hrun, hbl, Option.bind_some] at hr
    by_cases hcnd : 16 ≤ L.stackLog ∧ L.stackLog ≤ 30
    · rw [ite_true_of hcnd] at hr
      cases hr
      refine ⟨by rw [g15', UInt64.toNat_toBitVec, rateA_get hsz], by rw [hd2]; exact hLw, ?_⟩
      rw [hd2, hd1]; exact hts
    · rw [ite_false_of hcnd] at hr
      cases hr

end

end NativeRustcVmX64.Layout.ReadAnnouncedSizes
