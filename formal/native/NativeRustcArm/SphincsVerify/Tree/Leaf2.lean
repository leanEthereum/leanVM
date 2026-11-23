module

public import NativeRustcArm.SphincsVerify.Tree.Leaf1

/-!
# The one-time leaf's `th`, last calls

Hasher A, holding `PK.seed`, updated with the address (`b145`, `stage3`), cloned into hasher B
(`b146`, `memcpy`, `stage4`), B updated with the chain ends (`b147`, `stage5`) and finalized into
`22672` (`b148`, `stage6`): Keccak-256 of `PK.seed | ADRS | ends`, whose first 16 bytes are the
one-time leaf (`leaf`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [Host] (r : Run)

/-- At `b146`: hasher A has absorbed `PK.seed | ADRS`. -/
@[expose] def AtL3 (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ BytesAt m.dmem (r.off 28224) e.flatten ∧ e.flatten.length = 1024 ∧
    HasherHolds (bytesOf m.dmem (r.off 16400) 344) (r.seed ++ (r.key l).adrs 1)

/-- At `b147`: so has its clone, hasher B. -/
@[expose] def AtL4 (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ BytesAt m.dmem (r.off 28224) e.flatten ∧ e.flatten.length = 1024 ∧
    HasherHolds (bytesOf m.dmem (r.off 26768) 344) (r.seed ++ (r.key l).adrs 1)

/-- At `b148`: hasher B has absorbed `PK.seed | ADRS | ends`. -/
@[expose] def AtL5 (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ HasherHolds (bytesOf m.dmem (r.off 26768) 344) (r.seed ++ (r.key l).adrs 1 ++ e.flatten)

/-- At `b149`: the hash at `22672`. -/
@[expose] def AtL6 (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ BytesAt m.dmem (r.off 22672) (hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten))

variable {r}

/-- **`b145`**: `update` of hasher A with the address. -/
theorem stage3 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : AtL2 r l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b146Offset ∧ AtL3 r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b145Offset⟩ := by
  obtain ⟨hB, hE, hElen, hA, hH⟩ := h
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then (hb145 hp) run_b145 hwf (match_base hpre hB) fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st.data .X0 (r.off 16400) := (hm.regs .X0 _ rfl).trans (eval_ptr 16400)
  have h1 : Run.RegIs st.data .X1 (r.off 24720) := (hm.regs .X1 _ rfl).trans (eval_ptr 24720)
  have h2 : st.data.regs.X2.toNat = 32 := regIs_toNat (hm.regs .X2 _ rfl) (by decide)
  have hmem := hm.dmem_eq hwf rfl
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 16400) 344) r.seed := by
    rw [hmem]; exact hH
  refine call_then hpc hc.2.2.1 (r.update_pre hpre hB1.2.1 h0 h1 h2 (a := 16400) (b := 24720)
    (by decide) (by decide) (by decide) ⟨_, hH1⟩) fun st' hpc' hpost ↦ ?_
  obtain ⟨hh, hout, hS⟩ := r.update_out h0 h1 h2 hpost
  have hadrs : bytesOf st.data.dmem (r.off 24720) 32 = (r.key l).adrs 1 := by
    rw [hmem]
    exact bytesOf_of_bytesAt hA
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b145_next),
    hB1.of_call hpre hS (by decide) (by decide) (by decide) hout, ?_, hElen, ?_⟩
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by omega) (by omega)
      (by rw [hmem]; exact hE)
  · have := hh _ hH1
    rwa [hadrs] at this

/-- **`b146`**: hasher A cloned into hasher B (`memcpy`). -/
theorem stage4 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : AtL3 r l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b147Offset ∧ AtL4 r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b146Offset⟩ := by
  obtain ⟨hB, hE, hElen, hH⟩ := h
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then (hb146 hp) run_b146 hwf (match_base hpre hB) fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st.data .X0 (r.off 26768) := (hm.regs .X0 _ rfl).trans (eval_ptr 26768)
  have h1 : Run.RegIs st.data .X1 (r.off 16400) := (hm.regs .X1 _ rfl).trans (eval_ptr 16400)
  have h2 : st.data.regs.X2.toNat = 344 := regIs_toNat (hm.regs .X2 _ rfl) (by decide)
  have hmem := hm.dmem_eq hwf rfl
  refine call_then hpc hc.1 (r.memcpy_pre hpre hB1.2.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hc', hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b146_next),
    hB1.of_call hpre hS (by decide) (by decide) (by decide) hout, ?_, hElen, ?_⟩
  · exact r.bytesAt_of_call hpre hB1.2.1 (by decide) (by decide) hout (by omega) (by omega)
      (by rw [hmem]; exact hE)
  · have := bytesOf_of_bytesAt hc'
    rw [Hasher.length_bytesOf] at this
    rw [this, hmem]
    exact hH

/-- **`b147`**: `update` of hasher B with the chain ends. -/
theorem stage5 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : AtL4 r l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b148Offset ∧ AtL5 r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b147Offset⟩ := by
  obtain ⟨hB, hE, hElen, hH⟩ := h
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then (hb147 hp) run_b147 hwf (match_base hpre hB) fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st.data .X0 (r.off 26768) := (hm.regs .X0 _ rfl).trans (eval_ptr 26768)
  have h1 : Run.RegIs st.data .X1 (r.off 28224) := (hm.regs .X1 _ rfl).trans (eval_ptr 28224)
  have h2 : st.data.regs.X2.toNat = 1024 := regIs_toNat (hm.regs .X2 _ rfl) (by decide)
  have hmem := hm.dmem_eq hwf rfl
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 26768) 344) (r.seed ++ (r.key l).adrs 1) := by
    rw [hmem]; exact hH
  refine call_then hpc hc.2.2.1 (r.update_pre hpre hB1.2.1 h0 h1 h2 (a := 26768) (b := 28224)
    (by decide) (by decide) (by decide) ⟨_, hH1⟩) fun st' hpc' hpost ↦ ?_
  obtain ⟨hh, hout, hS⟩ := r.update_out h0 h1 h2 hpost
  have hends : bytesOf st.data.dmem (r.off 28224) 1024 = e.flatten := by
    rw [hmem, ← hElen]
    exact bytesOf_of_bytesAt hE
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b147_next),
    hB1.of_call hpre hS (by decide) (by decide) (by decide) hout, ?_⟩
  have := hh _ hH1
  rwa [hends] at this

/-- **`b148`**: `finalize` of hasher B into `22672`. -/
theorem stage6 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : AtL5 r l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b149Offset ∧ AtL6 r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b148Offset⟩ := by
  obtain ⟨hB, hH⟩ := h
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then (hb148 hp) run_b148 hwf (match_base hpre hB) fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st.data .X0 (r.off 22672) := (hm.regs .X0 _ rfl).trans (eval_ptr 22672)
  have h1 : Run.RegIs st.data .X1 (r.off 26768) := (hm.regs .X1 _ rfl).trans (eval_ptr 26768)
  have hmem := hm.dmem_eq hwf rfl
  have hH1 : HasherHolds (bytesOf st.data.dmem (r.off 26768) 344)
      (r.seed ++ (r.key l).adrs 1 ++ e.flatten) := by
    rw [hmem]; exact hH
  refine call_then hpc hc.2.2.2.1 (r.finalize_pre hpre hB1.2.1 h0 h1 (by decide) (by decide)
    (by decide) ⟨_, hH1⟩) fun st' hpc' hpost ↦ ?_
  obtain ⟨hf, hout, hS⟩ := r.finalize_out h0 h1 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b148_next),
    hB1.of_call hpre hS (by decide) (by decide) (by decide) hout, ?_⟩
  rw [finalize_eq hH1] at hf
  exact hf

end

end NativeRustcArm.SphincsVerifyProof.Tree
