module

public import NativeRustcX64.SphincsVerify.Tree.NodeC
public import NativeRustcX64.SphincsVerify.InlineTh.Final
public import NativeRustcX64.SphincsVerify.InlineTh.Model

/-!
# The fold's node: the final block and absorb (x86-64)

From `AtN6`: the final block's place zeroed (`b184`, `b185`, `memset`; `nodeF`), B's 80 buffered
bytes copied there (`b186`, `memcpy`; `nodeG`, to `AtN7`), the padding XORed in and the block
XORed into hasher A's zero state, `keccak_f` (`b187`; `nodeH`, to `AtN8`, by
`InlineTh.xorFinal`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

section
variable (r : Run) [Labels]

/-- **At `b186`**: the final block's place zero; RBX the input's length, R13 the place. -/
@[expose] def AtN6b (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4096) ∧ Run.RegIs m .rbx 80 ∧
    Run.RegIs m .r13 (r.off 2048) ∧ BytesAt m.dmem (r.off 4096) (List.replicate 200 0) ∧
    BytesAt m.dmem (r.off 776) (r.nodeIn l e z) ∧ BytesAt m.dmem (r.off 2048) (List.replicate 136 0) ∧
    Run.RegIs m .r15 (Labels.label "memset").toBitVec

/-- **At `b187`**: the final block (the input, zeros) at `2048`. -/
@[expose] def AtN7 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4096) ∧ Run.RegIs m .rbx 80 ∧
    Run.RegIs m .r13 (r.off 2048) ∧ BytesAt m.dmem (r.off 4096) (List.replicate 200 0) ∧
    BytesAt m.dmem (r.off 2048) (r.nodeIn l e z ++ List.replicate 56 0) ∧
    Run.RegIs m .r15 (Labels.label "memset").toBitVec

/-- **At `b188`**: hasher A's state the node's padded input absorbed. -/
@[expose] def AtN8 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4096) ∧
    Run.RegIs m .r13 (r.off 2048) ∧
    BytesAt m.dmem (r.off 4096) (keccakF (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z)))) ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec

end

variable [Host] {r : Run}

/-- **`b184`, `b185` and `memset`**: the final block's place zeroed. -/
theorem nodeF (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN6 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b186Offset ∧ AtN6b r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b184Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hbx, hZ, hT⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn r (e := e) hl hz
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b185Offset + b185.length)).toBitVec
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b185Offset + b185.length)).toBitVec)
    (known := kAB ++ [(.rbx, .lit 80)])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4096), (.rbp, .ptr 0 576), (.rbx, .lit 80)] from
      ⟨h12.trans (eval_ptr 4096).symm, hB.2.2.2.1.trans (eval_ptr 576).symm, hbx, trivial⟩)
  refine exec_then (hb184 hp) run_b184 hwf (fun _ h ↦ nomatch h) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := false) hpc1 rfl
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b184_next] at hpc1'
  refine exec_at (hb185 hp) (exec_after run_b184 run_b185) hwf (fun _ _ ↦ rfl) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hc2 := hB.atCall hpre hm2 hwf rfl (by decide)
  have h0 : Run.RegIs st2.data .rdi (r.off 2048) := (hm2.regs .rdi _ rfl).trans (eval_ptr 2048)
  have h1 : reg st2.data .rsi = 0 := hm2.regs .rsi _ rfl
  have h2 : (reg st2.data .rdx).toNat = 136 := regIs_toNat (hm2.regs .rdx _ rfl) (by decide)
  have h12' : Run.RegIs st2.data .r12 (r.off 4096) := (hm2.regs .r12 _ rfl).trans (eval_ptr 4096)
  have hbx' : Run.RegIs st2.data .rbx 80 := hm2.regs .rbx _ rfl
  have h13 : Run.RegIs st2.data .r13 (r.off 2048) := (hm2.regs .r13 _ rfl).trans (eval_ptr 2048)
  have k2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm2 hwf ho hb hn
  have hZ2 := k2 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)
  have hT2 := k2 (bs := r.nodeIn l e z) (by omega) hT (by rw [hlI]; decide)
  have hN2 := hN.of_match hpre hm2 hwf (by decide)
  refine call_then hpc2 hc.2.1 (r.memset_pre hpre hc2 h0 h2 (by decide))
    fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hz0, hout, hS⟩ := r.memset_out h0 h2 hpost
  have kc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hd : o + bs.length ≤ 2048 ∨ 2048 + 136 ≤ o) (hb : BytesAt st2.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc2 (by decide) (by decide) hout ho hd hb
  have hB' := Base.call hpre hB hm2 hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 2048) (n := 136) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc2 (a := 2048) (n := 136) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN2
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b185_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl hbx' hS, regIs_of_saved rfl h13 hS,
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ2,
    kc (by omega) (by omega) hT2, ?_,
    regIs_of_saved rfl (hm2.regs .r15 _ rfl) hS⟩
  rw [h1] at hz0
  exact hz0

/-- **`b186` and `memcpy`**: B's buffered input into the final block. -/
theorem nodeG (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN6b r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b187Offset ∧ AtN7 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b186Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hbx, h13, hZ, hT, hK, h15⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn r (e := e) hl hz
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b186Offset + b186.length)).toBitVec
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b186Offset + b186.length)).toBitVec)
    (known := kAB ++ [(.rbx, .lit 80), (.r13, .ptr 0 2048), (.r15, .label "memset")])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4096), (.rbp, .ptr 0 576), (.rbx, .lit 80),
      (.r13, .ptr 0 2048), (.r15, .label "memset")] from
      ⟨h12.trans (eval_ptr 4096).symm, hB.2.2.2.1.trans (eval_ptr 576).symm, hbx,
        h13.trans (eval_ptr 2048).symm, h15, trivial⟩)
  refine exec_then (hb186 hp) run_b186 hwf (fun _ _ ↦ rfl) hm0 fun st hm hpc ↦ ?_
  have hc1 := hB.atCall hpre hm hwf rfl (by decide)
  have h0 : Run.RegIs st.data .rdi (r.off 2048) := (hm.regs .rdi _ rfl).trans (eval_ptr 2048)
  have h1 : Run.RegIs st.data .rsi (r.off 776) := (hm.regs .rsi _ rfl).trans (eval_ptr 776)
  have h2 : (reg st.data .rdx).toNat = 80 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have h12' : Run.RegIs st.data .r12 (r.off 4096) := (hm.regs .r12 _ rfl).trans (eval_ptr 4096)
  have hbx' : Run.RegIs st.data .rbx 80 := hm.regs .rbx _ rfl
  have h13' : Run.RegIs st.data .r13 (r.off 2048) := (hm.regs .r13 _ rfl).trans (eval_ptr 2048)
  have k1 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm hwf ho hb hn
  have hZ1 := k1 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)
  have hK1 := k1 (by rw [List.length_replicate]; decide) hK (by rw [List.length_replicate]; decide)
  have hin := bytesOf_kept hpre hB.2.1.2.2.2 hm hwf (o := 776) (n := 80) (by decide) (by decide)
  have hN1 := hN.of_match hpre hm hwf (by decide)
  refine call_then hpc hc.1 (r.memcpy_pre hpre hc1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have kc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hd : o + bs.length ≤ 2048 ∨ 2048 + 80 ≤ o) (hb : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc1 (by decide) (by decide) hout ho hd hb
  have hIn : BytesAt st'.data.dmem (r.off 2048) (r.nodeIn l e z) := by
    rw [hin, ← hlI, bytesOf_of_bytesAt hT] at hcp
    exact hcp
  have hB' := Base.call hpre hB hm hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 2048) (n := 80) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc1 (a := 2048) (n := 80) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN1
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b186_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl hbx' hS, regIs_of_saved rfl h13' hS,
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ1,
    bytesAt_cat hlI hIn (kc (by rw [List.length_replicate]; decide) (by decide)
      (bytesAt_zero hK1 (i := 80) (k := 56) (by decide))),
    regIs_of_saved rfl (hm.regs .r15 _ rfl) hS⟩

/-- **`b187` and `keccak_f`**: the final absorb. -/
theorem nodeH (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN7 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b188Offset ∧ AtN8 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b187Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hbx, h13, hZ, hK, h15⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn r (e := e) hl hz
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b187Offset + b187.length)).toBitVec
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b187Offset + b187.length)).toBitVec)
    (known := kAB ++ [(.rbx, .lit 80), (.r13, .ptr 0 2048), (.r15, .label "memset")])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4096), (.rbp, .ptr 0 576), (.rbx, .lit 80),
      (.r13, .ptr 0 2048), (.r15, .label "memset")] from
      ⟨h12.trans (eval_ptr 4096).symm, hB.2.2.2.1.trans (eval_ptr 576).symm, hbx,
        h13.trans (eval_ptr 2048).symm, h15, trivial⟩)
  refine exec_then (hb187 hp) run_b187 hwf (fun _ _ ↦ rfl) hm0 fun st hm hpc ↦ ?_
  have hc1 := hB.atCall hpre hm hwf rfl (by decide)
  have h0 : Run.RegIs st.data .rdi (r.off 4096) := (hm.regs .rdi _ rfl).trans (eval_ptr 4096)
  have h12' : Run.RegIs st.data .r12 (r.off 4096) := (hm.regs .r12 _ rfl).trans (eval_ptr 4096)
  have h13' : Run.RegIs st.data .r13 (r.off 2048) := (hm.regs .r13 _ rfl).trans (eval_ptr 2048)
  have hX : BytesAt st.data.dmem (r.off 4096)
      (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z))) := by
    have := InlineTh.xorFinal hm hwf (r := 0) (b := r.base) (sz := frameRegion) rfl (oA := 4096)
      (oK := 2048) (L := 80) (by decide) (by decide +kernel) hlI (by decide) hK
    have hz200 : bytesOf (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b187Offset + b187.length)).toBitVec).mem0
        (r.off 4096) 200 = List.replicate 200 0 := by
      have := bytesOf_of_bytesAt hZ
      rwa [List.length_replicate] at this
    rwa [show r.base + BitVec.ofNat 64 4096 = r.off 4096 from rfl, hz200] at this
  have hN1 := hN.of_match hpre hm hwf (by decide)
  refine call_then hpc hc.2.2.2.2 (r.keccakF_pre hpre hc1 h0 (by decide))
    fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hk, hout, hS⟩ := r.keccakF_out h0 hpost
  have hlX : (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z))).length = 200 :=
    length_stateBytes _
  have hB' := Base.call hpre hB hm hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 4096) (n := 200) (N := keccakFStack) (by decide) (by decide) (by decide) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc1 (a := 4096) (n := 200) (N := keccakFStack)
    (by decide) (by decide) (by decide) hout hN1
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b187_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl h13' hS, ?_,
    regIs_of_saved rfl (hm.regs .rbx _ rfl) hS⟩
  have := bytesOf_of_bytesAt hX
  rw [hlX] at this
  rw [← this]
  exact hk

end

end NativeRustcX64.SphincsVerifyProof.Tree
