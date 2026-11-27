module

public import NativeRustcX64.SphincsVerify.Tree.NodeC
public import NativeRustcX64.SphincsVerify.InlineTh.Final
public import NativeRustcX64.SphincsVerify.InlineTh.Model

/-!
# The fold's node: the final block and absorb (x86-64)

From `AtN6`: the final block's place zeroed (`b174`, `b175`, `memset`; `nodeF`), B's 80 buffered
bytes copied there (`b176`, `memcpy`; `nodeG`, to `AtN7`), the padding XORed in and the block
XORed into hasher A's zero state, `keccak_f` (`b177`; `nodeH`, to `AtN8`, by
`InlineTh.xorFinal`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

section
variable (r : Run) [Labels]

/-- **At `b176`**: the final block's place zero; RBX the input's length, R13 the place. -/
@[expose] def AtN6b (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4072) ∧ Run.RegIs m .rbx 80 ∧
    Run.RegIs m .r13 (r.off 2024) ∧ BytesAt m.dmem (r.off 4072) (List.replicate 200 0) ∧
    BytesAt m.dmem (r.off 760) (r.nodeIn l e z) ∧ BytesAt m.dmem (r.off 2024) (List.replicate 136 0) ∧
    Run.RegIs m .r15 (Labels.label "memset").toBitVec

/-- **At `b177`**: the final block (the input, zeros) at `2024`. -/
@[expose] def AtN7 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4072) ∧ Run.RegIs m .rbx 80 ∧
    Run.RegIs m .r13 (r.off 2024) ∧ BytesAt m.dmem (r.off 4072) (List.replicate 200 0) ∧
    BytesAt m.dmem (r.off 2024) (r.nodeIn l e z ++ List.replicate 56 0) ∧
    Run.RegIs m .r15 (Labels.label "memset").toBitVec

/-- **At `b178`**: hasher A's state the node's padded input absorbed. -/
@[expose] def AtN8 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4072) ∧
    Run.RegIs m .r13 (r.off 2024) ∧
    BytesAt m.dmem (r.off 4072) (keccakF (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z)))) ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec

end

variable [ElfHost] {r : Run}

/-- **`b174`, `b175` and `memset`**: the final block's place zeroed. -/
theorem nodeF (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN6 r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b176Offset ∧ AtN6b r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b174Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hbx, hZ, hT⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn r (e := e) hl hz
  have hwf := frame_wf' hpre hB (ElfHost.addrOf r.sec (r.k + NativeRustcX64.Sphincs.SphincsVerify.b175Offset + b175.length)).toBitVec
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (ElfHost.addrOf r.sec (r.k + NativeRustcX64.Sphincs.SphincsVerify.b175Offset + b175.length)).toBitVec)
    (known := kAB ++ [(.rbx, .lit 80)])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4072), (.rbp, .ptr 0 560), (.rbx, .lit 80)] from
      ⟨h12.trans (eval_ptr 4072).symm, hB.2.2.2.1.trans (eval_ptr 560).symm, hbx, trivial⟩)
  refine exec_then_elf (hb183 hp) run_b174 hwf (fun _ h ↦ nomatch h) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := false) hpc1 rfl
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b174_next] at hpc1'
  refine exec_at_elf (hb184 hp) (exec_after run_b174 run_b175) hwf (fun _ _ ↦ rfl) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hc2 := hB.atCall hpre hm2 hwf rfl (by decide)
  have h0 : Run.RegIs st2.data .rdi (r.off 2024) := (hm2.regs .rdi _ rfl).trans (eval_ptr 2024)
  have h1 : reg st2.data .rsi = 0 := hm2.regs .rsi _ rfl
  have h2 : (reg st2.data .rdx).toNat = 136 := regIs_toNat (hm2.regs .rdx _ rfl) (by decide)
  have h12' : Run.RegIs st2.data .r12 (r.off 4072) := (hm2.regs .r12 _ rfl).trans (eval_ptr 4072)
  have hbx' : Run.RegIs st2.data .rbx 80 := hm2.regs .rbx _ rfl
  have h13 : Run.RegIs st2.data .r13 (r.off 2024) := (hm2.regs .r13 _ rfl).trans (eval_ptr 2024)
  have k2 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm2 hwf ho hb hn
  have hZ2 := k2 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)
  have hT2 := k2 (bs := r.nodeIn l e z) (by omega) hT (by rw [hlI]; decide)
  have hN2 := hN.of_match hpre hm2 hwf (by decide)
  refine call_then_elf hpc2 hc.2.1 (r.memset_pre hpre hc2 h0 h2 (by decide))
    fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hz0, hout, hS⟩ := r.memset_out h0 h2 hpost
  have kc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (hd : o + bs.length ≤ 2024 ∨ 2024 + 136 ≤ o) (hb : BytesAt st2.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc2 (by decide) (by decide) hout ho hd hb
  have hB' := Base.call hpre hB hm2 hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 2024) (n := 136) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc2 (a := 2024) (n := 136) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN2
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b175_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl hbx' hS, regIs_of_saved rfl h13 hS,
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ2,
    kc (by omega) (by omega) hT2, ?_,
    regIs_of_saved rfl (hm2.regs .r15 _ rfl) hS⟩
  rw [h1] at hz0
  exact hz0

/-- **`b176` and `memcpy`**: B's buffered input into the final block. -/
theorem nodeG (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN6b r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b177Offset ∧ AtN7 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b176Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hbx, h13, hZ, hT, hK, h15⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn r (e := e) hl hz
  have hwf := frame_wf' hpre hB (ElfHost.addrOf r.sec (r.k + NativeRustcX64.Sphincs.SphincsVerify.b176Offset + b176.length)).toBitVec
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (ElfHost.addrOf r.sec (r.k + NativeRustcX64.Sphincs.SphincsVerify.b176Offset + b176.length)).toBitVec)
    (known := kAB ++ [(.rbx, .lit 80), (.r13, .ptr 0 2024), (.r15, .label "memset")])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4072), (.rbp, .ptr 0 560), (.rbx, .lit 80),
      (.r13, .ptr 0 2024), (.r15, .label "memset")] from
      ⟨h12.trans (eval_ptr 4072).symm, hB.2.2.2.1.trans (eval_ptr 560).symm, hbx,
        h13.trans (eval_ptr 2024).symm, h15, trivial⟩)
  refine exec_then_elf (hb185 hp) run_b176 hwf (fun _ _ ↦ rfl) hm0 fun st hm hpc ↦ ?_
  have hc1 := hB.atCall hpre hm hwf rfl (by decide)
  have h0 : Run.RegIs st.data .rdi (r.off 2024) := (hm.regs .rdi _ rfl).trans (eval_ptr 2024)
  have h1 : Run.RegIs st.data .rsi (r.off 760) := (hm.regs .rsi _ rfl).trans (eval_ptr 760)
  have h2 : (reg st.data .rdx).toNat = 80 := regIs_toNat (hm.regs .rdx _ rfl) (by decide)
  have h12' : Run.RegIs st.data .r12 (r.off 4072) := (hm.regs .r12 _ rfl).trans (eval_ptr 4072)
  have hbx' : Run.RegIs st.data .rbx 80 := hm.regs .rbx _ rfl
  have h13' : Run.RegIs st.data .r13 (r.off 2024) := (hm.regs .r13 _ rfl).trans (eval_ptr 2024)
  have k1 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm hwf ho hb hn
  have hZ1 := k1 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)
  have hK1 := k1 (by rw [List.length_replicate]; decide) hK (by rw [List.length_replicate]; decide)
  have hin := bytesOf_kept hpre hB.2.1.2.2.2 hm hwf (o := 760) (n := 80) (by decide) (by decide)
  have hN1 := hN.of_match hpre hm hwf (by decide)
  refine call_then_elf hpc hc.1 (r.memcpy_pre hpre hc1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have kc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (hd : o + bs.length ≤ 2024 ∨ 2024 + 80 ≤ o) (hb : BytesAt st.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc1 (by decide) (by decide) hout ho hd hb
  have hIn : BytesAt st'.data.dmem (r.off 2024) (r.nodeIn l e z) := by
    rw [hin, ← hlI, bytesOf_of_bytesAt hT] at hcp
    exact hcp
  have hB' := Base.call hpre hB hm hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 2024) (n := 80) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc1 (a := 2024) (n := 80) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN1
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b176_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl hbx' hS, regIs_of_saved rfl h13' hS,
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ1,
    bytesAt_cat hlI hIn (kc (by rw [List.length_replicate]; decide) (by decide)
      (bytesAt_zero hK1 (i := 80) (k := 56) (by decide))),
    regIs_of_saved rfl (hm.regs .r15 _ rfl) hS⟩

/-- **`b177` and `keccak_f`**: the final absorb. -/
theorem nodeH (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN7 r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b178Offset ∧ AtN8 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b177Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hbx, h13, hZ, hK, h15⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn r (e := e) hl hz
  have hwf := frame_wf' hpre hB (ElfHost.addrOf r.sec (r.k + NativeRustcX64.Sphincs.SphincsVerify.b177Offset + b177.length)).toBitVec
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (ElfHost.addrOf r.sec (r.k + NativeRustcX64.Sphincs.SphincsVerify.b177Offset + b177.length)).toBitVec)
    (known := kAB ++ [(.rbx, .lit 80), (.r13, .ptr 0 2024), (.r15, .label "memset")])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4072), (.rbp, .ptr 0 560), (.rbx, .lit 80),
      (.r13, .ptr 0 2024), (.r15, .label "memset")] from
      ⟨h12.trans (eval_ptr 4072).symm, hB.2.2.2.1.trans (eval_ptr 560).symm, hbx,
        h13.trans (eval_ptr 2024).symm, h15, trivial⟩)
  refine exec_then_elf (hb186 hp) run_b177 hwf (fun _ _ ↦ rfl) hm0 fun st hm hpc ↦ ?_
  have hc1 := hB.atCall hpre hm hwf rfl (by decide)
  have h0 : Run.RegIs st.data .rdi (r.off 4072) := (hm.regs .rdi _ rfl).trans (eval_ptr 4072)
  have h12' : Run.RegIs st.data .r12 (r.off 4072) := (hm.regs .r12 _ rfl).trans (eval_ptr 4072)
  have h13' : Run.RegIs st.data .r13 (r.off 2024) := (hm.regs .r13 _ rfl).trans (eval_ptr 2024)
  have hX : BytesAt st.data.dmem (r.off 4072)
      (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z))) := by
    have := InlineTh.xorFinal hm hwf (r := 0) (b := r.base) (sz := frameRegion) rfl (oA := 4072)
      (oK := 2024) (L := 80) (by decide) (by decide +kernel) hlI (by decide) hK
    have hz200 : bytesOf (r.env m (fun _ ↦ 0) (ElfHost.addrOf r.sec (r.k + NativeRustcX64.Sphincs.SphincsVerify.b177Offset + b177.length)).toBitVec).mem0
        (r.off 4072) 200 = List.replicate 200 0 := by
      have := bytesOf_of_bytesAt hZ
      rwa [List.length_replicate] at this
    rwa [show r.base + BitVec.ofNat 64 4072 = r.off 4072 from rfl, hz200] at this
  have hN1 := hN.of_match hpre hm hwf (by decide)
  refine call_then_elf hpc hc.2.2.2.2 (r.keccakF_pre hpre hc1 h0 (by decide))
    fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hk, hout, hS⟩ := r.keccakF_out h0 hpost
  have hlX : (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z))).length = 200 :=
    length_stateBytes _
  have hB' := Base.call hpre hB hm hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 4072) (n := 200) (N := keccakFStack) (by decide) (by decide) (by decide) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc1 (a := 4072) (n := 200) (N := keccakFStack)
    (by decide) (by decide) (by decide) hout hN1
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b177_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl h13' hS, ?_,
    regIs_of_saved rfl (hm.regs .rbx _ rfl) hS⟩
  have := bytesOf_of_bytesAt hX
  rw [hlX] at this
  rw [← this]
  exact hk

end

end NativeRustcX64.SphincsVerifyProof.Tree
