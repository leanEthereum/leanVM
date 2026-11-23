module

public import NativeRustcX64.SphincsVerify.Tree.NodeB

/-!
# The fold's node: the children into hasher B, B's state into A (x86-64)

From `AtN4`: the children's `update` turn into hasher B (`b175`, `b177`, `b178`, `b179`,
`memcpy`; `nodeD`, to `AtN5`); `buf_len` 80 and B's state copied into A (`b180`, `b176`, `b183`,
`memcpy`; `nodeE`, to `AtN6`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

section
variable (r : Run) [Labels]

/-- **At `b180`**: hasher B holds `PK.seed | ADRS | children`, `buf_len` still 48; R12, R15 the
turn's bytes taken and left, R13 the children. -/
@[expose] def AtN5 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 32 ∧ Run.RegIs m .r15 32 ∧
    Run.RegIs m .r13 (r.off 3072) ∧ BytesAt m.dmem (r.off 576) (hbytes (r.nodeIn l e z) 48)

/-- **At `b184`**: hasher A's state zero, B's buffer the node's input; RBX its length, R12
hasher A. -/
@[expose] def AtN6 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4096) ∧ Run.RegIs m .rbx 80 ∧
    BytesAt m.dmem (r.off 4096) (List.replicate 200 0) ∧ BytesAt m.dmem (r.off 776) (r.nodeIn l e z)

end

variable [Host] {r : Run}

/-- **`b175` .. `b179` and `memcpy`**: the children into hasher B. -/
theorem nodeD (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN4 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b180Offset ∧ AtN5 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b175Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hH, hC⟩ := h
  have hl := hB.1
  have hlT : (r.seed ++ r.nodeAdrs l z).length = 48 := by
    rw [List.length_append, length_seed, length_nodeAdrs]
  have hlc := length_children r (cur := r.foldUpTo l e z) hl hz (length_foldUpTo r l e z)
  unfold hbytes at hH
  obtain ⟨hZ, hT, hZ88, hW⟩ := hbytes_parts hH (by omega)
  rw [hlT] at hZ88
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b179Offset + b179.length)).toBitVec
  have hld : (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b179Offset + b179.length)).toBitVec).load 0 912 8
      = (Nat.toUInt64 48).toBitVec := load_word hW
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b179Offset + b179.length)).toBitVec)
    (known := kAB) ⟨h12.trans (eval_ptr 4096).symm, hB.2.2.2.1.trans (eval_ptr 576).symm, trivial⟩
  refine exec_then (hb175 hp) run_b175 hwf (fun _ h ↦ nomatch h) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' : st1.pc = Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b177Offset) := hpc1.trans (lbl_74 hp)
  refine exec_at (hb177 hp) (exec_after run_b175 run_b177) hwf (fun _ h ↦ nomatch h) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := false) hpc2 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b177_next] at hpc2'
  refine exec_at (hb178 hp) (exec_after run_b177 run_b178) hwf (fun _ h ↦ nomatch h) hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hpc3' := pc_cond (b := false) hpc3 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b178_next] at hpc3'
  refine exec_at (hb179 hp) (exec_after run_b178 run_b179) hwf (fun _ _ ↦ rfl) hpc3' hm3
    fun st4 hm4 hpc4 ↦ ?_
  have hc4 := hB.atCall hpre hm4 hwf rfl (by decide)
  have h0 : Run.RegIs st4.data .rdi (r.off 824) := by
    unfold Run.RegIs reg
    rw [hm4.regs .rdi _ rfl]
    exact off_plus 776 48 (by sym_simp; rw [hld]; decide)
  have h1 : Run.RegIs st4.data .rsi (r.off 3072) := (hm4.regs .rsi _ rfl).trans (eval_ptr 3072)
  have h2 : (reg st4.data .rdx).toNat = 32 := by
    unfold reg
    rw [hm4.regs .rdx _ rfl]
    sym_simp
    rw [hld]
    decide
  have h12' : Run.RegIs st4.data .r12 32 := by
    unfold Run.RegIs reg
    rw [hm4.regs .r12 _ rfl]
    sym_simp
    rw [hld]
    decide
  have h15 : Run.RegIs st4.data .r15 32 := hm4.regs .r15 _ rfl
  have h13 : Run.RegIs st4.data .r13 (r.off 3072) := (hm4.regs .r13 _ rfl).trans (eval_ptr 3072)
  have k4 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm4 hwf ho hb hn
  have hch := bytesOf_kept hpre hB.2.1.2.2.2 hm4 hwf (o := 3072) (n := 32) (by decide) (by decide)
  have hN4 := hN.of_match hpre hm4 hwf (by decide)
  refine call_then hpc4 hc.1 (r.memcpy_pre hpre hc4 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have kc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hd : o + bs.length ≤ 824 ∨ 824 + 32 ≤ o) (hb : BytesAt m.dmem (r.off o) bs)
    (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_of_call hpre hc4 (by decide) (by decide) hout ho hd (k4 ho hb hn)
  have hCh : BytesAt st'.data.dmem (r.off 824) (r.children l (r.foldUpTo l e z) z) := by
    rw [hch, ← hlc, bytesOf_of_bytesAt hC] at hcp
    exact hcp
  have hlI := length_nodeIn r (e := e) hl hz
  have hB' := Base.call hpre hB hm4 hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 824) (n := 32) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc4 (a := 824) (n := 32) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN4
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b179_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl h15 hS, regIs_of_saved rfl h13 hS, ?_⟩
  unfold hbytes
  refine hbytes_of_parts (by omega) (kc (by rw [List.length_replicate]; decide)
    (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)) ?_ ?_
    (kc (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; decide) hW
      (by rw [length_wordBytes]; decide))
  · unfold Run.nodeIn
    exact bytesAt_cat hlT (kc (by omega) (by omega) hT (by rw [hlT]; decide)) hCh
  · rw [hlI]
    exact kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide)
      (bytesAt_zero hZ88 (i := 32) (k := 56) (by decide)) (by rw [List.length_replicate]; decide)

/-- **`b180`, `b176`, `b183` and `memcpy`**: `buf_len` 80, B's state into A. -/
theorem nodeE (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN5 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b184Offset ∧ AtN6 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b180Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, h15, h13, hH⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn r (e := e) hl hz
  unfold hbytes at hH
  obtain ⟨hZ, hT, -, hW⟩ := hbytes_parts hH (by omega)
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b183Offset + b183.length)).toBitVec
  have hld : (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b183Offset + b183.length)).toBitVec).load 0 912 8
      = (Nat.toUInt64 48).toBitVec := load_word hW
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b183Offset + b183.length)).toBitVec)
    (known := [(.rbp, .ptr 0 576), (.r12, .lit 32), (.r15, .lit 32), (.r13, .ptr 0 3072)])
    ⟨hB.2.2.2.1.trans (eval_ptr 576).symm, h12, h15, h13.trans (eval_ptr 3072).symm, trivial⟩
  refine exec_then (hb180 hp) run_b180 hwf (fun _ h ↦ nomatch h) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := true) hpc1 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_pos (rfl : true = true), lbl_78 hp] at hpc1'
  refine exec_at (hb176 hp) (exec_after run_b180 run_b176) hwf (fun _ h ↦ nomatch h) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := true) hpc2 rfl
  rw [Sym.ite_pos (rfl : true = true), lbl_79 hp] at hpc2'
  refine exec_at (hb183 hp) (exec_after run_b176 run_b183) hwf (fun _ _ ↦ rfl) hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hc3 := hB.atCall hpre hm3 hwf rfl (by decide)
  have h0 : Run.RegIs st3.data .rdi (r.off 4096) := (hm3.regs .rdi _ rfl).trans (eval_ptr 4096)
  have h1 : Run.RegIs st3.data .rsi (r.off 576) := (hm3.regs .rsi _ rfl).trans (eval_ptr 576)
  have h2 : (reg st3.data .rdx).toNat = 200 := regIs_toNat (hm3.regs .rdx _ rfl) (by decide)
  have h12' : Run.RegIs st3.data .r12 (r.off 4096) := (hm3.regs .r12 _ rfl).trans (eval_ptr 4096)
  have hbx : Run.RegIs st3.data .rbx 80 := by
    unfold Run.RegIs reg
    rw [hm3.regs .rbx _ rfl]
    sym_simp
    rw [hld]
    decide
  have k3 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29384)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm3 hwf ho hb hn
  have hZ3 := k3 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)
  have hT3 := k3 (bs := r.nodeIn l e z) (by omega) hT (by rw [hlI]; decide)
  have hN3 := hN.of_match hpre hm3 hwf (by decide)
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hc3 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hB' := Base.call hpre hB hm3 hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 4096) (n := 200) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc3 (a := 4096) (n := 200) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN3
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b183_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl hbx hS, ?_,
    r.bytesAt_of_call hpre hc3 (by decide) (by decide) hout (by omega) (by omega) hT3⟩
  have := bytesOf_of_bytesAt hZ3
  rw [List.length_replicate] at this
  rw [← this]
  exact hcp

end

end NativeRustcX64.SphincsVerifyProof.Tree
