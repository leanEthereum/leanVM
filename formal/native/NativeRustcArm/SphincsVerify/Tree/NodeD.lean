module

public import NativeRustcArm.SphincsVerify.Tree.NodeC

/-!
# The fold's node: the children into hasher B, B's state into A, the final block

From `AtN4`: the children's `update` turn into hasher B (`b157`, `b159`, `b160`, `b161`,
`memcpy`; `nodeD`, to `AtN5`); `buf_len` 80 and B's state copied into A (`b162`, `b158`, `b165`,
`memcpy`; `nodeE`, to `AtN6`); the final block: zeros, then B's 80 buffered bytes (`b166`,
`b167`, `memcpy`; `nodeF`, to `AtN7`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [ElfHost] (r : Run)

/-- **At `b166`**: hasher A's state zero, B's buffer the node's input; X23 its length. -/
@[expose] def AtN6 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NRegs r l z m ∧ Run.RegIs m .X23 80 ∧
    BytesAt m.dmem (r.off 8640) (List.replicate 200 0) ∧ BytesAt m.dmem (r.off 19208) (nodeIn r l e z)

/-- **At `b168`**: hasher A's state zero, the final block (the input, zeros) at `16960`. -/
@[expose] def AtN7 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NRegs r l z m ∧ Run.RegIs m .X23 80 ∧
    BytesAt m.dmem (r.off 8640) (List.replicate 200 0) ∧
    BytesAt m.dmem (r.off 16960) (nodeIn r l e z ++ List.replicate 56 0)

variable {r}

/-- **`b157` .. `b161` and `memcpy`**: the children into hasher B. -/
theorem nodeD (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN4 r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b162Offset ∧ AtN5 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b157Offset⟩ := by
  obtain ⟨hB, hz, hN, hH, hC⟩ := h
  have hl := hB.1
  have hlT : (r.seed ++ r.nodeAdrs l z).length = 48 := by
    rw [List.length_append, length_seed, length_nodeAdrs]
  have hlc := length_children (r := r) hl hz (length_foldUpTo r l e z)
  unfold hbytes at hH
  obtain ⟨hZ, hT, hZ88, hW⟩ := hbytes_parts hH (by omega)
  rw [hlT] at hZ88
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  have hld : (r.env m).load 0 19344 8 = (Nat.toUInt64 48).toBitVec := load_word hW
  refine exec_then_elf (hb157 hp) run_b157 hwf (match_base hpre hB) fun st1 hm1 hpc1 ↦ ?_
  have hpc1' : st1.pc = ElfHost.addrOf r.sec (r.k + NativeRustcArm.Sphincs.SphincsVerify.b159Offset) := hpc1.trans (lbl_69 hp)
  refine exec_at_elf (hb159 hp) (exec_after run_b157 run_b159) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := false) hpc2 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b159_next] at hpc2'
  refine exec_at_elf (hb160 hp) (exec_after run_b159 run_b160) hwf hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
  have hpc3' := pc_cond (b := false) hpc3 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b160_next] at hpc3'
  refine exec_at_elf (hb161 hp) (exec_after run_b160 run_b161) hwf hpc3' hm3 fun st4 hm4 hpc4 ↦ ?_
  have hB4 := Base.of_match hpre hB hm4 hwf rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl rfl
  have hN4 := hN.of_match hpre hm4 hwf rfl rfl (by decide)
  have h0 : Run.RegIs st4.data .X0 (r.off 19256) := by
    unfold Run.RegIs
    rw [hm4.regs .X0 _ rfl]
    sym_simp
    rw [hld, Run.off, BitVec.add_assoc]
    rfl
  have h1 : Run.RegIs st4.data .X1 (r.off 14912) := (hm4.regs .X1 _ rfl).trans (eval_ptr 14912)
  have h2 : st4.data.regs.X2.toNat = 32 := by
    have := hm4.regs .X2 _ rfl
    sym_simp at this
    rw [hld] at this
    exact regIs_toNat (this.trans (by decide)) (by decide)
  have h22 : Run.RegIs st4.data .X22 32 := by
    unfold Run.RegIs
    rw [hm4.regs .X22 _ rfl]
    sym_simp
    rw [hld]
    decide
  have h26 : Run.RegIs st4.data .X26 32 := hm4.regs .X26 _ rfl
  -- the blocks write nothing
  have hmem : st4.data.dmem = m.dmem := hm4.dmem_eq hwf rfl
  refine call_then_elf hpc4 hc.1 (r.memcpy_pre hpre hB4.2.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have kc : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 21616 →
      (o + bs.length ≤ 19256 ∨ 19288 ≤ o) → BytesAt m.dmem (r.off o) bs →
      BytesAt st'.data.dmem (r.off o) bs := fun ho hd h ↦
    r.bytesAt_of_call hpre hB4.2.1 (by decide) (by decide) hout ho hd (by rw [hmem]; exact h)
  have hCh : BytesAt st'.data.dmem (r.off 19256) (r.children l (r.foldUpTo l e z) z) := by
    have := bytesOf_of_bytesAt hC
    rw [hlc] at this
    rw [← this, ← hmem]
    exact hcp
  have hlI := length_nodeIn (r := r) (e := e) hl hz
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b161_next),
    hB4.of_call hpre hS (by decide) (by decide) (by decide) hout, hz,
    hN4.of_call hpre hB4.2.1 hS (by decide) (by decide) (by decide) hout,
    regIs_of_saved rfl h22 hS, regIs_of_saved rfl h26 hS, ?_⟩
  unfold hbytes
  refine hbytes_of_parts (by omega) (kc (by rw [List.length_replicate]; decide)
    (by rw [List.length_replicate]; decide) hZ) ?_ ?_ (kc (by rw [length_wordBytes]; decide)
    (by decide) hW)
  · unfold nodeIn
    refine bytesAt_cat hlT (kc (by omega) (by omega) hT) ?_
    exact hCh
  · rw [hlI]
    exact kc (by rw [List.length_replicate]; decide) (by decide)
      (bytesAt_zero hZ88 (i := 32) (k := 56) (by decide))

/-- **`b162`, `b158`, `b165` and `memcpy`**: `buf_len` 80, B's state into A. -/
theorem nodeE (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN5 r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b166Offset ∧ AtN6 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b162Offset⟩ := by
  obtain ⟨hB, hz, hN, h22, h26, hH⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn (r := r) (e := e) hl hz
  unfold hbytes at hH
  obtain ⟨hZ, hT, -, hW⟩ := hbytes_parts hH (by omega)
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  have hld : (r.env m).load 0 19344 8 = (Nat.toUInt64 48).toBitVec := load_word hW
  have hm0 : Match (r.env m) s5 m := r.match_frame hpre hB.2.1
    (allOf_append (allOf_keptRegs hB _) ⟨h22, h26, trivial⟩) trivial trivial trivial
  refine exec_then_elf (hb162 hp) run_b162 hwf hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := true) hpc1 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_pos (rfl : true = true), lbl_68 hp] at hpc1'
  refine exec_at_elf (hb158 hp) (exec_after run_b162 run_b158) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := true) hpc2 rfl
  rw [Sym.ite_pos (rfl : true = true), lbl_73 hp] at hpc2'
  refine exec_at_elf (hb165 hp) (exec_after run_b158 run_b165) hwf hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
  have hB3 := Base.of_match hpre hB hm3 hwf rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl rfl
  have hN3 := hN.of_match hpre hm3 hwf rfl rfl (by decide)
  have h0 : Run.RegIs st3.data .X0 (r.off 8640) := (hm3.regs .X0 _ rfl).trans (eval_ptr 8640)
  have h1 : Run.RegIs st3.data .X1 (r.off 19008) := (hm3.regs .X1 _ rfl).trans (eval_ptr 19008)
  have h2 : st3.data.regs.X2.toNat = 200 := regIs_toNat (hm3.regs .X2 _ rfl) (by decide)
  have h23 : Run.RegIs st3.data .X23 80 := by
    unfold Run.RegIs
    rw [hm3.regs .X23 _ rfl]
    sym_simp
    rw [hld]
    decide
  have k3 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 21616 → BytesAt m.dmem (r.off o) bs →
      Run.noWriteIn _ o bs.length = true → BytesAt st3.data.dmem (r.off o) bs :=
    fun ho h hn ↦ r.bytesAt_kept hpre hm3 hwf ho h hn
  have hZ3 := k3 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)
  have hT3 := k3 (by omega) hT (by rw [hlI]; decide)
  refine call_then_elf hpc3 hc.1 (r.memcpy_pre hpre hB3.2.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b165_next),
    hB3.of_call hpre hS (by decide) (by decide) (by decide) hout, hz,
    hN3.of_call hpre hB3.2.1 hS (by decide) (by decide) (by decide) hout,
    regIs_of_saved rfl h23 hS, ?_,
    r.bytesAt_of_call hpre hB3.2.1 (by decide) (by decide) hout (by omega) (by omega) hT3⟩
  have := bytesOf_of_bytesAt hZ3
  rw [List.length_replicate] at this
  rw [← this]
  exact hcp

/-- **`b166`, `b167` and `memcpy`**: the final block. -/
theorem nodeF (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN6 r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b168Offset ∧ AtN7 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b166Offset⟩ := by
  obtain ⟨hB, hz, hN, h23, hZ, hT⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn (r := r) (e := e) hl hz
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  have hm0 : Match (r.env m) s6 m := r.match_frame hpre hB.2.1
    (allOf_append (allOf_keptRegs hB _) ⟨h23, trivial⟩) trivial trivial trivial
  refine exec_then_elf (hb166 hp) run_b166 hwf hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := false) hpc1 rfl
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b166_next] at hpc1'
  refine exec_at_elf (hb167 hp) (exec_after run_b166 run_b167) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hB2 := Base.of_match hpre hB hm2 hwf rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl rfl
  have hN2 := hN.of_match hpre hm2 hwf rfl rfl (by decide)
  have h0 : Run.RegIs st2.data .X0 (r.off 16960) := (hm2.regs .X0 _ rfl).trans (eval_ptr 16960)
  have h1 : Run.RegIs st2.data .X1 (r.off 19208) := (hm2.regs .X1 _ rfl).trans (eval_ptr 19208)
  have h2 : st2.data.regs.X2.toNat = 80 := regIs_toNat (hm2.regs .X2 _ rfl) (by decide)
  have h23' : Run.RegIs st2.data .X23 80 := hm2.regs .X23 _ rfl
  have k2 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 21616 → BytesAt m.dmem (r.off o) bs →
      Run.noWriteIn _ o bs.length = true → BytesAt st2.data.dmem (r.off o) bs :=
    fun ho h hn ↦ r.bytesAt_kept hpre hm2 hwf ho h hn
  have hZ2 := k2 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide)
  have hT2 := k2 (by omega) hT (by rw [hlI]; decide)
  have hz56 : BytesAt st2.data.dmem (r.off 17040) (List.replicate 56 0) := by
    have e8 : (List.range 8).map (byteOf ((Sym.lit 0).eval (r.env m))) = List.replicate 8 0 := by
      simp only [Sym.eval]; decide
    refine bytesAt_cat (n := 8) rfl (write_eval hm2 (o := 17040) (by decide) (by decide) rfl e8) ?_
    refine bytesAt_cat (n := 8) rfl (write_eval hm2 (o := 17048) (by decide) (by decide) rfl e8) ?_
    refine bytesAt_cat (n := 8) rfl (write_eval hm2 (o := 17056) (by decide) (by decide) rfl e8) ?_
    refine bytesAt_cat (n := 8) rfl (write_eval hm2 (o := 17064) (by decide) (by decide) rfl e8) ?_
    refine bytesAt_cat (n := 8) rfl (write_eval hm2 (o := 17072) (by decide) (by decide) rfl e8) ?_
    refine bytesAt_cat (n := 8) rfl (write_eval hm2 (o := 17080) (by decide) (by decide) rfl e8) ?_
    exact write_eval hm2 (o := 17088) (by decide) (by decide) rfl e8
  refine call_then_elf hpc2 hc.1 (r.memcpy_pre hpre hB2.2.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have kc : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 21616 →
      (o + bs.length ≤ 16960 ∨ 17040 ≤ o) → BytesAt st2.data.dmem (r.off o) bs →
      BytesAt st'.data.dmem (r.off o) bs := fun ho hd h ↦
    r.bytesAt_of_call hpre hB2.2.1 (by decide) (by decide) hout ho hd h
  have hIn : BytesAt st'.data.dmem (r.off 16960) (nodeIn r l e z) := by
    have := bytesOf_of_bytesAt hT2
    rw [hlI] at this
    rw [← this]
    exact hcp
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b167_next),
    hB2.of_call hpre hS (by decide) (by decide) (by decide) hout, hz,
    hN2.of_call hpre hB2.2.1 hS (by decide) (by decide) (by decide) hout,
    regIs_of_saved rfl h23' hS,
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ2,
    bytesAt_cat hlI hIn (kc (by rw [List.length_replicate]; decide) (by decide) hz56)⟩

end

end NativeRustcArm.SphincsVerifyProof.Tree
