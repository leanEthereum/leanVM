module

public import NativeRustcArm.SphincsVerify.Fors.Node2

/-!
# A FORS node, part 3: the children and the final block (`b80 .. b90`)

From `N3`: the children by the inlined `update` loop on hasher B (`b80 .. b84`, one turn:
`memcpy` of their 32 bytes), `N4` at `b85`; the loop's end (`b85`, `b81`) and the state copied
back into hasher A (`b88`, `memcpy` of 200 bytes), `N5` at `b89`; the final block's 136 bytes
zeroed at `24720` and the buffered input copied there (`b89`, `b90`, `memcpy` of 80 bytes), `N6`
at `b91`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- The node's hash input: `PK.seed`, the address, the children. -/
def _root_.NativeRustcArm.SphincsVerifyProof.Run.nodeIn (r : Run) (c z : Nat) : List UInt8 :=
  r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z

/-- **At `b85`**: hasher B has buffered the node's input, its `buf_len` 48 (the loop's store of
80 comes next); the loop's registers. -/
structure N4 (r : Run) (c z : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  hz : z < 10
  x27 : Run.RegIs m .X27 (BitVec.ofNat 64 c)
  x19 : Run.RegIs m .X19 (kpW r)
  x28 : Run.RegIs m .X28 (BitVec.ofNat 64 (z + 1))
  x23 : Run.RegIs m .X23 (r.off 22672)
  x24 : Run.RegIs m .X24 (BitVec.ofNat 64 32)
  x26 : Run.RegIs m .X26 (BitVec.ofNat 64 32)
  st : BytesAt m.dmem (r.off 26768) (List.replicate 200 0)
  buf : BytesAt m.dmem (r.off 26968) (r.nodeIn c z)
  len : BytesAt m.dmem (r.off 27104) (wordBytes (48 : Nat).toUInt64)

/-- **At `b89`**: hasher A's state zero (copied from B), B's buffer the node's input; X25
`buf_len` 80. -/
structure N5 (r : Run) (c z : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  hz : z < 10
  x27 : Run.RegIs m .X27 (BitVec.ofNat 64 c)
  x19 : Run.RegIs m .X19 (kpW r)
  x28 : Run.RegIs m .X28 (BitVec.ofNat 64 (z + 1))
  x25 : Run.RegIs m .X25 (BitVec.ofNat 64 80)
  st : BytesAt m.dmem (r.off 16400) (List.replicate 200 0)
  buf : BytesAt m.dmem (r.off 26968) (r.nodeIn c z)

/-- **At `b91`**: the final block's bytes at `24720`, the node's input then zeros; hasher A's
state zero. -/
structure N6 (r : Run) (c z : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  hz : z < 10
  x27 : Run.RegIs m .X27 (BitVec.ofNat 64 c)
  x19 : Run.RegIs m .X19 (kpW r)
  x26 : Run.RegIs m .X26 (kpW r)
  x28 : Run.RegIs m .X28 (BitVec.ofNat 64 (z + 1))
  x25 : Run.RegIs m .X25 (BitVec.ofNat 64 80)
  st : BytesAt m.dmem (r.off 16400) (List.replicate 200 0)
  blk : BytesAt m.dmem (r.off 24720) (r.nodeIn c z ++ List.replicate 56 0)

end

public section

variable {r : Run}

theorem length_nodeIn {r : Run} {c z : Nat} (hc : c < 24) (hz : z < 10) : (r.nodeIn c z).length = 80 := by
  rw [Run.nodeIn, List.length_append, List.length_append, length_seed, length_nodeAdrsOf,
    length_childrenOf hc hz]

variable [Host]

/-- **The children** (`b80 .. b84` and `memcpy`): from `N3`, `N4` at `b85`. -/
theorem node_s4 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat} {m : MachineData}
    (h : N3 r c z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b85Offset ∧ N4 r c z st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b80Offset⟩ := by
  obtain ⟨hT, hz, h27, h19, h26, h28, hst, hbuf, hlen, hch⟩ := h
  have hB := hT.base
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hm : Match (r.env m) s80 m := match_frameS_lit (k := []) hpre hB trivial hlen
  refine exec_then (hb80 hp) run_b80 hwf hm fun st1 hm1 hpc1 ↦ ?_
  refine ev_at ((show st1.pc = _ from hpc1).trans (lbl_32 hp)) ?_
  refine exec_then (hb82 hp) (exec_after run_b80 run_b82) hwf hm1 fun st2 hm2 hpc2 ↦ ?_
  refine ev_at ((pc_false hpc2).trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b82_next)) ?_
  refine exec_then (hb83 hp) (exec_after run_b82 run_b83) hwf hm2 fun st3 hm3 hpc3 ↦ ?_
  refine ev_at ((pc_false hpc3).trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b83_next)) ?_
  refine exec_then (hb84 hp) (exec_after run_b83 run_b84) hwf hm3 fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hB4, hk4⟩ := hB.of_match hpre hm4 hwf rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st4.data .X0 (r.off 27016) := (hm4.regs .X0 _ rfl).trans (eval_ptr 27016)
  have h1 : Run.RegIs st4.data .X1 (r.off 22672) := (hm4.regs .X1 _ rfl).trans (eval_ptr 22672)
  have h2 : st4.data.regs.X2.toNat = 32 := regIs_toNat (hm4.regs .X2 _ rfl) (by decide)
  have hcl := length_childrenOf (r := r) hT.hc hz
  have hbl : (r.seed ++ r.nodeAdrsOf c z).length = 48 := by
    rw [List.length_append, length_seed, length_nodeAdrsOf]
  have hch4 := keep_blk hpre hm4 hwf hcl (by decide) rfl hch
  refine call_then hpc4 hc.1 (r.memcpy_pre hpre hB4.frame h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st5 hpc5 hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  obtain ⟨hB5, hk5⟩ := hB4.of_call hpre hS (a := 27016) (n := 32) (N := 0) (by decide) (by decide)
    hout (fun o h1 h2 ↦ by unfold Scr; omega)
  have hkc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29376)
      (hd : o + bs.length ≤ 27016 ∨ 27016 + 32 ≤ o) (h : BytesAt st4.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hB4.frame (a := 27016) (n := 32) (N := 0) (by decide) (by decide) hout
      ho hd h
  refine .done _ ⟨hpc5.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b84_next), ⟨TreeSt.of_keep hT hB5 (hk4.trans hk5), hz, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Run.RegIs, hS.1 .X27 rfl, reg_of hm4 rfl]; exact h27
  · rw [Run.RegIs, hS.1 .X19 rfl, reg_of hm4 rfl]; exact h19
  · rw [Run.RegIs, hS.1 .X28 rfl, reg_of hm4 rfl]; exact h28
  · rw [Run.RegIs, hS.1 .X23 rfl]; exact (hm4.regs .X23 _ rfl).trans (eval_ptr 22672)
  · rw [Run.RegIs, hS.1 .X24 rfl]; exact hm4.regs .X24 _ rfl
  · rw [Run.RegIs, hS.1 .X26 rfl]; exact hm4.regs .X26 _ rfl
  · exact hkc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide)
      (keep_blk hpre hm4 hwf (n := 200) (List.length_replicate ..) (by decide) rfl hst)
  · refine bytesAt_cat (n := 48) hbl (hkc (by rw [hbl]; decide) (by rw [hbl]; decide)
      (keep_blk hpre hm4 hwf hbl (by decide) rfl hbuf)) ?_
    have := hcp
    rwa [bytesOf_of_bytesAt' hch4 hcl] at this
  · exact hkc (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; decide)
      (write_val hm4 (o := 27104) (n := 8) rfl (by decide) (by decide) (lit_word 48))

/-- **The state copied back** (`b85`, `b81`, `b88` and `memcpy`): from `N4`, `N5` at `b89`. -/
theorem node_s5 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat} {m : MachineData}
    (h : N4 r c z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b89Offset ∧ N5 r c z st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b85Offset⟩ := by
  obtain ⟨hT, hz, h27, h19, h28, h23, h24, h26, hst, hbuf, hlen⟩ := h
  have hB := hT.base
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hm : Match (r.env m) s85 m :=
    match_frameS_lit (k := [(.X23, .ptr 0 22672), (.X24, .lit 32), (.X26, .lit 32)]) hpre hB
      ⟨known_ptr h23, h24, h26, trivial⟩ hlen
  refine exec_then (hb85 hp) run_b85 hwf hm fun st1 hm1 hpc1 ↦ ?_
  refine ev_at ((pc_true hpc1).trans (lbl_31 hp)) ?_
  refine exec_then (hb81 hp) (exec_after run_b85 run_b81) hwf hm1 fun st2 hm2 hpc2 ↦ ?_
  refine ev_at ((pc_true hpc2).trans (lbl_36 hp)) ?_
  refine exec_then (hb88 hp) (exec_after run_b81 run_b88) hwf hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hB3, hk3⟩ := hB.of_match hpre hm3 hwf rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st3.data .X0 (r.off 16400) := (hm3.regs .X0 _ rfl).trans (eval_ptr 16400)
  have h1 : Run.RegIs st3.data .X1 (r.off 26768) := (hm3.regs .X1 _ rfl).trans (eval_ptr 26768)
  have h2 : st3.data.regs.X2.toNat = 200 := regIs_toNat (hm3.regs .X2 _ rfl) (by decide)
  have hil := length_nodeIn (r := r) hT.hc hz
  have hst3 := keep_blk hpre hm3 hwf (n := 200) (List.length_replicate ..) (by decide) rfl hst
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hB3.frame h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  obtain ⟨hB4, hk4⟩ := hB3.of_call hpre hS (a := 16400) (n := 200) (N := 0) (by decide) (by decide)
    hout (fun o h1 h2 ↦ by unfold Scr; omega)
  refine .done _ ⟨hpc4.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b88_next), ⟨TreeSt.of_keep hT hB4 (hk3.trans hk4), hz, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · rw [Run.RegIs, hS.1 .X27 rfl, reg_of hm3 rfl]; exact h27
  · rw [Run.RegIs, hS.1 .X19 rfl, reg_of hm3 rfl]; exact h19
  · rw [Run.RegIs, hS.1 .X28 rfl, reg_of hm3 rfl]; exact h28
  · rw [Run.RegIs, hS.1 .X25 rfl]; exact hm3.regs .X25 _ rfl
  · have := hcp
    rwa [bytesOf_of_bytesAt' hst3 (List.length_replicate ..)] at this
  · exact r.bytesAt_of_call hpre hB3.frame (a := 16400) (n := 200) (N := 0) (by decide) (by decide)
      hout (by rw [hil]; decide) (by rw [hil]; decide) (keep_blk hpre hm3 hwf hil (by decide) rfl hbuf)

/-- **The final block** (`b89`, `b90` and `memcpy`): from `N5`, `N6` at `b91`. -/
theorem node_s6 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat} {m : MachineData}
    (h : N5 r c z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b91Offset ∧ N6 r c z st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b89Offset⟩ := by
  obtain ⟨hT, hz, h27, h19, h28, h25, hst, hbuf⟩ := h
  have hB := hT.base
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hm : Match (r.env m) s89 m := match_frameS hpre hB ⟨h25, trivial⟩ trivial
  refine exec_then (hb89 hp) run_b89 hwf hm fun st1 hm1 hpc1 ↦ ?_
  refine ev_at ((pc_false hpc1).trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b89_next)) ?_
  refine exec_then (hb90 hp) (exec_after run_b89 run_b90) hwf hm1 fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hB2, hk2⟩ := hB.of_match hpre hm2 hwf rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st2.data .X0 (r.off 24720) := (hm2.regs .X0 _ rfl).trans (eval_ptr 24720)
  have h1 : Run.RegIs st2.data .X1 (r.off 26968) := (hm2.regs .X1 _ rfl).trans (eval_ptr 26968)
  have h2 : st2.data.regs.X2.toNat = 80 := regIs_toNat (hm2.regs .X2 _ rfl) (by decide)
  have hil := length_nodeIn (r := r) hT.hc hz
  have hbuf2 := keep_blk hpre hm2 hwf hil (by decide) rfl hbuf
  have hz2 : BytesAt st2.data.dmem (r.off 24800) (List.replicate 56 0) :=
    write_zeros hm2 (by decide) (by decide +kernel)
  refine call_then hpc2 hc.1 (r.memcpy_pre hpre hB2.frame h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st3 hpc3 hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  obtain ⟨hB3, hk3⟩ := hB2.of_call hpre hS (a := 24720) (n := 80) (N := 0) (by decide) (by decide)
    hout (fun o h1 h2 ↦ by unfold Scr; omega)
  have hkc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29376)
      (hd : o + bs.length ≤ 24720 ∨ 24720 + 80 ≤ o) (h : BytesAt st2.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hB2.frame (a := 24720) (n := 80) (N := 0) (by decide) (by decide) hout
      ho hd h
  refine .done _ ⟨hpc3.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b90_next), ⟨TreeSt.of_keep hT hB3 (hk2.trans hk3), hz, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩⟩
  · rw [Run.RegIs, hS.1 .X27 rfl, reg_of hm2 rfl]; exact h27
  · rw [Run.RegIs, hS.1 .X19 rfl, reg_of hm2 rfl]; exact h19
  · rw [Run.RegIs, hS.1 .X26 rfl, hm2.regs .X26 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [h19]
    exact trunc_kpW
  · rw [Run.RegIs, hS.1 .X28 rfl, reg_of hm2 rfl]; exact h28
  · rw [Run.RegIs, hS.1 .X25 rfl]; exact hm2.regs .X25 _ rfl
  · exact hkc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide)
      (keep_blk hpre hm2 hwf (n := 200) (List.length_replicate ..) (by decide) rfl hst)
  · refine bytesAt_cat (n := 80) hil ?_ (hkc (by rw [List.length_replicate]; decide)
      (by rw [List.length_replicate]; decide) hz2)
    have := hcp
    rwa [bytesOf_of_bytesAt' hbuf2 hil] at this

end

end NativeRustcArm.SphincsVerifyProof.Fors
