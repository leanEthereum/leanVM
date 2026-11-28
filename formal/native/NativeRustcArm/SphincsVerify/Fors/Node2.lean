module

public import NativeRustcArm.SphincsVerify.Fors.Node1

/-!
# A FORS node, part 2: the prefix and the clone (`b68 .. b79`)

From `N1`: `PK.seed` buffered in hasher A (`b68`, the buffer not full), the address by the
inlined `update` loop (`b71 .. b75`, one turn: `memcpy` of its 32 bytes, the slice checks
passing), `N2` at `b76`; the loop's end (`b76`, `b72`) and the clone into hasher B (`b79`,
`memcpy` of 344 bytes), `N3` at `b80`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- **At `b76`**: hasher A's state zero, `PK.seed` and the address buffered, `buf_len` 16 (the
loop's store of 48 comes next); the loop's registers. -/
structure N2 (r : Run) (c z : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  hz : z < 10
  x19 : Run.RegIs m .X19 (BitVec.ofNat 64 c)
  x28 : Run.RegIs m .X28 (BitVec.ofNat 64 (z + 1))
  x27 : wordBytes (m.regs.getXReg .X27) = be64 (r.key 0).tree
  x26 : Run.RegIs m .X26 (kpW r)
  x23 : Run.RegIs m .X23 (r.off 23696)
  x24 : Run.RegIs m .X24 (BitVec.ofNat 64 32)
  x25 : Run.RegIs m .X25 (BitVec.ofNat 64 32)
  st : BytesAt m.dmem (r.off 16400) (List.replicate 200 0)
  buf : BytesAt m.dmem (r.off 16600) (r.seed ++ r.nodeAdrsOf c z)
  len : BytesAt m.dmem (r.off 16736) (wordBytes (16 : Nat).toUInt64)
  ch : BytesAt m.dmem (r.off 22672) (r.childrenOf c z)

/-- **At `b80`**: hasher B a copy of A (state zero, `PK.seed` and the address buffered,
`buf_len` 48); X27 the tree, X19 the key pair's word. -/
structure N3 (r : Run) (c z : Nat) (m : MachineData) : Prop where
  tree : TreeSt r c m
  hz : z < 10
  x27 : Run.RegIs m .X27 (BitVec.ofNat 64 c)
  x19 : Run.RegIs m .X19 (kpW r)
  x26 : Run.RegIs m .X26 (kpW r)
  x28 : Run.RegIs m .X28 (BitVec.ofNat 64 (z + 1))
  st : BytesAt m.dmem (r.off 26768) (List.replicate 200 0)
  buf : BytesAt m.dmem (r.off 26968) (r.seed ++ r.nodeAdrsOf c z)
  len : BytesAt m.dmem (r.off 27104) (wordBytes (48 : Nat).toUInt64)
  ch : BytesAt m.dmem (r.off 22672) (r.childrenOf c z)

end

public section

variable {r : Run}

theorem length_seed : r.seed.length = 16 := by
  show ((pkBytes r.w).take 16).length = 16
  rw [List.length_take, length_pkBytes]
  rfl

/-- `PK.seed` in the frame. -/
theorem bytesAt_seed {m : MachineData} (h : r.Inputs m) : BytesAt m.dmem (r.off 8208) r.seed := by
  have h1 := h.1
  rw [← List.take_append_drop 16 (pkBytes r.w)] at h1
  exact bytesAt_prefix h1

theorem length_nodeAdrsOf (c z : Nat) : (r.nodeAdrsOf c z).length = 32 := by
  rw [nodeAdrsOf_eq]; rfl

theorem length_childrenOf {c z : Nat} (hc : c < 24) (hz : z < 10) : (r.childrenOf c z).length = 32 := by
  rw [Run.childrenOf]
  split <;> simp [length_forsUpTo, length_pathNode hc hz]

theorem trunc_kpW : UnOp.apply .trunc .W32 (kpW r) = kpW r := by
  simp [UnOp.apply, kpW]

theorem zeros_slice {o n N : Nat} (h : o + n ≤ N) :
    ((List.replicate N (0 : UInt8)).drop o).take n = List.replicate n 0 := by
  rw [List.drop_replicate, List.take_replicate]
  congr 1
  omega

theorem wordBytes_zero : wordBytes (0 : Nat).toUInt64 = List.replicate 8 0 := rfl

variable [Host]

/-- **The prefix** (`b68 .. b75` and `memcpy`): from `N1`, `N2` at `b76`. -/
theorem node_s2 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat} {m : MachineData}
    (h : N1 r c z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b76Offset ∧ N2 r c z st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b68Offset⟩ := by
  obtain ⟨hT, hz, h19, h28, h27, h26, hA, hch, had⟩ := h
  have hB := hT.base
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hA0 : BytesAt m.dmem (r.off 16400) (List.replicate 200 0) := by
    have := bytesAt_slice hA 0 200
    rwa [zeros_slice (by decide)] at this
  have hlen0 : BytesAt m.dmem (r.off 16736) (wordBytes (0 : Nat).toUInt64) := by
    have := bytesAt_slice hA 336 8
    rwa [zeros_slice (by decide), ← wordBytes_zero] at this
  have hm : Match (r.env m) s68 m := match_frameS_lit (k := []) hpre hB trivial hlen0
  refine exec_then (hb68 hp) run_b68 hwf hm fun st1 hm1 hpc1 ↦ ?_
  refine ev_at ((pc_true hpc1).trans (lbl_24 hp)) ?_
  refine exec_then (hb71 hp) (exec_after run_b68 run_b71) hwf hm1 fun st2 hm2 hpc2 ↦ ?_
  refine ev_at ((show st2.pc = _ from hpc2).trans (lbl_26 hp)) ?_
  refine exec_then (hb73 hp) (exec_after run_b71 run_b73) hwf hm2 fun st3 hm3 hpc3 ↦ ?_
  refine ev_at ((pc_false hpc3).trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b73_next)) ?_
  refine exec_then (hb74 hp) (exec_after run_b73 run_b74) hwf hm3 fun st4 hm4 hpc4 ↦ ?_
  refine ev_at ((pc_false hpc4).trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b74_next)) ?_
  refine exec_then (hb75 hp) (exec_after run_b74 run_b75) hwf hm4 fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hB5, hk5⟩ := hB.of_match hpre hm5 hwf rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st5.data .X0 (r.off 16616) := (hm5.regs .X0 _ rfl).trans (eval_ptr 16616)
  have h1 : Run.RegIs st5.data .X1 (r.off 23696) := (hm5.regs .X1 _ rfl).trans (eval_ptr 23696)
  have h2 : st5.data.regs.X2.toNat = 32 := regIs_toNat (hm5.regs .X2 _ rfl) (by decide)
  have had5 : BytesAt st5.data.dmem (r.off 23696) (r.nodeAdrsOf c z) :=
    keep_blk hpre hm5 hwf (length_nodeAdrsOf c z) (by decide) rfl had
  refine call_then hpc5 hc.1 (r.memcpy_pre hpre hB5.frame h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st6 hpc6 hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  obtain ⟨hB6, hk6⟩ := hB5.of_call hpre hS (a := 16616) (n := 32) (N := 0) (by decide) (by decide)
    hout (fun o h1 h2 ↦ by unfold Scr; omega)
  have hkc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29376)
      (hd : o + bs.length ≤ 16616 ∨ 16616 + 32 ≤ o) (h : BytesAt st5.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hB5.frame (a := 16616) (n := 32) (N := 0) (by decide) (by decide) hout
      ho hd h
  have hseed := bytesAt_seed hB.inputs
  have hsl := length_seed (r := r)
  have hs0 := bytesAt_slice hseed 0 8
  have hs8 := bytesAt_slice hseed 8 8
  rw [List.drop_zero] at hs0
  refine .done _ ⟨hpc6.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b75_next), ⟨TreeSt.of_keep hT hB6 (hk5.trans hk6), hz, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Run.RegIs, hS.1 .X19 rfl, reg_of hm5 rfl]; exact h19
  · rw [Run.RegIs, hS.1 .X28 rfl, reg_of hm5 rfl]; exact h28
  · rw [hS.1 .X27 rfl, reg_of hm5 rfl]; exact h27
  · rw [Run.RegIs, hS.1 .X26 rfl, reg_of hm5 rfl]; exact h26
  · rw [Run.RegIs, hS.1 .X23 rfl]; exact (hm5.regs .X23 _ rfl).trans (eval_ptr 23696)
  · rw [Run.RegIs, hS.1 .X24 rfl]; exact hm5.regs .X24 _ rfl
  · rw [Run.RegIs, hS.1 .X25 rfl]; exact hm5.regs .X25 _ rfl
  · exact hkc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide)
      (keep_blk hpre hm5 hwf (n := 200) (List.length_replicate ..) (by decide) rfl hA0)
  · refine bytesAt_cat (n := 16) hsl (hkc (by rw [hsl]; omega) (by rw [hsl]; omega)
      (pieces16 hsl ?_ ?_)) ?_
    · exact write_load hm5 (o := 16600) (o' := 8208) (by decide) le_rfl (by decide) (by simp [hsl]) hs0
    · exact write_load hm5 (o := 16608) (o' := 8216) (by decide) le_rfl (by decide) (by simp [hsl]) hs8
    · have := hcp
      rwa [bytesOf_of_bytesAt' had5 (length_nodeAdrsOf c z)] at this
  · exact hkc (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; decide)
      (write_val hm5 (o := 16736) (n := 8) rfl (by decide) (by decide) (lit_word 16))
  · exact hkc (by rw [length_childrenOf hT.hc hz]; omega) (by rw [length_childrenOf hT.hc hz]; omega)
      (keep_blk hpre hm5 hwf (length_childrenOf hT.hc hz) (by decide) rfl hch)

/-- **The clone** (`b76`, `b72`, `b79` and `memcpy`): from `N2`, `N3` at `b80`. -/
theorem node_s3 (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {c z : Nat} {m : MachineData}
    (h : N2 r c z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b80Offset ∧ N3 r c z st.data) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b76Offset⟩ := by
  obtain ⟨hT, hz, h19, h28, h27, h26, h23, h24, h25, hst, hbuf, hlen, hch⟩ := h
  have hB := hT.base
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hm : Match (r.env m) s76 m :=
    match_frameS_lit (k := [(.X23, .ptr 0 23696), (.X24, .lit 32), (.X25, .lit 32)]) hpre hB
      ⟨known_ptr h23, h24, h25, trivial⟩ hlen
  refine exec_then (hb76 hp) run_b76 hwf hm fun st1 hm1 hpc1 ↦ ?_
  refine ev_at ((pc_true hpc1).trans (lbl_25 hp)) ?_
  refine exec_then (hb72 hp) (exec_after run_b76 run_b72) hwf hm1 fun st2 hm2 hpc2 ↦ ?_
  refine ev_at ((pc_true hpc2).trans (lbl_30 hp)) ?_
  refine exec_then (hb79 hp) (exec_after run_b72 run_b79) hwf hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hB3, hk3⟩ := hB.of_match hpre hm3 hwf rfl rfl rfl rfl rfl rfl
  have h0 : Run.RegIs st3.data .X0 (r.off 26768) := (hm3.regs .X0 _ rfl).trans (eval_ptr 26768)
  have h1 : Run.RegIs st3.data .X1 (r.off 16400) := (hm3.regs .X1 _ rfl).trans (eval_ptr 16400)
  have h2 : st3.data.regs.X2.toNat = 344 := regIs_toNat (hm3.regs .X2 _ rfl) (by decide)
  have hbl : (r.seed ++ r.nodeAdrsOf c z).length = 48 := by
    rw [List.length_append, length_seed, length_nodeAdrsOf]
  have hst3 := keep_blk hpre hm3 hwf (n := 200) (List.length_replicate ..) (by decide) rfl hst
  have hbuf3 := keep_blk hpre hm3 hwf hbl (by decide) rfl hbuf
  have hlen3 : BytesAt st3.data.dmem (r.off 16736) (wordBytes (48 : Nat).toUInt64) :=
    write_val hm3 (o := 16736) (n := 8) rfl (by decide) (by decide) (lit_word 48)
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hB3.frame h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st4 hpc4 hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  obtain ⟨hB4, hk4⟩ := hB3.of_call hpre hS (a := 26768) (n := 344) (N := 0) (by decide) (by decide)
    hout (fun o h1 h2 ↦ by unfold Scr; omega)
  refine .done _ ⟨hpc4.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b79_next), ⟨TreeSt.of_keep hT hB4 (hk3.trans hk4), hz, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Run.RegIs, hS.1 .X27 rfl, hm3.regs .X27 _ rfl]; exact h19
  · rw [Run.RegIs, hS.1 .X19 rfl, hm3.regs .X19 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [h26]
    exact trunc_kpW
  · rw [Run.RegIs, hS.1 .X26 rfl, reg_of hm3 rfl]; exact h26
  · rw [Run.RegIs, hS.1 .X28 rfl, reg_of hm3 rfl]; exact h28
  · exact slice_copy (o := 0) hcp hst3 (by rw [List.length_replicate]; decide)
  · exact slice_copy (o := 200) hcp hbuf3 (by rw [hbl]; omega)
  · exact slice_copy (o := 336) hcp hlen3 (by rw [length_wordBytes])
  · have hcl := length_childrenOf (r := r) hT.hc hz
    exact r.bytesAt_of_call hpre hB3.frame (a := 26768) (n := 344) (N := 0) (by decide) (by decide)
      hout (by rw [hcl]; omega) (by rw [hcl]; omega) (keep_blk hpre hm3 hwf hcl (by decide) rfl hch)

end

end NativeRustcArm.SphincsVerifyProof.Fors
