module

public import NativeRustcArm.SphincsVerify.Tree.NodeGlue

/-!
# The fold's node: `PK.seed` and the address into hasher A, the clone

From `AtN2` (hasher A zero): `PK.seed` buffered (`b154`, its block not full), the inlined
`update` loop's one turn copying the address after it (`b157`, `b159`, `b160`, `b161`, `memcpy`;
`nodeB`, to `AtN3`), the count of buffered bytes `48` (`b162`, `b158`, the loop done) and the
clone into hasher B (`b165`, `memcpy`; `nodeC`, to `AtN4`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [Host] (r : Run)

/-- **At `b162`**: hasher A's state zero, its buffer `PK.seed | ADRS` then zeros, `buf_len` 16
(not yet counted the address); X22, X23 the turn's bytes taken and left. -/
@[expose] def AtN3 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NRegs r l z m ∧ Run.RegIs m .X22 32 ∧ Run.RegIs m .X23 32 ∧
    BytesAt m.dmem (r.off 16400) (List.replicate 200 0) ∧
    BytesAt m.dmem (r.off 16600) (r.seed ++ r.nodeAdrs l z) ∧
    BytesAt m.dmem (r.off 16648) (List.replicate 88 0) ∧
    BytesAt m.dmem (r.off 16736) (wordBytes 16) ∧
    BytesAt m.dmem (r.off 22672) (r.children l (r.foldUpTo l e z) z)

/-- The bytes of a hasher whose state is zero and whose buffer holds `T`, `buf_len` `n`. -/
@[expose] def hbytes (T : List UInt8) (n : Nat) : List UInt8 :=
  List.replicate 200 0 ++ (T ++ (List.replicate (136 - T.length) 0 ++ wordBytes n.toUInt64))

/-- **At `b166`**: hasher B holds hasher A's bytes, `PK.seed | ADRS` buffered, `buf_len` 48. -/
@[expose] def AtN4 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NRegs r l z m ∧
    BytesAt m.dmem (r.off 26768) (hbytes (r.seed ++ r.nodeAdrs l z) 48) ∧
    BytesAt m.dmem (r.off 22672) (r.children l (r.foldUpTo l e z) z)

variable {r}

omit [Host] in
theorem seed_at {m : MachineData} (h : r.Inputs m) : BytesAt m.dmem (r.off 8208) r.seed := by
  have h1 := h.1
  rw [← List.take_append_drop 16 (pkBytes r.w)] at h1
  exact bytesAt_append_left h1

/-- **`b154` .. `b161` and `memcpy`**: `PK.seed` and the address into hasher A. -/
theorem nodeB (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN2 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b162Offset ∧ AtN3 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b154Offset⟩ := by
  obtain ⟨hB, hz, h19, h24, -, h27, hA0, hAd, hC⟩ := h
  have hN : NRegs r l z m := ⟨h19, h24, h27⟩
  have hl := hB.1
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  have hld : (r.env m).load 0 16736 8 = 0 := load_sub (i := 336) (v := 0) hA0 (by decide)
  have hseed := seed_at hB.2.2.1.1
  have hsl := length_seed (r := r)
  refine exec_then (hb154 hp) run_b154 hwf (match_base hpre hB) fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := true) hpc1 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_pos (rfl : true = true), lbl_69 hp] at hpc1'
  refine exec_at (hb157 hp) (exec_after run_b154 run_b157) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hpc2' : st2.pc = Host.addrOf (r.k + NativeRustcArm.Sphincs.SphincsVerify.b159Offset) := hpc2.trans (lbl_71 hp)
  refine exec_at (hb159 hp) (exec_after run_b157 run_b159) hwf hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
  have hpc3' := pc_cond (b := false) hpc3 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b159_next] at hpc3'
  refine exec_at (hb160 hp) (exec_after run_b159 run_b160) hwf hpc3' hm3 fun st4 hm4 hpc4 ↦ ?_
  have hpc4' := pc_cond (b := false) hpc4 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b160_next] at hpc4'
  refine exec_at (hb161 hp) (exec_after run_b160 run_b161) hwf hpc4' hm4 fun st5 hm5 hpc5 ↦ ?_
  have hB5 := Base.of_match hpre hB hm5 hwf rfl rfl (by decide) (by decide) rfl rfl rfl
  have hN5 := hN.of_match hm5 rfl rfl rfl
  have h0 : Run.RegIs st5.data .X0 (r.off 16616) := by
    unfold Run.RegIs
    rw [hm5.regs .X0 _ rfl]
    sym_simp
    rw [hld, Run.off, BitVec.add_assoc]
    rfl
  have h1 : Run.RegIs st5.data .X1 (r.off 23696) := (hm5.regs .X1 _ rfl).trans (eval_ptr 23696)
  have h2 : st5.data.regs.X2.toNat = 32 := by
    have := hm5.regs .X2 _ rfl
    sym_simp at this
    rw [hld] at this
    exact regIs_toNat (this.trans (by decide)) (by decide)
  have h22 : Run.RegIs st5.data .X22 32 := by
    unfold Run.RegIs
    rw [hm5.regs .X22 _ rfl]
    sym_simp
    rw [hld]
    decide
  have h23 : Run.RegIs st5.data .X23 32 := hm5.regs .X23 _ rfl
  -- the bytes after the blocks
  have k5 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 29376 → BytesAt m.dmem (r.off o) bs →
      Run.noWriteIn _ o bs.length = true → BytesAt st5.data.dmem (r.off o) bs :=
    fun ho h hn ↦ r.bytesAt_kept hpre hm5 hwf ho h hn
  have hAd5 := k5 (by rw [length_nodeAdrs]; decide) hAd (by rw [length_nodeAdrs]; decide)
  have hlc := length_children (r := r) hl hz (length_foldUpTo r l e z)
  have hC5 := k5 (by omega) hC (by rw [hlc]; decide)
  have hZ5 := k5 (by rw [List.length_replicate]; decide) (bytesAt_zero hA0 (i := 0) (k := 200)
    (by decide)) (by rw [List.length_replicate]; decide)
  have hZ88 := k5 (by rw [List.length_replicate]; decide) (bytesAt_zero hA0 (i := 248) (k := 88)
    (by decide)) (by rw [List.length_replicate]; decide)
  have hS5 : BytesAt st5.data.dmem (r.off 16600) r.seed := by
    rw [← List.take_append_drop 8 r.seed]
    refine bytesAt_cat (n := 8) (by simp [hsl]) (write_eval hm5 (o := 16600) (n := 8) (v := .load 0 8208 8)
      (by decide) (by decide) rfl (load_lo hseed hsl)) ?_
    exact write_eval hm5 (o := 16608) (n := 8) (v := .load 0 8216 8) (by decide) (by decide) rfl
      (load_hi hseed hsl)
  have hW5 : BytesAt st5.data.dmem (r.off 16736) (wordBytes 16) :=
    write_eval hm5 (o := 16736) (n := 8) (v := .bin .add .W64 (.load 0 16736 8) (.lit 16))
      (w := 16#64) (by decide) (by decide) (by sym_simp; rw [hld]; decide) (by decide)
  -- the call
  refine call_then hpc5 hc.1 (r.memcpy_pre hpre hB5.2.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have kc : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 29376 →
      (o + bs.length ≤ 16616 ∨ 16648 ≤ o) → BytesAt st5.data.dmem (r.off o) bs →
      BytesAt st'.data.dmem (r.off o) bs :=
    fun ho hd h ↦ r.bytesAt_of_call hpre hB5.2.1 (by decide) (by decide) hout ho hd h
  have hAdr : BytesAt st'.data.dmem (r.off 16616) (r.nodeAdrs l z) := by
    have := bytesOf_of_bytesAt hAd5
    rw [length_nodeAdrs] at this
    rw [← this]; exact hcp
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b161_next),
    hB5.of_call hpre hS (by decide) (by decide) (by decide) hout, hz, hN5.of_saved hS,
    regIs_of_saved rfl h22 hS, regIs_of_saved rfl h23 hS,
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ5,
    bytesAt_cat hsl (kc (by rw [hsl]; decide) (by rw [hsl]; omega) hS5) hAdr,
    kc (by rw [List.length_replicate]; decide) (by decide) hZ88,
    kc (by rw [length_wordBytes]; decide) (by decide) hW5,
    kc (by omega) (by omega) hC5⟩

end

end NativeRustcArm.SphincsVerifyProof.Tree
