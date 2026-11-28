module

public import NativeRustcX64.SphincsVerify.Tree.NodeA

/-!
# The fold's node: `PK.seed` and the address into hasher A, the clone (x86-64)

From `AtN2` (hasher A zero): `PK.seed` buffered (`b162`, its block not full), the inlined
`update` loop's one turn copying the address after it (`b165`, `b167`, `b168`, `b169`, `memcpy`;
`nodeB`, to `AtN3`), `buf_len` 48 (`b170`), the loop done (`b166`) and the clone into hasher B
(`b173`, `memcpy`; `nodeC`, to `AtN4`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

section
variable (r : Run) [Labels]

/-- **At `b170`**: hasher A's state zero, its buffer `PK.seed | ADRS` then zeros, `buf_len` 16;
RBX, R15 the turn's bytes taken and left, R13 the address's end. -/
@[expose] def AtN3 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4104) ∧
    Run.RegIs m .rbx 32 ∧ Run.RegIs m .r15 32 ∧ Run.RegIs m .r13 (r.off 3080) ∧
    BytesAt m.dmem (r.off 4104) (List.replicate 200 0) ∧
    BytesAt m.dmem (r.off 4304) (r.seed ++ r.nodeAdrs l z) ∧
    BytesAt m.dmem (r.off 4352) (List.replicate 88 0) ∧
    BytesAt m.dmem (r.off 4440) (wordBytes 16) ∧
    BytesAt m.dmem (r.off 19144) (r.children l (r.foldUpTo l e z) z)

/-- **At `b174`**: hasher B holds hasher A's bytes, `PK.seed | ADRS` buffered, `buf_len` 48. -/
@[expose] def AtN4 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NW r l z m ∧ Run.RegIs m .r12 (r.off 4104) ∧
    BytesAt m.dmem (r.off 560) (hbytes (r.seed ++ r.nodeAdrs l z) 48) ∧
    BytesAt m.dmem (r.off 19144) (r.children l (r.foldUpTo l e z) z)

end

section
variable {r : Run} [Labels]

/-- A fresh state of the frame with the registers `known`. -/
theorem match_fs (hpre : r.Pre) {m : MachineData} (hF : r.Frame m)
    (h14 : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec)
    {ret : BitVec 64} {known : List (Reg64 × Sym)}
    (hk : AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m (fun _ ↦ 0) ret)) known) :
    Match (r.env m (fun _ ↦ 0) ret) (frameS known) m :=
  r.match_frame hpre hF ⟨h14, hk⟩ trivial trivial trivial

/-- The bytes of a block's state a block does not write, as `bytesOf` reads them. -/
theorem bytesOf_kept (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hk : Kept r.m0.dmem m.dmem)
    (hm : Match (r.env m vars ret) S m') (hwf : (r.env m vars ret).WF) {o n : Nat}
    (ho : o + n ≤ 29400) (hn : Run.noWriteIn S o n = true) :
    bytesOf m'.dmem (r.off o) n = bytesOf m.dmem (r.off o) n := by
  have hmap := (r.frame_mapped hpre hk (a := o) (n := n) ho).1
  have := r.bytesAt_kept hpre hm hwf (by rw [Hasher.length_bytesOf]; exact ho)
    (Hasher.bytesAt_bytesOf hmap) (by rw [Hasher.length_bytesOf]; exact hn)
  have := bytesOf_of_bytesAt this
  rwa [Hasher.length_bytesOf] at this

/-- An address in the frame plus a known word. -/
theorem off_plus {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64} (o c : Nat)
    {x : BitVec 64} (hx : x = BitVec.ofNat 64 c) :
    BinOp.apply .add .W64 ((Sym.ptr 0 (o : Int)).eval (r.env m vars ret)) x = r.off (o + c) := by
  rw [hx]
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [eval_ptr, Run.off, Run.off, BitVec.add_assoc, ← BitVec.ofNat_add]

end

variable [Host] {r : Run}

/-- **`b162` .. `b169` and `memcpy`**: `PK.seed` and the address into hasher A. -/
theorem nodeB (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN2 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b170Offset ∧ AtN3 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b162Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hA0, hAd, hC⟩ := h
  have hl := hB.1
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b169Offset + b169.length)).toBitVec
  have hld : (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b169Offset + b169.length)).toBitVec).load 0 4440 8
      = 0 := load_sub (i := 336) (v := 0) hA0 (by decide)
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b169Offset + b169.length)).toBitVec)
    (known := kAB) ⟨h12.trans (eval_ptr 4104).symm, hB.2.2.2.1.trans (eval_ptr 560).symm, trivial⟩
  refine exec_then (hb162 hp) run_b162 hwf (fun _ h ↦ nomatch h) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := true) hpc1 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_pos (rfl : true = true), lbl_67 hp] at hpc1'
  refine exec_at (hb165 hp) (exec_after run_b162 run_b165) hwf (fun _ h ↦ nomatch h) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hpc2' : st2.pc = Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b167Offset) := hpc2.trans (lbl_68 hp)
  refine exec_at (hb167 hp) (exec_after run_b165 run_b167) hwf (fun _ h ↦ nomatch h) hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hpc3' := pc_cond (b := false) hpc3 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b167_next] at hpc3'
  refine exec_at (hb168 hp) (exec_after run_b167 run_b168) hwf (fun _ h ↦ nomatch h) hpc3' hm3
    fun st4 hm4 hpc4 ↦ ?_
  have hpc4' := pc_cond (b := false) hpc4 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b168_next] at hpc4'
  refine exec_at (hb169 hp) (exec_after run_b168 run_b169) hwf (fun _ _ ↦ rfl) hpc4' hm4
    fun st5 hm5 hpc5 ↦ ?_
  have hc5 := hB.atCall hpre hm5 hwf rfl (by decide)
  have h0 : Run.RegIs st5.data .rdi (r.off 4320) := by
    unfold Run.RegIs reg
    rw [hm5.regs .rdi _ rfl]
    exact off_plus 4304 16 (by sym_simp; rw [hld]; decide)
  have h1 : Run.RegIs st5.data .rsi (r.off 3080) := (hm5.regs .rsi _ rfl).trans (eval_ptr 3080)
  have h2 : (reg st5.data .rdx).toNat = 32 := by
    unfold reg
    rw [hm5.regs .rdx _ rfl]
    sym_simp
    rw [hld]
    decide
  have hbx : Run.RegIs st5.data .rbx 32 := by
    unfold Run.RegIs reg
    rw [hm5.regs .rbx _ rfl]
    sym_simp
    rw [hld]
    decide
  have h15 : Run.RegIs st5.data .r15 32 := hm5.regs .r15 _ rfl
  have h13 : Run.RegIs st5.data .r13 (r.off 3080) := (hm5.regs .r13 _ rfl).trans (eval_ptr 3080)
  have h12' : Run.RegIs st5.data .r12 (r.off 4104) := (hm5.regs .r12 _ rfl).trans (eval_ptr 4104)
  have k5 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29400)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm5 hwf ho hb hn
  have hlc := length_children r (cur := r.foldUpTo l e z) hl hz (length_foldUpTo r l e z)
  have hla := length_nodeAdrs r l z
  have hsl := length_seed r
  have hC5 := k5 (bs := r.children l (r.foldUpTo l e z) z) (by omega) hC (by rw [hlc]; decide)
  have hZ5 := k5 (by rw [List.length_replicate]; decide)
    (bytesAt_zero hA0 (i := 0) (k := 200) (by decide)) (by rw [List.length_replicate]; decide)
  have hZ88 := k5 (by rw [List.length_replicate]; decide)
    (bytesAt_zero hA0 (i := 248) (k := 88) (by decide)) (by rw [List.length_replicate]; decide)
  have hadr := bytesOf_kept hpre hB.2.1.2.2.2 hm5 hwf (o := 3080) (n := 32) (by decide) (by decide)
  have hseed : BytesAt st5.data.dmem (r.off 4304) r.seed := by
    have hs := hB.2.2.1.1.1
    rw [← List.take_append_drop 16 (pkBytes r.w)] at hs
    have hs := bytesAt_append_left hs
    rw [show (pkBytes r.w).take 16 = r.seed from rfl] at hs
    exact write_16 hm5 (o := 4304) (v₀ := .load 0 112 8) (v₁ := .load 0 120 8) (by decide) hsl
      (by decide) (by decide) (load_lo hs hsl) (load_hi hs hsl)
  have hW5 : BytesAt st5.data.dmem (r.off 4440) (wordBytes 16) :=
    write_eval hm5 (o := 4440) (n := 8) (v := .bin .add .W64 (.lit 16) (.load 0 4440 8))
      (w := 16#64) (by decide) (by decide) (by sym_simp; rw [hld]; decide) (by decide)
  have hN5 := hN.of_match hpre hm5 hwf (by decide)
  refine call_then hpc5 hc.1 (r.memcpy_pre hpre hc5 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have kc := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29400)
    (hd : o + bs.length ≤ 4320 ∨ 4320 + 32 ≤ o) (hb : BytesAt st5.data.dmem (r.off o) bs) ↦
    r.bytesAt_of_call hpre hc5 (by decide) (by decide) hout ho hd hb
  have hAd' : BytesAt st'.data.dmem (r.off 4320) (r.nodeAdrs l z) := by
    rw [hadr, ← hla, bytesOf_of_bytesAt hAd] at hcp
    exact hcp
  have hB' := Base.call hpre hB hm5 hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 4320) (n := 32) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc5 (a := 4320) (n := 32) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN5
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b169_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, regIs_of_saved rfl hbx hS, regIs_of_saved rfl h15 hS,
    regIs_of_saved rfl h13 hS,
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ5,
    bytesAt_cat hsl (kc (by omega) (by omega) hseed) hAd',
    kc (by rw [List.length_replicate]; decide) (by rw [List.length_replicate]; decide) hZ88,
    kc (by rw [length_wordBytes]; decide) (by rw [length_wordBytes]; omega) hW5,
    kc (by omega) (by omega) hC5⟩

/-- **`b170`, `b166`, `b173` and `memcpy`**: `buf_len` 48, the clone into hasher B. -/
theorem nodeC (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN3 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b174Offset ∧ AtN4 r l e z st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b170Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, hbx, h15, h13, hZ, hT, hZ88, hW, hC⟩ := h
  have hl := hB.1
  have hwf := frame_wf' hpre hB (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b173Offset + b173.length)).toBitVec
  have hld : (r.env m (fun _ ↦ 0) (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b173Offset + b173.length)).toBitVec).load 0 4440 8
      = (16 : UInt64).toBitVec := load_word hW
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := (Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b173Offset + b173.length)).toBitVec)
    (known := kAB ++ [(.rbx, .lit 32), (.r15, .lit 32), (.r13, .ptr 0 3080)])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4104), (.rbp, .ptr 0 560), (.rbx, .lit 32),
      (.r15, .lit 32), (.r13, .ptr 0 3080)] from
      ⟨h12.trans (eval_ptr 4104).symm, hB.2.2.2.1.trans (eval_ptr 560).symm, hbx, h15,
        h13.trans (eval_ptr 3080).symm, trivial⟩)
  refine exec_then (hb170 hp) run_b170 hwf (fun _ h ↦ nomatch h) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := true) hpc1 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_pos (rfl : true = true), lbl_72 hp] at hpc1'
  refine exec_at (hb166 hp) (exec_after run_b170 run_b166) hwf (fun _ h ↦ nomatch h) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := true) hpc2 rfl
  rw [Sym.ite_pos (rfl : true = true), lbl_73 hp] at hpc2'
  refine exec_at (hb173 hp) (exec_after run_b166 run_b173) hwf (fun _ _ ↦ rfl) hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hc3 := hB.atCall hpre hm3 hwf rfl (by decide)
  have h0 : Run.RegIs st3.data .rdi (r.off 560) := (hm3.regs .rdi _ rfl).trans (eval_ptr 560)
  have h1 : Run.RegIs st3.data .rsi (r.off 4104) := (hm3.regs .rsi _ rfl).trans (eval_ptr 4104)
  have h2 : (reg st3.data .rdx).toNat = 344 := regIs_toNat (hm3.regs .rdx _ rfl) (by decide)
  have h12' : Run.RegIs st3.data .r12 (r.off 4104) := (hm3.regs .r12 _ rfl).trans (eval_ptr 4104)
  have hlT : (r.seed ++ r.nodeAdrs l z).length = 48 := by
    rw [List.length_append, length_seed, length_nodeAdrs]
  have k3 := fun {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 29400)
    (hb : BytesAt m.dmem (r.off o) bs) (hn : Run.noWriteIn _ o bs.length = true) ↦
    r.bytesAt_kept hpre hm3 hwf ho hb hn
  have hlc := length_children r (cur := r.foldUpTo l e z) hl hz (length_foldUpTo r l e z)
  have hA3 : BytesAt st3.data.dmem (r.off 4104) (hbytes (r.seed ++ r.nodeAdrs l z) 48) := by
    unfold hbytes
    refine hbytes_of_parts (by omega)
      (k3 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide))
      (k3 (by omega) hT (by rw [hlT]; decide)) ?_ ?_
    · rw [hlT]
      exact k3 (by rw [List.length_replicate]; decide) hZ88 (by rw [List.length_replicate]; decide)
    · exact write_eval hm3 (o := 4440) (n := 8)
        (v := .bin .add .W64 (.lit 32) (.load 0 4440 8)) (w := 48#64) (by decide) (by decide)
        (by sym_simp; rw [hld]; decide) (by decide)
  have hC3 := k3 (bs := r.children l (r.foldUpTo l e z) z) (by omega) hC (by rw [hlc]; decide)
  have hN3 := hN.of_match hpre hm3 hwf (by decide)
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hc3 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hsp hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hlen := length_hbytes (T := r.seed ++ r.nodeAdrs l z) (by omega) 48
  have hB' := Base.call hpre hB hm3 hwf rfl (by decide) (by decide) rfl hS hsp
    (a := 560) (n := 344) (N := 0) (by decide) (by decide) (Nat.zero_le _) hout
  have hN' : NW r l z st'.data := NW.of_call hpre hc3 (a := 560) (n := 344) (N := 0) (by decide)
    (by decide) (Nat.zero_le _) hout hN3
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b173_next), hB', hz, hN',
    regIs_of_saved rfl h12' hS, ?_,
    r.bytesAt_of_call hpre hc3 (by decide) (by decide) hout (by omega) (by omega) hC3⟩
  have := bytesOf_of_bytesAt hA3
  rw [hlen] at this
  rw [← this]
  exact hcp

end

end NativeRustcX64.SphincsVerifyProof.Tree
