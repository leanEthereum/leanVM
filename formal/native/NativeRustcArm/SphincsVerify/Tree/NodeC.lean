module

public import NativeRustcArm.SphincsVerify.Tree.NodeB

/-!
# The fold's node: the clone, the children into hasher B

From `AtN3`: `buf_len` 48 (`b162`), the loop done (`b158`), hasher A cloned into hasher B
(`b165`, `memcpy`; `nodeC`, to `AtN4`); then the children's `update` loop's one turn into B
(`b166`, `b168`, `b169`, `b170`, `memcpy`; `nodeD`, to `AtN5`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [Host] (r : Run)

/-- The node's hash input: `PK.seed | ADRS | children`. -/
@[expose] def nodeIn (l : Nat) (e : List (List UInt8)) (z : Nat) : List UInt8 :=
  r.seed ++ r.nodeAdrs l z ++ r.children l (r.foldUpTo l e z) z

/-- **At `b171`**: hasher B holds `PK.seed | ADRS | children`, `buf_len` still 48; X22, X28 the
turn's bytes taken and left. -/
@[expose] def AtN5 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NRegs r l z m ∧ Run.RegIs m .X22 32 ∧ Run.RegIs m .X28 32 ∧
    BytesAt m.dmem (r.off 26768) (hbytes (nodeIn r l e z) 48)

variable {r}

omit [Host] in
theorem length_nodeIn {l z : Nat} {e : List (List UInt8)} (hl : l < 3) (hz : z < heightOf l) :
    (nodeIn r l e z).length = 80 := by
  rw [nodeIn, List.length_append, List.length_append, length_seed, length_nodeAdrs,
    length_children hl hz (length_foldUpTo r l e z)]

/-- **`b162`, `b158`, `b165` and `memcpy`**: the clone. -/
theorem nodeC (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN3 r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b166Offset ∧ AtN4 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b162Offset⟩ := by
  obtain ⟨hB, hz, hN, h22, h23, hZ, hSA, hZ88, hW, hC⟩ := h
  have hl := hB.1
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  have hld : (r.env m).load 0 16736 8 = (16 : UInt64).toBitVec := load_word hW
  have hm0 : Match (r.env m) s3 m := r.match_frame hpre hB.2.1
    (allOf_append (allOf_keptRegs hB _) ⟨h22, h23, trivial⟩) trivial trivial trivial
  refine exec_then (hb162 hp) run_b162 hwf hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := true) hpc1 (by sym_simp; rw [hld]; decide)
  rw [Sym.ite_pos (rfl : true = true), lbl_70 hp] at hpc1'
  refine exec_at (hb158 hp) (exec_after run_b162 run_b158) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := true) hpc2 rfl
  rw [Sym.ite_pos (rfl : true = true), lbl_75 hp] at hpc2'
  refine exec_at (hb165 hp) (exec_after run_b158 run_b165) hwf hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
  have hB3 := Base.of_match hpre hB hm3 hwf rfl rfl (by decide) (by decide) rfl rfl rfl
  have hN3 := hN.of_match hm3 rfl rfl rfl
  have h0 : Run.RegIs st3.data .X0 (r.off 26768) := (hm3.regs .X0 _ rfl).trans (eval_ptr 26768)
  have h1 : Run.RegIs st3.data .X1 (r.off 16400) := (hm3.regs .X1 _ rfl).trans (eval_ptr 16400)
  have h2 : st3.data.regs.X2.toNat = 344 := regIs_toNat (hm3.regs .X2 _ rfl) (by decide)
  have hlT : (r.seed ++ r.nodeAdrs l z).length = 48 := by
    rw [List.length_append, length_seed, length_nodeAdrs]
  have k3 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 29376 → BytesAt m.dmem (r.off o) bs →
      Run.noWriteIn _ o bs.length = true → BytesAt st3.data.dmem (r.off o) bs :=
    fun ho h hn ↦ r.bytesAt_kept hpre hm3 hwf ho h hn
  have hlc := length_children (r := r) hl hz (length_foldUpTo r l e z)
  have hA3 : BytesAt st3.data.dmem (r.off 16400) (hbytes (r.seed ++ r.nodeAdrs l z) 48) := by
    unfold hbytes
    refine hbytes_of_parts (by omega)
      (k3 (by rw [List.length_replicate]; decide) hZ (by rw [List.length_replicate]; decide))
      (k3 (by omega) hSA (by rw [hlT]; decide)) ?_ ?_
    · rw [hlT]
      exact k3 (by rw [List.length_replicate]; decide) hZ88 (by rw [List.length_replicate]; decide)
    · exact write_eval hm3 (o := 16736) (n := 8)
        (v := .bin .add .W64 (.load 0 16736 8) (.lit 32)) (w := 48#64) (by decide) (by decide)
        (by sym_simp; rw [hld]; decide) (by decide)
  have hC3 := k3 (by omega) hC (by rw [hlc]; decide)
  refine call_then hpc3 hc.1 (r.memcpy_pre hpre hB3.2.1 h0 h1 h2 (by decide) (by decide)
    (by decide)) fun st' hpc' hpost ↦ ?_
  obtain ⟨hcp, hout, hS⟩ := r.memcpy_out h0 h1 h2 hpost
  have hlen : (hbytes (r.seed ++ r.nodeAdrs l z) 48).length = 344 := by
    simp only [hbytes, List.length_append, List.length_replicate, hlT, length_wordBytes]
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b165_next),
    hB3.of_call hpre hS (by decide) (by decide) (by decide) hout, hz, hN3.of_saved hS, ?_,
    r.bytesAt_of_call hpre hB3.2.1 (by decide) (by decide) hout (by omega) (by omega) hC3⟩
  have := bytesOf_of_bytesAt hA3
  rw [hlen] at this
  rw [← this]
  exact hcp

end

end NativeRustcArm.SphincsVerifyProof.Tree
