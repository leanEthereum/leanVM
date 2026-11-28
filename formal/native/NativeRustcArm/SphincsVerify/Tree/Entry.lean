module

public import NativeRustcArm.SphincsVerify.Tree.Fold

/-!
# The fold's entry

From the one-time leaf's hash at `22672` (`AtL6`): the path's slice checks (`b149`, `b150`, the
panic `b192` unreachable: the path's nodes `pathStart l .. pathStart l + heightOf l` are within the
26), the height-0 case (`b151`, unreachable), the loop's registers and the leaf's 16 bytes
(`b152`; `entry`, to `AtNode … 0`); the region from the chain ends to the fold's end (`toFold`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [Host] {r : Run}

omit [Host] in
theorem l_cases {l : Nat} (hl : l < 3) : l = 0 ∨ l = 1 ∨ l = 2 := by omega

/-- **`b149` .. `b152`**: from the leaf's hash to the loop head. -/
theorem entry (hp : Placed code r.k) (hpre : r.Pre) {l : Nat} {e : List (List UInt8)}
    {m : MachineData} (h : AtL6 r l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b153Offset ∧ AtNode r l e 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b149Offset⟩ := by
  obtain ⟨hB, hH⟩ := h
  have hl := hB.1
  obtain ⟨-, -, -, h24, -, h40, -, -, -, -, -⟩ := hB.2.2.1.2
  have hld24 : (r.env m).load 0 24 8 = l.toUInt64.toBitVec := load_word h24
  have hld40 : (r.env m).load 0 40 8 = (layerHeights.getD l 0).toUInt64.toBitVec := load_word h40
  have hld376 : (r.env m).load 0 376 8 = r.off 12468 := load_word hB.2.2.1.1.2.2
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then (hb149 hp) run_b149 hwf (match_base hpre hB) fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := false) hpc1 (by
    sym_simp; rw [hld24, hld40]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b149_next] at hpc1'
  refine exec_at (hb150 hp) (exec_after run_b149 run_b150) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := false) hpc2 (by
    sym_simp; rw [hld24, hld40]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b150_next] at hpc2'
  refine exec_at (hb151 hp) (exec_after run_b150 run_b151) hwf hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
  have hpc3' := pc_cond (b := false) hpc3 (by
    sym_simp; rw [hld40]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b151_next] at hpc3'
  refine exec_at (hb152 hp) (exec_after run_b151 run_b152) hwf hpc3' hm3 fun st4 hm4 hpc4 ↦ ?_
  have hB4 := Base.of_match hpre hB hm4 hwf rfl rfl (by decide) (by decide) rfl rfl rfl
  have hhz : 0 < heightOf l := by rcases l_cases hl with rfl | rfl | rfl <;> decide
  have hhash : (hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten)).length = 32 :=
    NativeRustc.Sphincs.length_hashBytes _
  refine .done _ ⟨hpc4.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b152_next), hB4, hhz, ?_, ?_, ?_, ?_, ?_⟩
  · exact hm4.regs .X19 _ rfl
  · unfold Run.RegIs
    rw [hm4.regs .X24 _ rfl]
    sym_simp
    rw [hld24, hld376, Run.off, BitVec.add_assoc]
    congr 1
    rcases l_cases hl with rfl | rfl | rfl <;> decide
  · exact (hm4.regs .X20 _ rfl).trans (eval_ptr 21648)
  · unfold Run.RegIs
    rw [hm4.regs .X27 _ rfl]
    sym_simp
    rw [hld24]
    rcases l_cases hl with rfl | rfl | rfl <;> decide
  · show BytesAt st4.data.dmem (r.off 20624)
      ((hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten)).take 16)
    generalize hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten) = V at hH hhash ⊢
    have lo := bytes_load (vars := fun _ ↦ 0) (n := 8) (bytesAt_sub hH 0 8) (by simp [hhash])
      (by decide)
    have hi := bytes_load (vars := fun _ ↦ 0) (n := 8) (bytesAt_sub hH 8 8) (by simp [hhash])
      (by decide)
    rw [List.drop_zero] at lo
    rw [List.take_add (l := V) (i := 8) (j := 8)]
    refine bytesAt_cat (n := 8) (by simp [hhash]) (write_eval hm4 (o := 20624)
      (v := .load 0 22672 8) (by decide) (by decide) rfl lo) ?_
    exact write_eval hm4 (o := 20632) (v := .load 0 22680 8) (by decide) (by decide) rfl hi

/-- **From layer `l`'s chain ends to the fold's end.** -/
theorem toFold (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : r.AtWotsPk l e m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b179Offset ∧ AtFold r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b143Offset⟩ :=
  Eventually.bind (stage1 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (stage2 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (stage3 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (stage4 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (stage5 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (stage6 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (entry hp hpre h) <| at_pc fun _ h ↦ fold hp hc hpre h

end

end NativeRustcArm.SphincsVerifyProof.Tree
