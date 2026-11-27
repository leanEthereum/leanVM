module

public import NativeRustcArm.SphincsVerify.Tree.Fold

/-!
# The fold's entry

From the one-time leaf's hash at `14912` (`AtL6`): the path's slice checks (`b140`, `b141`, the
panic `b183` unreachable: the path's nodes `pathStart l .. pathStart l + heightOf l` are within the
26), the height-0 case (`b142`, unreachable), the loop's registers, path pointer spill `432` and
the leaf's 16 bytes (`b143`; `entry`, to `AtNode … 0`); the region from the chain ends to the
fold's end (`toFold`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [ElfHost] {r : Run}

omit [ElfHost] in
theorem l_cases {l : Nat} (hl : l < 3) : l = 0 ∨ l = 1 ∨ l = 2 := by omega

/-- **`b140` .. `b143`**: from the leaf's hash to the loop head. -/
theorem entry (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) {l : Nat} {e : List (List UInt8)}
    {m : MachineData} (h : AtL6 r l e m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset ∧ AtNode r l e 0 st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b140Offset⟩ := by
  obtain ⟨hB, hH⟩ := h
  have hl := hB.1
  obtain ⟨-, -, -, h32, -, h48, -⟩ := hB.2.2.1.2
  have hld32 : (r.env m).load 0 32 8 = l.toUInt64.toBitVec := load_word h32
  have hld48 : (r.env m).load 0 48 8 = (layerHeights.getD l 0).toUInt64.toBitVec := load_word h48
  have hld392 : (r.env m).load 0 392 8 = r.off 4708 := load_word hB.2.2.1.1.2.2
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then_elf (hb140 hp) run_b140 hwf (match_base hpre hB) fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := false) hpc1 (by
    sym_simp; rw [hld32, hld48]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b140_next] at hpc1'
  refine exec_at_elf (hb141 hp) (exec_after run_b140 run_b141) hwf hpc1' hm1 fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := false) hpc2 (by
    sym_simp; rw [hld32, hld48]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b141_next] at hpc2'
  refine exec_at_elf (hb142 hp) (exec_after run_b141 run_b142) hwf hpc2' hm2 fun st3 hm3 hpc3 ↦ ?_
  have hpc3' := pc_cond (b := false) hpc3 (by
    sym_simp; rw [hld48]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b142_next] at hpc3'
  refine exec_at_elf (hb143 hp) (exec_after run_b142 run_b143) hwf hpc3' hm3 fun st4 hm4 hpc4 ↦ ?_
  have hB4 := Base.of_match hpre hB hm4 hwf rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl rfl
  have hhz : 0 < heightOf l := by rcases l_cases hl with rfl | rfl | rfl <;> decide
  have hhash : (hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten)).length = 32 :=
    NativeRustc.Sphincs.length_hashBytes _
  refine .done _ ⟨hpc4.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b143_next), hB4, hhz, ?_, ?_, ?_, ?_⟩
  · exact hm4.regs .X24 _ rfl
  · have hv : (Sym.bin .add .W64 (.load 0 392 8) (.un (.shift .LSL 4) .W64
      (.ite (.cmp .eq .W64 (.load 0 32 8) (.lit 0)) (.lit 0)
        (.ite (.cmp .eq .W64 (.load 0 32 8) (.lit 1)) (.lit 8) (.lit 16))))).eval (r.env m) =
        r.off (4708 + 16 * pathStart l) := by
      sym_simp
      rw [hld32, hld392, Run.off, BitVec.add_assoc]
      congr 1
      rcases l_cases hl with rfl | rfl | rfl <;> decide
    exact write_eval hm4 (o := 432) (n := 8) (by decide) (by decide) hv (bytes_word _)
  · unfold Run.RegIs
    rw [hm4.regs .X28 _ rfl]
    sym_simp
    rw [hld32]
    rcases l_cases hl with rfl | rfl | rfl <;> decide
  · show BytesAt st4.data.dmem (r.off 12864)
      ((hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten)).take 16)
    generalize hashBytes (r.seed ++ (r.key l).adrs 1 ++ e.flatten) = V at hH hhash ⊢
    have lo := bytes_load (vars := fun _ ↦ 0) (n := 8) (bytesAt_sub hH 0 8) (by simp [hhash])
      (by decide)
    have hi := bytes_load (vars := fun _ ↦ 0) (n := 8) (bytesAt_sub hH 8 8) (by simp [hhash])
      (by decide)
    rw [List.drop_zero] at lo
    rw [List.take_add (l := V) (i := 8) (j := 8)]
    refine bytesAt_cat (n := 8) (by simp [hhash]) (write_eval hm4 (o := 12864)
      (v := .load 0 14912 8) (by decide) (by decide) rfl lo) ?_
    exact write_eval hm4 (o := 12872) (v := .load 0 14920 8) (by decide) (by decide) rfl hi

/-- **From layer `l`'s chain ends to the fold's end.** -/
theorem toFold (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : r.AtWotsPk l e m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b170Offset ∧ AtFold r l e st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b134Offset⟩ :=
  Eventually.bind_elf (stage1 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (stage2 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (stage3 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (stage4 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (stage5 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (stage6 hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind_elf (entry hp hpre h) <| at_pc fun _ h ↦ fold hp hc hpre h

end

end NativeRustcArm.SphincsVerifyProof.Tree
