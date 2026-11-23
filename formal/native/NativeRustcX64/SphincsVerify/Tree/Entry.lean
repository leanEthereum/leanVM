module

public import NativeRustcX64.SphincsVerify.Tree.Leaf

/-!
# The fold's entry (x86-64)

From the one-time leaf at `9408` (`b158` .. `b161`): the path's slice checks (the panic `b200`
unreachable: layer `l`'s nodes `pathStart l .. pathStart l + heightOf l` are within the 26), the
height-0 case (`b160`, unreachable), the loop's state: the path's address at `72`, the layer's
word `l << 24` at `96`, the leaf at `10368`, RCX `0` (`entry`, to `AtNode … 0`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

variable (r : Run)

/-- **The fold's loop head**, `z` steps done: RCX `z`, R12 hasher A, the path's address at `72`,
the layer's word at `96`, the value at `10368`. -/
@[expose] def AtNode [Labels] (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ Run.RegIs m .rcx (BitVec.ofNat 64 z) ∧
    Run.RegIs m .r12 (r.off 4096) ∧ r.WordAt m 72 (r.addr (24764 + 16 * pathStart l)) ∧
    r.WordAt m 96 (l * 16777216).toUInt64 ∧ BytesAt m.dmem (r.off 10368) (r.foldUpTo l e z) ∧
    Run.RegIs m .rbx (Labels.label "memset").toBitVec

variable {r} [Host]

omit [Host] in
theorem l_cases {l : Nat} (hl : l < 3) : l = 0 ∨ l = 1 ∨ l = 2 := by omega

/-- **`b158` .. `b161`**: from the leaf to the loop head. -/
theorem entry (hp : Placed code r.k) (hpre : r.Pre) {l : Nat} {e : List (List UInt8)}
    {m : MachineData} (h : LeafC r l e m)
    (hV : BytesAt m.dmem (r.off 9408) (wotsLeafHash r.seed (r.key l) e)) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b162Offset ∧ AtNode r l e 0 st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b158Offset⟩ := by
  have hl := h.1.1
  have hwf := frame_wf' hpre h.1 0
  have hld96 : (r.env m (fun _ ↦ 0) 0).load 0 96 8 = l.toUInt64.toBitVec := load_word h.2.1.2.2
  have hld160 : (r.env m (fun _ ↦ 0) 0).load 0 160 8 = (heightOf l).toUInt64.toBitVec :=
    load_word h.1.2.2.1.2.2.1
  refine exec_then (hb158 hp) run_b158 hwf (fun _ h ↦ nomatch h) (match_leaf hpre h _)
    fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := false) hpc1 (by
    sym_simp; rw [hld96, hld160]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b158_next] at hpc1'
  refine exec_at (hb159 hp) (exec_after run_b158 run_b159) hwf (fun _ h ↦ nomatch h) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hpc2' := pc_cond (b := false) hpc2 (by
    sym_simp; rw [hld96, hld160]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b159_next] at hpc2'
  refine exec_at (hb160 hp) (exec_after run_b159 run_b160) hwf (fun _ h ↦ nomatch h) hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hpc3' := pc_cond (b := false) hpc3 (by
    sym_simp; rw [hld160]; rcases l_cases hl with rfl | rfl | rfl <;> decide)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b160_next] at hpc3'
  refine exec_at (hb161 hp) (exec_after run_b160 run_b161) hwf (fun _ h ↦ nomatch h) hpc3' hm3
    fun st4 hm4 hpc4 ↦ ?_
  have hB4 := Base.of_match hpre h.1 hm4 hwf rfl (by decide) (by decide) rfl
  have hlen : (wotsLeafHash r.seed (r.key l) e).length = 16 := length_th _ _ _
  refine .done _ ⟨hpc4.trans (pc_after NativeRustcX64.Sphincs.SphincsVerify.b161_next), hB4, heightOf_pos hl,
    hm4.regs .rcx _ rfl, (hm4.regs .r12 _ rfl).trans (eval_ptr 4096), ?_, ?_, ?_,
    hm4.regs .rbx _ rfl⟩
  · refine write_eval hm4 (o := 72) (n := 8) (v := pathSym) (w := r.off (24764 + 16 * pathStart l)) (by decide)
      (by decide) ?_ (bytes_word _)
    simp only [pathSym, Sym.eval, SBool.eval, BinOp.apply, CmpOp.apply, low_W64,
      ext_W64, hld96, Run.env_base0]
    show r.base + _ + _ = r.base + _
    refine (BitVec.add_assoc _ _ _).trans (congrArg (r.base + ·) ?_)
    rcases l_cases hl with rfl | rfl | rfl <;> decide
  · refine write_eval hm4 (o := 96) (n := 8) (v := .bin .shl .W32 (.load 0 96 8) (.lit 24))
      (w := (l * 16777216).toUInt64.toBitVec) (by decide)
      (by decide) ?_ (bytes_word _)
    sym_simp
    rw [hld96]
    rcases l_cases hl with rfl | rfl | rfl <;> decide
  · exact write_16 hm4 (o := 10368) (v₀ := .load 0 9408 8) (v₁ := .load 0 9416 8) (by decide) hlen
      (by decide) (by decide) (load_lo hV hlen) (load_hi hV hlen)

end

end NativeRustcX64.SphincsVerifyProof.Tree
