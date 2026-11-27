module

public import NativeRustcArm.SphincsVerify.Tree.NodeD
public import NativeRustcArm.SphincsVerify.InlineTh.Final
public import NativeRustcArm.SphincsVerify.InlineTh.Model

/-!
# The fold's node: the final absorb, the node's value

From `AtN7`: the final block XORed into hasher A's zero state and `keccak_f` (`b168`;
`nodeG`, to `AtN8`, by `InlineTh.xorFinal`), then the node's value, A's first 16 bytes, to
`12864` (`b169`): the fold after `z + 1` steps (`InlineTh.th_short`); back to the loop head
while the height is below the layer's, else on (`nodeH`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable [ElfHost] (r : Run)

/-- **At `b169`**: hasher A's state the node's padded input absorbed. -/
@[expose] def AtN8 (l : Nat) (e : List (List UInt8)) (z : Nat) (m : MachineData) : Prop :=
  Base r l m ∧ z < heightOf l ∧ NRegs r l z m ∧
    BytesAt m.dmem (r.off 8640)
      (keccakF (xorBlock (List.replicate 200 0) (finalBlock (nodeIn r l e z))))

/-- **After the fold** (`b170`): the layer's root at `12864`. -/
@[expose] def AtFold (l : Nat) (e : List (List UInt8)) (m : MachineData) : Prop :=
  Base r l m ∧ BytesAt m.dmem (r.off 12864) (r.foldUpTo l e (heightOf l))

variable {r}

/-- **`b168` and `keccak_f`**: the final absorb. -/
theorem nodeG (hp : PlacedIn code r.sec r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN7 r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b169Offset ∧ AtN8 r l e z st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b168Offset⟩ := by
  obtain ⟨hB, hz, hN, h23, hZ, hK⟩ := h
  have hl := hB.1
  have hlI := length_nodeIn (r := r) (e := e) hl hz
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  have hm0 : Match (r.env m) s7 m := r.match_frame hpre hB.2.1
    (allOf_append (allOf_keptRegs hB _) ⟨h23, trivial⟩) trivial trivial trivial
  refine exec_then_elf (hb168 hp) run_b168 hwf hm0 fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl rfl
  have hN1 := hN.of_match hpre hm hwf rfl rfl (by decide)
  have h0 : Run.RegIs st.data .X0 (r.off 8640) := (hm.regs .X0 _ rfl).trans (eval_ptr 8640)
  have hX : BytesAt st.data.dmem (r.off 8640)
      (xorBlock (List.replicate 200 0) (finalBlock (nodeIn r l e z))) := by
    have := InlineTh.xorFinal hm hwf (r := 0) (b := r.base) (sz := 21616) rfl (oA := 8640)
      (oK := 16960) (L := 80) (by decide) (by decide +kernel) hlI (by decide) hK
    have hz200 : bytesOf (r.env m).mem0 (r.off 8640) 200 = List.replicate 200 0 := by
      have := bytesOf_of_bytesAt hZ
      rwa [List.length_replicate] at this
    rwa [show r.base + BitVec.ofNat 64 8640 = r.off 8640 from rfl, hz200] at this
  refine call_then_elf hpc hc.2.2.2.2 (r.keccakF_pre hpre hB1.2.1 h0 (by decide))
    fun st' hpc' hpost ↦ ?_
  obtain ⟨hk, hout, hS⟩ := r.keccakF_out h0 hpost
  have hlX : (xorBlock (List.replicate 200 0) (finalBlock (nodeIn r l e z))).length = 200 :=
    length_stateBytes _
  refine .done _ ⟨hpc'.trans (pc_after NativeRustcArm.Sphincs.SphincsVerify.b168_next),
    hB1.of_call hpre hS (by decide) (by decide) (by decide) hout, hz,
    hN1.of_call hpre hB1.2.1 hS (by decide) (by decide) (by decide) hout, ?_⟩
  have := bytesOf_of_bytesAt hX
  rw [hlX] at this
  rw [← this]
  exact hk

omit [ElfHost] in
theorem length_keccakF'' (b : List UInt8) : (keccakF b).length = 200 := length_stateBytes _

omit [ElfHost] in
/-- The node's value is the fold's next step. -/
theorem node_value {l z : Nat} {e : List (List UInt8)} (hl : l < 3) (hz : z < heightOf l) :
    (keccakF (xorBlock (List.replicate 200 0) (finalBlock (nodeIn r l e z)))).take 16 =
      r.foldUpTo l e (z + 1) := by
  rw [foldUpTo_succ, Run.foldStep_eq, InlineTh.th_short]
  · rfl
  · show (nodeIn r l e z).length < 136
    rw [length_nodeIn hl hz]; decide

/-- **`b169`**: the node's value to `12864`; the loop's test. -/
theorem nodeH (hp : PlacedIn code r.sec r.k) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtN8 r l e z m) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ (z + 1 < heightOf l ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b144Offset ∧
      AtNode r l e (z + 1) st.data) ∨ (z + 1 = heightOf l ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b170Offset ∧ AtFold r l e st.data))
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b169Offset⟩ := by
  obtain ⟨hB, hz, hN, hV⟩ := h
  have hl := hB.1
  have hh := heightOf_le hl
  have hwf := r.frame_wf hpre hB.2.1 (fun _ ↦ 0)
  refine exec_then_elf (hb169 hp) run_b169 hwf (match_base hpre hB) fun st hm hpc ↦ ?_
  have hB1 := Base.of_match hpre hB hm hwf rfl rfl (by decide) (by decide) (by decide) rfl rfl rfl rfl
  have hN1 := hN.of_match hpre hm hwf rfl rfl (by decide)
  have hVal : BytesAt st.data.dmem (r.off 12864) (r.foldUpTo l e (z + 1)) := by
    rw [← node_value hl hz]
    have hlen := length_keccakF'' (xorBlock (List.replicate 200 0) (finalBlock (nodeIn r l e z)))
    generalize keccakF (xorBlock (List.replicate 200 0) (finalBlock (nodeIn r l e z))) = V at hV hlen ⊢
    have lo := bytes_load (vars := fun _ ↦ 0) (n := 8) (bytesAt_sub hV 0 8) (by simp [hlen]) (by decide)
    have hi := bytes_load (vars := fun _ ↦ 0) (n := 8) (bytesAt_sub hV 8 8) (by simp [hlen]) (by decide)
    rw [List.drop_zero] at lo
    rw [List.take_add (l := V) (i := 8) (j := 8)]
    refine bytesAt_cat (n := 8) (by simp [hlen]) (write_eval hm (o := 12864)
      (v := .load 0 8640 8) (by decide) (by decide) rfl lo) ?_
    exact write_eval hm (o := 12872) (v := .load 0 8648 8) (by decide) (by decide) rfl hi
  obtain ⟨-, -, -, -, -, h48w, -⟩ := hB.2.2.1.2
  have h48 : (r.env m).load 0 48 8 = (heightOf l).toUInt64.toBitVec := load_word h48w
  have hc : ∀ b : Bool, (z + 1 ≠ heightOf l) = (b = true) →
      SBool.eval (r.env m) (.not (.cmp .eq .W64 (.reg .X24) (.load 0 48 8))) = b := by
    intro b hb
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [h48, hN.1]
    have hne : (BitVec.ofNat 64 (z + 1) == (heightOf l).toUInt64.toBitVec) =
        decide (z + 1 = heightOf l) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      constructor
      · intro he
        have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        exact this
      · intro he; rw [he]; rfl
    rw [hne]
    cases b <;> simp_all
  by_cases hzh : z + 1 = heightOf l
  · have hpc' := pc_cond (b := false) hpc (hc false (by simp [hzh]))
    rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcArm.Sphincs.SphincsVerify.b169_next] at hpc'
    refine .done _ (Or.inr ⟨hzh, hpc', hB1, ?_⟩)
    rw [← hzh]; exact hVal
  · have hpc' := pc_cond (b := true) hpc (hc true (by simp [hzh]))
    rw [Sym.ite_pos (rfl : true = true), lbl_59 hp] at hpc'
    exact .done _ (Or.inl ⟨by omega, hpc', hB1, by omega, hN1.1, hN1.2.1, hN1.2.2, hVal⟩)

end

end NativeRustcArm.SphincsVerifyProof.Tree
