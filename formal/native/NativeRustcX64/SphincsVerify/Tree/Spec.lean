module

public import NativeRustcX64.SphincsVerify.Tree.NodeD
public import NativeRustcX64.SphincsVerify.Compose

/-!
# Region 5c: a layer's tree (x86-64)

The node's last block `b178` (the value, hasher A's first 16 bytes, to `8296`; the loop's test):
back to the loop head with `z + 1` steps (`nodeI_loop`), or, after the last, `b179`, `b181` (the
root to `144`, the next layer's registers) and on to the layer loop `b95` (`l < 2`) or `b182`
(the comparison with `PK.root`) and the epilogue (`fold_exit`). A node (`node`), the fold
(`fold`, by `Sym.loop`), the region (`tree_spec : TreeSpec`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Tree

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcX64.Sym
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcX64.Sphincs.SphincsVerify

public section

/-! ## Values -/

theorem toBitVec_toUInt64 (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

theorem length_keccakF' (b : List UInt8) : (keccakF b).length = 200 := length_stateBytes _

/-- The node's value is the fold's next step. -/
theorem node_value (r : Run) {l z : Nat} {e : List (List UInt8)} (hl : l < 3)
    (hz : z < heightOf l) :
    (keccakF (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z)))).take 16 =
      r.foldUpTo l e (z + 1) := by
  rw [foldUpTo_succ, Run.foldStep, InlineTh.th_short]
  · rfl
  · show (r.nodeIn l e z).length < 136
    rw [length_nodeIn r hl hz]; decide

/-- A 64-bit value is determined by its 8 bytes. -/
theorem eq_of_bytes {x y : BitVec 64}
    (h : (List.range 8).map (byteOf x) = (List.range 8).map (byteOf y)) : x = y := by
  rw [bytes_word, bytes_word] at h
  have := congrArg (fun b ↦ littleEndianLane b 0) h
  simp only [littleEndianLane_wordBytes] at this
  have := congrArg UInt64.toBitVec this
  simpa using this

/-- **Two 16-byte values are equal** when their words are. -/
theorem beq_eq_words {a b : List UInt8} {A B C D : BitVec 64}
    (hA : (List.range 8).map (byteOf A) = a.take 8) (hC : (List.range 8).map (byteOf C) = a.drop 8)
    (hB : (List.range 8).map (byteOf B) = b.take 8) (hD : (List.range 8).map (byteOf D) = b.drop 8) :
    (a == b) = (A == B && C == D) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    subst h
    exact ⟨eq_of_bytes (hA.trans hB.symm), eq_of_bytes (hC.trans hD.symm)⟩
  · rintro ⟨rfl, rfl⟩
    rw [← List.take_append_drop 8 a, ← List.take_append_drop 8 b, ← hA, ← hC, ← hB, ← hD]

/-- The comparison of `b182`: the words' XORs' OR is zero. -/
theorem xor_or_eq_zero (A B C D : BitVec 64) :
    ((A ^^^ B ||| C ^^^ D) == 0#64) = (A == B && C == D) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (fun v ↦ v.getLsbD i) h <;>
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_zero] at this <;>
      revert this <;> cases A.getLsbD i <;> cases B.getLsbD i <;> cases C.getLsbD i <;>
      cases D.getLsbD i <;> simp
  · rintro ⟨rfl, rfl⟩
    simp

theorem merge_ite (c : Bool) :
    BinOp.apply .merge .W8 (BitVec.ofNat 64 0) (if c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)
      = if c then 1 else 0 := by
  cases c <;> decide

/-! ## The node's last block -/

variable [Host] {r : Run}

/-- The value's two words, written from hasher A's first 16 bytes. -/
theorem value_at {l z : Nat} {e : List (List UInt8)} {m m' : MachineData}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hm : Match (r.env m vars ret) S m')
    (hl : l < 3) (hz : z < heightOf l)
    (hV : BytesAt m.dmem (r.off 4072)
      (keccakF (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z))))) {o : Nat}
    (ho : o + 16 ≤ frameRegion)
    (w0 : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.load 0 4072 8, i))
    (w1 : ∀ i < 8, findWrite 0 (o + 8 + i) S.mem = some (.load 0 4080 8, i)) :
    BytesAt m'.dmem (r.off o) (r.foldUpTo l e (z + 1)) := by
  rw [← node_value r hl hz]
  have hlen := length_keccakF' (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z)))
  generalize keccakF (xorBlock (List.replicate 200 0) (finalBlock (r.nodeIn l e z))) = V at hV hlen ⊢
  have lo := bytes_load (vars := vars) (ret := ret) (n := 8) (bytesAt_sub hV 0 8)
    (by simp [hlen]) (by decide)
  have hi := bytes_load (vars := vars) (ret := ret) (n := 8) (bytesAt_sub hV 8 8)
    (by simp [hlen]) (by decide)
  rw [List.drop_zero] at lo
  exact write_16 hm ho (by simp [hlen]) w0 w1
    (by rw [List.take_take]; exact lo)
    (by rw [List.drop_take, show 16 - 8 = 8 from rfl]; exact hi)

/-- **`b178`, back to the loop head** with `z + 1 < heightOf l`. -/
theorem nodeI_loop (hp : Placed code r.k) (hpre : r.Pre) {l : Nat} {e : List (List UInt8)}
    {z : Nat} {m : MachineData} (h : AtN8 r l e z m) (hlt : z + 1 < heightOf l) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset ∧ AtNode r l e (z + 1) st.data)
      ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b178Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, h13, hV, hbx⟩ := h
  have hl := hB.1
  have hh := heightOf_le hl
  have hwf := frame_wf' hpre hB 0
  have hld64 : (r.env m (fun _ ↦ 0) 0).load 0 56 8 = (z + 1).toUInt64.toBitVec := load_word hN.1
  have hld160 : (r.env m (fun _ ↦ 0) 0).load 0 168 8 = (heightOf l).toUInt64.toBitVec :=
    load_word hB.2.2.1.2.2.1
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := 0)
    (known := kAB ++ [(.r13, .ptr 0 2024), (.rbx, .label "memset")])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4072), (.rbp, .ptr 0 560),
      (.r13, .ptr 0 2024), (.rbx, .label "memset")] from
      ⟨h12.trans (eval_ptr 4072).symm, hB.2.2.2.1.trans (eval_ptr 560).symm,
        h13.trans (eval_ptr 2024).symm, hbx, trivial⟩)
  refine exec_then (hb187 hp) run_b178 hwf (fun _ h ↦ nomatch h) hm0 fun st hm hpc ↦ ?_
  have hpc' := pc_cond (b := true) hpc (by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hld64, hld160, toBitVec_toUInt64]
    rw [Bool.not_eq_true', beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega)
  rw [Sym.ite_pos (rfl : true = true), lbl_65 hp] at hpc'
  refine .done _ ⟨hpc', Base.of_match hpre hB hm hwf rfl (by decide) (by decide) rfl, hlt,
    (hm.regs .rcx _ rfl).trans (hld64.trans (toBitVec_toUInt64 _)),
    (hm.regs .r12 _ rfl).trans (eval_ptr 4072), ?_, ?_,
    value_at hm hl hz hV (o := 8296) (by decide) (by decide) (by decide),
    hm.regs .rbx _ rfl⟩
  · have := hN.of_match hpre hm hwf (by decide); exact this.2.1
  · have := hN.of_match hpre hm hwf (by decide); exact this.2.2

omit [Host] in
theorem pkRoot_at [Labels] {m : MachineData} (h : r.Inputs m) : BytesAt m.dmem (r.off 128) r.pk.root := by
  have h1 := h.1
  rw [← List.take_append_drop 16 r.pkB] at h1
  have := bytesAt_append_right h1
  rwa [List.length_take, r.hpk, Run.off_add] at this

/-- **`b178` after the last node, `b179`, `b181`**: the root to `144`, on to the next layer, or
`b182`'s comparison with `PK.root` and the epilogue. -/
theorem fold_exit (hp : Placed code r.k) (hpre : r.Pre) {l : Nat} {e : List (List UInt8)}
    {z : Nat} {m : MachineData} (h : AtN8 r l e z m) (heq : z + 1 = heightOf l) :
    Eventually (step1 Host.exe) (fun st ↦
      if l = 2 then r.Done (r.layerRoot l e == r.pk.root) st
      else st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset ∧ r.AtLayer (l + 1) (r.layerRoot l e) st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b178Offset⟩ := by
  obtain ⟨hB, hz, hN, h12, h13, hV, hbx⟩ := h
  have hl := hB.1
  have hh := heightOf_le hl
  have hwf := frame_wf' hpre hB 0
  have hld64 : (r.env m (fun _ ↦ 0) 0).load 0 56 8 = (z + 1).toUInt64.toBitVec := load_word hN.1
  have hld160 : (r.env m (fun _ ↦ 0) 0).load 0 168 8 = (heightOf l).toUInt64.toBitVec :=
    load_word hB.2.2.1.2.2.1
  obtain ⟨hIn, -, -, h200, h208, -, h568⟩ := hB.2.2.1
  have hld200 : (r.env m (fun _ ↦ 0) 0).load 0 192 8 = (l + 1).toUInt64.toBitVec := load_word h200
  have hld208 : (r.env m (fun _ ↦ 0) 0).load 0 200 8 = (4656 + 1028 * (l + 1)).toUInt64.toBitVec :=
    load_word h208
  have hm0 := match_fs hpre hB.2.1 hB.2.2.2.2 (ret := 0)
    (known := kAB ++ [(.r13, .ptr 0 2024), (.rbx, .label "memset")])
    (show AllOf _ [(Reg64.r12, Sym.ptr 0 4072), (.rbp, .ptr 0 560),
      (.r13, .ptr 0 2024), (.rbx, .label "memset")] from
      ⟨h12.trans (eval_ptr 4072).symm, hB.2.2.2.1.trans (eval_ptr 560).symm,
        h13.trans (eval_ptr 2024).symm, hbx, trivial⟩)
  refine exec_then (hb187 hp) run_b178 hwf (fun _ h ↦ nomatch h) hm0 fun st1 hm1 hpc1 ↦ ?_
  have hpc1' := pc_cond (b := false) hpc1 (by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hld64, hld160, heq]
    simp)
  rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b178_next] at hpc1'
  refine exec_at (hb188 hp) (exec_after run_b178 run_b179) hwf (fun _ h ↦ nomatch h) hpc1' hm1
    fun st2 hm2 hpc2 ↦ ?_
  have hpc2' : st2.pc = Host.addrOf (r.k + NativeRustcX64.Sphincs.SphincsVerify.b181Offset) := hpc2.trans (lbl_82 hp)
  refine exec_at (hb190 hp) (exec_after run_b179 run_b181) hwf (fun _ h ↦ nomatch h) hpc2' hm2
    fun st3 hm3 hpc3 ↦ ?_
  have hroot := layerRoot_eq r hl e
  rw [← heq] at hroot
  have hlen : (r.layerRoot l e).length = 16 := by rw [hroot]; exact length_foldUpTo r l e _
  have hR : BytesAt st3.data.dmem (r.off 144) (r.layerRoot l e) := by
    rw [hroot]
    exact value_at hm3 hl hz hV (o := 144) (by decide) (by decide) (by decide)
  have hF3 : r.Frame st3.data := Run.Frame.of_match r hpre hB.2.1 hm3 hwf rfl (by decide)
  by_cases h2 : l = 2
  · subst h2
    simp only [↓reduceIte]
    have hpc3' := pc_cond (b := false) hpc3 (by sym_simp; rw [hld208]; decide)
    rw [Sym.ite_neg Bool.false_ne_true, pc_after NativeRustcX64.Sphincs.SphincsVerify.b181_next] at hpc3'
    refine exec_at (hb191 hp) (exec_after run_b181 run_b182) hwf (fun _ h ↦ nomatch h) hpc3' hm3
      fun st4 hm4 hpc4 ↦ ?_
    have hF4 : r.Frame st4.data := Run.Frame.of_match r hpre hB.2.1 hm4 hwf rfl (by decide)
    have hpc4' : st4.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b187Offset := hpc4.trans (lbl_85 hp)
    have hpk := pkRoot_at hIn
    have hRm : BytesAt m.dmem (r.off 4072) (r.layerRoot 2 e) := by
      rw [hroot, ← node_value r hl hz]
      have := bytesAt_sub hV 0 16
      simpa using this
    have hlo := load_lo (vars := fun _ ↦ 0) (ret := 0) hRm hlen
    have hhi := load_hi (vars := fun _ ↦ 0) (ret := 0) hRm hlen
    have hcmp := beq_eq_words hlo hhi (load_lo (vars := fun _ ↦ 0) (ret := 0) hpk (length_pkRoot r))
      (load_hi (vars := fun _ ↦ 0) (ret := 0) hpk (length_pkRoot r))
    have hx := hm4.regs .rax _ rfl
    obtain ⟨d, pc⟩ := st4
    simp only at hpc4'
    subst hpc4'
    refine done_of_epilogue r hp hpre d hF4 ?_
    show d.regs.get64 .rax = _
    rw [hx, hcmp]
    have hx1 : ∀ x y : BitVec 64, BinOp.apply .xor .W64 x y = x ^^^ y := fun x y ↦ by
      simp [BinOp.apply]
    have hor : ∀ x y : BitVec 64, BinOp.apply .or .W64 x y = x ||| y := fun x y ↦ by
      simp [BinOp.apply]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, hx1, hor]
    rw [show (4072 + 8 : Nat) = 4080 from rfl, show (128 + 8 : Nat) = 136 from rfl,
      xor_or_eq_zero, merge_ite]
  · simp only [h2, ↓reduceIte]
    have hl2 : l < 2 := by omega
    have hpc3' := pc_cond (b := true) hpc3 (by
      sym_simp; rw [hld208]; rcases l_cases hl with rfl | rfl | rfl <;> first | decide | omega)
    rw [Sym.ite_pos (rfl : true = true), lbl_38 hp] at hpc3'
    have hB3 := Base.of_match hpre hB hm3 hwf rfl (by decide) (by decide) rfl
    have h176 : r.WordAt st3.data 184 (r.addr (17436 + 1028 * (l + 1))) := by
      refine write_eval hm3 (o := 184) (n := 8)
        (v := .bin .add .W64 (.lit 12780) (.bin .add .W64 (.ptr 0 0) (.load 0 200 8)))
        (w := r.off (17436 + 1028 * (l + 1))) (by decide) (by decide) ?_ (bytes_word _)
      sym_simp
      rw [hld208, toBitVec_toUInt64]
      show BitVec.ofNat 64 12780 + (r.base + BitVec.ofInt 64 0 +
        BitVec.ofNat 64 (4656 + 1028 * (l + 1))) = r.base + BitVec.ofNat 64 (17436 + 1028 * (l + 1))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
      omega
    refine .done _ ⟨hpc3', by omega, hlen, hF3, hB3.2.2.1.1, ?_, ?_, hm3.regs .rdx _ rfl,
      hm3.regs .rbx _ rfl, (hm3.regs .r12 _ rfl).trans (eval_ptr 4072), hB3.2.2.2.1,
      (hm3.regs .r13 _ rfl).trans (eval_ptr 2024), (hm3.regs .r15 _ rfl).trans (eval_ptr 144), hR,
      h176, hB3.2.2.1.2.2.2.2.2.2, hB3.2.2.2.2⟩
    · exact (hm3.regs .rcx _ rfl).trans (hld208.trans (toBitVec_toUInt64 _))
    · exact (hm3.regs .rsi _ rfl).trans (hld200.trans (toBitVec_toUInt64 _))

/-- **A node of the fold**: from the loop head with `z` steps done to the loop head with `z + 1`
or, after the last, the region's end. -/
theorem node (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {z : Nat} {m : MachineData} (h : AtNode r l e z m) :
    Eventually (step1 Host.exe) (fun st ↦ (z + 1 < heightOf l ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset ∧
      AtNode r l e (z + 1) st.data) ∨ (if l = 2 then r.Done (r.layerRoot l e == r.pk.root) st
      else st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset ∧ r.AtLayer (l + 1) (r.layerRoot l e) st.data)) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset⟩ :=
  Eventually.bind (nodeA hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (nodeB hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (nodeC hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (nodeD hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (nodeE hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (nodeF hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (nodeG hp hc hpre h) <| at_pc fun _ h ↦
  Eventually.bind (nodeH hp hc hpre h) <| at_pc fun m h ↦ by
    by_cases hlt : z + 1 < heightOf l
    · exact Eventually.mono (nodeI_loop hp hpre h hlt) fun st h' ↦ Or.inl ⟨hlt, h'⟩
    · exact Eventually.mono (fold_exit hp hpre h (by have := h.2.1; omega)) fun st h' ↦ Or.inr h'

/-- **The fold's loop**: from the loop head with no step done to the region's end. -/
theorem fold (hp : Placed code r.k) (hc : Callees) (hpre : r.Pre) {l : Nat}
    {e : List (List UInt8)} {m : MachineData} (h : AtNode r l e 0 m) :
    Eventually (step1 Host.exe) (fun st ↦ if l = 2 then r.Done (r.layerRoot l e == r.pk.root) st
      else st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset ∧ r.AtLayer (l + 1) (r.layerRoot l e) st.data) ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset⟩ := by
  refine Sym.loop (fun n st ↦ ∃ z, z + n = heightOf l ∧ st.pc = r.pc NativeRustcX64.Sphincs.SphincsVerify.b152Offset ∧ AtNode r l e z st.data)
    (fun n st ⟨z, hn, hpc, hz⟩ ↦ ?_) (n := heightOf l) ⟨0, by omega, rfl, h⟩
  refine Eventually.mono (at_pc (fun m h ↦ node hp hc hpre h) st ⟨hpc, hz⟩) fun st' h' ↦ ?_
  rcases h' with ⟨hlt, hpc', h'⟩ | h'
  · exact Or.inr ⟨n - 1, by omega, z + 1, by omega, hpc', h'⟩
  · exact Or.inl h'

/-- **Region 5c, a layer's tree** (x86-64): from `b142`, layer `l`'s chain ends `e`, to the next
layer at `b95` with the layer's root, or, after the last, returned the comparison with
`PK.root`. -/
theorem tree_spec : TreeSpec := by
  intro l e r hp hc hpre m h
  have hl := h.1
  have hEl := h.2.1
  refine Eventually.bind (stage1 hp hc hpre h) (at_pc (P := fun d ↦ LeafC r l e d ∧
    BytesAt d.dmem (r.off 2024) ((r.key l).adrs 1) ∧ BytesAt d.dmem (r.off 4072) Keccak.new)
    fun m hm ↦ ?_)
  refine Eventually.bind (stage2 hp hc hpre hm.1 hm.2.1 hm.2.2) (at_pc (P := fun d ↦
    LeafC r l e d ∧ BytesAt d.dmem (r.off 2024) ((r.key l).adrs 1) ∧
    HasherHolds (bytesOf d.dmem (r.off 4072) 344) r.seed) fun m hm ↦ ?_)
  refine Eventually.bind (stage3 hp hc hpre hm.1 hm.2.1 hm.2.2) (at_pc (P := fun d ↦
    LeafC r l e d ∧ HasherHolds (bytesOf d.dmem (r.off 4072) 344) (r.seed ++ (r.key l).adrs 1))
    fun m hm ↦ ?_)
  refine Eventually.bind (stage4 hp hc hpre hm.1 hm.2) (at_pc (P := fun d ↦
    LeafC r l e d ∧ Run.RegIs d .rbp (r.off 560) ∧
    HasherHolds (bytesOf d.dmem (r.off 560) 344) (r.seed ++ (r.key l).adrs 1))
    fun m hm ↦ ?_)
  refine Eventually.bind (stage5 hp hc hpre hm.1 hm.2.1 hm.2.2) (at_pc (P := fun d ↦
    LeafC r l e d ∧ Run.RegIs d .rbp (r.off 560) ∧
    HasherHolds (bytesOf d.dmem (r.off 560) 344)
      (r.seed ++ (r.key l).adrs 1 ++ e.flatten)) fun m hm ↦ ?_)
  refine Eventually.bind (stage6 hp hc hpre hm.1 hm.2.1 hm.2.2) (at_pc (P := fun d ↦
    LeafC r l e d ∧ Run.RegIs d .rbp (r.off 560) ∧
    BytesAt d.dmem (r.off 11368) (hashBytes (r.seed ++ (r.key l).adrs 1 ++
      e.flatten))) fun m hm ↦ ?_)
  have hv : BytesAt m.dmem (r.off 11368) (wotsLeafHash r.seed (r.key l) e) := by
    simpa [wotsLeafHash, th, List.drop_zero] using bytesAt_sub hm.2.2 0 16
  exact Eventually.bind (entry hp hpre hm.1 hm.2.1 hv) (at_pc fun m h ↦ fold hp hc hpre h)

end

end NativeRustcX64.SphincsVerifyProof.Tree
