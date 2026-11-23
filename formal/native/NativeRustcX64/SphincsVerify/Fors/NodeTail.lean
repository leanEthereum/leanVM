module

public import NativeRustcX64.SphincsVerify.Fors.NodeMid
public import NativeRustcX64.SphincsVerify.InlineTh.Final

/-!
# A FORS node, its end: the inlined `finalize` and the new value (x86-64)

From `N2` at `b91` (directive 1017): `b91` checks B's `buf_len`, `b92` zeroes the final block at
`2048` (`memset`), `b93` copies B's 80 buffered bytes there (`memcpy`), `b94` XORs the padded
block into hasher A's zero state and calls `keccak_f`; `b95` copies the first 16 bytes to the
current value at `10368` and restores the loop's registers: the next node's head
(`AtNode r c (z + 1)` at `b65`), or after height 9 the tree's end (`AtRoot r c` at `b96`)
(**`node_tail`**).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash
open NativeRustcX64.Sphincs.SphincsVerify NativeRustcX64.SphincsVerifyProof.InlineTh

@[expose] public section

/-- **At a tree's end** `b96`: tree `c`'s root at `10368`, R13 the tree, R12 hasher A, R15 the
tree's word, EBP the key pair's. -/
structure AtRoot [Labels] (r : Run) (c : Nat) (m : MachineData) : Prop where
  keep : Keep0 r c m
  r13 : Run.RegIs m .r13 (BitVec.ofNat 64 c)
  r12 : Run.RegIs m .r12 (r.off 4096)
  r15 : wordBytes (UInt64.ofBitVec (reg m .r15)) = be64 (r.key 0).tree
  rbp : wordBytes (UInt64.ofBitVec (reg m .rbp)) = be32 (r.key 0).leaf ++ [0, 0, 0, 0]
  root : BytesAt m.dmem (r.off 10368) (r.forsRoot c)
  rbx : Run.RegIs m .rbx (Labels.label "memset").toBitVec

end

public section

variable [Host] {r : Run}

omit [Host] in
/-- The value after one more step, `th` of a short input. -/
theorem forsUpTo_succ_eq (r : Run) {c z : Nat} (hc : c < 24) (hz : z < 10) :
    r.forsUpTo c (z + 1) = (Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0)
      (Keccak.finalBlock (r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z)))).take 16 := by
  rw [r.forsUpTo_succ, r.forsStep_eq]
  refine th_short ?_
  rw [List.length_append, List.length_append, Digest.length_seed,
    show (r.nodeAdrsOf c z).length = 32 from length_forsNodeAdrs _ _ _ _, r.length_childrenOf hc hz]
  decide

/-- **A node's end**: from `N2 r c z` at `b91`, the next node's head or the tree's end. -/
theorem node_tail (hp : Placed Sphincs.SphincsVerify.code r.k) (hc : Callees) (hpre : r.Pre)
    {c z : Nat} {m : MachineData} (h : N2 r c z m) {R : MachineState → Prop}
    (next : z + 1 < 10 → ∀ m', AtNode r c (z + 1) m' →
      Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b65Offset⟩)
    (done : z + 1 = 10 → ∀ m', AtRoot r c m' → Eventually (step1 Host.exe) R ⟨m', r.pc NativeRustcX64.Sphincs.SphincsVerify.b96Offset⟩) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Sphincs.SphincsVerify.b91Offset⟩ := by
  obtain ⟨hK, hz, w64, w104, h13, h15, h12, ha0, hT, h14⟩ := h
  have hc24 := hK.2.1.hc
  have hTl : (r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z).length = 80 := by
    rw [List.length_append, List.length_append, Digest.length_seed,
      show (r.nodeAdrsOf c z).length = 32 from length_forsNodeAdrs _ _ _ _,
      r.length_childrenOf hc24 hz]
  -- b91, b92: the block zeroed
  have hwf := r.frame_wf hpre hK.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b93Offset).toBitVec
  have hm := match_frameS hpre hK.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b93Offset).toBitVec)
    (k := [(.r13, .lit 80), (.r15, .ptr 0 2048), (.r12, .ptr 0 4096), (.r14, .label "memcpy")])
    ⟨Chains.known_lit h13, Chains.known_ptr h15, Chains.known_ptr h12, h14, trivial⟩
  refine Chains.blk r hp b91_in_code (List.cons_ne_nil _ _) run_b91 hwf (fun _ h ↦ nomatch h) hm
    fun st₁ hm₁ hpc₁ ↦ ?_
  refine Chains.pc_at (a := r.pc NativeRustcX64.Sphincs.SphincsVerify.b92Offset) (Chains.pc_false hpc₁) ?_
  refine Chains.blk r hp b92_in_code (List.cons_ne_nil _ _) (exec_after run_b91 run_b92) hwf
    (fun _ _ ↦ rfl) hm₁ fun st₂ hm₂ hpc₂ ↦ ?_
  have kept₂ : KeptBy r _ m st₂.data := keptBy_of_match hpre hm₂ hwf
  refine memset_then hpre hc hpc₂ (KeepC.of_block hpre hK hm₂ hwf (by decide +kernel) rfl)
    (a := 2048) (n := 136) (Chains.regIs_ptr hm₂ rfl) (Chains.toNat_of_lit hm₂ rfl (by decide))
    (Chains.toNat_of_lit hm₂ rfl (by decide)) (by decide) fun m₃ hK₃ hS₃ hkc₃ hz₃ ↦ ?_
  have g13 : Run.RegIs _ .r13 (BitVec.ofNat 64 80) :=
    Chains.RegIs.of_saved hS₃ rfl (Chains.regIs_lit hm₂ rfl)
  have g15 : Run.RegIs _ .r15 (r.off 2048) :=
    Chains.RegIs.of_saved hS₃ rfl (Chains.regIs_ptr hm₂ rfl)
  have g12 : Run.RegIs _ .r12 (r.off 4096) :=
    Chains.RegIs.of_saved hS₃ rfl (Chains.regIs_ptr hm₂ rfl)
  have g14 := Chains.RegIs.of_saved hS₃ rfl (Chains.regIs_label (y := .r14) hm₂ rfl)
  have gbx := Chains.RegIs.of_saved hS₃ rfl (Chains.regIs_label (y := .rbx) hm₂ rfl)
  have W := NativeRustc.length_wordBytes
  have g64 := hkc₃ (by flen) (by flen) (kept₂ (by flen) (by rw [W]; decide +kernel) w64)
  have g104 := hkc₃ (by flen) (by flen) (kept₂ (by flen) (by rw [W]; decide +kernel) w104)
  have ga0 := hkc₃ (by flen) (by flen)
    (kept₂ (by flen) (by rw [List.length_replicate]; decide +kernel) ha0)
  have gT := hkc₃ (by rw [hTl]; omega) (by rw [hTl]; omega)
    (kept₂ (by rw [hTl]; omega) (by rw [hTl]; decide +kernel) hT)
  -- b93: B's 80 bytes into the block
  have hwf₃ := r.frame_wf hpre hK₃.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b94Offset).toBitVec
  have hm₃ := match_frameS hpre hK₃.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b94Offset).toBitVec)
    (k := [(.r13, .lit 80), (.r15, .ptr 0 2048), (.r12, .ptr 0 4096), (.r14, .label "memcpy")])
    ⟨Chains.known_lit g13, Chains.known_ptr g15, Chains.known_ptr g12, g14, trivial⟩
  refine Chains.blk r hp b93_in_code (List.cons_ne_nil _ _) run_b93 hwf₃ (fun _ _ ↦ rfl) hm₃
    fun st₄ hm₄ hpc₄ ↦ ?_
  have kept₄ : KeptBy r _ m₃ st₄.data := keptBy_of_match hpre hm₄ hwf₃
  refine memcpy_then hpre hc hpc₄ (KeepC.of_block hpre hK₃ hm₄ hwf₃ (by decide +kernel) rfl)
    (a := 2048) (b := 776) (n := 80) (Chains.regIs_ptr hm₄ rfl) (Chains.regIs_ptr hm₄ rfl)
    (Chains.toNat_of_lit hm₄ rfl (by decide)) (by decide) (by decide) (by decide) hTl
    (kept₄ (by rw [hTl]; omega) (by rw [hTl]; decide +kernel) gT) fun m₅ hK₅ hS₅ hkc₅ hT₅ ↦ ?_
  have g13 : Run.RegIs _ .r13 (BitVec.ofNat 64 80) :=
    Chains.RegIs.of_saved hS₅ rfl (Chains.regIs_lit hm₄ rfl)
  have g15 : Run.RegIs _ .r15 (r.off 2048) :=
    Chains.RegIs.of_saved hS₅ rfl (Chains.regIs_ptr hm₄ rfl)
  have g12 : Run.RegIs _ .r12 (r.off 4096) :=
    Chains.RegIs.of_saved hS₅ rfl (Chains.regIs_ptr hm₄ rfl)
  have g14 := Chains.RegIs.of_saved hS₅ rfl (Chains.regIs_label (y := .r14) hm₄ rfl)
  have gbx := Chains.RegIs.of_saved hS₅ rfl (Chains.regIs_reg hm₄ rfl gbx)
  have g64 := hkc₅ (by flen) (by flen) (kept₄ (by flen) (by rw [W]; decide +kernel) g64)
  have g104 := hkc₅ (by flen) (by flen) (kept₄ (by flen) (by rw [W]; decide +kernel) g104)
  have ga0 := hkc₅ (by flen) (by flen)
    (kept₄ (by flen) (by rw [List.length_replicate]; decide +kernel) ga0)
  have gz := hkc₅ (by flen) (by flen) (kept₄ (by flen)
    (by rw [List.length_replicate]; decide +kernel)
    (zeros_slice hz₃ (a := 80) (k := 56) (by omega)))
  have gblk : BytesAt m₅.dmem (r.off 2048)
      ((r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z) ++ List.replicate (136 - 80) 0) :=
    Chains.BytesAt.cat hT₅ gz (by rw [hTl])
  -- b94: the padded block XORed into A, `keccak_f`
  have hwf₅ := r.frame_wf hpre hK₅.1.2.2.2 (fun _ ↦ 0) (r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset).toBitVec
  have hm₅ := match_frameS hpre hK₅.1 (ret := (r.pc NativeRustcX64.Sphincs.SphincsVerify.b95Offset).toBitVec)
    (k := [(.r13, .lit 80), (.r15, .ptr 0 2048), (.r12, .ptr 0 4096), (.r14, .label "memcpy")])
    ⟨Chains.known_lit g13, Chains.known_ptr g15, Chains.known_ptr g12, g14, trivial⟩
  refine Chains.blk r hp b94_in_code (List.cons_ne_nil _ _) run_b94 hwf₅ (fun _ _ ↦ rfl) hm₅
    fun st₆ hm₆ hpc₆ ↦ ?_
  have kept₆ : KeptBy r _ m₅ st₆.data := keptBy_of_match hpre hm₆ hwf₅
  have hxor := xorFinal hm₆ hwf₅ (r := 0) (b := r.base) (sz := frameRegion) rfl (oA := 4096)
    (oK := 2048) (by decide) (by decide +kernel) hTl (by decide) gblk
  have hz0 : bytesOf m₅.dmem (r.off 4096) 200 = List.replicate 200 0 := by
    have := bytesOf_of_bytesAt (zeros_slice ga0 (a := 0) (k := 200) (by omega))
    rwa [List.length_replicate] at this
  have hxor' : BytesAt st₆.data.dmem (r.off 4096) (Keccak.xorBlock (List.replicate 200 0)
      (Keccak.finalBlock (r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z))) := by
    rw [← hz0]
    exact hxor
  refine keccakF_then hpre hc hpc₆ (KeepC.of_block hpre hK₅ hm₆ hwf₅ (by decide +kernel) rfl)
    (a := 4096) (Chains.regIs_ptr hm₆ rfl) (by decide) fun m₇ hK₇ hS₇ hkc₇ hA₇ ↦ ?_
  have hlen : (Keccak.xorBlock (List.replicate 200 0)
      (Keccak.finalBlock (r.seed ++ r.nodeAdrsOf c z ++ r.childrenOf c z))).length = 200 :=
    Keccak.length_stateBytes _
  rw [← hlen, bytesOf_of_bytesAt hxor'] at hA₇
  have hcur₇ := Chains.take_of_bytesAt hA₇ 16
  rw [← forsUpTo_succ_eq r hc24 hz] at hcur₇
  have g12 := Chains.RegIs.of_saved hS₇ rfl (Chains.regIs_ptr (y := .r12) (o := 4096) hm₆ rfl)
  have g14 := Chains.RegIs.of_saved hS₇ rfl (Chains.regIs_label (y := .r14) hm₆ rfl)
  have gbx := Chains.RegIs.of_saved hS₇ rfl (Chains.regIs_reg hm₆ rfl gbx)
  have g64 := hkc₇ (by flen) (by flen) (kept₆ (by flen) (by rw [W]; decide +kernel) g64)
  have g104 := hkc₇ (by flen) (by flen) (kept₆ (by flen) (by rw [W]; decide +kernel) g104)
  -- b95: the new value, the loop's registers, the branch
  have hwf₇ := r.frame_wf hpre hK₇.1.2.2.2 (fun _ ↦ 0) 0
  have hm₇ := match_frameS hpre hK₇.1 (ret := 0) (k := []) trivial
  refine Chains.blk r hp b95_in_code (List.cons_ne_nil _ _) run_b95 hwf₇ (fun _ h ↦ nomatch h)
    hm₇ fun st₈ hm₈ hpc₈ ↦ ?_
  have hK₈ := Keep.of_block hpre hK₇ hm₈ hwf₇ (by decide +kernel) rfl
  have kept₈ : KeptBy r _ m₇ st₈.data := keptBy_of_match hpre hm₈ hwf₇
  have hcur₈ := Chains.frame_copy16 hm₈ (o := 10368) (o' := 4096) (by decide) (by decide +kernel)
    (by decide +kernel) (r.length_forsUpTo c (z + 1)) hcur₇
  have hl64 := Chains.load_word (vars := fun _ ↦ 0) (ret := 0) g64
  have hrcx : Run.RegIs st₈.data .rcx (BitVec.ofNat 64 (z + 1)) := by
    unfold Run.RegIs reg
    rw [hm₈.regs .rcx _ rfl, hl64]
    rfl
  have hr13 : Run.RegIs st₈.data .r13 (BitVec.ofNat 64 c) := by
    unfold Run.RegIs reg
    rw [hm₈.regs .r13 _ rfl, Chains.load_word g104]
    rfl
  have hr15 : wordBytes (UInt64.ofBitVec (reg st₈.data .r15)) = be64 (r.key 0).tree := by
    unfold reg
    rw [hm₈.regs .r15 _ rfl, ← bytes_word]
    exact bytes_load (env := r.env m₇ (fun _ ↦ 0) 0) (k := 0) (o := 80) hK₇.2.1.w80 rfl
      (by decide)
  have hrbp : wordBytes (UInt64.ofBitVec (reg st₈.data .rbp)) =
      be32 (r.key 0).leaf ++ [0, 0, 0, 0] := by
    unfold reg
    rw [hm₈.regs .rbp _ rfl, ← bytes_word]
    exact bytes_load4 (env := r.env m₇ (fun _ ↦ 0) 0) (k := 0) (o := 60) hK₇.2.1.w60 rfl
  have hr12 := Chains.regIs_reg hm₈ rfl g12
  have hcnd : (SBool.not (SBool.cmp .eq .W64 (.load 0 64 8) (.lit 10))).eval
      (r.env m₇ (fun _ ↦ 0) 0) = decide (z + 1 < 10) := by
    show (!(CmpOp.apply .eq .W64 ((Sym.load 0 64 8).eval (r.env m₇ (fun _ ↦ 0) 0))
      (BitVec.ofNat 64 10))) = _
    rw [hl64, Chains.toBitVec_toUInt64]
    interval_cases z <;> decide
  have hpc := Chains.pc_cond hpc₈
  rw [hcnd] at hpc
  by_cases hlt : z + 1 < 10
  · simp only [hlt, decide_true, ite_true] at hpc
    rw [Chains.labelAt r hp b65_in_code rfl] at hpc
    exact Chains.pc_at hpc (next hlt _ ⟨hK₈, hlt, hrcx, hr13, hr12, hr15, hrbp,
      kept₈ (by flen) (by rw [W]; decide +kernel) g104, hcur₈,
      Chains.regIs_reg hm₈ rfl gbx, Chains.regIs_reg hm₈ rfl g14⟩)
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false] at hpc
    have h10 : z + 1 = 10 := by omega
    refine Chains.pc_at hpc (done h10 _ ⟨⟨hK₈.1, hK₈.2.1⟩, hr13, hr12, hr15, hrbp, ?_,
      Chains.regIs_reg hm₈ rfl gbx⟩)
    rw [r.forsRoot_eq hc24, ← h10]
    exact hcur₈

end

end NativeRustcX64.SphincsVerifyProof.Fors
