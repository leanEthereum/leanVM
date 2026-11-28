module

public import NativeRustcArm.SphincsVerify.Digest.Keep
public import NativeRustcArm.SphincsVerify.Digest.Bits
public import NativeRustcArm.SphincsVerify.Digest.Exec
public import NativeRustcArm.SphincsVerify.Rev
import Mathlib.Tactic.IntervalCases

/-!
# `digest_fields`' leaves: the loop `b57`

`.LSphincsVerify_19` (directive 621): turn `c` (X8 `10 c`, X9 `base + 16400 + 8 c`) reads bits
`10 c .. 10 c + 9` of `h_msg` (`H`, at X21 `base + 24720`) and stores leaf `c` as a word at X9
(`LoopInv`); after 24 turns it falls through to `b58` (directive 692) with the 24 leaves' words at
`16400` (`AfterLoop`, `loop_spec`).
-/

namespace NativeRustcArm.SphincsVerifyProof.Digest

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- Leaf `i` of `digest_fields` of `H`. -/
def leafOf (H : List UInt8) (i : Nat) : Nat :=
  (List.range 10).foldl (fun v j ↦ v <<< 1 ||| digestBit H (10 * i + j)) 0

/-- The first `c` leaves' words. -/
def leavesBytes (H : List UInt8) (c : Nat) : List UInt8 :=
  wordsBytes ((List.range c).map fun i ↦ (leafOf H i).toUInt64)

/-- **At the loop's head, turn `c`**: what the digest keeps, the loop's registers, `H` at `24720`,
the first `c` leaves at `16400`. -/
def LoopInv (r : Run) (H : List UInt8) (c : Nat) (m : MachineData) : Prop :=
  c < 24 ∧ Keep r m ∧ Run.RegIs m .X8 (BitVec.ofNat 64 (10 * c)) ∧
    Run.RegIs m .X9 (r.off (16400 + 8 * c)) ∧ Run.RegIs m .X10 (BitVec.ofNat 64 6) ∧
    Run.RegIs m .X21 (r.off 24720) ∧ Run.RegIs m .X23 (r.off 21648) ∧
    BytesAt m.dmem (r.off 24720) H ∧ BytesAt m.dmem (r.off 16400) (leavesBytes H c)

/-- **After the loop**: what the digest keeps, X23, `H` at `24720`, the 24 leaves at `16400`. -/
def AfterLoop (r : Run) (H : List UInt8) (m : MachineData) : Prop :=
  Keep r m ∧ Run.RegIs m .X23 (r.off 21648) ∧ BytesAt m.dmem (r.off 24720) H ∧
    BytesAt m.dmem (r.off 16400) (leavesBytes H 24)

end

public section

theorem length_leavesBytes (H : List UInt8) (c : Nat) : (leavesBytes H c).length = 8 * c := by
  simp [leavesBytes, Native.Keccak.Proof.length_wordsBytes]

theorem leavesBytes_succ (H : List UInt8) (c : Nat) :
    leavesBytes H (c + 1) = leavesBytes H c ++ wordBytes (leafOf H c).toUInt64 := by
  rw [leavesBytes, leavesBytes, List.range_succ, List.map_append]
  simp [Native.Keccak.wordsBytes]

section
variable [Labels]

/-- The loop's byte indices are below `30`. -/
theorem bix_lt (env : Env) {c : Nat} (hc : c < 24) (hx : env.regs .X8 = BitVec.ofNat 64 (10 * c))
    {j : Nat} (hj : j < 10) : ((bix j).eval env).toNat < 30 := by
  interval_cases j <;>
  · simp only [bix, ↓reduceIte, Nat.reduceEqDiff]
    sym_simp
    rw [hx]
    clear hx
    revert c
    decide

/-- The loop's branch back: another turn while `c + 1 < 24`. -/
theorem cond_eval (env : Env) {c : Nat} (hc : c < 24) (hx : env.regs .X8 = BitVec.ofNat 64 (10 * c)) :
    (SBool.not (.cmp .eq .W64 (.bin .add .W64 (.reg .X8) (.lit 10)) (.lit 240))).eval env =
      decide (c + 1 < 24) := by
  sym_simp
  rw [hx]
  clear hx
  revert c
  decide

/-- The bit index's next value. -/
theorem add10_eval (env : Env) {c : Nat} (hx : env.regs .X8 = BitVec.ofNat 64 (10 * c)) :
    (Sym.bin .add .W64 (.reg .X8) (.lit 10)).eval env = BitVec.ofNat 64 (10 * (c + 1)) := by
  sym_simp
  rw [hx, Nat.mul_succ, BitVec.ofNat_add]

omit [Labels] in
/-- A byte of region 0 holding `H`. -/
theorem load_byte {env : Env} {H : List UInt8} (h : BytesAt env.mem0 (env.base 0) H) {k : Nat}
    (hk : k < H.length) : env.load 0 k 1 = BitVec.ofNat 64 (H.getD k 0).toNat := by
  rw [Env.load_of_bytesAt (n := 1) (bs := [H.getD k 0]) rfl ?_]
  · simp [Int.ofBytes]
  · intro i hi
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff] at hi
    subst hi
    have := h k hk
    simpa [List.getD_eq_getElem?_getD, hk] using this

end

variable [NativeRustcArm.Host]

/-- **A turn of the loop**: leaf `c` stored, then the next turn or `b58`. -/
theorem loop_step (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {H : List UInt8} (hH : H.length = 64) {c : Nat} {m : MachineData} (hI : LoopInv r H c m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset ∧ AfterLoop r H st.data) ∨
      (st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b57Offset ∧ LoopInv r H (c + 1) st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b57Offset⟩ := by
  obtain ⟨hc, hK, h8, h9, h10, h21, h23, hHb, hL⟩ := hI
  have hF : r.Frame m := hK.1
  have hwf := wf_frame2 hpre hF (a := 24720) (n := 64) (a' := 16400 + 8 * c) (n' := 8)
    (by omega) (by omega) (by omega) (fun _ ↦ 0)
  have hx8 : (Env.ofMachine m [(r.off 24720, 64), (r.off (16400 + 8 * c), 8)]).regs .X8 =
      BitVec.ofNat 64 (10 * c) := h8
  have hm : Match (Env.ofMachine m [(r.off 24720, 64), (r.off (16400 + 8 * c), 8)]) s57 m := by
    refine match_ofMachine ⟨rfl, (by intro h; cases h), rfl, (by intro h; cases h), trivial⟩ rfl
      ⟨?_, ?_, ?_, trivial⟩ trivial ?_ trivial
    · show _ = r.off 24720 + BitVec.ofInt 64 0
      rw [h21]
      simp
    · show _ = r.off (16400 + 8 * c) + BitVec.ofInt 64 0
      rw [h9]
      simp
    · exact h10
    · simp only [List.map_cons, List.map_nil, AllOf]
      exact ⟨bix_lt _ hc hx8 (by decide), bix_lt _ hc hx8 (by decide), bix_lt _ hc hx8 (by decide),
        bix_lt _ hc hx8 (by decide), bix_lt _ hc hx8 (by decide), bix_lt _ hc hx8 (by decide),
        bix_lt _ hc hx8 (by decide), bix_lt _ hc hx8 (by decide), bix_lt _ hc hx8 (by decide),
        trivial⟩
  have hk := Sphincs.SphincsVerify.b57_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk run_b57 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨m', pc⟩ := st
  simp only [PcOk] at hpc
  rw [cond_eval _ hc hx8] at hpc
  simp only at hm'
  -- memory: the leaf's word, the rest kept
  have hso : SameOutside m.dmem m'.dmem (InRange (r.off (16400 + 8 * c)) 8) :=
    sameOutside_region hm' hwf (k := 1) rfl rfl
  have hK' : Keep r m' := hK.of_range hpre (a := 16400 + 8 * c) (n := 8)
    ⟨by omega, by omega⟩ hso (hm'.sp.trans hF.1) ((hm'.regs .X29 _ rfl).trans hF.2.1)
    (hm'.kept hwf)
  have hb : ∀ k < 30, (Env.ofMachine m [(r.off 24720, 64), (r.off (16400 + 8 * c), 8)]).load 0 k 1 =
      BitVec.ofNat 64 (H.getD k 0).toNat := fun k hk ↦ load_byte hHb (by omega)
  have hleaf : BytesAt m'.dmem (r.off (16400 + 8 * c)) (wordBytes (leafOf H c).toUInt64) := by
    have := hm'.bytesAt_write (r := 1) (o := 0) (n := 8) (b := r.off (16400 + 8 * c)) (sz := 8)
      rfl (by decide) (v := comb t0 t1 t2 t3 t4 t5 t6 t7 t8 t9)
      (fun i hi ↦ findWrite_head (ws := []) hi)
    rw [comb_leaf _ H hc hx8 hb, bytes_word] at this
    simp only [BitVec.add_zero] at this
    exact this
  have hH' := keep_range hpre hHb hso (by rw [hH]; omega) (by rw [hH]; omega) (by omega)
  have hL' := keep_range hpre hL hso (by rw [length_leavesBytes]; omega)
    (by rw [length_leavesBytes]; omega) (by omega)
  have hL'' : BytesAt m'.dmem (r.off 16400) (leavesBytes H (c + 1)) := by
    rw [leavesBytes_succ]
    refine bytesAt_append hL' ?_
    rw [length_leavesBytes, Run.off_add]
    exact hleaf
  have h23' := regIs_keep hm' rfl h23
  by_cases hlast : c + 1 < 24
  · refine .done _ (.inr ⟨?_, hlast, hK', ?_, ?_, regIs_lit hm' rfl, ?_, h23', hH', hL''⟩)
    · rw [hpc, decide_eq_true hlast]
      simp only [↓reduceIte]
      exact Run.label_of_block r hp Sphincs.SphincsVerify.b57_in_code rfl
    · unfold Run.RegIs
      rw [hm'.regs .X8 _ rfl, add10_eval _ hx8]
    · unfold Run.RegIs
      rw [hm'.regs .X9 _ rfl]
      show (Env.ofMachine m _ _).base 1 + BitVec.ofInt 64 8 = _
      rw [Env.base_ofMachine m _ _ rfl, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 by decide,
        Run.off_add, show 16400 + 8 * c + 8 = 16400 + 8 * (c + 1) by omega]
    · unfold Run.RegIs
      rw [hm'.regs .X21 _ rfl]
      simp [Sym.eval]
  · have hc23 : c = 23 := by omega
    subst hc23
    refine .done _ (.inl ⟨?_, hK', h23', hH', hL''⟩)
    rw [hpc, decide_eq_false hlast]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rfl

/-- **The loop**: from turn `c`, the machine reaches `b58` with the 24 leaves. -/
theorem loop_spec (r : Run) (hp : Placed Sphincs.SphincsVerify.code r.k) (hpre : r.Pre)
    {H : List UInt8} (hH : H.length = 64) {c : Nat} {m : MachineData} (hI : LoopInv r H c m) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b58Offset ∧ AfterLoop r H st.data)
      ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b57Offset⟩ := by
  refine Sym.loop (fun n st ↦ ∃ c, n = 24 - c ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b57Offset ∧ LoopInv r H c st.data)
    (fun n st ⟨c, hn, hpc, hI⟩ ↦ ?_) ⟨c, rfl, rfl, hI⟩
  obtain ⟨m, pc⟩ := st
  simp only at hpc
  subst hpc
  refine NativeRustcArm.Eventually.mono (loop_step r hp hpre hH hI) fun st h ↦ ?_
  rcases h with h | ⟨hpc, hI'⟩
  · exact .inl h
  · exact .inr ⟨24 - (c + 1), by have := hI.1; have := hI'.1; omega, c + 1, rfl, hpc, hI'⟩

end

end NativeRustcArm.SphincsVerifyProof.Digest
