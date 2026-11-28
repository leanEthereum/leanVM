module

public import NativeRustcVmArm.Keccak.WordsHash.Inv
public import NativeRustcVmArm.Keccak.WordsHash.Blocks
public import NativeRustcVmArm.Spec.Keccak

/-!
# `keccak256_words::<hash_words's closure>`: one lane of a block

The words of the slice as the body loads them (`load_word`: a word of a region at a word of the
slice is `word`; `word_ge`: past the slice, `0`), the comparisons the branches take
(`ult_ofNat`), and the step of the last block's lane `j` (`tailZ_step`: the word past the slice,
lane `j` XORed with zero; `tailL_step`: the word loaded at X21 plus X9 words), each from the
invariant before lane `j` to the one after it, at the next lane's loaded or zero block.
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
  LeanVM.Protocol.KeccakHash NativeRustcArm
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep load_of_wordAt
  load_eq_of_bytes)
open NativeRustcVmArm.Keccak NativeRustcVm.Keccak

public section

/-- Past the slice, a word is zero. -/
theorem word_ge {m0 : MachineData} {i : Nat} (hi : m0.regs.X4.toNat ≤ i) : word m0 i = 0 := by
  rw [word, Native.Keccak.Proof.littleEndianLane_eq]
  rw [Native.Keccak.Proof.laneOf_congr (g := fun _ => 0) fun t ht => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [Hasher.length_bytesOf]; omega)]
    rfl]
  exact Native.Keccak.Proof.laneOf_zero

/-- An unsigned comparison of sums that do not wrap. -/
theorem ult_ofNat {a b c : Nat} (hab : a + b < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).ult (BitVec.ofNat 64 c) = decide (a + b < c) := by
  rw [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt hc]

variable {env : Env}

/-- **A word of the slice**: where region `r` is at word `i0` of the slice, unchanged since the
entry, its word `q` is word `i0 + q`. -/
theorem load_word {m0 : MachineData} {r i0 q sz : Nat}
    (hb : env.regions[r]? = some (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * i0), sz))
    (hi : i0 + q < m0.regs.X4.toNat)
    (hsame : ∀ t < 8, env.mem0.get? (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * (i0 + q) + t)) =
      m0.dmem.get? (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * (i0 + q) + t))) :
    env.load r (8 * q) 8 = (word m0 (i0 + q)).toBitVec := by
  apply load_eq_of_bytes
  intro t ht
  rw [Env.base_eq hb, addr_add, show 8 * i0 + (8 * q + t) = 8 * (i0 + q) + t by omega, hsame t ht,
    word, Native.Keccak.Proof.littleEndianLane_eq, Hasher.laneOf_byte _ ht, Hasher.getD_bytesOf _ _
      (by omega)]

theorem memExtE3 (i : Nat) :
    UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 (BitVec.ofNat 64 i) = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq]
  omega

theorem eor64 (x y : BitVec 64) : BinOp.apply .eor .W64 x y = x ^^^ y := by
  simp [BinOp.apply]

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp [BinOp.apply]

/-- The last block's words begin at `base`. -/
abbrev base (m0 : MachineData) : Nat := 17 * nb m0

/-- The state after the whole blocks. -/
abbrev stA (m0 : MachineData) : KeccakState := wordBlocks (word m0) (nb m0)

/-- Word `base + j` is below the bound X22. -/
@[expose] def cmpJ (j : Nat) : SBool := .cmp .ult .W64 (.bin .add .W64 (.reg .X23) (.lit j)) (.reg .X22)

/-- The facts of the precondition the steps use. -/
structure Geo (m0 : MachineData) : Prop where
  stk : StackOk m0 NativeRustcVmArm.keccak256WordsStack
  len : m0.regs.X2.toNat = 8 * m0.regs.X4.toNat
  map : Mapped m0.dmem m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat)
  nw : NoWrap m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat)
  ap : 0 < m0.regs.X4.toNat → Apart m0.regs.X3.toBitVec (8 * m0.regs.X4.toNat)
    (stackBelow m0 NativeRustcVmArm.keccak256WordsStack) NativeRustcVmArm.keccak256WordsStack

theorem base_le {m0 : MachineData} (g : Geo m0) : base m0 + 17 ≤ m0.regs.X4.toNat + 17 ∧
    8 * m0.regs.X4.toNat < 2 ^ 64 + 1 := by
  have := g.len
  have := m0.regs.X2.toNat_lt
  unfold base nb
  omega

/-- Bytes of the slice are the entry's. -/
theorem slice_same {m0 m : MachineData} (g : Geo m0) (hc : Ctx m0 m) {p : Nat}
    (hp : p < 8 * m0.regs.X4.toNat) :
    m.dmem.get? (m0.regs.X3.toBitVec + BitVec.ofNat 64 p) =
      m0.dmem.get? (m0.regs.X3.toBitVec + BitVec.ofNat 64 p) := by
  have hst := g.stk
  refine hc.same _ (not_inRange_of_apart g.nw ?_ (g.ap (by omega)) hp)
  have := hst.2.1
  have := @sp_lt m0
  have hs := stack_toNat hst
  unfold NoWrap
  rw [hs]
  simp only [NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack] at *
  omega

variable [Host]

/-- **The invariant before lane `j` of the last block**: `Ctx`, the first `j` lanes XORed, X9
word `base + j`, at lane `j`'s loaded block `sL` if it is in the slice, else its zero block. -/
@[expose] def TailAt (m0 : MachineData) (k j sL sZ : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (pre (stA m0) (word m0) (base m0) j) ∧
    (j ≠ 0 → (st.data.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (base m0 + j)) ∧
    st.pc = if base m0 + j < m0.regs.X4.toNat then Host.addrOf (k + sL) else Host.addrOf (k + sZ)

/-- The branch after lane `j`. -/
theorem tail_pc {m0 m : MachineData} (g : Geo m0) (hc : Ctx m0 m) {rs : List (BitVec 64 × Nat)}
    {j : Nat} (hj : j ≤ 17) {st : MachineState} {s n : Nat} {pos : Bool} {lbl : Label}
    {sL sZ k : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + n = if pos then sZ else sL)
    (hpc : PcOk (Env.ofMachine m rs) (.cond (if pos then cmpJ j else .not (cmpJ j)) lbl)
      (Host.addrOf (k + s + n)) st) :
    st.pc = if base m0 + j < m0.regs.X4.toNat then Host.addrOf (k + sL) else
      Host.addrOf (k + sZ) := by
  have hb := base_le g
  have hev : (cmpJ j).eval (Env.ofMachine m rs) = decide (base m0 + j < m0.regs.X4.toNat) := by
    simp only [cmpJ, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, add64,
      Env.ofMachine_regs]
    have h4 := m0.regs.X4.toNat_lt
    have e : m0.regs.X4.toBitVec = BitVec.ofNat 64 m0.regs.X4.toNat := by simp
    rw [hc.x23, hc.x22, e, ult_ofNat (by unfold base at hb; omega) h4]
  simp only [PcOk] at hpc
  rw [hpc, Nat.add_assoc, hnext]
  cases pos <;> simp only [Bool.false_eq_true, ↓reduceIte, SBool.eval, hev] at hlab ⊢ <;>
    rw [hlab] <;> by_cases h : base m0 + j < m0.regs.X4.toNat <;> simp [h]

/-- **A lane of the last block past the slice**: lane `j` XORed with zero. -/
theorem tailZ_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {j : Nat} (hj : j < 16)
    (hz : m0.regs.X4.toNat ≤ base m0 + j) (hc : Ctx m0 m)
    (hl : Lanes m0 m (pre (stA m0) (word m0) (base m0) j))
    {blk : List Directive} {s : Nat} {S : SState} {x : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startMain = some (S, x))
    (hmem : S.mem = [⟨0, 8 + 8 * j, 8, .load 0 (8 + 8 * j) 8⟩]) (hsp : S.sp = .ptr 0 0)
    (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs)
    (hx9 : S.reg .X9 = some (.bin .add .W64 (.reg .X23) (.lit (j + 1))))
    {pos : Bool} {lbl : Label}
    (hexit : x = .cond (if pos then cmpJ (j + 1) else .not (cmpJ (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (TailAt m0 k (j + 1) sL sZ) ⟨m, Host.addrOf (k + s)⟩ := by
  have hstk := g.stk
  let env := Env.ofMachine m [(frame m0, 288)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env startMain m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_then hk hx hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
  · refine ctx_step hstk hc hm' hwf rfl hsp hregs fun w hw => ?_
    rw [hmem, List.mem_singleton] at hw
    subst hw
    exact ⟨rfl, by simp; omega⟩
  · have := lanes_step hm' rfl (by omega) hmem hl (x := Keccak.lane (stA m0) j ^^^ word m0 (base m0 + j))
      (by
        rw [word_ge hz, UInt64.xor_zero]
        show env.load 0 (8 + 8 * j) 8 = _
        rw [load_of_wordAt (r := 0) (hl j (by omega))]
        simp [pre])
    rwa [pre_succ _ _ _ _ rfl] at this
  · intro _
    rw [hm'.regs .X9 _ hx9]
    show BinOp.apply .add .W64 (m.regs.getXReg .X23).toBitVec (BitVec.ofNat 64 (j + 1)) = _
    rw [add64, hc.x23, BitVec.ofNat_add_ofNat]
  · rw [hexit] at hpc
    exact tail_pc g hc (by omega) hlab hnext hpc

omit [Host] in
/-- Words `i0` to `i0 + c` of the slice: in it, apart from the stack, mapped. -/
theorem slice_region {m0 m : MachineData} (g : Geo m0) (hc : Ctx m0 m) {i0 c : Nat}
    (hi : i0 + c ≤ m0.regs.X4.toNat) (hc0 : 0 < c) :
    let a := m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * i0)
    a.toNat = m0.regs.X3.toBitVec.toNat + 8 * i0 ∧ (Mapped m.dmem a (8 * c) ∧ NoWrap a (8 * c)) ∧
      Apart (frame m0) 288 a (8 * c) := by
  intro a
  have hnw := g.nw
  have hst := g.stk
  have hap := g.ap (by omega)
  have := hst.2.1
  have := @sp_lt m0
  have hs := stack_toNat hst
  have hf := frame_toNat hst
  unfold NoWrap at hnw
  have ha : a.toNat = m0.regs.X3.toBitVec.toNat + 8 * i0 := toNat_add_ofNat _ _ (by omega)
  refine ⟨ha, ⟨fun t ht => ?_, ?_⟩, ?_⟩
  · rw [addr_add]
    exact hc.kept _ (g.map _ (by omega))
  · unfold NoWrap
    omega
  · unfold Apart at hap ⊢
    rw [hs] at hap
    simp only [NativeRustcVmArm.keccak256WordsStack, NativeRustcVmArm.keccakFStack] at *
    omega

omit [Host] in
/-- The address of word `i` of the slice. -/
theorem addr_word {m0 m : MachineData} (hc : Ctx m0 m) {i : Nat} {x : XReg}
    (hx : (m.regs.getXReg x).toBitVec = BitVec.ofNat 64 i) :
    BinOp.apply .add .W64 (m.regs.getXReg .X21).toBitVec
      (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 (m.regs.getXReg x).toBitVec) =
      m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * i) := by
  rw [add64, hx, memExtE3, hc.x21]

/-- **A lane of the last block in the slice**: lane `j` XORed with the word loaded. -/
theorem tailL_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {j : Nat} (hj : j < 16)
    (hin : base m0 + j < m0.regs.X4.toNat) (hc : Ctx m0 m)
    (hl : Lanes m0 m (pre (stA m0) (word m0) (base m0) j))
    {a : Sym} (ha : (a = addrX9 ∧ (m.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (base m0 + j)) ∨
      (a = addrX23 ∧ j = 0))
    {blk : List Directive} {s : Nat} {S : SState} {x : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s))
    (hx : exec blk (init [(288, true), (8, false)] (.ptr 0 0) [] [] [] [(a, 1, 0)]) = some (S, x))
    (hmem : S.mem = [⟨0, 8 + 8 * j, 8, .bin .eor .W64 (.load 0 (8 + 8 * j) 8) (.load 1 0 8)⟩])
    (hsp : S.sp = .ptr 0 0)
    (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs)
    (hx9' : S.reg .X9 = some (.bin .add .W64 (.reg .X23) (.lit (j + 1))))
    {pos : Bool} {lbl : Label}
    (hexit : x = .cond (if pos then cmpJ (j + 1) else .not (cmpJ (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (TailAt m0 k (j + 1) sL sZ) ⟨m, Host.addrOf (k + s)⟩ := by
  have hstk := g.stk
  obtain ⟨hat, hreg1, hap1⟩ := slice_region g hc (i0 := base m0 + j) (c := 1) (by omega) (by omega)
  let env := Env.ofMachine m [(frame m0, 288),
    (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * (base m0 + j)), 8)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, hreg1, trivial⟩
      (List.pairwise_pair.mpr hap1)
  have hm : Match env (init [(288, true), (8, false)] (.ptr 0 0) [] [] [] [(a, 1, 0)]) m := by
    refine match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide),
      trivial⟩ (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial ⟨?_, trivial⟩
    show a.eval env = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * (base m0 + j)) +
      BitVec.ofInt 64 0
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
    rcases ha with ⟨rfl, hx9⟩ | ⟨rfl, rfl⟩
    · exact addr_word hc hx9
    · exact addr_word hc hc.x23
  refine exec_then hk hx hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
  · refine ctx_step hstk hc hm' hwf rfl hsp hregs fun w hw => ?_
    rw [hmem, List.mem_singleton] at hw
    subst hw
    exact ⟨rfl, by simp; omega⟩
  · have hw : env.load 1 (8 * 0) 8 = (word m0 (base m0 + j + 0)).toBitVec :=
      load_word (r := 1) rfl (by omega) fun t ht => slice_same g hc (by omega)
    have := lanes_step hm' rfl (by omega) hmem hl
      (x := Keccak.lane (stA m0) j ^^^ word m0 (base m0 + j))
      (by
        show BinOp.apply .eor .W64 (env.load 0 (8 + 8 * j) 8) (env.load 1 0 8) = _
        rw [eor64, load_of_wordAt (r := 0) (hl j (by omega))]
        simp only [Nat.mul_zero, Nat.add_zero] at hw
        rw [hw]
        simp [pre])
    rwa [pre_succ _ _ _ _ rfl] at this
  · intro _
    rw [hm'.regs .X9 _ hx9']
    show BinOp.apply .add .W64 (m.regs.getXReg .X23).toBitVec (BitVec.ofNat 64 (j + 1)) = _
    rw [add64, hc.x23, BitVec.ofNat_add_ofNat]
  · rw [hexit] at hpc
    exact tail_pc g hc (by omega) hlab hnext hpc

end

end NativeRustcVmArm.WordsHash
