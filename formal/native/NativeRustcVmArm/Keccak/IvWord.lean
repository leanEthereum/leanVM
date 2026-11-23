module

public import NativeRustcVmArm.Code.Vm.IvWord.Names
public import NativeRustcVmArm.Keccak.IvWord.Blocks
public import NativeRustcVmArm.Keccak.Common
public import NativeRustcVm.Keccak.Words
public import NativeRustcVm.MemLemmas

/-!
# `iv_word` meets its contract

`ivWord_spec`: `iv_word(bc, n, k)` returns word `k` of `ivWords` of the `n` words at `bc`
(`IvWordPost`). For `k = 0` the tag's first word (`tag`, `b5`); else X8 the top byte of word
`k - 1` of `ext` (`top`: the tag's ninth byte for `k = 1`, `first`, `b6`; the top byte of word
`k - 2` of the bytecode, `loadTop`, `b3`, or zero past it, `none9`, `b9`), then ORed with word
`k - 1` of the bytecode shifted by 8 if it is one (`loadWord`, `b7`), returned (`ret8`, `b8`).
Every block keeps memory, the callee-saved registers, SP, X30 and the arguments (`Fr`).
-/

namespace NativeRustcVmArm.IvWordRun

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm.Keccak (ivWord ivWord_succ getD_ivWords getD_eq_zero)
open Vm.IvWord

@[expose] public section

/-- What `iv_word` keeps from its entry `m0`: memory, the callee-saved registers, SP, X30 and its
arguments. -/
def Fr (m0 m : MachineData) : Prop :=
  m.dmem = m0.dmem ∧ Saved m0 m ∧ m.regs.X30 = m0.regs.X30 ∧ m.regs.X0 = m0.regs.X0 ∧
    m.regs.X1 = m0.regs.X1 ∧ m.regs.X2 = m0.regs.X2

/-- The top byte of word `K - 1` of `ext`: the tag's ninth for `K = 1`. -/
def top (w : List UInt64) (K : Nat) : UInt64 :=
  (if K - 1 = 0 then tagLast <<< 56 else w.getD (K - 2) 0) >>> 56

/-- The words at the entry's X0, `n` of them, are `w`. -/
def Ws (m0 : MachineData) (w : List UInt64) : Prop :=
  w.length = m0.regs.X1.toNat ∧ NativeRustcVm.WordsAt m0.dmem m0.regs.X0.toBitVec w

/-- Before `loadWord` (`b7`): X9 is `k - 1`, a word of the bytecode, X8 `top`. -/
def At7 [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Fr m0 st.data ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.IvWord.b7Offset) ∧ 1 ≤ m0.regs.X2.toNat ∧
    (st.data.regs.getXReg .X9).toNat = m0.regs.X2.toNat - 1 ∧
    m0.regs.X2.toNat - 1 < m0.regs.X1.toNat ∧
    ∀ w, Ws m0 w → st.data.regs.getXReg .X8 = top w m0.regs.X2.toNat

/-- Before `ret8` (`b8`): X8 is the result. -/
def At8 [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Fr m0 st.data ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.IvWord.b8Offset) ∧
    ∀ w, Ws m0 w → st.data.regs.getXReg .X8 = ivWord w m0.regs.X2.toNat

end

public section

theorem ivWord_top (w : List UInt64) {K : Nat} (hK : 1 ≤ K) :
    ivWord w K = top w K ||| (w.getD (K - 1) 0 <<< 8) := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
  rw [ivWord_succ, top]
  rcases j with _ | j
  · rfl
  · simp

theorem Fr.x0 {m0 m : MachineData} (h : Fr m0 m) :
    (m.regs.getXReg .X0).toBitVec = m0.regs.X0.toBitVec := congrArg UInt64.toBitVec h.2.2.2.1

theorem Fr.x1 {m0 m : MachineData} (h : Fr m0 m) :
    (m.regs.getXReg .X1).toBitVec.toNat = m0.regs.X1.toNat := congrArg UInt64.toNat h.2.2.2.2.1

theorem Fr.x2 {m0 m : MachineData} (h : Fr m0 m) :
    (m.regs.getXReg .X2).toBitVec.toNat = m0.regs.X2.toNat := congrArg UInt64.toNat h.2.2.2.2.2

theorem if_not {α : Type} {p : Prop} [Decidable p] (a b : α) :
    (if (!decide p) = true then a else b) = if p then b else a := by
  by_cases h : p <;> simp [h]

/-- A block without stores keeping the callee-saved registers, SP and X30. -/
theorem keep_step [Labels] {env : Env} {S0 S : SState} {m0 m m' : MachineData} (hfr : Fr m0 m)
    (hm0 : Match env S0 m) (hm : Match env S m') (hwf : env.WF) (hd : m.dmem = env.mem0)
    (hmem : S.mem = []) (hk : keeps S0 S = true)
    (h30 : S0.reg .X30 = some (.reg .X30) ∧ S.reg .X30 = some (.reg .X30)) :
    m'.dmem = m0.dmem ∧ Saved m0 m' ∧ m'.regs.X30 = m0.regs.X30 := by
  obtain ⟨hd0, hs0, h30', -⟩ := hfr
  have hs := Match.saved hm0 hm hwf hd hk
  have hd' : m'.dmem = m0.dmem := (hm.dmem_eq hwf hmem).trans (hd.symm.trans hd0)
  exact ⟨hd', ⟨fun r hr => (hs.1 r hr).trans (hs0.1 r hr), hs.2.1.trans hs0.2.1,
    fun p h => by rw [hd']; exact h⟩, (Match.reg_eq hm0 hm h30.1 h30.2).trans h30'⟩

/-- A block without stores keeping the callee-saved registers, SP, X30 and the arguments. -/
theorem fr_step [Labels] {env : Env} {S0 S : SState} {m0 m m' : MachineData} (hfr : Fr m0 m)
    (hm0 : Match env S0 m) (hm : Match env S m') (hwf : env.WF) (hd : m.dmem = env.mem0)
    (hmem : S.mem = []) (hk : keeps S0 S = true)
    (hr : ∀ r ∈ [XReg.X0, .X1, .X2, .X30], S0.reg r = some (.reg r) ∧ S.reg r = some (.reg r)) :
    Fr m0 m' := by
  obtain ⟨hd', hs', h30'⟩ := keep_step hfr hm0 hm hwf hd hmem hk (hr .X30 (by simp))
  obtain ⟨-, -, -, h0, h1, h2⟩ := hfr
  have e : ∀ r ∈ [XReg.X0, .X1, .X2, .X30], m'.regs.getXReg r = m.regs.getXReg r :=
    fun r hr' => Match.reg_eq hm0 hm (hr r hr').1 (hr r hr').2
  refine ⟨hd', hs', h30', ?_, ?_, ?_⟩
  · exact (e .X0 (by simp)).trans h0
  · exact (e .X1 (by simp)).trans h1
  · exact (e .X2 (by simp)).trans h2

theorem cmp_eq64 (x : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn]

theorem cmp_ult64 (x y : BitVec 64) : CmpOp.apply .ult .W64 x y = decide (x.toNat < y.toNat) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult]

theorem memExtE3 (i : Nat) :
    UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 (BitVec.ofNat 64 i) = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq]
  omega

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp [BinOp.apply]

theorem lsl64 (x : BitVec 64) (n : Nat) : UnOp.apply (.shift .LSL n) .W64 x = x <<< n := by
  simp only [UnOp.apply, low_W64, ext_W64, shiftW]

theorem orr64 (x y : BitVec 64) : BinOp.apply .orr .W64 x y = x ||| y := by
  simp [BinOp.apply]

theorem sub64_toNat {x : BitVec 64} {n : Nat} (h : n ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 n)).toNat = x.toNat - n := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  omega

/-- A byte, loaded. -/
theorem load_one {env : Env} {r off : Nat} {b : UInt8}
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 off) [b]) :
    env.load r off 1 = BitVec.ofNat 64 b.toNat := by
  rw [Env.load_of_bytesAt (n := 1) rfl h]
  show BitVec.ofInt 64 (0 * 256 + (b.toNat : Int)) = _
  simp

/-- The top byte of a word, loaded. -/
theorem load_top {env : Env} {r : Nat} {x : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r) x) : env.load r 7 1 = (x >>> 56).toBitVec := by
  rw [load_one (b := (x >>> 56).toUInt8) ?_]
  · apply BitVec.eq_of_toNat_eq
    have hx := x.toNat_lt
    have e : (x >>> 56).toUInt8.toNat = (x >>> 56).toNat := by
      rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have h56 : (56 : UInt64).toNat % 64 = 56 := rfl
      rw [h56]
      omega
    rw [BitVec.toNat_ofNat, e, UInt64.toNat_toBitVec]
    have := (x >>> 56).toNat_lt
    omega
  · intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    have := h 7 (by simp [LeanVM.Protocol.KeccakHash.wordBytes])
    rw [addr_add]
    simpa [LeanVM.Protocol.KeccakHash.wordBytes] using this

/-- Word `j` of the bytecode. -/
theorem ws_word {m0 : MachineData} {w : List UInt64} (hw : Ws m0 w) {j : Nat}
    (hj : j < m0.regs.X1.toNat) :
    NativeRustcVm.WordAt m0.dmem (m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * j)) (w.getD j 0) := by
  have := NativeRustcVm.WordsAt.getElem hw.2 (i := j) (by rw [hw.1]; exact hj)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hw.1]; exact hj),
    Option.getD_some]

/-- The region of word `j` of the bytecode. -/
theorem wf_word {m0 m : MachineData} (hfr : Fr m0 m) (hmap : Mapped m0.dmem m0.regs.X0.toBitVec
    (8 * m0.regs.X1.toNat)) (hnw : NoWrap m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat)) {j : Nat}
    (hj : j < m0.regs.X1.toNat) :
    (Env.ofMachine m [(m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * j), 8)]).WF := by
  unfold NoWrap at hnw
  refine Env.wf_of ⟨⟨fun i hi => ?_, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
  · rw [addr_add, Env.ofMachine_mem0, hfr.1]
    exact hmap _ (by omega)
  · unfold NoWrap
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

variable [Host]

omit [Host] in
/-- A label of a block. -/
theorem label_at [Host] {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) {l : Label} {b' : List Directive} (h : b = .label l :: b') :
    Labels.label l = Host.addrOf (k + j) := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

/-- The return: X0 the result. -/
theorem ret_run {k : Nat} (hp : Placed code k) {m0 : MachineData} {st : MachineState}
    (h : At8 m0 k st) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧ IvWordPost m0 st'.data) st := by
  obtain ⟨hfr, hpc, hv⟩ := h
  refine exec_at (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) ret8 (Env.wf_nil _) hpc
    (match_nil _) fun st' hm hpc' => .done _ ?_
  have hfr' := keep_step hfr (match_nil _) hm (Env.wf_nil _) rfl rfl (by decide +kernel)
    ⟨rfl, rfl⟩
  simp only [PcOk] at hpc'
  refine ⟨?_, fun w hlen hw => ?_, hfr'.1, hfr'.2.1⟩
  · rw [hpc', retOf, retOf, hfr'.2.2]
  · apply UInt64.toBitVec_inj.mp
    rw [show st'.data.regs.X0 = st'.data.regs.getXReg .X0 from rfl, hm.regs .X0 _ rfl]
    show (st.data.regs.getXReg .X8).toBitVec = _
    rw [hv w ⟨hlen, hw⟩, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
      ← List.getD_eq_getElem?_getD, getD_ivWords]

/-- `loadWord`: word `k - 1` ORed in. -/
theorem word_run {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (hmap : Mapped m0.dmem m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat))
    (hnw : NoWrap m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat)) {st : MachineState}
    (h : At7 m0 k st) : Eventually (step1 Host.exe) (At8 m0 k) st := by
  obtain ⟨hfr, hpc, hK, hx9, hlt, hv⟩ := h
  let j := m0.regs.X2.toNat - 1
  let env := Env.ofMachine st.data [(m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * j), 8)]
  have hwf : env.WF := wf_word hfr hmap hnw hlt
  have hm : Match env startWord st.data :=
    match_ofMachine ⟨rfl, fun h => absurd h (by decide), trivial⟩ rfl trivial trivial trivial
      ⟨by
        show BinOp.apply .add .W64 (st.data.regs.getXReg .X0).toBitVec
          (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 (st.data.regs.getXReg .X9).toBitVec) =
          _ + BitVec.ofInt 64 0
        rw [show (st.data.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 j by
            apply BitVec.eq_of_toNat_eq
            simp only [UInt64.toNat_toBitVec, hx9, BitVec.toNat_ofNat, j]
            have := m0.regs.X2.toNat_lt
            omega,
          memExtE3, add64, show st.data.regs.getXReg .X0 = m0.regs.X0 from
            hfr.2.2.2.1]
        simp, trivial⟩
  refine exec_at (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) loadWord hwf hpc hm
    fun st' hm' hpc' => .done _ ⟨?_, ?_, fun w hw => ?_⟩
  · exact fr_step hfr hm hm' hwf rfl rfl (by decide +kernel) (by decide +kernel)
  · simp only [PcOk] at hpc'
    exact hpc'
  · apply UInt64.toBitVec_inj.mp
    rw [hm'.regs .X8 _ rfl]
    simp only [Sym.eval, env, Env.ofMachine_regs]
    rw [Keccak.load_wordAt (by
        rw [Env.ofMachine_mem0, hfr.1, Env.base_ofMachine _ _ _ rfl,
          show ∀ b : BitVec 64, b + BitVec.ofNat 64 0 = b from fun b => BitVec.add_zero b]
        exact ws_word hw hlt), hv w hw, ivWord_top w hK, orr64, lsl64, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftLeft]
    rfl

/-- From X8 `top` and X9 `k - 1`: `loadWord` if word `k - 1` is in the bytecode, and the return. -/
theorem top_run {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (hmap : Mapped m0.dmem m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat))
    (hnw : NoWrap m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat)) {st : MachineState}
    (hfr : Fr m0 st.data) (hK : 1 ≤ m0.regs.X2.toNat)
    (hx9 : (st.data.regs.getXReg .X9).toNat = m0.regs.X2.toNat - 1)
    (hv : ∀ w, Ws m0 w → st.data.regs.getXReg .X8 = top w m0.regs.X2.toNat)
    (hpc : st.pc = if m0.regs.X2.toNat - 1 < m0.regs.X1.toNat then Host.addrOf (k + NativeRustcVmArm.Vm.IvWord.b7Offset)
      else Host.addrOf (k + NativeRustcVmArm.Vm.IvWord.b8Offset)) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧ IvWordPost m0 st'.data) st := by
  by_cases h : m0.regs.X2.toNat - 1 < m0.regs.X1.toNat
  · simp only [h, ↓reduceIte] at hpc
    exact Eventually.bind (word_run hp hmap hnw ⟨hfr, hpc, hK, hx9, h, hv⟩) fun _ h8 =>
      ret_run hp h8
  · simp only [h, ↓reduceIte] at hpc
    refine ret_run hp ⟨hfr, hpc, fun w hw => ?_⟩
    rw [hv w hw, ivWord_top w hK, getD_eq_zero (by rw [hw.1]; omega)]
    simp

/-- `top_run` through a jump to the return (`jmp4`, `jmp10`). -/
theorem jmp_run {k e : Nat} (hp : Placed code k) {b : List Directive} (hb : b.IsInfixAt code e)
    (hne : b ≠ []) {S : SState} (hx : exec b start = some (S, .jump NativeRustcVmArm.Vm.IvWord.label_7))
    (h8 : S.reg .X8 = some (.reg .X8)) (h9 : S.reg .X9 = some (.reg .X9))
    (hk : keeps start S = true) (hr : ∀ r ∈ [XReg.X0, .X1, .X2, .X30],
      start.reg r = some (.reg r) ∧ S.reg r = some (.reg r)) (hmem : S.mem = [])
    {m0 : MachineData}
    (hmap : Mapped m0.dmem m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat))
    (hnw : NoWrap m0.regs.X0.toBitVec (8 * m0.regs.X1.toNat)) {st : MachineState}
    (hfr : Fr m0 st.data) (hK : 1 ≤ m0.regs.X2.toNat)
    (hx9 : (st.data.regs.getXReg .X9).toNat = m0.regs.X2.toNat - 1)
    (hv : ∀ w, Ws m0 w → st.data.regs.getXReg .X8 = top w m0.regs.X2.toNat)
    (hpc : st.pc = if m0.regs.X2.toNat - 1 < m0.regs.X1.toNat then Host.addrOf (k + NativeRustcVmArm.Vm.IvWord.b7Offset)
      else Host.addrOf (k + e)) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧ IvWordPost m0 st'.data) st := by
  by_cases h : m0.regs.X2.toNat - 1 < m0.regs.X1.toNat
  · exact top_run hp hmap hnw hfr hK hx9 hv (by simp only [h, ↓reduceIte] at hpc ⊢; exact hpc)
  · simp only [h, ↓reduceIte] at hpc
    refine exec_at (hb.trans hp.1 hne) hx (Env.wf_nil _) hpc (match_nil _) fun st' hm hpc' => ?_
    have e8 := Match.reg_eq (match_nil _) hm rfl h8
    have e9 := Match.reg_eq (match_nil _) hm rfl h9
    refine top_run hp hmap hnw (fr_step hfr (match_nil _) hm (Env.wf_nil _) rfl hmem hk hr) hK
      (by rw [e9]; exact hx9) (fun w hw => by rw [e8]; exact hv w hw) ?_
    simp only [h, ↓reduceIte, PcOk] at hpc' ⊢
    rw [hpc']
    exact label_at hp b8_in_code rfl

/-- **`iv_word` meets its contract.** -/
theorem _root_.NativeRustcVmArm.ivWord_spec {k : Nat} (hp : Placed Vm.IvWord.code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.IvWord.entryLabel) IvWordPre IvWordPost := by
  intro m0 hpre
  obtain ⟨hmap, hnw⟩ := hpre
  rw [show Labels.label NativeRustcVmArm.Vm.IvWord.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.IvWord.b0Offset) from hp.label NativeRustcVmArm.Vm.IvWord.entry_at]
  have hfr0 : Fr m0 m0 := ⟨rfl, ⟨fun _ _ => rfl, rfl, fun _ h => h⟩, rfl, rfl, rfl, rfl⟩
  have hKlt := m0.regs.X2.toNat_lt
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) zero (Env.wf_nil m0)
    (match_nil m0) fun st0 hm0 hpc0 => ?_
  have hfr1 := fr_step hfr0 (match_nil m0) hm0 (Env.wf_nil m0) rfl rfl (by decide +kernel)
    (by decide +kernel)
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_eq64 _ 0 (by decide),
    NativeRustcVmArm.Vm.IvWord.b0_length, NativeRustcVmArm.Vm.IvWord.b0Length, NativeRustcVmArm.Vm.IvWord.b0Offset, Nat.add_zero] at hpc0
  rw [Fr.x2 hfr0] at hpc0
  by_cases hk0 : m0.regs.X2.toNat = 0
  · -- `k = 0`: the tag's first word
    simp only [hk0, decide_true, ↓reduceIte] at hpc0
    rw [label_at hp b5_in_code rfl] at hpc0
    refine exec_at (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) tag (Env.wf_nil _) hpc0
      (match_nil _) fun st hm hpc => .done _ ?_
    obtain ⟨hd, hs, h30⟩ := keep_step hfr1 (match_nil _) hm (Env.wf_nil _) rfl rfl
      (by decide +kernel) ⟨rfl, rfl⟩
    simp only [PcOk] at hpc
    refine ⟨by rw [hpc, retOf, retOf, h30], fun w _ _ => ?_, hd, hs⟩
    apply UInt64.toBitVec_inj.mp
    rw [show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl, hm.regs .X0 _ rfl, hk0,
      Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD,
      getD_ivWords]
    rfl
  simp only [hk0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc0
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) one (Env.wf_nil _) hpc0
    (match_nil _) fun st1 hm1 hpc1 => ?_
  have hfr2 := fr_step hfr1 (match_nil _) hm1 (Env.wf_nil _) rfl rfl (by decide +kernel)
    (by decide +kernel)
  have hx9 : (st1.data.regs.getXReg .X9).toNat = m0.regs.X2.toNat - 1 := by
    show (st1.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [hm1.regs .X9 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [sub64_toNat (by rw [Fr.x2 hfr1]; omega), Fr.x2 hfr1]
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_eq64 _ 1 (by decide),
    NativeRustcVmArm.Vm.IvWord.b1_length, NativeRustcVmArm.Vm.IvWord.b1Length] at hpc1
  rw [Fr.x2 hfr1] at hpc1
  by_cases hk1 : m0.regs.X2.toNat = 1
  · -- `k = 1`: the tag's ninth byte
    simp only [hk1, decide_true, ↓reduceIte] at hpc1
    rw [label_at hp b6_in_code rfl] at hpc1
    refine exec_at (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) first (Env.wf_nil _) hpc1
      (match_nil _) fun st2 hm2 hpc2 => ?_
    have hfr3 := fr_step hfr2 (match_nil _) hm2 (Env.wf_nil _) rfl rfl (by decide +kernel)
      (by decide +kernel)
    have e9 := Match.reg_eq (match_nil _) hm2 (r := .X9) rfl rfl
    refine top_run hp hmap hnw hfr3 (by omega) (by rw [e9]; exact hx9) (fun w _ => ?_) ?_
    · apply UInt64.toBitVec_inj.mp
      rw [hm2.regs .X8 _ rfl, top, hk1]
      simp only [Sym.eval, ↓reduceIte]
      decide
    · simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_ult64,
        NativeRustcVmArm.Vm.IvWord.b6_length, NativeRustcVmArm.Vm.IvWord.b6Length, if_not] at hpc2
      rw [Fr.x1 hfr2, UInt64.toNat_toBitVec, hx9, label_at hp b8_in_code rfl] at hpc2
      exact hpc2
  simp only [hk1, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  refine exec_at (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) two (Env.wf_nil _) hpc1
    (match_nil _) fun st2 hm2 hpc2 => ?_
  have hfr3 := fr_step hfr2 (match_nil _) hm2 (Env.wf_nil _) rfl rfl (by decide +kernel)
    (by decide +kernel)
  have hx9' : (st2.data.regs.getXReg .X9).toNat = m0.regs.X2.toNat - 1 := by
    rw [Match.reg_eq (match_nil _) hm2 (r := .X9) rfl rfl]
    exact hx9
  have hx8 : (st2.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 (m0.regs.X2.toNat - 2) := by
    rw [hm2.regs .X8 _ rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [sub64_toNat (by rw [Fr.x2 hfr2]; omega), Fr.x2 hfr2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_ult64,
    NativeRustcVmArm.Vm.IvWord.b2_length, NativeRustcVmArm.Vm.IvWord.b2Length, if_not] at hpc2
  rw [sub64_toNat (by rw [Fr.x2 hfr2]; omega), Fr.x2 hfr2, Fr.x1 hfr2] at hpc2
  by_cases h2 : m0.regs.X2.toNat - 2 < m0.regs.X1.toNat
  · -- the top byte of word `k - 2`
    simp only [h2, ↓reduceIte] at hpc2
    let env := Env.ofMachine st2.data
      [(m0.regs.X0.toBitVec + BitVec.ofNat 64 (8 * (m0.regs.X2.toNat - 2)), 8)]
    have hwf : env.WF := wf_word hfr3 hmap hnw h2
    have hm : Match env startTop st2.data :=
      match_ofMachine ⟨rfl, fun h => absurd h (by decide), trivial⟩ rfl trivial trivial trivial
        ⟨by
          show BinOp.apply .add .W64 (st2.data.regs.getXReg .X0).toBitVec
            (UnOp.apply (.shift .LSL 3) .W64 (st2.data.regs.getXReg .X8).toBitVec) =
            _ + BitVec.ofInt 64 0
          rw [hx8, lsl64, add64, Fr.x0 hfr3]
          simp only [Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some, BitVec.ofInt_ofNat, BitVec.add_zero]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
          omega, trivial⟩
    refine exec_at (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) loadTop hwf hpc2 hm
      fun st3 hm3 hpc3 => ?_
    have hfr4 := fr_step hfr3 hm hm3 hwf rfl rfl (by decide +kernel) (by decide +kernel)
    have e9 := Match.reg_eq hm hm3 (r := .X9) rfl rfl
    simp only [PcOk, SBool.eval, Sym.eval, env, Env.ofMachine_regs, cmp_ult64,
      NativeRustcVmArm.Vm.IvWord.b3_length, NativeRustcVmArm.Vm.IvWord.b3Length, decide_eq_true_eq] at hpc3
    rw [Fr.x1 hfr3, UInt64.toNat_toBitVec, hx9', label_at hp b7_in_code rfl,
      show k + NativeRustcVmArm.Vm.IvWord.b3Offset + 4 = k + NativeRustcVmArm.Vm.IvWord.b4Offset by simpa only [NativeRustcVmArm.Vm.IvWord.b3_length, NativeRustcVmArm.Vm.IvWord.b3Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.IvWord.b3_next] at hpc3
    refine jmp_run hp b4_in_code (List.cons_ne_nil _ _) jmp4 rfl rfl (by decide +kernel)
      (by decide +kernel) rfl hmap hnw hfr4 (by omega) (by rw [e9]; exact hx9')
      (fun w hw => ?_) hpc3
    apply UInt64.toBitVec_inj.mp
    rw [hm3.regs .X8 _ rfl]
    show env.load 0 7 1 = _
    rw [load_top (by
        rw [Env.ofMachine_mem0, hfr3.1, Env.base_ofMachine _ _ _ rfl]
        exact ws_word hw h2), ]
    simp only [top, show m0.regs.X2.toNat - 1 ≠ 0 by omega, ↓reduceIte]
  · -- past the bytecode: zero
    simp only [h2, ↓reduceIte] at hpc2
    rw [label_at hp b9_in_code rfl] at hpc2
    refine exec_at (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) none9 (Env.wf_nil _) hpc2
      (match_nil _) fun st3 hm3 hpc3 => ?_
    have hfr4 := fr_step hfr3 (match_nil _) hm3 (Env.wf_nil _) rfl rfl (by decide +kernel)
      (by decide +kernel)
    have e9 := Match.reg_eq (match_nil _) hm3 (r := .X9) rfl rfl
    simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_ult64,
      NativeRustcVmArm.Vm.IvWord.b9_length, NativeRustcVmArm.Vm.IvWord.b9Length, decide_eq_true_eq] at hpc3
    rw [Fr.x1 hfr3, UInt64.toNat_toBitVec, hx9', label_at hp b7_in_code rfl,
      show k + NativeRustcVmArm.Vm.IvWord.b9Offset + 4 = k + NativeRustcVmArm.Vm.IvWord.b10Offset by simpa only [NativeRustcVmArm.Vm.IvWord.b9_length, NativeRustcVmArm.Vm.IvWord.b9Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.IvWord.b9_next] at hpc3
    refine jmp_run hp b10_in_code (List.cons_ne_nil _ _) jmp10 rfl rfl (by decide +kernel)
      (by decide +kernel) rfl hmap hnw hfr4 (by omega) (by rw [e9]; exact hx9')
      (fun w hw => ?_) hpc3
    apply UInt64.toBitVec_inj.mp
    rw [hm3.regs .X8 _ rfl]
    simp only [top, show m0.regs.X2.toNat - 1 ≠ 0 by omega, ↓reduceIte]
    rw [getD_eq_zero (by rw [hw.1]; omega)]
    rfl

end

end NativeRustcVmArm.IvWordRun
