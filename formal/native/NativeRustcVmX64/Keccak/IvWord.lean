module

public import NativeRustcVmX64.Keccak.IvWord.Blocks
public import NativeRustcVmX64.Keccak.Common
public import NativeRustcVm.Keccak.Words
public import NativeRustcVm.MemLemmas
public import NativeRustcVmX64.Code.Vm.IvWord.Names

/-!
# `iv_word` meets its contract (x86-64)

`ivWord_spec`: `iv_word(bc, n, k)` returns word `k` of `ivWords` of the `n` words at `bc` in RAX
(`IvWordPost`). For `k = 0` the tag's first word (`tag`, `b5`); else RAX the top byte of word
`k - 1` of `ext` (`top`: the tag's ninth byte for `k = 1`, `first`, `b6`; the top byte of word
`k - 2` of the bytecode, `loadTop`, `b3`, or zero past it, `none9`, `b9`), then ORed with word
`k - 1` of the bytecode shifted by 8 if it is one (`loadWord`, `b7`), returned (`ret8`, `b8`).
Every block keeps memory, the callee-saved registers, RSP and the arguments (`Fr`); RCX is
`k - 1` from `b1` on.
-/

namespace NativeRustcVmX64.IvWordRun

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeVm.Model
open NativeRustcVm.Keccak (ivWord ivWord_succ getD_ivWords getD_eq_zero)
open Vm.IvWord

@[expose] public section

/-- What `iv_word` keeps from its entry `m0`: memory, the callee-saved registers, RSP and its
arguments. -/
def Fr (m0 m : MachineData) : Prop :=
  m.dmem = m0.dmem ∧ Saved m0 m ∧
    ∀ r ∈ [Reg64.rsp, .rdi, .rsi, .rdx], m.regs.get64 r = m0.regs.get64 r

/-- The top byte of word `K - 1` of `ext`: the tag's ninth for `K = 1`. -/
def top (w : List UInt64) (K : Nat) : UInt64 :=
  (if K - 1 = 0 then tagLast <<< 56 else w.getD (K - 2) 0) >>> 56

/-- The words at the entry's RDI, `n` (RSI) of them, are `w`. -/
def Ws (m0 : MachineData) (w : List UInt64) : Prop :=
  w.length = (m0.regs.get64 .rsi).toNat ∧ NativeRustcVm.WordsAt m0.dmem (m0.regs.get64 .rdi) w

/-- Before `loadWord` (`b7`): RCX is `k - 1`, a word of the bytecode, RAX `top`. -/
def At7 [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Fr m0 st.data ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.IvWord.b7Offset) ∧ 1 ≤ (m0.regs.get64 .rdx).toNat ∧
    (m0.regs.get64 .rdx).toNat - 1 < (m0.regs.get64 .rsi).toNat ∧
    ∀ w, Ws m0 w → st.data.regs.get64 .rax = (top w (m0.regs.get64 .rdx).toNat).toBitVec

/-- Before `ret8` (`b8`): RAX is the result. -/
def At8 [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Fr m0 st.data ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.IvWord.b8Offset) ∧
    ∀ w, Ws m0 w → st.data.regs.get64 .rax = (ivWord w (m0.regs.get64 .rdx).toNat).toBitVec

end

public section

theorem ivWord_top (w : List UInt64) {K : Nat} (hK : 1 ≤ K) :
    ivWord w K = top w K ||| (w.getD (K - 1) 0 <<< 8) := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
  rw [ivWord_succ, top]
  rcases j with _ | j
  · rfl
  · simp

theorem Fr.reg {m0 m : MachineData} (h : Fr m0 m) {r : Reg64}
    (hr : r ∈ [Reg64.rsp, .rdi, .rsi, .rdx]) : m.regs.get64 r = m0.regs.get64 r := h.2.2 r hr

theorem if_not {α : Type} {p : Prop} [Decidable p] (a b : α) :
    (if (!decide p) = true then a else b) = if p then b else a := by
  by_cases h : p <;> simp [h]

/-- A block without stores keeping the callee-saved registers, RSP and the arguments. -/
theorem fr_step [Labels] {env : Env} {S0 S : SState} {m0 m m' : MachineData} (hfr : Fr m0 m)
    (hm0 : Match env S0 m) (hm : Match env S m') (hwf : env.WF) (hd : m.dmem = env.mem0)
    (hmem : S.mem = []) (hk : keeps S0 S = true)
    (hr : ∀ r ∈ [Reg64.rsp, .rdi, .rsi, .rdx], S0.reg r = some (.reg r) ∧ S.reg r = some (.reg r)) :
    Fr m0 m' := by
  obtain ⟨hd0, hs0, hr0⟩ := hfr
  have hs := Match.saved hm0 hm hwf hd hk
  refine ⟨(hm.dmem_eq hwf hmem).trans (hd.symm.trans hd0),
    ⟨fun r hr' => (hs.1 r hr').trans (hs0.1 r hr'), fun p h => hs.2 p (hs0.2 p h)⟩,
    fun r hr' => (Match.reg_eq hm0 hm (hr r hr').1 (hr r hr').2).trans (hr0 r hr')⟩

theorem cmp_eq64 (x : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn]

theorem cmp_ult64 (x y : BitVec 64) : CmpOp.apply .ult .W64 x y = decide (x.toNat < y.toNat) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult]

theorem sub64_toNat {x : BitVec 64} {n : Nat} (h : n ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 n)).toNat = x.toNat - n := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  omega

theorem addm2_toNat {x : BitVec 64} (h : 2 ≤ x.toNat) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 18446744073709551614)).toNat = x.toNat - 2 := by
  have e : BitVec.ofNat 64 18446744073709551614 = -2#64 := by decide
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [e, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using h)]
  rfl

/-- A byte, loaded. -/
theorem load_one [Labels] {env : Env} {r off : Nat} {b : UInt8}
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 off) [b]) :
    env.load r off 1 = BitVec.ofNat 64 b.toNat := by
  rw [Env.load_of_bytesAt (n := 1) rfl h]
  show BitVec.ofInt 64 (0 * 256 + (b.toNat : Int)) = _
  simp

/-- The top byte of a word, loaded and zero-extended. -/
theorem load_top [Labels] {env : Env} {r : Nat} {x : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r) x) :
    UnOp.apply (.zext .W8) .W32 (env.load r 7 1) = (x >>> 56).toBitVec := by
  rw [load_one (b := (x >>> 56).toUInt8) ?_]
  · apply BitVec.eq_of_toNat_eq
    have hx := x.toNat_lt
    have e : (x >>> 56).toUInt8.toNat = (x >>> 56).toNat := by
      rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have h56 : (56 : UInt64).toNat % 64 = 56 := rfl
      rw [h56]
      omega
    have := (x >>> 56).toNat_lt
    have hlt : (x >>> 56).toNat < 256 := by
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have h56 : (56 : UInt64).toNat % 64 = 56 := rfl
      rw [h56]
      omega
    simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth, BitVec.toNat_ofNat, e,
      UInt64.toNat_toBitVec, Width.bits]
    omega
  · intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    have := h 7 (by simp [LeanVM.Protocol.KeccakHash.wordBytes])
    rw [addr_add]
    simpa [LeanVM.Protocol.KeccakHash.wordBytes] using this

/-- Word `j` of the bytecode. -/
theorem ws_word {m0 : MachineData} {w : List UInt64} (hw : Ws m0 w) {j : Nat}
    (hj : j < (m0.regs.get64 .rsi).toNat) :
    NativeRustcVm.WordAt m0.dmem (m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j)) (w.getD j 0) := by
  have := NativeRustcVm.WordsAt.getElem hw.2 (i := j) (by rw [hw.1]; exact hj)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hw.1]; exact hj),
    Option.getD_some]

/-- The region of word `j` of the bytecode. -/
theorem wf_word {m0 m : MachineData} (hfr : Fr m0 m)
    (hmap : Mapped m0.dmem (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat))
    (hnw : NoWrap (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat)) {j : Nat}
    (hj : j < (m0.regs.get64 .rsi).toNat) :
    (Env.ofMachine m [(m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j), 8)]).WF := by
  unfold NoWrap at hnw
  refine Env.wf_of ⟨⟨fun i hi => ?_, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
  · rw [addr_add, Env.ofMachine_mem0, hfr.1]
    exact hmap _ (by omega)
  · unfold NoWrap
    rw [toNat_add_ofNat _ _ (by omega)]
    omega

/-- `addrX` at the machine: the argument's word RDX, `c` words below, is region 0's base plus
`8 c`. -/
theorem addrX_eval [Labels] {m0 m : MachineData} (hfr : Fr m0 m) {j c : Nat}
    (hj : j + c = (m0.regs.get64 .rdx).toNat) :
    addrX.eval (Env.ofMachine m [(m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j), 8)]) =
      (Env.ofMachine m [(m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j), 8)]).base 0 +
        BitVec.ofInt 64 (8 * c : Nat) := by
  simp only [addrX, Sym.eval, Env.ofMachine_regs, BinOp.apply, low_W64, ext_W64,
    Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some, Option.getD_some,
    hfr.reg (r := .rdi) (by simp), hfr.reg (r := .rdx) (by simp), BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Width.bits]
  have := (m0.regs.get64 .rdx).isLt
  rw [← hj] at this ⊢
  omega

/-- The bytecode's words, read where the frame keeps memory. -/
theorem ws_word' {m0 m : MachineData} (hfr : Fr m0 m) {w : List UInt64} (hw : Ws m0 w) {j : Nat}
    (hj : j < (m0.regs.get64 .rsi).toNat) [Labels] :
    NativeRustcVm.WordAt (Env.ofMachine m [(m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j), 8)]).mem0
      ((Env.ofMachine m [(m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j), 8)]).base 0)
      (w.getD j 0) := by
  rw [Env.ofMachine_mem0, hfr.1, Env.base_ofMachine _ _ _ _ rfl]
  exact ws_word hw hj

variable [Host]

/-- The return: from `sRet` (the return address at RSP the region), back to the entry's caller
with RSP 8 above, memory and the callee-saved registers kept, RAX `v`. -/
theorem ret_at {ds : List Directive} {k : Nat} {S' : SState} (hk : ds.IsInfixAt Host.prog k)
    (hx : exec ds sRet = some (S', .ret (.load 0 0 8))) (hrsp : S'.reg .rsp = some (.ptr 0 8))
    (hmem : S'.mem = []) (hkeeps : keeps sRet S' = true) {v : Sym} (hv : S'.reg .rax = some v)
    {m0 : MachineData} {st : MachineState} (hpc : st.pc = Host.addrOf k) (hstk : StackOk m0 0)
    (hfr : Fr m0 st.data) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ st'.data.dmem = m0.dmem ∧ Saved m0 st'.data ∧
      st'.data.regs.get64 .rax = v.eval (Env.ofMachine st.data [(rspOf m0, 8)])) st := by
  obtain ⟨-, hnw, hmap⟩ := hstk
  rw [show rspOf m0 - BitVec.ofNat 64 0 = rspOf m0 from BitVec.sub_zero _] at hmap
  have hsp : st.data.regs.get64 .rsp = rspOf m0 := hfr.reg (by simp)
  let env := Env.ofMachine st.data [(rspOf m0, 8)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun i hi => by
        show (st.data.dmem.get? (rspOf m0 + _)).isSome = true
        rw [hfr.1]
        exact hmap i (by omega), by unfold NoWrap; exact hnw⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env sRet st.data := match_ofMachine ⟨rfl, trivial⟩
    ⟨show st.data.regs.get64 .rsp = (Sym.ptr 0 0).eval env by
      simp [Sym.eval, env, hsp], trivial⟩ trivial trivial trivial
  have hread := hm.read hwf (r := 0) (o := 0) (n := 8) rfl (by decide) (by decide)
  refine exec_at hk hx hwf (fun _ h => nomatch h) hpc hm fun st' hm' hpc' =>
    .done _ ⟨?_, ?_, ?_, ?_, hm'.regs .rax v hv⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    have hb : env.base 0 + BitVec.ofNat 64 0 = rspOf m0 := by simp [env]
    rw [hb, show st.data.dmem = m0.dmem from hfr.1] at hread
    exact (retOf_of_loadInt hread).symm
  · have h := hm'.regs .rsp _ hrsp
    simp only [Sym.eval, env, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some] at h
    exact h
  · exact (hm'.dmem_eq hwf hmem).trans hfr.1
  · have hs := Match.saved hm hm' hwf rfl hkeeps
    exact ⟨fun r hr => (hs.1 r hr).trans (hfr.2.1.1 r hr), fun p h => hs.2 p (hfr.2.1.2 p h)⟩

/-- The final return: RAX the result. -/
theorem ret_run {k : Nat} (hp : Placed code k) {m0 : MachineData} (hstk : StackOk m0 0)
    {st : MachineState} (h : At8 m0 k st) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ IvWordPost m0 st'.data) st := by
  obtain ⟨hfr, hpc, hv⟩ := h
  refine Eventually.mono (ret_at (b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) ret8 rfl rfl
    (by decide +kernel) rfl hpc hstk hfr) fun st' ⟨hpc', hrsp', hd', hs', hrax⟩ =>
      ⟨hpc', hrsp', fun w hlen hw => ?_, hd', hs'⟩
  show st'.data.regs.get64 .rax = _
  rw [hrax]
  show st.data.regs.get64 .rax = _
  rw [hv w ⟨hlen, hw⟩, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← List.getD_eq_getElem?_getD, getD_ivWords]

/-- `loadWord`: word `k - 1` ORed in. -/
theorem word_run {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (hmap : Mapped m0.dmem (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat))
    (hnw : NoWrap (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat)) {st : MachineState}
    (h : At7 m0 k st) : Eventually (step1 Host.exe) (At8 m0 k) st := by
  obtain ⟨hfr, hpc, hK, hlt, hv⟩ := h
  let j := (m0.regs.get64 .rdx).toNat - 1
  let env := Env.ofMachine st.data [(m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j), 8)]
  have hwf : env.WF := wf_word hfr hmap hnw hlt
  have hm : Match env startWord st.data :=
    match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
      ⟨addrX_eval hfr (j := j) (c := 1) (by omega), trivial⟩
  refine exec_at (b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) loadWord hwf nofun hpc hm
    fun st' hm' hpc' => .done _ ⟨?_, ?_, fun w hw => ?_⟩
  · exact fr_step hfr hm hm' hwf rfl rfl (by decide +kernel) (by decide +kernel)
  · simp only [PcOk] at hpc'
    exact hpc'
  · show st'.data.regs.get64 .rax = _
    rw [hm'.regs .rax _ rfl]
    simp only [Sym.eval, env, Env.ofMachine_regs, BinOp.apply, low_W64, ext_W64]
    rw [Keccak.load_wordAt (by
        rw [show ∀ b : BitVec 64, b + BitVec.ofNat 64 0 = b from fun b => BitVec.add_zero b]
        exact ws_word' hfr hw hlt),
      hv w hw, ivWord_top w hK, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft]
    rfl

/-- From RAX `top` and RCX `k - 1`: `loadWord` if word `k - 1` is in the bytecode, and the
return. -/
theorem top_run {k : Nat} (hp : Placed code k) {m0 : MachineData} (hstk : StackOk m0 0)
    (hmap : Mapped m0.dmem (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat))
    (hnw : NoWrap (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat)) {st : MachineState}
    (hfr : Fr m0 st.data) (hK : 1 ≤ (m0.regs.get64 .rdx).toNat)
    (hv : ∀ w, Ws m0 w → st.data.regs.get64 .rax = (top w (m0.regs.get64 .rdx).toNat).toBitVec)
    (hpc : st.pc = if (m0.regs.get64 .rdx).toNat - 1 < (m0.regs.get64 .rsi).toNat then
      Host.addrOf (k + NativeRustcVmX64.Vm.IvWord.b7Offset) else Host.addrOf (k + NativeRustcVmX64.Vm.IvWord.b8Offset)) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ IvWordPost m0 st'.data) st := by
  by_cases h : (m0.regs.get64 .rdx).toNat - 1 < (m0.regs.get64 .rsi).toNat
  · simp only [h, ↓reduceIte] at hpc
    exact Eventually.bind (word_run hp hmap hnw ⟨hfr, hpc, hK, h, hv⟩) fun _ h8 =>
      ret_run hp hstk h8
  · simp only [h, ↓reduceIte] at hpc
    refine ret_run hp hstk ⟨hfr, hpc, fun w hw => ?_⟩
    rw [hv w hw, ivWord_top w hK, getD_eq_zero (by rw [hw.1]; omega)]
    simp

/-- `top_run` through a jump to the return (`jmp4`, `jmp10`). -/
theorem jmp_run {k e : Nat} (hp : Placed code k) {b : List Directive} (hb : b.IsInfixAt code e)
    (hne : b ≠ []) {S : SState} (hx : exec b start = some (S, .jump NativeRustcVmX64.Vm.IvWord.label_9))
    (hrax : S.reg .rax = some (.reg .rax)) (hk : keeps start S = true)
    (hr : ∀ r ∈ [Reg64.rsp, .rdi, .rsi, .rdx],
      start.reg r = some (.reg r) ∧ S.reg r = some (.reg r)) (hmem : S.mem = [])
    {m0 : MachineData} (hstk : StackOk m0 0)
    (hmap : Mapped m0.dmem (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat))
    (hnw : NoWrap (m0.regs.get64 .rdi) (8 * (m0.regs.get64 .rsi).toNat)) {st : MachineState}
    (hfr : Fr m0 st.data) (hK : 1 ≤ (m0.regs.get64 .rdx).toNat)
    (hv : ∀ w, Ws m0 w → st.data.regs.get64 .rax = (top w (m0.regs.get64 .rdx).toNat).toBitVec)
    (hpc : st.pc = if (m0.regs.get64 .rdx).toNat - 1 < (m0.regs.get64 .rsi).toNat then
      Host.addrOf (k + NativeRustcVmX64.Vm.IvWord.b7Offset) else Host.addrOf (k + e)) :
    Eventually (step1 Host.exe) (fun st' => st'.pc = retOf m0 ∧
      rspOf st'.data = rspOf m0 + 8#64 ∧ IvWordPost m0 st'.data) st := by
  by_cases h : (m0.regs.get64 .rdx).toNat - 1 < (m0.regs.get64 .rsi).toNat
  · exact top_run hp hstk hmap hnw hfr hK hv (by simp only [h, ↓reduceIte] at hpc ⊢; exact hpc)
  · simp only [h, ↓reduceIte] at hpc
    refine exec_at (hb.trans hp.1 hne) hx (Env.wf_nil _) nofun hpc (match_nil _)
      fun st' hm hpc' => ?_
    have e0 := Match.reg_eq (match_nil _) hm rfl hrax
    refine top_run hp hstk hmap hnw (fr_step hfr (match_nil _) hm (Env.wf_nil _) rfl hmem hk hr)
      hK (fun w hw => by rw [e0]; exact hv w hw) ?_
    simp only [h, ↓reduceIte, PcOk] at hpc' ⊢
    rw [hpc']
    exact hp.label NativeRustcVmX64.Vm.IvWord.label_9_at

/-- **`iv_word` meets its contract.** -/
theorem ivWord_spec {k : Nat} (hp : Placed Vm.IvWord.code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.IvWord.entryLabel) IvWordPre IvWordPost := by
  intro m0 hpre
  obtain ⟨hstk, hmap, hnw⟩ := hpre
  rw [show Labels.label NativeRustcVmX64.Vm.IvWord.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.IvWord.b0Offset) from hp.label NativeRustcVmX64.Vm.IvWord.entry_at]
  have hfr0 : Fr m0 m0 := ⟨rfl, ⟨fun _ _ => rfl, fun _ h => h⟩, fun _ _ => rfl⟩
  have hKlt := (m0.regs.get64 .rdx).isLt
  refine exec_then (b0_in_code.trans hp.1 (List.cons_ne_nil _ _)) zero (Env.wf_nil m0) nofun
    (match_nil m0) fun st0 hm0 hpc0 => ?_
  have hfr1 := fr_step hfr0 (match_nil m0) hm0 (Env.wf_nil m0) rfl rfl (by decide +kernel)
    (by decide +kernel)
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, BinOp.apply, low_W64, ext_W64,
    BitVec.and_self, cmp_eq64 _ 0 (by decide), NativeRustcVmX64.Vm.IvWord.b0_length] at hpc0
  by_cases hk0 : (m0.regs.get64 .rdx).toNat = 0
  · -- `k = 0`: the tag's first word
    simp only [show (m0.regs.get64 .rdx).toNat = 0 from hk0, decide_true, ↓reduceIte] at hpc0
    rw [hp.label NativeRustcVmX64.Vm.IvWord.label_1_at] at hpc0
    refine Eventually.mono (ret_at (b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) tag rfl rfl
      (by decide +kernel) rfl hpc0 hstk hfr1) fun st' ⟨hpc', hrsp', hd', hs', hrax⟩ =>
        ⟨hpc', hrsp', fun w _ _ => ?_, hd', hs'⟩
    show st'.data.regs.get64 .rax = _
    rw [hrax, hk0, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
      ← List.getD_eq_getElem?_getD, getD_ivWords]
    rfl
  simp only [show ¬ (m0.regs.get64 .rdx).toNat = 0 from hk0, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hpc0
  refine exec_at (b1_in_code.trans hp.1 (List.cons_ne_nil _ _)) one (Env.wf_nil _) nofun hpc0
    (match_nil _) fun st1 hm1 hpc1 => ?_
  have hfr2 := fr_step hfr1 (match_nil _) hm1 (Env.wf_nil _) rfl rfl (by decide +kernel)
    (by decide +kernel)
  have hrdx1 : st0.data.regs.get64 .rdx = m0.regs.get64 .rdx := hfr1.reg (by simp)
  have hrsi1 : st0.data.regs.get64 .rsi = m0.regs.get64 .rsi := hfr1.reg (by simp)
  have hrcx : (st1.data.regs.get64 .rcx).toNat = (m0.regs.get64 .rdx).toNat - 1 := by
    rw [hm1.regs .rcx _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [sub64_toNat (by rw [hrdx1]; omega), hrdx1]
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_eq64 _ 0 (by decide),
    NativeRustcVmX64.Vm.IvWord.b1_length] at hpc1
  rw [sub64_toNat (by rw [hrdx1]; omega), hrdx1] at hpc1
  by_cases hk1 : (m0.regs.get64 .rdx).toNat = 1
  · -- `k = 1`: the tag's ninth byte
    simp only [show (m0.regs.get64 .rdx).toNat - 1 = 0 by omega, decide_true,
      ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.IvWord.label_3_at] at hpc1
    refine exec_at (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) first (Env.wf_nil _) nofun hpc1
      (match_nil _) fun st2 hm2 hpc2 => ?_
    have hfr3 := fr_step hfr2 (match_nil _) hm2 (Env.wf_nil _) rfl rfl (by decide +kernel)
      (by decide +kernel)
    refine top_run hp hstk hmap hnw hfr3 (by omega) (fun w _ => ?_) ?_
    · show st2.data.regs.get64 .rax = _
      rw [hm2.regs .rax _ rfl, top, hk1]
      simp only [Sym.eval, Nat.sub_self, ↓reduceIte]
      decide
    · simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_ult64,
        NativeRustcVmX64.Vm.IvWord.b6_length, if_not] at hpc2
      rw [hrcx, hfr2.reg (r := .rsi) (by simp), hp.label NativeRustcVmX64.Vm.IvWord.label_9_at] at hpc2
      exact hpc2
  simp only [show ¬ (m0.regs.get64 .rdx).toNat - 1 = 0 by omega,
    decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  refine exec_at (b2_in_code.trans hp.1 (List.cons_ne_nil _ _)) two (Env.wf_nil _) nofun hpc1
    (match_nil _) fun st2 hm2 hpc2 => ?_
  have hfr3 := fr_step hfr2 (match_nil _) hm2 (Env.wf_nil _) rfl rfl (by decide +kernel)
    (by decide +kernel)
  have hrcx2 : (st2.data.regs.get64 .rcx).toNat = (m0.regs.get64 .rdx).toNat - 1 := by
    rw [Match.reg_eq (match_nil _) hm2 (r := .rcx) rfl rfl]
    exact hrcx
  have hrdx2 : st1.data.regs.get64 .rdx = m0.regs.get64 .rdx := hfr2.reg (by simp)
  have hrsi2 : st1.data.regs.get64 .rsi = m0.regs.get64 .rsi := hfr2.reg (by simp)
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_ult64,
    NativeRustcVmX64.Vm.IvWord.b2_length, if_not] at hpc2
  rw [addm2_toNat (by rw [hrdx2]; omega), hrdx2, hrsi2] at hpc2
  by_cases h2 : (m0.regs.get64 .rdx).toNat - 2 < (m0.regs.get64 .rsi).toNat
  · -- the top byte of word `k - 2`
    simp only [show (m0.regs.get64 .rdx).toNat - 2 < (m0.regs.get64 .rsi).toNat from h2,
      ↓reduceIte] at hpc2
    let j := (m0.regs.get64 .rdx).toNat - 2
    let env := Env.ofMachine st2.data [(m0.regs.get64 .rdi + BitVec.ofNat 64 (8 * j), 8)]
    have hwf : env.WF := wf_word hfr3 hmap hnw h2
    have hm : Match env startTop st2.data :=
      match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial
        ⟨addrX_eval hfr3 (j := j) (c := 2) (by omega), trivial⟩
    refine exec_at (b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) loadTop hwf nofun hpc2 hm
      fun st3 hm3 hpc3 => ?_
    have hfr4 := fr_step hfr3 hm hm3 hwf rfl rfl (by decide +kernel) (by decide +kernel)
    have e1 := Match.reg_eq hm hm3 (r := .rcx) rfl rfl
    simp only [PcOk, SBool.eval, Sym.eval, env, Env.ofMachine_regs, cmp_ult64,
      decide_eq_true_eq] at hpc3
    rw [hrcx2, hfr3.reg (r := .rsi) (by simp), hp.label NativeRustcVmX64.Vm.IvWord.label_8_at,
      show k + NativeRustcVmX64.Vm.IvWord.b3Offset + b3.length = k + NativeRustcVmX64.Vm.IvWord.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.IvWord.b3_next]] at hpc3
    refine jmp_run hp b4_in_code (List.cons_ne_nil _ _) jmp4 rfl (by decide +kernel)
      (by decide +kernel) rfl hstk hmap hnw hfr4 (by omega) (fun w hw => ?_) hpc3
    show st3.data.regs.get64 .rax = _
    rw [hm3.regs .rax _ rfl]
    show UnOp.apply (.zext .W8) .W32 (env.load 0 7 1) = _
    rw [load_top (ws_word' hfr3 hw h2)]
    simp only [top, show (m0.regs.get64 .rdx).toNat - 1 ≠ 0 by omega, ↓reduceIte]
  · -- past the bytecode: zero
    simp only [show ¬ (m0.regs.get64 .rdx).toNat - 2 < (m0.regs.get64 .rsi).toNat from h2,
      ↓reduceIte] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.IvWord.label_5_at] at hpc2
    refine exec_at (b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) none9 (Env.wf_nil _) nofun
      hpc2 (match_nil _) fun st3 hm3 hpc3 => ?_
    have hfr4 := fr_step hfr3 (match_nil _) hm3 (Env.wf_nil _) rfl rfl (by decide +kernel)
      (by decide +kernel)
    simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_ult64,
      decide_eq_true_eq] at hpc3
    rw [hrcx2, hfr3.reg (r := .rsi) (by simp), hp.label NativeRustcVmX64.Vm.IvWord.label_8_at,
      show k + NativeRustcVmX64.Vm.IvWord.b9Offset + b9.length = k + NativeRustcVmX64.Vm.IvWord.b10Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.IvWord.b9_next]] at hpc3
    refine jmp_run hp b10_in_code (List.cons_ne_nil _ _) jmp10 rfl (by decide +kernel)
      (by decide +kernel) rfl hstk hmap hnw hfr4 (by omega) (fun w hw => ?_) hpc3
    show st3.data.regs.get64 .rax = _
    rw [hm3.regs .rax _ rfl]
    simp only [top, show (m0.regs.get64 .rdx).toNat - 1 ≠ 0 by omega, ↓reduceIte]
    rw [getD_eq_zero (by rw [hw.1]; omega)]
    rfl

end

end NativeRustcVmX64.IvWordRun
