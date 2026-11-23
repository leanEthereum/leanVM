module

public import NativeRustcVmX64.Layout.StackPoint.Exec
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.SelectorPoint.Names
public import NativeRustcVmX64.Code.Vm.StackPoint.Names

/-!
# `stack_point` on x86-64

**`stackPoint_spec`**: rustc's `stack_point(p, point, stack_log, out)`, placed anywhere in the
program, meets `StackPointPre`/`StackPointPost` (`NativeRustcVmX64.Spec.Ring`) given
`selector_point`'s contract. The prologue (`b0`) pushes R15, R14, R12, RBX, RAX, computes
`n = |point| + (stack_log - vc)` and returns RAX = `0` past `66` (`b10`). Else `b1` keeps
`out + 16|point|` in RAX, and the point is copied into `out` (`Copy`): two elements a turn (`b4`, the
loop `b5`, `Pair`), then the odd one (`b7`); `b8` calls `selector_point(index >> vc,
out + 16|point|, tail)`, and `b9`, `b10` return RAX = `1`, RDX = `n`.
-/

namespace NativeRustcVmX64.Layout.StackPoint

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.StackPoint NativeVm.Model
open NativeRustcVmX64.Field (frameEnv frame_wf match_frame midS)
open NativeRustcVmX64.Arrays (Body after after_eq exec_after freeRegs keepsAll keepsRegs restores
  pc_cond stackOk_mono regs_eq_of elem_of_apart)
open NativeRustcVmX64.Transcript (infix_of infix_take infix_drop)
open NativeRustcVm (ewsOf ewOf EWsAt EWAt)

public section

/-- The stack. -/
abbrev S : Nat := stackPointStack
/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := reg m .r9
/-- `out`'s bytes. -/
abbrev outB : Nat := 16 * stackPointOut
/-- The point. -/
abbrev pt (m : MachineData) : BitVec 64 := reg m .rdx
/-- Its length. -/
abbrev len (m : MachineData) : Nat := (reg m .rcx).toNat
/-- Its elements. -/
abbrev ptl (m : MachineData) : List EW := ewsOf m.dmem (pt m) (len m)
/-- The selector's length. -/
abbrev tl (m : MachineData) : Nat := (reg m .r8).toNat - (reg m .rdi).toNat
/-- The stack point's length. -/
abbrev nn (m : MachineData) : Nat := len m + tl m
/-- The pairs' part of the point. -/
abbrev E (m : MachineData) : Nat := len m / 2 * 2

theorem S_eq : S = 64 := rfl

/-- The facts of the precondition the blocks use. -/
structure Facts (m0 : MachineData) : Prop where
  stack : StackOk m0 S
  pr : Readable m0 (pt m0) (16 * len m0)
  po : OffStack m0 (pt m0) (16 * len m0) S
  or : Readable m0 (out m0) outB
  oo : OffStack m0 (out m0) outB S
  apart : Apart (out m0) outB (pt m0) (16 * len m0)
  len64 : len m0 < 64

theorem Facts.of_pre {m0 : MachineData} (h : StackPointPre m0) : Facts m0 :=
  ⟨h.1, h.2.1.1, h.2.1.2, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem Facts.onw {m0 : MachineData} (hF : Facts m0) : (out m0).toNat + 1056 ≤ 2 ^ 64 := hF.or.2
theorem Facts.pnw {m0 : MachineData} (hF : Facts m0) : (pt m0).toNat + 16 * len m0 ≤ 2 ^ 64 :=
  hF.pr.2

/-- The registers the body keeps. -/
structure Regs (m0 st : MachineData) : Prop where
  rcx : reg st .rcx = reg m0 .rcx
  rdx : reg st .rdx = reg m0 .rdx
  rsi : reg st .rsi = reg m0 .rsi
  rdi : reg st .rdi = reg m0 .rdi
  r8 : reg st .r8 = BitVec.ofNat 64 (tl m0)
  r9 : reg st .r9 = reg m0 .r9
  rbx : reg st .rbx = BitVec.ofNat 64 (nn m0)

theorem Regs.of {m0 st st' : MachineData} (h : Regs m0 st)
    (he : ∀ r ∈ keepB, reg st' r = reg st r) : Regs m0 st' :=
  ⟨(he .rcx (by simp [keepB])).trans h.rcx, (he .rdx (by simp [keepB])).trans h.rdx,
    (he .rsi (by simp [keepB])).trans h.rsi, (he .rdi (by simp [keepB])).trans h.rdi,
    (he .r8 (by simp [keepB])).trans h.r8, (he .r9 (by simp [keepB])).trans h.r9,
    (he .rbx (by simp [keepB])).trans h.rbx⟩

/-- **`i` elements of the point copied** into `out`. -/
structure Copy (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  body : Body m0 48 S slots (out m0) outB st
  regs : Regs m0 st
  rax : reg st .rax = out m0 + BitVec.ofNat 64 (16 * len m0)
  le : i ≤ len m0
  copied : EWsAt st.dmem (out m0) ((ptl m0).take i)

/-- A block keeping the copy's registers, writing nothing, keeps the copy. -/
theorem Copy.of_block [Labels] {m0 st st' : MachineData} {i : Nat} {env : Env} {S₀ S₁ : SState}
    (hc : Copy m0 i st) (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF)
    (hd : st.dmem = env.mem0) (hk : keepsAll S₀ S₁ (freeRegs slots) = true)
    (hkc : keepsRegs S₀ S₁ keepC = true) : Copy m0 i st' := by
  have e := regs_eq_of hm₀ hm hkc
  have hdm : st'.dmem = st.dmem := (hm.dmem_eq hwf (mem_of_keepsAll hk)).trans hd.symm
  exact ⟨hc.body.of_block hm₀ hm hwf hd hk, hc.regs.of fun r hr ↦ e r (by
      simp only [keepC, List.mem_append]; exact Or.inl hr),
    (e .rax (by simp [keepC])).trans hc.rax, hc.le, by rw [hdm]; exact hc.copied⟩

/-- Element `i` of the point, read in a body. -/
theorem Facts.elem {m0 st : MachineData} (hF : Facts m0)
    (hb : Body m0 48 S slots (out m0) outB st) {i : Nat} (hi : i < len m0) :
    ewOf st.dmem (pt m0 + BitVec.ofNat 64 (16 * i)) = (ptl m0)[i]'(by simp; exact hi) := by
  rw [elem_of_apart hb.same hF.stack hF.pr.2 hF.po (Arrays.apart_symm hF.apart) hF.or.2 hi]

/-- The copy extended by one element. -/
theorem copied_succ {d : Mem 64} {a : BitVec 64} {xs : List EW} {i : Nat} (hi : i < xs.length)
    (h : EWsAt d a (xs.take i)) (he : EWAt d (a + BitVec.ofNat 64 (16 * i)) xs[i]) :
    EWsAt d a (xs.take (i + 1)) := by
  rw [List.take_succ_eq_append_getElem hi, NativeRustcVm.ewsAt_append_iff,
    NativeRustcVm.ewsAt_singleton_iff, List.length_take, Nat.min_eq_left (by omega)]
  exact ⟨h, he⟩

/-- An element, copied by a block from region `2` to region `1` at offset `o`. -/
theorem copy_el [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {o : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[1]? = some (b, sz)) (hle : o + 16 ≤ sz)
    (h0 : ∀ i < 8, findWrite 1 (o + i) S.mem = some (.load 2 o 8, i))
    (h1 : ∀ i < 8, findWrite 1 (o + 8 + i) S.mem = some (.load 2 (o + 8) 8, i)) :
    EWAt m.dmem (b + BitVec.ofNat 64 o) (ewOf env.mem0 (env.base 2 + BitVec.ofNat 64 o)) := by
  have := Arrays.ewAt_of_writes hm hb hle h0 h1
  rw [Arrays.eval_load, Arrays.eval_load] at this
  rw [Arrays.ewOf_loads]
  exact this

/-- Bytes of `out` below `16 i` stay, when the writes are in `out` from `16 i`. -/
theorem copied_keep {d d' : Mem 64} {a : BitVec 64} {xs : List EW} {i L : Nat}
    (ha : a.toNat + 16 * i + L ≤ 2 ^ 64) (hL : 0 < L) (h : EWsAt d a (xs.take i))
    (hs : ∀ q, ¬InRange (a + BitVec.ofNat 64 (16 * i)) L q → d'.get? q = d.get? q) :
    EWsAt d' a (xs.take i) :=
  Arrays.ewsAt_congr h fun j hj ↦ hs _ fun hin ↦ by
    have hj' : j < 16 * i := by
      have := List.length_take_le i xs
      omega
    rw [Sym.inRange_iff (by rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega),
      NativeRustcVm.toNat_add_ofNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega)] at hin
    omega

/-- The environment of a block copying `l` bytes at `16 i` from the point to `out`. -/
theorem Facts.wf3 {m0 st : MachineData} (hF : Facts m0) (hk : Kept m0.dmem st.dmem) {i l : Nat}
    (hil : 16 * i + l ≤ 16 * len m0) (hl : 0 < l) :
    (Env.ofMachine st [(stackBelow m0 48, 48 + 8), (out m0 + BitVec.ofNat 64 (16 * i), l),
      (pt m0 + BitVec.ofNat 64 (16 * i), l)]).WF := by
  have hlen := hF.len64
  have hon := hF.onw
  have hpn := hF.pnw
  have hS1 := hF.stack.1
  have hS2 := hF.stack.2.1
  have hoo := hF.oo
  have hpo := hF.po
  have hap := hF.apart
  have hoB : outB = 1056 := rfl
  unfold OffStack NativeRustcX64.Apart at hoo hpo
  unfold NativeRustcX64.Apart at hap
  rw [hoB] at hoo hap
  rw [Arrays.stackBelow_toNat hS1] at hoo hpo
  simp only [S, stackPointStack, selectorPointStack, Nat.reduceAdd] at hoo hpo hS1 hS2
  have hfb := Arrays.stackBelow_toNat (m := m0) (n := 48) (by omega)
  have e1 := NativeRustcVm.toNat_add_ofNat (a := out m0) (i := 16 * i) (by omega)
  have e2 := NativeRustcVm.toNat_add_ofNat (a := pt m0) (i := 16 * i) (by omega)
  refine Env.wf_of ⟨⟨fun j hj ↦ hk _ (Transcript.frame_mapped hF.stack (by decide) j hj),
      Transcript.frame_noWrap hF.stack (by decide)⟩,
    ⟨fun j hj ↦ by rw [NativeRustcVm.addr_add_add]; exact hk _ (hF.or.1 _ (by rw [hoB]; omega)),
      show (out m0 + BitVec.ofNat 64 (16 * i)).toNat + l ≤ 2 ^ 64 by rw [e1]; omega⟩,
    ⟨fun j hj ↦ by rw [NativeRustcVm.addr_add_add]; exact hk _ (hF.pr.1 _ (by omega)),
      show (pt m0 + BitVec.ofNat 64 (16 * i)).toNat + l ≤ 2 ^ 64 by rw [e2]; omega⟩, trivial⟩
    (Transcript.pairwise3 ?_ ?_ ?_)
  · show NativeRustcX64.Apart (stackBelow m0 48) (48 + 8) (out m0 + BitVec.ofNat 64 (16 * i)) l
    unfold NativeRustcX64.Apart; rw [hfb, e1]; omega
  · show NativeRustcX64.Apart (stackBelow m0 48) (48 + 8) (pt m0 + BitVec.ofNat 64 (16 * i)) l
    unfold NativeRustcX64.Apart; rw [hfb, e2]; omega
  · show NativeRustcX64.Apart (out m0 + BitVec.ofNat 64 (16 * i)) l
      (pt m0 + BitVec.ofNat 64 (16 * i)) l
    unfold NativeRustcX64.Apart; rw [e1, e2]; omega

/-- **The pair loop's head** `.L5`: `i` elements copied. -/
structure Pair (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  copy : Copy m0 i st
  lt : i + 2 ≤ E m0
  r10 : reg st .r10 = BitVec.ofNat 64 i
  r11 : reg st .r11 = BitVec.ofNat 64 (E m0)
  r14 : reg st .r14 = BitVec.ofNat 64 (16 * i + 24)
  even : i % 2 = 0

/-- **At `.L8`**: the point copied, the selector's arguments in place. -/
structure Ready (m0 : MachineData) (st : MachineData) : Prop where
  body : Body m0 48 S slots (out m0) outB st
  rsi : reg st .rsi = reg m0 .rsi
  rdi : reg st .rdi = reg m0 .rdi
  r8 : reg st .r8 = BitVec.ofNat 64 (tl m0)
  rbx : reg st .rbx = BitVec.ofNat 64 (nn m0)
  rax : reg st .rax = out m0 + BitVec.ofNat 64 (16 * len m0)
  copied : EWsAt st.dmem (out m0) (ptl m0)
  fit : nn m0 ≤ 66

theorem Copy.ready {m0 st : MachineData} (hc : Copy m0 (len m0) st) (hfit : nn m0 ≤ 66) :
    Ready m0 st :=
  ⟨hc.body, hc.regs.rsi, hc.regs.rdi, hc.regs.r8, hc.regs.rbx, hc.rax, by
    have := hc.copied
    rwa [List.take_of_length_le (by simp)] at this, hfit⟩

theorem E_le (m0 : MachineData) : E m0 ≤ len m0 := Nat.div_mul_le_self _ _

/-- `b0`'s byte test: neither flag set. -/
theorem merge_bits (r1 r2 : BitVec 64) (p q : Bool) :
    CmpOp.apply .eq .W8 (BinOp.apply .or .W8
      (BinOp.apply .merge .W8 r1 (if p = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0))
      (BinOp.apply .merge .W8 r2 (if q = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)))
      (BitVec.ofNat 64 0) = (!p && !q) := by
  cases p <;> cases q <;> simp only [CmpOp.apply, BinOp.apply, Transcript.low8_replaceLow,
    Bool.false_eq_true, ↓reduceIte] <;> decide

/-- `b0`'s tail length. -/
theorem tlS_toNat [Labels] (env : Env) :
    (tlS.eval env).toNat = (env.regs .r8).toNat - (env.regs .rdi).toNat := by
  simp only [tlS, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  split
  · rename_i h
    simp only [BitVec.ult, decide_eq_true_eq] at h
    rw [BitVec.toNat_ofNat]
    omega
  · rename_i h
    simp only [BitVec.ult, decide_eq_true_eq] at h
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]

/-- `b0`'s length, modulo `2^64`. -/
theorem nS_toNat [Labels] (env : Env) : (nS.eval env).toNat =
    ((env.regs .r8).toNat - (env.regs .rdi).toNat + (env.regs .rcx).toNat) % 2 ^ 64 := by
  show (BinOp.apply .add .W64 (tlS.eval env) (env.regs .rcx)).toNat = _
  rw [Arrays.add_eval, BitVec.toNat_add, tlS_toNat]

/-- `b0`'s check: the stack point's length is at most `66` (for a point below `64`). -/
theorem okS_eval [Labels] (env : Env) (hl : (env.regs .rcx).toNat < 64) :
    okS.eval env = decide ((env.regs .rcx).toNat +
      ((env.regs .r8).toNat - (env.regs .rdi).toNat) ≤ 66) := by
  have hN := nS_toNat env
  simp only [okS, SBool.eval]
  refine (merge_bits _ _ _ _).trans ?_
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, BitVec.ult, hN, BitVec.toNat_ofNat]
  have ha := (env.regs .r8).isLt
  by_cases hw : (env.regs .r8).toNat - (env.regs .rdi).toNat + (env.regs .rcx).toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hw]
    by_cases h66 : (env.regs .rcx).toNat + ((env.regs .r8).toNat - (env.regs .rdi).toNat) ≤ 66
    · simp [h66]; omega
    · simp [h66]; omega
  · have h66 : ¬(env.regs .rcx).toNat + ((env.regs .r8).toNat - (env.regs .rdi).toNat) ≤ 66 := by
      omega
    simp [h66]
    omega

/-- `b1`'s test: `len = 0`. -/
theorem zero_eval [Labels] (env : Env) {n : Nat} (hx : (env.regs .rcx).toNat = n) :
    SBool.eval env (.cmp .eq .W64 (.bin .and .W64 (.reg .rcx) (.reg .rcx)) (.lit 0)) =
      decide (n = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  by_cases h : n = 0
  · have : env.regs .rcx = BitVec.ofNat 64 0 := BitVec.eq_of_toNat_eq (by simp [hx, h])
    simp [this, h]
  · have : env.regs .rcx ≠ BitVec.ofNat 64 0 := fun h' ↦ h (by rw [← hx, h']; rfl)
    simp [this, h]

/-- `b6`'s test: `len` even. -/
theorem even_eval [Labels] (env : Env) {n : Nat} (hx : (env.regs .rcx).toNat = n) :
    SBool.eval env (.cmp .eq .W8 (.bin .and .W8 (.reg .rcx) (.lit 1)) (.lit 0)) =
      decide (n % 2 = 0) := by
  have hl : low .W8 (BinOp.apply .and .W8 (env.regs .rcx) (BitVec.ofNat 64 1)) =
      BitVec.ofNat 8 (n % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BinOp.apply, toNat_low, toNat_ext, BitVec.toNat_and, BitVec.toNat_ofNat,
      show Width.W8.bits = 8 from rfl, Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod, hx]
    omega
  show (low .W8 (BinOp.apply .and .W8 (env.regs .rcx) (BitVec.ofNat 64 1)) ==
    low .W8 (BitVec.ofNat 64 0)) = _
  rw [hl]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

theorem and62 : ∀ x : Fin 64, x.val &&& 62 = x.val / 2 * 2 := by decide

/-- `b4`'s pair bound: `len & 62` is `E`. -/
theorem r11_eval (x : BitVec 64) (h : x.toNat < 64) :
    BinOp.apply .and .W32 (UnOp.apply .trunc .W32 x) (BitVec.ofNat 64 62) =
      BitVec.ofNat 64 (x.toNat / 2 * 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, UnOp.apply, toNat_ext, BitVec.toNat_and, toNat_low, BitVec.toNat_ofNat,
    show Width.W32.bits = 32 from rfl]
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by decide : 62 < 2 ^ 32), Nat.mod_eq_of_lt (by omega)]
  have := and62 ⟨x.toNat, h⟩
  simp only at this
  rw [this]

/-- The selector's index: `index >> vc`, `0` from `vc = 64`. -/
theorem sel_eval (i v : BitVec 64) :
    (if CmpOp.apply .ult .W64 v (BitVec.ofNat 64 64) = true then
      BinOp.apply .shr .W64 i (UnOp.apply .trunc .W32 v) else BitVec.ofNat 64 0).toNat =
      i.toNat >>> v.toNat := by
  split
  · rename_i h
    simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq,
      show Width.W64.bits = 64 from rfl, Nat.reducePow, Nat.reduceMod] at h
    have hc : shiftCount .W64 (UnOp.apply .trunc .W32 v) = v.toNat := by
      unfold shiftCount shiftMask
      simp only [UnOp.apply, toNat_low, toNat_ext]
      rw [show Width.W8.bits = 8 from rfl, show Width.W32.bits = 32 from rfl,
        Nat.mod_eq_of_lt (show v.toNat < 2 ^ 32 by omega), Nat.mod_eq_of_lt (by omega)]
      exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)
    simp only [BinOp.apply, hc, low_W64, ext_W64]
    exact BitVec.toNat_ushiftRight i _
  · rename_i h
    simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq,
      show Width.W64.bits = 64 from rfl, Nat.reducePow, Nat.reduceMod] at h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    rw [Nat.shiftRight_eq_div_pow]
    have := i.isLt
    have : 2 ^ 64 ≤ 2 ^ v.toNat := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.div_eq_of_lt (by omega)).symm

variable [Host] {k : Nat}

/-- **A turn of the pair loop** `b5`: `point[i]`, `point[i + 1]` copied. -/
theorem stepPair (hp : Placed code k) {m0 : MachineData} (hF : Facts m0)
    {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b5Offset)) (hI : Pair m0 i st.data) :
    Eventually (step1 Host.exe) (fun s ↦ (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b6Offset) ∧ Copy m0 (E m0) s.data ∧
        reg s.data .r10 = BitVec.ofNat 64 (E m0)) ∨
      (s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b5Offset) ∧ Pair m0 (i + 2) s.data)) st := by
  have hlt := hI.lt
  have hE := E_le m0
  have hlen := hF.len64
  have hon := hF.onw
  have hb := hI.copy.body
  have hwf := hF.wf3 hb.kept (i := i) (l := 32) (by omega) (by omega)
  have hm : Match (Env.ofMachine st.data [(stackBelow m0 48, 48 + 8),
      (out m0 + BitVec.ofNat 64 (16 * i), 32), (pt m0 + BitVec.ofNat 64 (16 * i), 32)]) pairS
      st.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial ⟨?_, ?_, trivial⟩
    · show reg st.data .r9 + reg st.data .r14 = (out m0 + BitVec.ofNat 64 (16 * i)) + BitVec.ofInt 64 24
      rw [hI.copy.regs.r9, hI.r14, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
        NativeRustcVm.addr_add_add]
    · show reg st.data .rdx + reg st.data .r14 = (pt m0 + BitVec.ofNat 64 (16 * i)) + BitVec.ofInt 64 24
      rw [hI.copy.regs.rdx, hI.r14, show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl,
        NativeRustcVm.addr_add_add]
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkc, hw, hv0, hv1, hv2, hv3, h14, h10, hzf⟩ := after_eq run_b5 ▸ b5_facts
  have e1 := regs_eq_of hm hm1 hkc
  have hb1 := body_of_store (r := 1) hb hwf hm hm1 hk le_rfl rfl hw
    (fun p h ↦ NativeRustcVm.InRange.of_sub h hF.or.2 (by show 16 * i + 32 ≤ 1056; omega))
    (fun p hp ↦ (slots_ok p hp).2)
  have hws : ∀ q, ¬InRange (out m0 + BitVec.ofNat 64 (16 * i)) 32 q →
      st1.data.dmem.get? q = st.data.dmem.get? q := fun q hq ↦
    hm1.get?_mem0 hwf fun hW ↦ hq (Arrays.written_region (r := 1) rfl hwf le_rfl hw hW)
  have hl : i + 1 < (ptl m0).length := by simp; omega
  have w0 := copy_el hm1 (o := 0) rfl (by omega) hv0 hv1
  have w1 := copy_el hm1 (o := 16) rfl (by omega) hv2 hv3
  rw [show (Env.ofMachine st.data [(stackBelow m0 48, 48 + 8),
      (out m0 + BitVec.ofNat 64 (16 * i), 32), (pt m0 + BitVec.ofNat 64 (16 * i), 32)]).base 2 =
      pt m0 + BitVec.ofNat 64 (16 * i) from rfl, Env.ofMachine_mem0] at w0 w1
  rw [BitVec.add_zero, BitVec.add_zero, hF.elem hb (by omega)] at w0
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add,
    show 16 * i + 16 = 16 * (i + 1) by omega, hF.elem hb (by omega)] at w1
  have hcop : EWsAt st1.data.dmem (out m0) ((ptl m0).take (i + 2)) := by
    have h0 := copied_keep (L := 32) (by omega) (by omega)
      hI.copy.copied hws
    exact copied_succ hl (copied_succ (by omega) h0 w0) w1
  have hcopy : Copy m0 (i + 2) st1.data :=
    ⟨hb1, hI.copy.regs.of fun r hr ↦ e1 r (by
        simp only [keepC, List.mem_append]; exact Or.inl (Or.inl hr)),
      (e1 .rax (by simp [keepC])).trans hI.copy.rax, by omega, hcop⟩
  have hr10 : reg st1.data .r10 = BitVec.ofNat 64 (i + 2) := by
    rw [show reg st1.data .r10 = _ from hm1.regs .r10 _ h10]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st.data.regs.get64 .r10 = reg st.data .r10 from rfl, hI.r10, ← BitVec.ofNat_add,
      Nat.add_comm]
  simp only [PcOk] at hpc1
  obtain ⟨hy, hn⟩ := pc_cond hpc1
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hy hn
  rw [show st.data.regs.get64 .r11 = reg st.data .r11 from rfl,
    show st.data.regs.get64 .r10 = reg st.data .r10 from rfl, hI.r11, hI.r10, ← BitVec.ofNat_add,
    NativeRustcX64.Sym.ofNat_beq (by omega) (by omega)] at hy hn
  by_cases hlast : E m0 = 2 + i
  · refine .done _ (Or.inl ⟨(hn (by simp [hlast])).trans (congrArg Host.addrOf
      (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.StackPoint.b5_next])), by rw [hlast, Nat.add_comm]; exact hcopy,
      by rw [hr10, hlast, Nat.add_comm]⟩)
  · refine .done _ (Or.inr ⟨(hy (by simp [hlast])).trans (hp.label NativeRustcVmX64.Vm.StackPoint.label_5_at), hcopy, ?_,
      hr10, (e1 .r11 (by simp [keepC])).trans hI.r11, ?_, ?_⟩)
    · have : E m0 % 2 = 0 := by simp [E]
      have := hI.even
      omega
    · rw [show reg st1.data .r14 = _ from hm1.regs .r14 _ h14]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .r14 = reg st.data .r14 from rfl, hI.r14, ← BitVec.ofNat_add]
      congr 1
      omega
    · have := hI.even
      omega

/-- **The odd element** (`b7`): `point[len - 1]` copied, on to `.L8`. -/
theorem odd (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) (hfit : nn m0 ≤ 66)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b7Offset)) (hc : Copy m0 (len m0 - 1) st.data)
    (hl : 1 ≤ len m0) (hr10 : reg st.data .r10 = BitVec.ofNat 64 (len m0 - 1)) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b8Offset) ∧ Ready m0 s.data) st := by
  have hlen := hF.len64
  have hon := hF.onw
  have hS := hF.stack
  have h48 : 48 ≤ S := by decide
  have hwf := hc.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h48
  refine exec_at (infix_of ((infix_take b7 2).trans b7_in_code (by simp [b7])) (by simp [b7]) hp)
    run_b7a hwf nofun hpc hc.body.mid_match fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkc, h10⟩ := after_eq run_b7a ▸ b7a_facts
  have hc1 := hc.of_block hc.body.mid_match hm1 hwf rfl hk hkc
  have hr10' : reg st1.data .r10 = BitVec.ofNat 64 (16 * (len m0 - 1)) := by
    rw [show reg st1.data .r10 = _ from hm1.regs .r10 _ h10]
    rw [Arrays.eval_shl_lit _ (by decide), Arrays.eval_reg]
    show reg st.data .r10 <<< 4 = _
    rw [hr10]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  simp only [PcOk] at hpc1
  -- `b7b`
  have hb1 := hc1.body
  have hwf2 := hF.wf3 hb1.kept (i := len m0 - 1) (l := 16) (by omega) (by omega)
  have hm2 : Match (Env.ofMachine st1.data [(stackBelow m0 48, 48 + 8),
      (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16),
      (pt m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16)]) oneS st1.data := by
    refine match_ofMachine ⟨rfl, rfl, rfl, trivial⟩ ⟨hb1.rsp, trivial⟩ trivial trivial ⟨?_, ?_, trivial⟩
    · show reg st1.data .r9 + reg st1.data .r10 = _ + BitVec.ofInt 64 0
      rw [hc1.regs.r9, hr10', Transcript.ofInt_zero64, BitVec.add_zero]
      rfl
    · show reg st1.data .rdx + reg st1.data .r10 = _ + BitVec.ofInt 64 0
      rw [hc1.regs.rdx, hr10', Transcript.ofInt_zero64, BitVec.add_zero]
      rfl
  have hl7 : (b7.take 2).length = 2 := rfl
  refine exec_at (infix_of ((infix_drop b7 2).trans b7_in_code (by simp [b7])) (by simp [b7]) hp)
    run_b7b hwf2 nofun (hpc1.trans (congrArg Host.addrOf (by omega))) hm2 fun st2 hm3 hpc2 ↦ ?_
  obtain ⟨hk2, hkr, hw, hv0, hv1⟩ := after_eq run_b7b ▸ b7b_facts
  have e2 := regs_eq_of hm2 hm3 hkr
  have hb2 := body_of_store (r := 1) hb1 hwf2 hm2 hm3 hk2 le_rfl rfl hw
    (fun p h ↦ NativeRustcVm.InRange.of_sub h hF.or.2 (by show 16 * (len m0 - 1) + 16 ≤ 1056; omega))
    (fun p hp ↦ (slots_ok p hp).2)
  have hws : ∀ q, ¬InRange (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1))) 16 q →
      st2.data.dmem.get? q = st1.data.dmem.get? q := fun q hq ↦
    hm3.get?_mem0 hwf2 fun hW ↦ hq (Arrays.written_region (r := 1) rfl hwf2 le_rfl hw hW)
  have w0 := copy_el hm3 (o := 0) rfl (by omega) hv0 hv1
  rw [show (Env.ofMachine st1.data [(stackBelow m0 48, 48 + 8),
      (out m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16),
      (pt m0 + BitVec.ofNat 64 (16 * (len m0 - 1)), 16)]).base 2 =
      pt m0 + BitVec.ofNat 64 (16 * (len m0 - 1)) from rfl, Env.ofMachine_mem0,
    BitVec.add_zero, BitVec.add_zero, hF.elem hb1 (by omega)] at w0
  have hcop : EWsAt st2.data.dmem (out m0) ((ptl m0).take (len m0)) := by
    have h0 := copied_keep (L := 16) (by omega) (by omega) hc1.copied hws
    have := copied_succ (by simp; omega) h0 w0
    rwa [Nat.sub_add_cancel hl] at this
  simp only [PcOk] at hpc2
  refine .done _ ⟨hpc2.trans (congrArg Host.addrOf (by have hn := NativeRustcVmX64.Vm.StackPoint.b7_next; have hl := NativeRustcVmX64.Vm.StackPoint.b7_length; simp only [NativeRustcVmX64.Vm.StackPoint.b7Length] at hl; simp only [List.length_drop]; omega)), ⟨hb2, (e2 .rsi (by simp)).trans hc1.regs.rsi, (e2 .rdi (by simp)).trans hc1.regs.rdi,
    (e2 .r8 (by simp)).trans hc1.regs.r8, (e2 .rbx (by simp)).trans hc1.regs.rbx,
    (e2 .rax (by simp)).trans hc1.rax, by rwa [List.take_of_length_le (by simp)] at hcop, hfit⟩⟩

/-- `stack_point`'s postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧ StackPointPost m0 s.data

/-- **The epilogue** `b10`: RAX as given, RDX = `n`. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b10Offset)) (hb : Body m0 48 S slots (out m0) outB st.data)
    (hbx : reg st.data .rbx = BitVec.ofNat 64 (nn m0))
    (hres : if nn m0 ≤ stackPointOut then reg st.data .rax = 1#64 ∧
        EWsAt st.data.dmem (out m0) (stackPoint ⟨(reg m0 .rdi).toNat, (reg m0 .rsi).toNat⟩
          (slice m0 (reg m0 .rdx) (reg m0 .rcx)) (reg m0 .r8).toNat).toList
      else reg st.data .rax = 0#64) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hF.stack
  have h48 : 48 ≤ S := by decide
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10
    (hb.wf (vars := fun _ ↦ 0) (ret := 0) hS h48) nofun hpc hb.mid_match fun st' hm' hpc' ↦
      .done _ ?_
  obtain ⟨hres', hmem, hax, hdx⟩ := after_eq run_b10 ▸ b10_restores
  obtain ⟨hpc'', hrsp, hdm, hsaved⟩ := hb.done hS h48 hm' hpc' hres' hmem
    (Arrays.ret_not_in hS hF.or.2 hF.oo)
  have ha : reg st'.data .rax = reg st.data .rax := hm'.regs .rax _ hax
  have hd : reg st'.data .rdx = reg st.data .rbx := hm'.regs .rdx _ hdx
  refine ⟨hpc'', hrsp, ?_, fun p hp' ↦ by rw [hdm]; exact hb.same p hp', hsaved⟩
  have hnn : (reg m0 .rcx).toNat + ((reg m0 .r8).toNat - (reg m0 .rdi).toNat) = nn m0 := rfl
  simp only [hnn]
  split
  · rename_i h
    simp only [h, ↓reduceIte] at hres
    refine ⟨ha.trans hres.1, ?_, by rw [hdm]; exact hres.2⟩
    rw [hd, hbx, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by unfold stackPointOut at h; omega)
  · rename_i h
    simp only [h, ↓reduceIte] at hres
    exact ha.trans hres

/-- **The selector** (`b8`, `selector_point`, `b9`), then the epilogue. -/
theorem tail (hp : Placed code k)
    (hsel : Spec (Labels.label NativeRustcVmX64.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost)
    {m0 : MachineData} (hF : Facts m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b8Offset))
    (hR : Ready m0 st.data) : Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hF.stack
  have h48 : 48 ≤ S := by decide
  have hS64 := S_eq
  have hnn : nn m0 = len m0 + tl m0 := rfl
  have hlen := hF.len64
  have hfit := hR.fit
  have hon := hF.onw
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hb := hR.body
  have hwf := hb.wf (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b8Offset + b8.length)).toBitVec) hS h48
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 hwf (fun _ _ ↦ rfl) hpc
    hb.mid_match fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hk, hkb, hsp, hw, hdi, hsi, hdx⟩ := after_eq run_b8 ▸ b8_call
  have e1 := regs_eq_of hb.mid_match hm1 hkb
  have hrsp1 : rspOf st1.data = stackBelow m0 48 := by
    show st1.data.regs.get64 .rsp = _
    rw [hm1.regs .rsp _ hsp]
    simp [Sym.eval]
  have hk1 : Kept m0.dmem st1.data.dmem := fun p h ↦ hm1.kept hwf p (hb.kept p h)
  have hrsi : reg st1.data .rsi = out m0 + BitVec.ofNat 64 (16 * len m0) :=
    (hm1.regs .rsi _ hsi).trans hR.rax
  have hrdx : reg st1.data .rdx = BitVec.ofNat 64 (tl m0) := (hm1.regs .rdx _ hdx).trans hR.r8
  have hrdi : (reg st1.data .rdi).toNat = (reg m0 .rsi).toNat >>> (reg m0 .rdi).toNat := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi]
    have h1 : st.data.regs.get64 .rdi = reg m0 .rdi := hR.rdi
    have h2 : st.data.regs.get64 .rsi = reg m0 .rsi := hR.rsi
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs]
    refine (sel_eval _ _).trans ?_
    rw [h1, h2]
  have htl : (reg st1.data .rdx).toNat = tl m0 := by
    rw [hrdx, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hoB : outB = 1056 := rfl
  have e3 := NativeRustcVm.toNat_add_ofNat (a := out m0) (i := 16 * len m0) (by omega)
  have hpre : SelectorPointPre st1.data := by
    refine ⟨Transcript.stackOk_callee hS hk1 hrsp1 (by decide), ?_, ?_⟩
    · rw [hrsi, htl]
      exact ⟨fun j hj ↦ by rw [NativeRustcVm.addr_add_add]; exact hk1 _ (hF.or.1 _ (by rw [hoB]; omega)),
        show (out m0 + BitVec.ofNat 64 (16 * len m0)).toNat + 16 * tl m0 ≤ 2 ^ 64 by rw [e3]; omega⟩
    · have ha := Transcript.apart_callee hF.oo hrsp1 hS1 (n' := 16) (by decide)
      show NativeRustcX64.Apart (reg st1.data .rsi) (16 * (reg st1.data .rdx).toNat)
        (stackBelow st1.data 16) (16 + 8)
      rw [hrsi, htl]
      unfold NativeRustcX64.Apart
      unfold NativeRustcVm.Apart at ha
      rw [e3]; rw [hoB] at ha; omega
  refine call_then hpc1 hsel hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hsel2, hch, hsv⟩ := hpost
  rw [hrsi, htl, hrdi] at hsel2
  rw [hrsi, htl] at hch
  have hsub : ∀ p, InRange (out m0 + BitVec.ofNat 64 (16 * len m0)) (16 * tl m0) p →
      InRange (out m0) outB p := fun p h ↦
    NativeRustcVm.InRange.of_sub h hF.or.2 (by rw [hoB]; omega)
  have hoa : ∀ p, InRange (out m0) outB p → ¬InRange (stackBelow m0 S) S p := by
    intro p h1 h2
    have ho := hF.oo
    have hsn := Transcript.stack_noWrap hS
    unfold OffStack NativeRustcX64.Apart at ho
    unfold NativeRustcVm.NoWrap at hsn
    rw [hoB] at h1 ho
    rw [Sym.inRange_iff (by omega)] at h1
    rw [Sym.inRange_iff hsn] at h2
    rw [Arrays.stackBelow_toNat hS1] at ho h2
    omega
  have hb2 := body_after_call (n := 16) hb hS (by decide) (L := 8) (by decide) slots_ok hwf
    hb.mid_match hm1 hk hsp hw hsv hrsp2
    (fun p hp' ↦ hch p fun h ↦ hp' (h.elim (fun h ↦ Or.inl (hsub p h)) Or.inr)) hoa
  -- the copy kept by the call
  have hrsp0 := (rspOf m0).isLt
  have hfb := Arrays.stackBelow_toNat (m := m0) (n := 48) (by omega)
  have hcb : (stackBelow st1.data 16).toNat = (rspOf m0).toNat - 64 := by
    rw [Arrays.stackBelow_toNat (by rw [hrsp1, hfb]; omega), hrsp1, hfb]
    omega
  have ho := hF.oo
  unfold OffStack NativeRustcX64.Apart at ho
  rw [hoB, Arrays.stackBelow_toNat hS1, hS64] at ho
  have hcop : EWsAt st2.data.dmem (out m0) (ptl m0) := by
    refine Arrays.ewsAt_congr hR.copied fun j hj ↦ ?_
    simp only [NativeRustcVm.length_ewsOf] at hj
    have hq := NativeRustcVm.toNat_add_ofNat (a := out m0) (i := j) (by omega)
    have h21 : st2.data.dmem.get? (out m0 + BitVec.ofNat 64 j) =
        st1.data.dmem.get? (out m0 + BitVec.ofNat 64 j) := hch _ fun h ↦ h.elim
      (fun h ↦ by rw [Sym.inRange_iff (by rw [e3]; omega), e3, hq] at h; omega)
      (fun h ↦ by
        rw [show selectorPointStack = 16 from rfl, Sym.inRange_iff (by rw [hcb]; omega), hcb,
          hq] at h
        omega)
    rw [h21]
    exact hm1.get?_mem0 hwf fun hW ↦ by
      have h := Arrays.written_region0 rfl hwf (by omega) hw hW
      rw [Sym.inRange_iff (by rw [hfb]; omega), hfb, hq] at h
      omega
  have hpt : (stackPoint ⟨(reg m0 .rdi).toNat, (reg m0 .rsi).toNat⟩
      (slice m0 (reg m0 .rdx) (reg m0 .rcx)) (reg m0 .r8).toNat).toList =
      ptl m0 ++ (selectorPoint ((reg m0 .rsi).toNat >>> (reg m0 .rdi).toNat) (tl m0)).toList := by
    simp [stackPoint, slice]
  have hres2 : EWsAt st2.data.dmem (out m0) (stackPoint ⟨(reg m0 .rdi).toNat, (reg m0 .rsi).toNat⟩
      (slice m0 (reg m0 .rdx) (reg m0 .rcx)) (reg m0 .r8).toNat).toList := by
    rw [hpt, NativeRustcVm.ewsAt_append_iff, NativeRustcVm.length_ewsOf]
    exact ⟨hcop, hsel2⟩
  have hbx2 : reg st2.data .rbx = BitVec.ofNat 64 (nn m0) := by
    rw [show reg st2.data .rbx = reg st1.data .rbx from hsv.1 .rbx rfl,
      e1 .rbx (by simp)]
    exact hR.rbx
  -- `b9`
  have hwf2 := hb2.wf (vars := fun _ ↦ 0) (ret := 0) hS h48
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf2 nofun
    (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.StackPoint.b8_next))) hb2.mid_match
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hk3, hkb3, hax⟩ := after_eq run_b9 ▸ b9_facts
  have e3' := regs_eq_of hb2.mid_match hm3 hkb3
  have hdm3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 (mem_of_keepsAll hk3)
  simp only [PcOk] at hpc3
  refine finish hp hF (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.StackPoint.b9_next)))
    (hb2.of_block hb2.mid_match hm3 hwf2 rfl hk3) ((e3' .rbx (by simp)).trans hbx2) ?_
  simp only [show nn m0 ≤ stackPointOut from hfit, ↓reduceIte]
  refine ⟨?_, by rw [hdm3]; exact hres2⟩
  rw [show reg st3.data .rax = _ from hm3.regs .rax _ hax]
  rfl
/-- **The copy** (`b2`-`b7`) from `.L8`'s complement: `len ≥ 1` copied, on to the selector. -/
theorem copyAll (hp : Placed code k)
    (hsel : Spec (Labels.label NativeRustcVmX64.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost)
    {m0 : MachineData} (hF : Facts m0) (hfit : nn m0 ≤ 66) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b2Offset)) (hc : Copy m0 0 st.data) (hl : 1 ≤ len m0) :
    Eventually (step1 Host.exe) (Post m0) st := by
  have hS := hF.stack
  have h48 : 48 ≤ S := by decide
  have hlen := hF.len64
  have hwf := hc.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h48
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf nofun hpc hc.body.mid_match
    fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hk2, hkc2, hz2⟩ := after_eq run_b2 ▸ b2_facts
  have hc2 := hc.of_block hc.body.mid_match hm2 hwf rfl hk2 hkc2
  simp only [PcOk] at hpc2
  obtain ⟨hy, hn⟩ := pc_cond hpc2
  have hrc : st.data.regs.get64 .rcx = reg m0 .rcx := hc.regs.rcx
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs, hrc] at hy hn
  by_cases h1 : len m0 = 1
  · -- `b3`: R10 = 0, on to `.L7`
    have hr1 : reg m0 .rcx = BitVec.ofNat 64 1 := BitVec.eq_of_toNat_eq (by simp [h1])
    have hpc3 := hn (by simp [hr1])
    have hwf2 := hc2.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h48
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf2 nofun
      (hpc3.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.StackPoint.b2_next)))
      hc2.body.mid_match fun st3 hm3 hpc4 ↦ ?_
    obtain ⟨hk3, hkc3, h10⟩ := after_eq run_b3 ▸ b3_facts
    have hc3 := hc2.of_block hc2.body.mid_match hm3 hwf2 rfl hk3 hkc3
    simp only [PcOk] at hpc4
    refine eventually_trans _ _ _ _ (odd hp hF hfit (hpc4.trans (hp.label NativeRustcVmX64.Vm.StackPoint.label_7_at))
      (by rw [h1]; exact hc3) hl ?_) fun s h ↦ tail hp hsel hF h.1 h.2
    rw [show reg st3.data .r10 = _ from hm3.regs .r10 _ h10, h1]
    rfl
  · -- `b4`, the pair loop, `b6`
    have hr1 : reg m0 .rcx ≠ BitVec.ofNat 64 1 := fun h ↦ h1 (by
      show (reg m0 .rcx).toNat = 1
      rw [h]
      rfl)
    have hpc3 := (hy (by simp [hr1])).trans (hp.label NativeRustcVmX64.Vm.StackPoint.label_4_at)
    have hwf2 := hc2.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h48
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf2 nofun hpc3
      hc2.body.mid_match fun st4 hm4 hpc4 ↦ ?_
    obtain ⟨hk4, hkc4, h11, h14, h10⟩ := after_eq run_b4 ▸ b4_facts
    have hc4 := hc2.of_block hc2.body.mid_match hm4 hwf2 rfl hk4 hkc4
    simp only [PcOk] at hpc4
    have hP : Pair m0 0 st4.data := by
      refine ⟨hc4, by simp only [E]; omega, hm4.regs .r10 _ h10, ?_, hm4.regs .r14 _ h14, rfl⟩
      rw [show reg st4.data .r11 = _ from hm4.regs .r11 _ h11]
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .rcx = reg m0 .rcx from hc2.regs.rcx]
      exact r11_eval _ hlen
    refine eventually_trans _ _ _ _ (Sym.loop (Q := fun s ↦ s.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b6Offset) ∧
        Copy m0 (E m0) s.data ∧ reg s.data .r10 = BitVec.ofNat 64 (E m0))
      (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b5Offset) ∧ ∃ i, E m0 - i = n ∧ Pair m0 i st.data)
      (fun n st ⟨hpc, i, hn, hI⟩ ↦ Eventually.mono (stepPair hp hF hpc hI) fun st' h ↦ by
        rcases h with h | ⟨hpc', hI'⟩
        · exact Or.inl h
        · exact Or.inr ⟨E m0 - (i + 2), by have := hI.lt; omega, hpc', i + 2, rfl, hI'⟩)
      ⟨hpc4.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.StackPoint.b4_next)), 0, rfl, hP⟩)
      fun s ⟨hpc6, hc6, h106⟩ ↦ ?_
    have hwf6 := hc6.body.wf (vars := fun _ ↦ 0) (ret := 0) hS h48
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf6 nofun hpc6
      hc6.body.mid_match fun st7 hm7 hpc7 ↦ ?_
    obtain ⟨hk7, hkc7, hz7⟩ := after_eq run_b6 ▸ b6_facts
    have e7 := regs_eq_of hc6.body.mid_match hm7 hkc7
    have hc7 := hc6.of_block hc6.body.mid_match hm7 hwf6 rfl hk7 (by
      simp only [keepsRegs, List.all_append, Bool.and_eq_true] at hkc7 ⊢; exact hkc7.1)
    simp only [PcOk] at hpc7
    obtain ⟨hy7, hn7⟩ := pc_cond hpc7
    rw [even_eval _ (n := len m0) (congrArg BitVec.toNat hc6.regs.rcx)] at hy7 hn7
    by_cases hev : len m0 % 2 = 0
    · have hE : E m0 = len m0 := by simp only [E]; omega
      refine tail hp hsel hF ((hy7 (by simp [hev])).trans (hp.label NativeRustcVmX64.Vm.StackPoint.label_8_at))
        (Copy.ready (by rw [← hE]; exact hc7) hfit)
    · have hE : E m0 = len m0 - 1 := by simp only [E]; omega
      refine eventually_trans _ _ _ _ (odd hp hF hfit ((hn7 (by simp [hev])).trans (congrArg Host.addrOf
        (by rw [Nat.add_assoc, NativeRustcVmX64.Vm.StackPoint.b6_next]))) (by rw [← hE]; exact hc7) hl ?_)
        fun s h ↦ tail hp hsel hF h.1 h.2
      rw [e7 .r10 (by simp [keepC, keepB]), h106, hE]

/-- **`stack_point`'s contract.** -/
theorem stackPoint_spec (hp : Placed code k)
    (hsel : Spec (Labels.label NativeRustcVmX64.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.StackPoint.entryLabel) StackPointPre StackPointPost := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hS := hF.stack
  have h48 : 48 ≤ S := by decide
  have hlen := hF.len64
  have hS48 := stackOk_mono hS h48
  have hwf := frame_wf (m0 := m0) (m := m0) (vars := fun _ ↦ 0) (ret := 0) hS48 fun _ h ↦ h
  have hm : Match (frameEnv m0 m0 48) entryS m0 := match_frame
  rw [show Labels.label NativeRustcVmX64.Vm.StackPoint.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.StackPoint.b0Offset) from hp.label NativeRustcVmX64.Vm.StackPoint.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  obtain ⟨hw, hregs, hmem, hsp, hkr, h8, hbx, hax, hzf⟩ := after_eq run_b0 ▸ b0_facts
  have hb0 : Body m0 48 S slots (out m0) outB st0.data := Body.of_entry hS h48 hm0 hsp hw hregs hmem
  have e0 := regs_eq_of hm hm0 hkr
  have hbx0 : reg st0.data .rbx = BitVec.ofNat 64 (nn m0) := by
    rw [show reg st0.data .rbx = _ from hm0.regs .rbx _ hbx]
    apply BitVec.eq_of_toNat_eq
    rw [nS_toNat, BitVec.toNat_ofNat]
    exact congrArg (· % 2 ^ 64) (Nat.add_comm _ _)
  have hok : okS.eval (frameEnv m0 m0 48) = decide (nn m0 ≤ 66) := okS_eval _ hlen
  simp only [PcOk, NativeRustcVmX64.Vm.StackPoint.b0_length] at hpc0
  obtain ⟨hy, hn⟩ := pc_cond hpc0
  have hy' : (!(okS.eval (frameEnv m0 m0 48))) = true → _ := hy
  have hn' : ¬(!(okS.eval (frameEnv m0 m0 48))) = true → _ := hn
  rw [hok] at hy' hn'
  by_cases h66 : nn m0 ≤ 66
  · have hpc1 := hn' (by simp [h66])
    have hr : Regs m0 st0.data := ⟨e0 .rcx (by simp), e0 .rdx (by simp), e0 .rsi (by simp),
      e0 .rdi (by simp), by
        rw [show reg st0.data .r8 = _ from hm0.regs .r8 _ h8]
        apply BitVec.eq_of_toNat_eq
        rw [tlS_toNat, BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (by have := (reg m0 .r8).isLt; omega)).symm,
      e0 .r9 (by simp), hbx0⟩
    have hwf0 := hb0.wf (vars := fun _ ↦ 0) (ret := 0) hS h48
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf0 nofun
      (hpc1.trans (congrArg Host.addrOf (by rw [← NativeRustcVmX64.Vm.StackPoint.b0_length, Nat.add_assoc, NativeRustcVmX64.Vm.StackPoint.b0_next]))) hb0.mid_match fun st1 hm1 hpc2 ↦ ?_
    obtain ⟨hk1, hkb1, hax1, hz1⟩ := after_eq run_b1 ▸ b1_facts
    have e1 := regs_eq_of hb0.mid_match hm1 hkb1
    have hc1 : Copy m0 0 st1.data := by
      refine ⟨hb0.of_block hb0.mid_match hm1 hwf0 rfl hk1, hr.of fun r hr' ↦ e1 r hr', ?_,
        Nat.zero_le _, by simpa using NativeRustcVm.ewsAt_nil _ _⟩
      rw [show reg st1.data .rax = _ from hm1.regs .rax _ hax1, Arrays.eval_add,
        Arrays.eval_shl_lit _ (by decide), Arrays.eval_reg, Arrays.eval_reg]
      show reg st0.data .r9 + reg st0.data .rcx <<< 4 = _
      rw [hr.r9, hr.rcx]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      have : len m0 = (reg m0 .rcx).toNat := rfl
      omega
    simp only [PcOk] at hpc2
    obtain ⟨hy2, hn2⟩ := pc_cond hpc2
    rw [zero_eval _ (n := len m0) (congrArg BitVec.toNat hr.rcx)] at hy2 hn2
    by_cases hl0 : len m0 = 0
    · exact tail hp hsel hF ((hy2 (by simp [hl0])).trans (hp.label NativeRustcVmX64.Vm.StackPoint.label_8_at))
        (Copy.ready (by rw [hl0]; exact hc1) h66)
    · exact copyAll hp hsel hF h66 ((hn2 (by simp [hl0])).trans
        (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.StackPoint.b1_next))) hc1 (by omega)
  · have hpc1 := (hy' (by simp [h66])).trans (hp.label NativeRustcVmX64.Vm.StackPoint.label_9_at)
    exact finish hp hF hpc1 hb0 hbx0 (by
      simp only [show ¬nn m0 ≤ stackPointOut from h66, ↓reduceIte]
      rw [show reg st0.data .rax = _ from hm0.regs .rax _ hax]
      rfl)

end

end NativeRustcVmX64.Layout.StackPoint
