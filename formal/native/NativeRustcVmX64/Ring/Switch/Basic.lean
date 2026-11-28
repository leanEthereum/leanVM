module

public import NativeRustcVmX64.Ring.Switch.Exec
public import NativeRustcVmX64.Ring.Stack
public import NativeRustcVmX64.Transcript.Callee
public import NativeRustcVm.Ring.Math
public import NativeRustcVm.Transcript.Update

/-!
# `ring_switch`: its facts between the blocks (x86-64)

From the entry state `m0` (the `TState` at RDI, `s` at RSI, the `RingW` at RDX): what changes
(`Ch`: the `RingW`, the `TState`, the stack), the entry's facts unpacked (`P`), the frame's bytes
kept by a callee below it or a write outside it (`frame_keep`), the challenges' halves read from
the frame (`take_of`, `drop_of`), AL's test (`al_test`).
-/

namespace NativeRustcVmX64.Ring.Switch

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- The bytes `ring_switch` may change: the `RingW`, the `TState`, the stack. -/
def Ch (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (reg m0 .rdx) ringWBytes q ∨ InRange (reg m0 .rdi) tstateBytes q ∨
    InRange (stackBelow m0 ringSwitchStack) ringSwitchStack q

end

public section

variable {m0 : MachineData}

theorem stack_eq : ringSwitchStack = 3008 := rfl

/-- The entry's facts. -/
structure P [Labels] (m0 : MachineData) (a : DecArea) (s : TState) : Prop where
  st : StackOk m0 ringSwitchStack
  rc : RcAt m0 ringSwitchStack
  ts : TStateAt m0.dmem (reg m0 .rdi) a s
  tok : TStateOk m0 (reg m0 .rdi) a ringSwitchStack
  out : OutOk m0 (reg m0 .rdi) a (reg m0 .rdx) ringWBytes ringSwitchStack
  sl : ArrOk m0 (reg m0 .rsi) coeffCount ringSwitchStack
  slT : Apart (reg m0 .rsi) (16 * coeffCount) (reg m0 .rdi) tstateBytes
  slO : Apart (reg m0 .rsi) (16 * coeffCount) (reg m0 .rdx) ringWBytes

theorem P.intro [Labels] {a : DecArea} {s : TState} (h : RingSwitchPre a s m0) : P m0 a s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

/-- A range apart from the stack (and the return address) has no byte of the frame. -/
theorem not_frame (hst : StackOk m0 ringSwitchStack) {a : BitVec 64} {n : Nat}
    (hap : Apart a n (stackBelow m0 ringSwitchStack) (ringSwitchStack + 8)) (hw : NoWrap a n)
    {j : Nat} (hj : j < 432 + 8) : ¬InRange a n (off (stackBelow m0 432) j) := by
  have h1 := hst.1
  have h2 := hst.2.1
  have hs := stackBelow_toNat (m := m0) (n := 432) (by rw [stack_eq] at h1; omega)
  have hS := stackBelow_toNat (m := m0) (n := ringSwitchStack) h1
  show ¬NativeRustcVm.InRange a n _
  rw [inRange_iff' hw, toNat_off (by omega), hs]
  unfold Apart at hap
  rw [hS] at hap
  rw [stack_eq] at h1 hap
  omega

/-- The frame's bytes from `o` (`16 n` of them) read the same after a change outside the frame. -/
theorem frame_keep {d d' : DataMem} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) {o n : Nat}
    (hR : ∀ j, o ≤ j → j < o + 16 * n → ¬R (off (stackBelow m0 432) j)) :
    NativeRustcVm.ewsOf d' (off (stackBelow m0 432) o) n =
      NativeRustcVm.ewsOf d (off (stackBelow m0 432) o) n :=
  NativeRustcVm.ewsOf_congr fun i hi ↦ by
    rw [off_add]
    exact hs _ (hR _ (by omega) (by omega))

theorem ewsOf_take (d : DataMem) (b : BitVec 64) {n k : Nat} (h : k ≤ n) :
    (NativeRustcVm.ewsOf d b n).take k = NativeRustcVm.ewsOf d b k := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, NativeRustcVm.getElem_ewsOf]

theorem ewsOf_drop (d : DataMem) (b : BitVec 64) (n k : Nat) :
    (NativeRustcVm.ewsOf d b (k + n)).drop k =
      NativeRustcVm.ewsOf d (b + BitVec.ofNat 64 (16 * k)) n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, NativeRustcVm.getElem_ewsOf]
  rw [NativeRustcVm.addr_add_add, Nat.mul_add]

/-- Elements read from words equal pairwise. -/
theorem ewsOf_of_words {d d' : DataMem} {b b' : BitVec 64} {n : Nat}
    (h : ∀ j < 2 * n, NativeRustcVm.wordOf d' (b' + BitVec.ofNat 64 (8 * j)) =
      NativeRustcVm.wordOf d (b + BitVec.ofNat 64 (8 * j))) :
    NativeRustcVm.ewsOf d' b' n = NativeRustcVm.ewsOf d b n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [NativeRustcVm.getElem_ewsOf]
  simp only [NativeRustcVm.length_ewsOf] at h1
  unfold NativeRustcVm.ewOf
  have e0 := h (2 * i) (by omega)
  have e1 := h (2 * i + 1) (by omega)
  rw [show 8 * (2 * i) = 16 * i by omega] at e0
  rw [show 8 * (2 * i + 1) = 16 * i + 8 by omega, ← NativeRustcVm.addr_add_add,
    ← NativeRustcVm.addr_add_add] at e1
  rw [e0]
  exact congrArg _ e1

/-- The challenges' first `8`, from the 16 the frame holds. -/
theorem take_of {d : DataMem} {b : BitVec 64} {xs : Array EW} (hsz : xs.size = 16)
    (h : NativeRustcVm.EWsAt d b xs.toList) :
    (NativeRustcVm.ewsOf d b 8).toArray = xs.extract 0 8 := by
  have e := NativeRustcVm.ewsOf_of_ewsAt h
  rw [Array.length_toList, hsz] at e
  rw [← ewsOf_take d b (show 8 ≤ 16 by decide), e]
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

/-- The challenges' last `8`. -/
theorem drop_of {d : DataMem} {b : BitVec 64} {xs : Array EW} (hsz : xs.size = 16)
    (h : NativeRustcVm.EWsAt d b xs.toList) :
    (NativeRustcVm.ewsOf d (b + BitVec.ofNat 64 128) 8).toArray = xs.extract 8 xs.size := by
  have e := NativeRustcVm.ewsOf_of_ewsAt h
  rw [Array.length_toList, hsz] at e
  rw [show (128 : Nat) = 16 * 8 from rfl, ← ewsOf_drop d b 8 8, e]
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract, hsz]

/-- AL's test: `test %al, %al` is zero exactly when AL is. -/
theorem al_test (x : BitVec 64) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x x) (BitVec.ofNat 64 0) =
      decide (x.toNat % 256 = 0) := by
  simp only [CmpOp.apply, BinOp.apply]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, toNat_low, toNat_low,
    toNat_ext, BitVec.toNat_and, toNat_low, Nat.and_self]
  simp [Width.bits]

theorem boolRet_trunc (x : BitVec 64) :
    (UnOp.apply .trunc .W32 (UnOp.apply .trunc .W32 x)).toNat % 256 = x.toNat % 256 := by
  simp only [UnOp.apply, toNat_ext, toNat_low]
  simp only [Width.bits]
  omega

/-- `sampleChallenges n` returns `n` challenges. -/
theorem sample_size {n : Nat} {s s' : TState} {xs : Array EW}
    (h : (sampleChallenges n).run s = some (xs, s')) : xs.size = n := by
  have key : ∀ (l : List Nat) (acc : Array EW) (s s' : TState) (xs : Array EW),
      (l.foldlM (fun acc _ ↦ do pure (acc.push (← sampleChallenge))) acc : VM (Array EW)).run s =
        some (xs, s') → xs.size = acc.size + l.length := by
    intro l
    induction l with
    | nil =>
      intro acc s s' xs h
      simp only [List.foldlM_nil, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; simp
    | cons x l ih =>
      intro acc s s' xs h
      simp only [List.foldlM_cons, StateT.run_bind] at h
      cases hr : (sampleChallenge.run s) with
      | none =>
        simp only [bind, StateT.run] at h hr
        simp [hr] at h
      | some p =>
        obtain ⟨x, s1⟩ := p
        simp only [bind, StateT.run] at h hr
        simp only [hr, pure, StateT.pure, Option.bind_some] at h
        have := ih _ _ _ _ h
        simp at this
        simp; omega
  have := key (List.range n) #[] s s' xs h
  simpa using this

/-- Parts of two apart ranges are apart. -/
theorem apart_parts {a b : BitVec 64} {N M oa la ob lb : Nat} (h : Apart a N b M)
    (ha : NoWrap a N) (hb : NoWrap b M) (h1 : oa + la ≤ N) (h2 : ob + lb ≤ M) (hla : 0 < la)
    (hlb : 0 < lb) : Apart (off a oa) la (off b ob) lb := by
  unfold NoWrap at ha hb
  unfold Apart at h ⊢
  rw [toNat_off (b := a) (j := oa) (by omega), toNat_off (b := b) (j := ob) (by omega)]
  omega

/-- A part of a range apart from the stack, apart from a callee's stack below the frame. -/
theorem apart_part_callee {d : MachineData} {a : BitVec 64} {N o l n F n' : Nat}
    (h : Apart a N (stackBelow m0 n) (n + 8)) (ha : NoWrap a N) (hol : o + l ≤ N) (hl : 0 < l)
    (hsp : rspOf d = stackBelow m0 F) (hn : n ≤ (rspOf m0).toNat) (hn' : F + n' ≤ n) :
    Apart (off a o) l (stackBelow d n') (n' + 8) := by
  have := apart_callee h hsp hn hn'
  unfold NoWrap at ha
  unfold NativeRustcVm.Apart at this
  unfold Apart
  rw [toNat_off (b := a) (j := o) (by omega)]
  omega

end

end NativeRustcVmX64.Ring.Switch
