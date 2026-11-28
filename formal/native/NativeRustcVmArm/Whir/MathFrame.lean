module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Spec.Whir
public import NativeRustcArm.Hasher.Bytes
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmArm.Basic

/-!
# Frames, calls and outputs of `whir.rs`'s leaf functions

What the proofs of `fold_row`, `lanes_of`, `subspace_table`, `subspace_at_table`, `novel_eval`,
`induced_weight` and `glued_eval` share.

- `Frame m0 F S slots outs st`: the state `st` of a function's body entered in `m0`: SP `F` bytes
  below the entry's, the prologue's slots there (`SlotsAt`), the other callee-saved registers the
  entry's, memory as at the entry but in the outputs `outs` and the `S` bytes of stack
  (`ChangesIn`), every mapped byte still mapped. The prologue makes one (`Frame.of_entry`), a call
  keeps one (`Frame.call`, the callee's stack `Frame.stackOk`, an argument apart from it
  `Frame.offStack`), the epilogue restores the entry's registers (`Frame.ret`).
- Arguments a body reads: unchanged where apart from the outputs and the stack
  (`Frame.get?_eq`).
-/

namespace NativeRustcVmArm.Whir

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcVm (Region InAny wordOf ewOf leNat bytesFrom)

public section

/-! ## Basics (as the array functions' proofs have them) -/

theorem toNat_sub_ofNat {a : BitVec 64} {j : Nat} (h : j ≤ a.toNat) :
    (a - BitVec.ofNat 64 j).toNat = a.toNat - j := by
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    show 2 ^ 64 - j + a.toNat = (a.toNat - j) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_add_ofNat' {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem not_inRange_below {b : BitVec 64} {n j : Nat} (h : n + j < 2 ^ 64) :
    ¬InRange (b - BitVec.ofNat 64 n) n (b + BitVec.ofNat 64 j) := by
  unfold InRange
  rw [show b + BitVec.ofNat 64 j - (b - BitVec.ofNat 64 n) = BitVec.ofNat 64 (n + j) by
    rw [BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  omega

/-- The `F` bytes below SP, within the `S` the function may use. -/
theorem frame_ok {m : MachineData} {F S : Nat} (hS : StackOk m S) (hF : F ≤ S) :
    Mapped m.dmem (m.regs.SP.toBitVec - BitVec.ofNat 64 F) F ∧
      NoWrap (m.regs.SP.toBitVec - BitVec.ofNat 64 F) F ∧
      (m.regs.SP.toBitVec - BitVec.ofNat 64 F).toNat = m.regs.SP.toBitVec.toNat - F := by
  obtain ⟨-, hle, hmap⟩ := hS
  have hle' : S ≤ m.regs.SP.toBitVec.toNat := hle
  have e := toNat_sub_ofNat (a := m.regs.SP.toBitVec) (j := F) (by omega)
  refine ⟨fun i hi ↦ ?_, by unfold NoWrap; rw [e]; have := m.regs.SP.toBitVec.isLt; omega, e⟩
  have := hmap (S - F + i) (by omega)
  have e' : m.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 i =
      m.regs.SP.toBitVec - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F + i) := by
    bv_omega
  rw [e']
  exact this

theorem stack_noWrap {m : MachineData} {S : Nat} (hS : StackOk m S) : NoWrap (stackBelow m S) S :=
  (frame_ok hS (Nat.le_refl _)).2.1

/-- A byte of a region apart from another is not one of the other's. -/
theorem not_inRange_of_apart {a b : BitVec 64} {n n' j : Nat} (hA : Apart a n b n')
    (hna : NoWrap a n) (hnb : NoWrap b n') (hj : j < n) : ¬InRange b n' (a + BitVec.ofNat 64 j) := by
  unfold Apart NoWrap at *
  rw [Sym.inRange_iff hnb, toNat_add_ofNat' (by omega)]
  omega

theorem natOfBytes_eq_leNat (bs : List UInt8) : Nat.ofBytes bs = leNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Nat.ofBytes bs * 256 + b.toNat = b.toNat + 256 * leNat bs
    rw [ih]; omega

theorem leNat_lt (bs : List UInt8) : leNat bs < 2 ^ (8 * bs.length) := by
  rw [← natOfBytes_eq_leNat]; exact natOfBytes_lt bs

/-- **An eight-byte load** is the word of the eight bytes. -/
theorem load8_eq (env : Env) (r off : Nat) :
    env.load r off 8 = (wordOf env.mem0 (env.base r + BitVec.ofNat 64 off)).toBitVec := by
  unfold Env.load wordOf bytesFrom
  have hbs : ((List.range 8).map fun i ↦
      (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i))).getD 0) =
      (List.range 8).map fun i ↦
        (env.mem0.get? (env.base r + BitVec.ofNat 64 off + BitVec.ofNat 64 i)).getD 0 := by
    apply List.map_congr_left; intro i _; rw [addr_add]
  rw [hbs, ofBytes_natCast, natOfBytes_eq_leNat]
  generalize ((List.range 8).map fun i ↦
    (env.mem0.get? (env.base r + BitVec.ofNat 64 off + BitVec.ofNat 64 i)).getD 0) = bs
  have hlt := leNat_lt bs
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  omega

/-- **Bytes above SP survive a call** whose changes are in the stack below SP. -/
theorem BytesAt.of_call {d d' : DataMem} {a sp : BitVec 64} {bs : List UInt8} {N : Nat}
    (h : NativeRustcVm.BytesAt d a bs)
    (hs : SameOutside d d' (InRange (sp - BitVec.ofNat 64 N) N)) (hN : N ≤ sp.toNat)
    (ha : sp.toNat ≤ a.toNat) (hnw : a.toNat + bs.length ≤ 2 ^ 64) :
    NativeRustcVm.BytesAt d' a bs := by
  refine NativeRustcVm.BytesAt.of_sameOutside_apart h hs ?_ hnw ?_
  · unfold NativeRustcVm.Apart; rw [toNat_sub_ofNat hN]; omega
  · unfold NativeRustcVm.NoWrap; rw [toNat_sub_ofNat hN]; have := sp.isLt; omega

/-- The first `j` of the `n` bytes `bytesOf` reads. -/
theorem bytesOf_take (d : DataMem) (a : BitVec 64) {j n : Nat} (h : j ≤ n) :
    (NativeRustcArm.bytesOf d a n).take j = NativeRustcArm.bytesOf d a j := by
  simp [NativeRustcArm.bytesOf, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- A one-region environment: register `r` points `o` bytes into the region. -/
theorem match_one [Labels] {st : MachineData} {a : BitVec 64} {n : Nat} {r : XReg} {o : Int}
    (h : (st.regs.getXReg r).toBitVec = a + BitVec.ofInt 64 o) :
    Match (Env.ofMachine st [(a, n)]) (init [(n, false)] .sp [(r, .ptr 0 o)]) st :=
  match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl ⟨h, trivial⟩ trivial trivial
    trivial

/-- A one-region environment is well formed. -/
theorem wf_one {m : MachineData} {a : BitVec 64} {n : Nat} (h : Mapped m.dmem a n)
    (hn : NoWrap a n) : (Env.ofMachine m [(a, n)]).WF :=
  Env.wf_of ⟨⟨h, hn⟩, trivial⟩ (List.pairwise_singleton _ _)

/-- The prologue's slots: register `r`'s entry value at `fb + o` for each `(o, r)`. -/
@[expose] def SlotsAt (d : DataMem) (fb : BitVec 64) (m0 : MachineData)
    (slots : List (Nat × XReg)) : Prop :=
  ∀ p ∈ slots, BytesAt d (fb + BitVec.ofNat 64 p.1)
    ((List.range 8).map (byteOf (m0.regs.getXReg p.2).toBitVec))

theorem ofInt_ofBytes_byteOf (x : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map (byteOf x))) = x := by
  have := ofBytes_byteOf x 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [this, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- **A slot read back** is the entry's register. -/
theorem slot_load [Labels] {env : Env} {m0 : MachineData} {slots : List (Nat × XReg)} {r : Nat}
    (h : SlotsAt env.mem0 (env.base r) m0 slots) {o : Nat} {x : XReg} (hp : (o, x) ∈ slots) :
    env.load r o 8 = (m0.regs.getXReg x).toBitVec := by
  rw [Env.load_of_bytesAt (by simp) (h _ hp), ofInt_ofBytes_byteOf]

/-- **The prologue's writes** fill the slots. -/
theorem slotsAt_of_writes [Labels] {m0 m : MachineData} {rs : List (BitVec 64 × Nat)}
    {S : SState} {fb : BitVec 64} {F : Nat} {slots : List (Nat × XReg)}
    (hm : Match (Env.ofMachine m0 ((fb, F) :: rs)) S m)
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i)) :
    SlotsAt m.dmem fb m0 slots := fun p hp ↦
  hm.bytesAt_write (r := 0) rfl (hw p hp).1 (hw p hp).2

/-- The callee-saved registers. -/
@[expose] def calleeRegs : List XReg :=
  [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

theorem mem_calleeRegs {r : XReg} (h : calleeSaved r = true) : r ∈ calleeRegs := by
  cases r <;> simp_all [calleeSaved, calleeRegs]

/-- The callee-saved registers and X30. -/
@[expose] def savedRegs : List XReg :=
  [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29, .X30]

theorem mem_savedRegs {r : XReg} (h : calleeSaved r = true) : r ∈ savedRegs := by
  cases r <;> simp_all [calleeSaved, savedRegs]

/-- The epilogue's registers: each slot's register its load from the frame (region 0), the other
callee-saved registers and X30 kept, SP the frame's top. -/
@[expose] def restores (slots : List (Nat × XReg)) (F : Nat) (S : SState) : Bool :=
  savedRegs.all (fun r ↦ S.reg r == some (match slots.find? (·.2 == r) with
    | some p => .load 0 p.1 8
    | none => .reg r)) && S.sp == .ptr 0 (F : Int)

theorem find?_mem {slots : List (Nat × XReg)} {r : XReg} {p : Nat × XReg}
    (h : slots.find? (·.2 == r) = some p) : p ∈ slots ∧ p.2 = r := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, XReg.eq_of_beq this⟩

theorem find?_none {slots : List (Nat × XReg)} {r : XReg}
    (h : slots.find? (·.2 == r) = none) : r ∉ slots.map (·.2) := by
  intro hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have := List.find?_eq_none.mp h p hp
  exact absurd this (by cases p.2 <;> decide)

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (NativeRustcVm.wordBytes v)) = v.toBitVec := by
  have hw := Hasher.wordBytes_ofBitVec v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  unfold NativeRustcVm.wordBytes
  rw [hw, hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := v.toBitVec.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

/-- **A word at a region's offset** is what the environment loads there. -/
theorem load_word {env : Env} {r off : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 off) v) :
    env.load r off 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (NativeRustcVm.length_wordBytes v) h, ofInt_ofBytes_wordBytes]

/-- **A word a block wrote**: an 8-byte write of `v` at offset `o` of region `r`. -/
theorem Match.wordAt_write [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := by
  have := hm.bytesAt_write hb hle hw
  unfold NativeRustcVm.WordAt NativeRustcVm.wordBytes
  rw [Hasher.wordBytes_ofBitVec]
  exact this

/-- **Where a block wrote**: in region `r`, when every write of the block is there. -/
theorem Written.inRange {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hnw : b.toNat + sz ≤ 2 ^ 64)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz) {p : BitVec 64} (h : Written env S p) :
    InRange b sz p := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hle⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  exact (NativeRustcVm.inRange_iff hnw).mpr ⟨by omega, by omega⟩

/-! ## The stack below a frame -/

section
variable {m m' : MachineData} {f N N' : Nat}

theorem toNat_stackBelow (h : N ≤ m.regs.SP.toNat) :
    (stackBelow m N).toNat = m.regs.SP.toNat - N :=
  NativeRustcVm.toNat_sub_ofNat h

/-- The SP `f` bytes below. -/
theorem toNat_sp_sub (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f)
    (hf : f ≤ m.regs.SP.toNat) : m'.regs.SP.toNat = m.regs.SP.toNat - f := by
  show m'.regs.SP.toBitVec.toNat = _
  rw [hsp]
  exact NativeRustcVm.toNat_sub_ofNat hf

/-- **A callee's `StackOk`** from its caller's, `f` bytes of frame (a multiple of `16`) further
down, every byte of the caller kept. -/
theorem StackOk.sub (h : StackOk m N)
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hf : f % 16 = 0)
    (hfN : f + N' ≤ N) (hk : Kept m.dmem m'.dmem) : StackOk m' N' := by
  obtain ⟨hal, hN, hmap⟩ := h
  have h1 := toNat_sp_sub hsp (by omega)
  have hs : m.regs.SP.toNat = m.regs.SP.toBitVec.toNat := rfl
  have hs' : m'.regs.SP.toNat = m'.regs.SP.toBitVec.toNat := rfl
  have hlt := m.regs.SP.toBitVec.isLt
  refine ⟨by omega, by omega, fun i hi ↦ hk _ ?_⟩
  have : m'.regs.SP.toBitVec - BitVec.ofNat 64 N' + BitVec.ofNat 64 i =
      m.regs.SP.toBitVec - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - f - N' + i) := by
    apply BitVec.eq_of_toNat_eq
    have e1 : (m'.regs.SP.toBitVec - BitVec.ofNat 64 N').toNat = m'.regs.SP.toNat - N' :=
      NativeRustcVm.toNat_sub_ofNat (by omega)
    have e2 : (m.regs.SP.toBitVec - BitVec.ofNat 64 N).toNat = m.regs.SP.toNat - N :=
      NativeRustcVm.toNat_sub_ofNat hN
    rw [NativeRustcVm.toNat_add_ofNat (by rw [e1]; omega),
      NativeRustcVm.toNat_add_ofNat (by rw [e2]; omega), e1, e2]
    omega
  rw [this]
  exact hmap _ (by omega)

end

/-! ## The stack -/

section
variable {m m' : MachineData} {f N N' : Nat}

/-- **A callee's stack is inside its caller's**, `f` bytes of frame further down. -/
theorem inRange_stack_sub {p : BitVec 64} (h : InRange (stackBelow m' N') N' p)
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hfN : f + N' ≤ N)
    (hN : N ≤ m.regs.SP.toNat) : InRange (stackBelow m N) N p := by
  have h1 := toNat_sp_sub hsp (by omega)
  have h2 : (stackBelow m' N').toNat = m'.regs.SP.toNat - N' := toNat_stackBelow (by omega)
  have h3 : (stackBelow m N).toNat = m.regs.SP.toNat - N := toNat_stackBelow hN
  have hs := m.regs.SP.toNat_lt
  have hs' : m.regs.SP.toNat = m.regs.SP.toBitVec.toNat := rfl
  refine NativeRustcVm.InRange.mono h ?_ ?_ ?_ ?_
  · unfold NativeRustcVm.NoWrap; omega
  · unfold NativeRustcVm.NoWrap; omega
  · omega
  · omega

/-- **The frame is inside the stack**: the `f` bytes below SP, among the `N ≥ f`. -/
theorem inRange_frame {p : BitVec 64}
    (h : InRange (m.regs.SP.toBitVec - BitVec.ofNat 64 f) f p) (hf : f ≤ N)
    (hN : N ≤ m.regs.SP.toNat) : InRange (stackBelow m N) N p :=
  inRange_stack_sub (m' := m) (f := 0) (N' := f) (by simpa [stackBelow] using h)
    (by simp) (by omega) hN

/-- A range apart from a caller's stack is apart from a callee's, `f` bytes further down. -/
theorem offStack_sub {x : BitVec 64} {n : Nat} (h : OffStack m x n N)
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hfN : f + N' ≤ N)
    (hN : N ≤ m.regs.SP.toNat) : OffStack m' x n N' := by
  have h1 := toNat_sp_sub hsp (by omega)
  have h2 : (stackBelow m' N').toNat = m'.regs.SP.toNat - N' := toNat_stackBelow (by omega)
  unfold OffStack Apart at h ⊢
  rw [toNat_stackBelow hN] at h
  omega

/-- A range apart from the stack is apart from the frame, its top `f` bytes. -/
theorem apart_frame {x : BitVec 64} {n : Nat} (h : OffStack m x n N) (hf : f ≤ N)
    (hN : N ≤ m.regs.SP.toNat) :
    Apart x n (m.regs.SP.toBitVec - BitVec.ofNat 64 f) f := by
  have := offStack_sub (m' := m) (f := 0) (N' := f) h (by simp) (by omega) hN
  simpa [OffStack, stackBelow] using this

end

/-- The frame's base is 16-byte aligned. -/
theorem frame_aligned {m : MachineData} {F S : Nat} (hS : StackOk m S) (hF : F ≤ S)
    (h16 : F % 16 = 0) : (m.regs.SP.toBitVec - BitVec.ofNat 64 F).toNat % 16 = 0 := by
  rw [(frame_ok hS hF).2.2]
  have := hS.1
  have : m.regs.SP.toNat = m.regs.SP.toBitVec.toNat := rfl
  omega

/-! ## Sub-ranges of arguments -/

theorem Readable.sub {m : MachineData} {a : BitVec 64} {N o n : Nat} (h : Readable m a N)
    (hle : o + n ≤ N) : Readable m (a + BitVec.ofNat 64 o) n :=
  ⟨fun i hi ↦ by rw [addr_add]; exact h.1 _ (by omega), NativeRustcVm.NoWrap.sub h.2 hle⟩

theorem OffStack.sub {m : MachineData} {a : BitVec 64} {N o n S : Nat} (h : OffStack m a N S)
    (hw : NoWrap a N) (hle : o + n ≤ N) : OffStack m (a + BitVec.ofNat 64 o) n S := by
  unfold OffStack Apart at *
  unfold NoWrap at hw
  rcases NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by omega) with h1 | ⟨h1, h2⟩ <;>
    rw [h1] <;> omega

theorem WhirIn.sub {m : MachineData} {a : BitVec 64} {N o n S : Nat} (h : WhirIn m a N S)
    (hle : o + n ≤ N) : WhirIn m (a + BitVec.ofNat 64 o) n S :=
  ⟨Readable.sub h.1 hle, OffStack.sub h.2 h.1.2 hle⟩

/-- A slice inside an argument: readable and apart from the stack. -/
theorem WhirIn.sliceOk {m : MachineData} {a : BitVec 64} {N o S : Nat} {n : UInt64}
    (h : WhirIn m a N S) (hle : o + 16 * n.toNat ≤ N) :
    SliceOk m (UInt64.ofBitVec (a + BitVec.ofNat 64 o)) n S :=
  WhirIn.sub h hle

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := rfl

/-! ## Changes -/

/-- `ChangesIn` is transitive, the second state's stack inside the first's. -/
theorem ChangesIn.trans {m m' m'' : MachineData} {N N' f : Nat} {rs : List Region}
    (h : ChangesIn m m' N rs) (h' : ChangesIn m' m'' N' rs)
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hfN : f + N' ≤ N)
    (hN : N ≤ m.regs.SP.toNat) : ChangesIn m m'' N rs := fun p hp ↦ by
  rw [h' p fun hp' ↦ hp (hp'.elim .inl fun hs ↦ .inr (inRange_stack_sub hs hsp hfN hN))]
  exact h p hp

/-- A callee's stack changes, inside a caller's stack: a `ChangesIn` of the caller. -/
theorem ChangesIn.of_stack {m m' m'' : MachineData} {N N' f : Nat} {rs : List Region}
    (h : ChangesIn m m' N rs)
    (h' : SameOutside m'.dmem m''.dmem (InRange (stackBelow m' N') N'))
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hfN : f + N' ≤ N)
    (hN : N ≤ m.regs.SP.toNat) : ChangesIn m m'' N rs := fun p hp ↦ by
  rw [h' p fun hs ↦ hp (.inr (inRange_stack_sub hs hsp hfN hN))]
  exact h p hp

/-- `ChangesIn` with more regions. -/
theorem ChangesIn.mono {m m' : MachineData} {N : Nat} {rs rs' : List Region}
    (h : ChangesIn m m' N rs) (hr : ∀ r ∈ rs, r ∈ rs') : ChangesIn m m' N rs' :=
  fun p hp ↦ h p fun h' ↦ hp (h'.elim (fun hi ↦ .inl (hi.mono hr)) .inr)

theorem ChangesIn.refl (m : MachineData) (N : Nat) (rs : List Region) : ChangesIn m m N rs :=
  fun _ _ ↦ rfl

/-- `Changes` of no output: the stack only. -/
theorem changesIn_of_changes {m m' : MachineData} {N : Nat} (h : Changes m m' N 0 0) :
    SameOutside m.dmem m'.dmem (InRange (stackBelow m N) N) :=
  fun p hp ↦ h p fun h' ↦ h'.elim (fun h0 ↦ absurd h0 (by unfold InRange; omega)) hp

/-! ## The frame -/

/-- **A function's body**: `F` bytes of frame below the entry's SP `m0`, the prologue's slots
there, the other callee-saved registers the entry's, memory as at the entry but in the outputs
`outs` and the `S` bytes of stack, every mapped byte still there. -/
structure Frame (m0 : MachineData) (F S : Nat) (slots : List (Nat × XReg)) (outs : List Region)
    (st : MachineData) : Prop where
  sp : st.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 F
  frame : SlotsAt st.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) m0 slots
  regs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → st.regs.getXReg r = m0.regs.getXReg r
  same : ChangesIn m0 st S outs
  kept : Kept m0.dmem st.dmem

/-- The callee-saved registers no slot saves. -/
@[expose] def freeRegs (slots : List (Nat × XReg)) : List XReg :=
  calleeRegs.filter fun r ↦ !(slots.map (·.2)).contains r

theorem mem_freeRegs {slots : List (Nat × XReg)} {r : XReg} (hr : calleeSaved r = true)
    (hn : r ∉ slots.map (·.2)) : r ∈ freeRegs slots := by
  refine List.mem_filter.mpr ⟨mem_calleeRegs hr, ?_⟩
  rw [Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false]
  intro x hx hb
  exact hn (XReg.eq_of_beq hb ▸ hx)

/-- Where every write of a block is in region `r`, memory changes only there. -/
theorem same_region [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    (hall : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz) :
    SameOutside env.mem0 m.dmem (InRange b sz) := by
  refine fun p hp ↦ hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ hp ?_
  obtain ⟨hr, hle⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  rw [Sym.inRange_iff (hwf.noWrap r b sz hb)]
  omega

/-- Where every write of a block is in the first `len` bytes of region `r`, memory changes only
there. -/
theorem same_region_le [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz len : Nat} (hb : env.regions[r]? = some (b, sz))
    (hlen : len ≤ sz) (hall : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ len) :
    SameOutside env.mem0 m.dmem (InRange b len) := by
  refine fun p hp ↦ hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ hp ?_
  obtain ⟨hr, hle⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  have := hwf.noWrap r b sz hb
  rw [Sym.inRange_iff (by omega)]
  omega

section
variable {m0 st st' : MachineData} {F S N : Nat} {slots : List (Nat × XReg)} {outs : List Region}

/-- A callee's `StackOk` in a body. -/
theorem Frame.stackOk (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hF : F % 16 = 0)
    (hle : F + N ≤ S) : StackOk st N :=
  StackOk.sub hS hb.sp hF hle hb.kept

/-- An argument apart from the caller's stack is apart from a callee's. -/
theorem Frame.offStack (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hle : F + N ≤ S)
    {x : BitVec 64} {n : Nat} (h : OffStack m0 x n S) : OffStack st x n N :=
  offStack_sub h hb.sp hle hS.2.1

/-- An argument readable at the entry is readable in a body. -/
theorem Frame.readable (hb : Frame m0 F S slots outs st) {x : BitVec 64} {n : Nat}
    (h : Readable m0 x n) : Readable st x n :=
  ⟨fun i hi ↦ hb.kept _ (h.1 i hi), h.2⟩

/-- A slice readable at the entry, apart from the caller's stack. -/
theorem Frame.sliceOk (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hle : F + N ≤ S)
    {a n : UInt64} (h : SliceOk m0 a n S) : SliceOk st a n N :=
  ⟨hb.readable h.1, hb.offStack hS hle h.2⟩

/-- **Bytes a body did not change**: outside the outputs and the stack. -/
theorem Frame.get?_eq (hb : Frame m0 F S slots outs st) {p : BitVec 64}
    (h : ¬(InAny outs p ∨ InRange (stackBelow m0 S) S p)) : st.dmem.get? p = m0.dmem.get? p :=
  hb.same p h

/-- A state with the entry's memory, callee-saved registers and SP: a body without frame. -/
theorem Frame.of_saved (hs : Saved m0 st) (hd : st.dmem = m0.dmem) : Frame m0 0 S [] outs st where
  sp := by rw [hs.2.1]; simp
  frame := fun _ hp ↦ absurd hp List.not_mem_nil
  regs := fun r hr _ ↦ hs.1 r hr
  same := fun p _ ↦ by rw [hd]
  kept := hs.2.2

/-- **A step of a body**: the next state keeps the free callee-saved registers, SP and the mapped
bytes, and changes memory only in `R`, among the outputs and the stack and apart from the
slots. -/
theorem Frame.change (hb : Frame m0 F S slots outs st) {R : BitVec 64 → Prop}
    (hsame : SameOutside st.dmem st'.dmem R)
    (hR : ∀ p, R p → InAny outs p ∨ InRange (stackBelow m0 S) S p)
    (hfr : ∀ q ∈ slots, ∀ i < 8,
      ¬R (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 q.1 + BitVec.ofNat 64 i))
    (hregs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) →
      st'.regs.getXReg r = st.regs.getXReg r)
    (hsp : st'.regs.SP = st.regs.SP) (hkept : Kept st.dmem st'.dmem) :
    Frame m0 F S slots outs st' := by
  refine ⟨hsp ▸ hb.sp, fun q hq i hi ↦ ?_, fun r hr hn ↦ (hregs r hr hn).trans (hb.regs r hr hn),
    fun p hp ↦ ?_, fun p hp ↦ hkept p (hb.kept p hp)⟩
  · simp only [List.length_map, List.length_range] at hi
    rw [hsame _ (hfr q hq i hi)]
    exact hb.frame q hq i hi
  · rw [hsame p fun h ↦ hp (hR p h)]
    exact hb.same p hp

/-- **A call** keeps a body: the callee changes only its stack below the body's SP, keeps the
callee-saved registers, SP and the mapped bytes. -/
theorem Frame.call (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hle : F + N ≤ S)
    (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hsame : SameOutside st.dmem st'.dmem (InRange (stackBelow st N) N)) (hsaved : Saved st st') :
    Frame m0 F S slots outs st' := by
  have hS' := hS.2.1
  refine hb.change hsame (fun p h ↦ .inr (inRange_stack_sub h hb.sp hle hS')) (fun q hq i hi ↦ ?_)
    (fun r hr _ ↦ hsaved.1 r hr) hsaved.2.1 hsaved.2.2
  unfold stackBelow
  rw [hb.sp, addr_add]
  have := hslots q hq
  have := m0.regs.SP.toNat_lt
  exact not_inRange_below (by omega)

/-- `S₁` keeps `S₀`'s SP and the registers `rs`. -/
@[expose] def keepsRegs (S₀ S₁ : SState) (rs : List XReg) : Bool :=
  rs.all (fun r ↦ (S₀.reg r).isSome && S₁.reg r == S₀.reg r) && S₁.sp == S₀.sp

/-- **A block** keeps a body: it keeps the free callee-saved registers and SP, and writes into
region `r` only, a range among the outputs and the stack, apart from the slots. -/
theorem Frame.of_block [Labels] {env : Env} {S₀ S₁ : SState} (hb : Frame m0 F S slots outs st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ (freeRegs slots) = true) {r : Nat} {a : BitVec 64} {n len : Nat}
    (hr : env.regions[r]? = some (a, n)) (hlen : len ≤ n)
    (hall : ∀ w ∈ S₁.mem, w.r = r ∧ w.off + w.n ≤ len)
    (hR : ∀ p, InRange a len p → InAny outs p ∨ InRange (stackBelow m0 S) S p)
    (hfr : ∀ q ∈ slots, ∀ i < 8,
      ¬InRange a len (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 q.1 +
        BitVec.ofNat 64 i)) :
    Frame m0 F S slots outs st' := by
  simp only [keepsRegs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
  obtain ⟨hregs, hsp⟩ := hk
  refine hb.change (hd ▸ same_region_le hm hwf hr hlen hall) hR hfr (fun r' hr' hn ↦ ?_)
    (Match.sp_eq hm₀ hm hsp) (hd ▸ hm.kept hwf)
  obtain ⟨hs, he⟩ := hregs r' (mem_freeRegs hr' hn)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Match.reg_eq hm₀ hm hv (he.trans hv)

/-- **A block without writes** keeps a body. -/
theorem Frame.of_regs [Labels] {env : Env} {S₀ S₁ : SState} (hb : Frame m0 F S slots outs st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsRegs S₀ S₁ (freeRegs slots) = true) (hmem : S₁.mem = []) :
    Frame m0 F S slots outs st' := by
  simp only [keepsRegs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hk
  obtain ⟨hregs, hsp⟩ := hk
  refine hb.change (R := fun _ ↦ False) (fun p _ ↦ by rw [hm.dmem_eq hwf hmem, hd])
    (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) (fun r' hr' hn ↦ ?_)
    (Match.sp_eq hm₀ hm hsp) (hd ▸ hm.kept hwf)
  obtain ⟨hs, he⟩ := hregs r' (mem_freeRegs hr' hn)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Match.reg_eq hm₀ hm hv (he.trans hv)

/-- **Frame bytes survive a call**: the callee changes only the stack below the body's SP. -/
theorem Frame.bytes_call (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hle : F + N ≤ S)
    (hsame : SameOutside st.dmem st'.dmem (InRange (stackBelow st N) N)) {o : Nat}
    {bs : List UInt8} (hlen : o + bs.length ≤ F)
    (h : NativeRustcVm.BytesAt st.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 o)
      bs) :
    NativeRustcVm.BytesAt st'.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 o)
      bs := by
  rcases Nat.eq_zero_or_pos bs.length with h0 | hpos
  · rw [List.length_eq_zero_iff.mp h0]; exact NativeRustcVm.BytesAt.nil _ _
  obtain ⟨-, hnw, he⟩ := frame_ok hS (show F ≤ S by omega)
  unfold NoWrap at hnw
  have hS' : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have hsp : st.regs.SP.toBitVec.toNat = m0.regs.SP.toBitVec.toNat - F := by rw [hb.sp, he]
  refine BytesAt.of_call h (sp := st.regs.SP.toBitVec) hsame (by omega) ?_ ?_ <;>
    rw [toNat_add_ofNat' (by omega)] <;> omega

/-- **An argument's bytes in a body**: those of a region apart from the outputs and the
stack. -/
theorem Frame.get?_arg (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) {a : BitVec 64}
    {n : Nat} (hin : WhirIn m0 a n S) (hap : ∀ r ∈ outs, Apart a n r.addr r.size ∧ NoWrap r.addr r.size) :
    ∀ j < n, st.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  fun _ hj ↦ hb.get?_eq fun h ↦ h.elim
    (fun ⟨r, hr, hp⟩ ↦ not_inRange_of_apart (hap r hr).1 hin.1.2 (hap r hr).2 hj hp)
    (not_inRange_of_apart hin.2 hin.1.2 (stack_noWrap hS) hj)

/-- The frame's base `F` below the entry's SP. -/
theorem Frame.fb_toNat (hS : StackOk m0 S) (hF : F ≤ S) :
    (m0.regs.SP.toBitVec - BitVec.ofNat 64 F).toNat = m0.regs.SP.toBitVec.toNat - F :=
  (frame_ok hS hF).2.2

/-- A range inside the frame is inside the stack. -/
theorem inRange_frame_sub (hS : StackOk m0 S) (hF : F ≤ S) {o n : Nat} (hle : o + n ≤ F)
    {p : BitVec 64} (h : InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 o) n p) :
    InRange (stackBelow m0 S) S p :=
  inRange_frame (NativeRustcVm.InRange.of_sub h (frame_ok hS hF).2.1 hle) hF hS.2.1

/-- A range of the frame apart from the slots. -/
theorem not_inRange_slot (hS : StackOk m0 S) (hF : F ≤ S) {o n q i : Nat} (hle : o + n ≤ F)
    (hq : q + 8 ≤ F) (hi : i < 8) (hap : o + n ≤ q ∨ q + 8 ≤ o) :
    ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 o) n
      (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 q + BitVec.ofNat 64 i) := by
  obtain ⟨-, hnw, -⟩ := frame_ok hS hF
  unfold NoWrap at hnw
  by_cases hn : n = 0
  · subst hn; unfold InRange; omega
  have h1 := NativeRustcVm.NoWrap.sub hnw hle
  unfold NativeRustcVm.NoWrap at h1
  rw [addr_add, Sym.inRange_iff h1, toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
  omega

/-- **The entry block**: from the entry, with the frame as region 0 of the environment, the
prologue's writes in the frame and the other callee-saved registers untouched make a body. -/
theorem Frame.of_entry [Labels] {rs : List (BitVec 64 × Nat)} {S' : SState} (hS : StackOk m0 S)
    (hF : F ≤ S) (hwf : (Env.ofMachine m0 ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)).WF)
    (hm : Match (Env.ofMachine m0 ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)) S' st)
    (hsp : S'.sp = .ptr 0 0)
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S'.mem = some (.reg p.2, i))
    (hregs : ∀ r ∈ freeRegs slots, S'.reg r = some (.reg r))
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Frame m0 F S slots outs st := by
  obtain ⟨-, -, he⟩ := frame_ok hS hF
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  refine ⟨?_, slotsAt_of_writes hm hw, fun r hr hn ↦ ?_, fun p hp ↦ ?_, hm.kept hwf⟩
  · rw [hm.sp, hsp]; simp [Sym.eval]
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs r _ (hregs r (mem_freeRegs hr hn))]
    rfl
  · refine hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb, h1, h2⟩ ↦ hp (Or.inr ?_)
    obtain ⟨hr, hoff⟩ := hmem w hw'
    rw [hr] at hb
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [Sym.inRange_iff (stack_noWrap hS), show (stackBelow m0 S).toNat = m0.regs.SP.toBitVec.toNat - S
      from toNat_sub_ofNat hSle]
    have := m0.regs.SP.toBitVec.isLt
    rw [he] at h1 h2
    omega

/-- **A call writing a frame range**: the callee changes its stack below the body's SP and the
`n` bytes at `o` of the frame, below the slots. -/
theorem Frame.call_out (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S) (hle : F + N ≤ S)
    {o n : Nat} (hon : o + n ≤ F) (hslots : ∀ p ∈ slots, o + n ≤ p.1 ∧ p.1 + 8 ≤ F)
    (hsame : SameOutside st.dmem st'.dmem (fun p ↦
      NativeRustcVm.InAny [⟨m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 o, n⟩] p ∨
        InRange (stackBelow st N) N p))
    (hsaved : Saved st st') : Frame m0 F S slots outs st' := by
  have hS' := hS.2.1
  refine hb.change hsame (fun p h ↦ h.elim (fun ⟨r, hr, hp⟩ ↦ ?_)
      fun h ↦ .inr (inRange_stack_sub h hb.sp hle hS')) (fun q hq i hi h ↦ ?_)
    (fun r hr _ ↦ hsaved.1 r hr) hsaved.2.1 hsaved.2.2
  · simp only [List.mem_singleton] at hr
    subst hr
    exact .inr (inRange_frame_sub hS (by omega) hon hp)
  · obtain ⟨h1, h2⟩ := hslots q hq
    rcases h with ⟨r, hr, hp⟩ | hp
    · simp only [List.mem_singleton] at hr
      subst hr
      exact not_inRange_slot hS (by omega) hon h2 hi (.inl h1) hp
    · revert hp
      unfold stackBelow
      rw [hb.sp, addr_add]
      have := m0.regs.SP.toNat_lt
      exact not_inRange_below (by omega)

/-- **Frame bytes such a call keeps**: apart from the range it writes. -/
theorem Frame.bytes_call_out (hb : Frame m0 F S slots outs st) (hS : StackOk m0 S)
    (hle : F + N ≤ S) {o n o' : Nat} {bs : List UInt8} (hlen : o' + bs.length ≤ F)
    (hap : o' + bs.length ≤ o ∨ o + n ≤ o') (hon : o + n ≤ F)
    (hsame : SameOutside st.dmem st'.dmem (fun p ↦
      NativeRustcVm.InAny [⟨m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 o, n⟩] p ∨
        InRange (stackBelow st N) N p))
    (h : NativeRustcVm.BytesAt st.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F +
      BitVec.ofNat 64 o') bs) :
    NativeRustcVm.BytesAt st'.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 o')
      bs := by
  refine NativeRustcVm.BytesAt.of_sameOutside h hsame fun i hi hp ↦ ?_
  obtain ⟨-, hnw, he⟩ := frame_ok hS (show F ≤ S by omega)
  unfold NoWrap at hnw
  rcases hp with ⟨r, hr, hp⟩ | hp
  · simp only [List.mem_singleton] at hr
    subst hr
    revert hp
    show ¬InRange _ n _
    by_cases hn : n = 0
    · subst hn; unfold InRange; omega
    rw [addr_add, Sym.inRange_iff (NativeRustcVm.NoWrap.sub hnw (by omega)),
      toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  · revert hp
    unfold stackBelow
    rw [hb.sp, addr_add]
    have := m0.regs.SP.toNat_lt
    have hS' : S ≤ m0.regs.SP.toNat := hS.2.1
    exact not_inRange_below (by omega)

/-- **The epilogue**: run from a body with the frame as region 0, it restores the entry's
callee-saved registers, X30 and SP, and keeps the mapped bytes. -/
theorem Frame.ret [Labels] {rs : List (BitVec 64 × Nat)} {S₁ : SState}
    (hb : Frame m0 F S slots outs st)
    (hm : Match (Env.ofMachine st ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)) S₁ st')
    (hwf : (Env.ofMachine st ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)).WF)
    (hx30 : (XReg.X30) ∈ slots.map (·.2)) (hr : restores slots F S₁ = true) :
    Saved m0 st' ∧ st'.regs.X30 = m0.regs.X30 := by
  simp only [restores, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hbase : (Env.ofMachine st ((m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F) :: rs)).base 0 =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 F := rfl
  have hreg : ∀ r ∈ savedRegs, st'.regs.getXReg r = m0.regs.getXReg r := by
    intro r hrs
    have h := hm.regs r _ (hr r hrs)
    cases hf : slots.find? (·.2 == r) with
    | some p =>
      obtain ⟨hp, rfl⟩ := find?_mem hf
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      exact slot_load (r := 0) (by rw [hbase]; exact hb.frame) hp
    | none =>
      rw [hf] at h
      apply UInt64.toBitVec_inj.mp
      rw [h]
      show (st.regs.getXReg r).toBitVec = _
      by_cases hc : calleeSaved r = true
      · rw [hb.regs r hc (find?_none hf)]
      · have : r = .X30 := by
          cases r <;> simp_all [calleeSaved, savedRegs]
        subst this
        exact absurd hx30 (find?_none hf)
  refine ⟨⟨fun r hc ↦ hreg r (mem_savedRegs hc), ?_, fun p hp ↦ hm.kept hwf p (hb.kept p hp)⟩,
    hreg .X30 (by simp [savedRegs])⟩
  apply UInt64.toBitVec_inj.mp
  rw [hm.sp, hsp]
  simp only [Sym.eval, hbase]
  rw [show BitVec.ofInt 64 (F : Int) = BitVec.ofNat 64 F from rfl, BitVec.sub_add_cancel]

end

/-! ## Values the executor computes -/

/-- An unsigned comparison with a literal. -/
theorem ult_ofNat {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 n) = decide (x.toNat < n) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- A word's bit vector against a literal. -/
theorem toBitVec_ult_ofNat {w : UInt64} {n : Nat} (hn : n < 2 ^ 64) :
    w.toBitVec.ult (BitVec.ofNat 64 n) = decide (w.toNat < n) := ult_ofNat hn

theorem toBitVec_beq_zero (w : UInt64) : (w.toBitVec == 0#64) = decide (w = 0) := by
  by_cases h : w = 0
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    exact fun h' ↦ h (UInt64.toBitVec_inj.mp (h'.trans rfl))

/-- A register from its bit vector. -/
theorem reg_eq {x : UInt64} {v : BitVec 64} (h : x.toBitVec = v) : x = UInt64.ofBitVec v := by
  rw [← h]

theorem natCast_toUInt64_toNat {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem bv_beq_toNat (a b : BitVec 64) : (a == b) = decide (a.toNat = b.toNat) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [beq_eq_false_iff_ne.mpr h]
    exact (decide_eq_false fun h' ↦ h (BitVec.eq_of_toNat_eq h')).symm

theorem bv_ult_toNat (a b : BitVec 64) : a.ult b = decide (a.toNat < b.toNat) := rfl

theorem Readable.mono {m : MachineData} {a : BitVec 64} {N n : Nat} (h : Readable m a N)
    (hle : n ≤ N) : Readable m a n :=
  ⟨fun i hi ↦ h.1 i (by omega), NativeRustcVm.NoWrap.mono h.2 hle⟩

/-- **Bytes a block kept**: in region `r`, a range no write of the block touches. -/
theorem Match.keep [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    {o len : Nat} (hle : o + len ≤ sz)
    (hall : ∀ w ∈ S.mem, w.r = r ∧ (w.off + w.n ≤ o ∨ o + len ≤ w.off)) :
    ∀ i < len, m.dmem.get? (b + BitVec.ofNat 64 (o + i)) =
      env.mem0.get? (b + BitVec.ofNat 64 (o + i)) := by
  intro i hi
  refine hm.get?_mem0 hwf fun ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ ?_
  obtain ⟨hr, hoff⟩ := hall w hw
  rw [hr, hb] at hb'
  cases hb'
  have hnw := hwf.noWrap r b sz hb
  rw [toNat_add_ofNat' (by omega)] at h1 h2
  omega

end

end NativeRustcVmArm.Whir
