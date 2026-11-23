module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcArm.Sym
public import NativeRustcVmArm.Spec.Arrays
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# The array functions' proofs: what they share

- Loads: the eight bytes the executor loads are `wordOf` of them (`load8_eq`), sixteen an `ewOf`
  (`ewOf_loads`).
- Addresses: a callee's stack inside the caller's (`inRange_mono`), apart from the caller's frame
  (`not_inRange_below`).
- The frame: the prologue's slots (`SlotsAt`, from the writes `slotsAt_of_writes`), read back
  (`slot_load`); the state of a function's body, `F` bytes of frame below the entry's SP, `S`
  bytes of stack in all (`Body`): kept across a call of `EW::mul` (`Body.call`, its precondition
  `Body.ewMulPre`) and a block that writes nothing (`Body.of_block`); the epilogue restores the
  entry's registers (`restores`, `Body.saved`).
-/

namespace NativeRustcVmArm.Arrays

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm (wordOf ewOf ewsOf bytesFrom leNat)

public section

/-! ## Runs -/

/-- The state `exec ds S` ends in (`S` where it fails). -/
@[expose] def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

/-! ## Loads -/

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
  have hbs : ((List.range 8).map fun i ↦ (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i))).getD 0) =
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

/-- **Sixteen bytes loaded as two words** are an `E` element. -/
theorem ewOf_loads (env : Env) (r off : Nat) :
    (ewOf env.mem0 (env.base r + BitVec.ofNat 64 off)) =
      ⟨UInt64.ofBitVec (env.load r off 8), UInt64.ofBitVec (env.load r (off + 8) 8)⟩ := by
  rw [load8_eq, load8_eq, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec, ← addr_add]
  rfl

/-! ## Addresses -/

theorem inRange_mono {a p : BitVec 64} {c n N : Nat} (h : InRange (a + BitVec.ofNat 64 c) n p)
    (hle : c + n ≤ N) : InRange a N p := by
  unfold InRange at *
  by_cases hN : N < 2 ^ 64
  · have e : p - a = (p - (a + BitVec.ofNat 64 c)) + BitVec.ofNat 64 c := by
      bv_omega
    rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have := (p - a).isLt
    omega

theorem not_inRange_below {b : BitVec 64} {n j : Nat} (h : n + j < 2 ^ 64) :
    ¬InRange (b - BitVec.ofNat 64 n) n (b + BitVec.ofNat 64 j) := by
  unfold InRange
  rw [show b + BitVec.ofNat 64 j - (b - BitVec.ofNat 64 n) = BitVec.ofNat 64 (n + j) by
    rw [BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  omega


/-! ## Regions -/

/-- A one-region environment of a machine state is well formed. -/
theorem wf_one {m : MachineData} {a : BitVec 64} {n : Nat} (h : Mapped m.dmem a n) (hn : NoWrap a n)
    (vars : Nat → BitVec 64 := fun _ ↦ 0) : (Env.ofMachine m [(a, n)] vars).WF :=
  Env.wf_of ⟨⟨h, hn⟩, trivial⟩ (List.pairwise_singleton _ _)

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
  rw [inRange_iff hnb, toNat_add_ofNat' (by omega)]
  omega

/-- **Bytes of an argument a body did not change**: those of a region apart from the outputs and
the stack. -/
theorem same_of_apart {m0 st : MachineData} {S : Nat} {oa : BitVec 64} {on : Nat} {a : BitVec 64}
    {n : Nat} (hc : Changes m0 st S oa on) (hS : StackOk m0 S) (hna : NoWrap a n)
    (hst : OffStack m0 a n S) (ho : Apart a n oa on) (hno : NoWrap oa on) :
    ∀ j < n, st.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  fun _ hj ↦ hc _ fun h ↦ h.elim (not_inRange_of_apart ho hna hno hj)
    (not_inRange_of_apart hst hna (stack_noWrap hS) hj)

/-- **An element of an argument slice**, read in a body. -/
theorem elem_of_apart {m0 st : MachineData} {S : Nat} {oa : BitVec 64} {on : Nat} {a : BitVec 64}
    {n i : Nat} (hc : Changes m0 st S oa on) (hS : StackOk m0 S) (hna : NoWrap a (16 * n))
    (hst : OffStack m0 a (16 * n) S) (ho : Apart a (16 * n) oa on) (hno : NoWrap oa on)
    (hi : i < n) :
    ewOf st.dmem (a + BitVec.ofNat 64 (16 * i)) = (ewsOf m0.dmem a n)[i]'(by simp; exact hi) := by
  rw [NativeRustcVm.getElem_ewsOf]
  exact NativeRustcVm.ewOf_congr fun j hj ↦ by
    rw [NativeRustcVm.addr_add]
    exact same_of_apart hc hS hna hst ho hno _ (by omega)

theorem apart_zero (a : BitVec 64) (n : Nat) : Apart a n 0 0 := Or.inr (Nat.zero_le _)

theorem noWrap_zero : NoWrap 0 0 := by unfold NoWrap; simp

/-- The `16` bytes of element `i < n` of a readable slice are mapped in a state that kept them. -/
theorem elem_mapped {m0 st : MachineData} {a : BitVec 64} {n i : Nat} (h : Readable m0 a (16 * n))
    (hk : Kept m0.dmem st.dmem) (hi : i < n) :
    Mapped st.dmem (a + BitVec.ofNat 64 (16 * i)) 16 ∧ NoWrap (a + BitVec.ofNat 64 (16 * i)) 16 := by
  obtain ⟨hm, hn⟩ := h
  unfold NoWrap at *
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [NativeRustcVm.addr_add]; exact hk _ (hm _ (by omega))
  · rw [toNat_add_ofNat' (by omega)]; omega

/-! ## The frame -/

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

/-- The `n` bytes of stack below `sp - F` are among the `S` below `sp`. -/
theorem inRange_stack {sp p : BitVec 64} {F n S : Nat} (hle : F + n ≤ S) (hS : S ≤ sp.toNat)
    (h : InRange (sp - BitVec.ofNat 64 F - BitVec.ofNat 64 n) n p) :
    InRange (sp - BitVec.ofNat 64 S) S p := by
  refine inRange_mono (c := S - F - n) (n := n) ?_ (by omega)
  rw [show sp - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F - n) =
    sp - BitVec.ofNat 64 F - BitVec.ofNat 64 n by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := sp.isLt
    rw [Nat.mod_eq_of_lt (show S < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show S - F - n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show F < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
    omega]
  exact h

/-- **A function's body**: `F` bytes of frame below the entry's SP `m0`, the prologue's slots
there, the other callee-saved registers the entry's, memory as at the entry but in the outputs
(`oa`, `on`) and the `S` bytes of stack, every mapped byte still there. -/
structure Body (m0 : MachineData) (F S : Nat) (slots : List (Nat × XReg)) (oa : BitVec 64)
    (on : Nat) (st : MachineData) : Prop where
  sp : st.regs.SP.toBitVec = m0.regs.SP.toBitVec - BitVec.ofNat 64 F
  frame : SlotsAt st.dmem (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) m0 slots
  regs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → st.regs.getXReg r = m0.regs.getXReg r
  same : Changes m0 st S oa on
  kept : Kept m0.dmem st.dmem

/-- `EW::mul`'s precondition in a body. -/
theorem Body.ewMulPre {m0 st : MachineData} {F S : Nat} {slots : List (Nat × XReg)} {oa : BitVec 64}
    {on : Nat} (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hF : F % 16 = 0)
    (hle : F + ewMulStack ≤ S) : EWMulPre st := by
  obtain ⟨hal, hSle, hmap⟩ := hS
  have hsp : st.regs.SP.toNat = m0.regs.SP.toNat - F := by
    rw [← UInt64.toNat_toBitVec, hb.sp, BitVec.toNat_sub, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
    have := m0.regs.SP.toNat_lt
    omega
  refine ⟨by omega, by omega, fun i hi ↦ ?_⟩
  have hi' : S - F - ewMulStack + i < S := by omega
  have := hb.kept _ (hmap _ hi')
  have hS' : S ≤ m0.regs.SP.toBitVec.toNat := hSle
  have e : st.regs.SP.toBitVec - BitVec.ofNat 64 ewMulStack + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F - ewMulStack + i) := by
    rw [hb.sp]
    simp only [ewMulStack] at *
    bv_omega
  rw [e]
  exact this

/-- **A call of `EW::mul`** keeps a body. -/
theorem Body.call {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S)
    (hle : F + ewMulStack ≤ S) (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hpost : EWMulPost st st') : Body m0 F S slots oa on st' := by
  obtain ⟨-, -, hsame, hsaved⟩ := hpost
  have hS' := hS.2.1
  have hcallee : ∀ p, InRange (stackBelow st ewMulStack) ewMulStack p →
      InRange (stackBelow m0 S) S p := fun p h ↦ by
    unfold stackBelow at h
    rw [hb.sp] at h
    exact inRange_stack hle hS' h
  refine ⟨hsaved.2.1 ▸ hb.sp, fun p hp i hi ↦ ?_, fun r hr hn ↦ (hsaved.1 r hr).trans
    (hb.regs r hr hn), fun p hp ↦ ?_, fun p hp ↦ hsaved.2.2 p (hb.kept p hp)⟩
  · rw [hsame _ ?_]
    · exact hb.frame p hp i hi
    · simp only [List.length_map, List.length_range] at hi
      unfold stackBelow
      rw [hb.sp, addr_add]
      have := hslots p hp
      have := m0.regs.SP.toNat_lt
      have h592 : ewMulStack = 592 := rfl
      exact not_inRange_below (by omega)
  · rw [hsame p fun h ↦ hp (Or.inr (hcallee p h))]
    exact hb.same p hp

/-- `r` is one of the slots' registers. -/
@[expose] def inSlots (slots : List (Nat × XReg)) (r : XReg) : Bool := slots.any (·.2 == r)

theorem inSlots_false {slots : List (Nat × XReg)} {r : XReg} (h : r ∉ slots.map (·.2)) :
    inSlots slots r = false := by
  unfold inSlots
  rw [List.any_eq_false]
  intro p hp he
  exact h (List.mem_map.mpr ⟨p, hp, XReg.eq_of_beq he⟩)

/-- `S` keeps `S₀`'s SP, every register of `rs` and writes nothing. -/
@[expose] def keepsAll (S₀ S : SState) (rs : List XReg) : Bool :=
  rs.all (fun r ↦ (S₀.reg r).isSome && S.reg r == S₀.reg r) && S.sp == S₀.sp && S.mem.isEmpty

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

/-- **A block that writes nothing and keeps the callee-saved registers and SP** keeps a body. -/
theorem Body.of_block [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} {env : Env} {S₀ S₁ : SState} (hb : Body m0 F S slots oa on st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsAll S₀ S₁ (calleeRegs.filter fun r ↦ !inSlots slots r) = true) :
    Body m0 F S slots oa on st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, hmem⟩ := hk
  have hdm : st'.dmem = st.dmem := (hm.dmem_eq hwf hmem).trans hd.symm
  refine ⟨?_, ?_, fun r hr' hn ↦ ?_, ?_, ?_⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · rw [hdm]; exact hb.frame
  · obtain ⟨hs, he⟩ := hr r (List.mem_filter.mpr ⟨mem_calleeRegs hr', by
      rw [inSlots_false hn]; rfl⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · intro p hp; rw [hdm]; exact hb.same p hp
  · rw [hdm]; exact hb.kept

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

/-- **The epilogue**: run from a body with the frame as region 0, it restores the entry's
callee-saved registers, X30 and SP. -/
theorem Body.saved [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} {S₁ : SState} (hb : Body m0 F S slots oa on st)
    (hm : Match (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]) S₁ st')
    (hwf : (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]).WF)
    (hx30 : (XReg.X30) ∈ slots.map (·.2))
    (hr : restores slots F S₁ = true) (hmem : S₁.mem = []) :
    Saved m0 st' ∧ st'.regs.X30 = m0.regs.X30 ∧ st'.dmem = st.dmem := by
  simp only [restores, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hbase : (Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]).base 0 =
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
  have hdm : st'.dmem = st.dmem := hm.dmem_eq hwf hmem
  refine ⟨⟨fun r hc ↦ hreg r (mem_savedRegs hc), ?_, ?_⟩, hreg .X30 (by simp [savedRegs]), hdm⟩
  · apply UInt64.toBitVec_inj.mp
    rw [hm.sp, hsp]
    simp only [Sym.eval, hbase]
    rw [show BitVec.ofInt 64 (F : Int) = BitVec.ofNat 64 F from rfl, BitVec.sub_add_cancel]
  · rw [hdm]; exact hb.kept

/-- Writes into the frame (region 0) change memory only in the stack. -/
theorem changes_of_frame [Labels] {m0 st : MachineData} {F S : Nat} {oa : BitVec 64} {on : Nat}
    {S' : SState} (hS : StackOk m0 S) (hF : F ≤ S)
    (hm : Match (Env.ofMachine m0 [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]) S' st)
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Changes m0 st S oa on := by
  obtain ⟨hmap, hnw, he⟩ := frame_ok hS hF
  have hwf := wf_one hmap hnw
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  intro p hp
  refine hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb, h1, h2⟩ ↦ hp (Or.inr ?_)
  obtain ⟨hr, hoff⟩ := hmem w hw'
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [inRange_iff (stack_noWrap hS), show (stackBelow m0 S).toNat = m0.regs.SP.toBitVec.toNat - S
    from toNat_sub_ofNat hSle]
  have := m0.regs.SP.toBitVec.isLt
  rw [he] at h1 h2
  omega

/-- **The entry block**: from the entry, the prologue's writes in the frame (region 0) and the
other callee-saved registers untouched make a body. -/
theorem Body.of_entry [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} {S' : SState} (hS : StackOk m0 S) (hF : F ≤ S)
    (hm : Match (Env.ofMachine m0 [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]) S' st)
    (hsp : S'.sp = .ptr 0 0)
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S'.mem = some (.reg p.2, i))
    (hregs : ∀ r ∈ calleeRegs, inSlots slots r = false → S'.reg r = some (.reg r))
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Body m0 F S slots oa on st := by
  obtain ⟨hmap, hnw, he⟩ := frame_ok hS hF
  have hwf := wf_one hmap hnw
  have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  refine ⟨?_, slotsAt_of_writes hm hw, fun r hr hn ↦ ?_, fun p hp ↦ ?_, hm.kept hwf⟩
  · rw [hm.sp, hsp]; simp [Sym.eval]
  · apply UInt64.toBitVec_inj.mp
    rw [hm.regs r _ (hregs r (mem_calleeRegs hr) (inSlots_false hn))]
    rfl
  · exact changes_of_frame hS hF hm hmem p hp

/-- **An element loaded into two registers** from region 0 of a fresh environment. -/
theorem ew_of_loads [Labels] {st m : MachineData} {a : BitVec 64} {n : Nat}
    {rs : List (BitVec 64 × Nat)} {S' : SState} {lo hi : XReg} {off : Nat}
    (hm : Match (Env.ofMachine st ((a, n) :: rs)) S' m) (hlo : S'.reg lo = some (.load 0 off 8))
    (hhi : S'.reg hi = some (.load 0 (off + 8) 8)) :
    (⟨m.regs.getXReg lo, m.regs.getXReg hi⟩ : EW) = ewOf st.dmem (a + BitVec.ofNat 64 off) := by
  have h := ewOf_loads (Env.ofMachine st ((a, n) :: rs)) 0 off
  simp only [Env.ofMachine_mem0, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
    Option.getD_some] at h
  rw [h]
  have h0 := hm.regs lo _ hlo
  have h1 := hm.regs hi _ hhi
  simp only [Sym.eval] at h0 h1
  rw [← h0, ← h1, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]

@[simp] theorem base0 (st : MachineData) (a : BitVec 64) (n : Nat) (rs : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64) : (Env.ofMachine st ((a, n) :: rs) vars).base 0 = a := rfl

theorem add_ofNat_zero (a : BitVec 64) : a + BitVec.ofNat 64 0 = a := by simp

theorem ofInt_eq_ofNat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by simp

/-- An `if` on a `Bool`, whatever its decidability instance (the executor's evaluations carry
instances `rw` and `split` cannot see through), is `cond`. -/
theorem ite_bool {α : Sort _} {c : Bool} {inst : Decidable (c = true)} (a b : α) :
    @ite α (c = true) inst a b = cond c a b := by
  cases inst with
  | isTrue h => exact (Bool.cond_pos h).symm
  | isFalse h => exact (Bool.cond_neg (Bool.eq_false_iff.mpr h)).symm

/-- A conditional branch's target, by the condition, whatever its decidability instance (the
executor's evaluations carry instances `rw`, `simp` and `split` cannot see through: state the
condition with `show`). -/
theorem pc_cond {pc a b : Int64} {c : Prop} {inst : Decidable c} (h : pc = @ite _ c inst a b) :
    (c → pc = a) ∧ (¬c → pc = b) := by
  cases inst with
  | isTrue hc => exact ⟨fun _ ↦ h, fun hn ↦ absurd hc hn⟩
  | isFalse hc => exact ⟨fun hn ↦ absurd hn hc, fun _ ↦ h⟩

/-! ## Loading a slice's element -/

/-- At a load of an element: region 0 the element, `r` its address plus `o`. -/
@[expose] def ldS (r : XReg) (o : Int) : SState := init [(16, false)] .sp [(r, .ptr 0 o)]

theorem regs_eq_of [Labels] {env : Env} {S₀ S₁ : SState} {m m' : MachineData}
    (hm : Match env S₀ m) (hm' : Match env S₁ m') (rs : List XReg)
    (h : (rs.all fun r ↦ (S₀.reg r).isSome && S₁.reg r == S₀.reg r) = true) :
    ∀ r ∈ rs, m'.regs.getXReg r = m.regs.getXReg r := by
  intro r hr
  rw [List.all_eq_true] at h
  have := h r hr
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at this
  obtain ⟨⟨v, hv⟩, he⟩ := this
  exact Match.reg_eq hm hm' hv (he.trans hv)

/-- **A block loading element `i` of a slice** (`a`, `n` elements, apart from the outputs and the
stack) from a body, register `r` holding its address plus `o`: the block's run from `ldS r o`,
then `cont` with the element in `lo`, `hi`, the body kept, the registers `rs` kept. -/
theorem load_step [Host] {m0 st : MachineData} {pc : Int64} {F S : Nat}
    {slots : List (Nat × XReg)} {oa : BitVec 64} {on : Nat} {a : BitVec 64} {n i : Nat}
    {ds : List Directive} {kk : Nat} {r lo hi' : XReg} {o : Int} {S' : SState} {x : Exit}
    {R : MachineState → Prop} (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds (ldS r o) = some (S', x))
    (hlo : S'.reg lo = some (.load 0 0 8)) (hhi : S'.reg hi' = some (.load 0 8 8))
    (hkeep : keepsAll (ldS r o) S' (calleeRegs.filter fun r ↦ !inSlots slots r) = true)
    (rs : List XReg) (hrs : (rs.all fun q ↦ ((ldS r o).reg q).isSome &&
      S'.reg q == (ldS r o).reg q) = true)
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hr : Readable m0 a (16 * n))
    (hst : OffStack m0 a (16 * n) S) (ho : Apart a (16 * n) oa on) (hno : NoWrap oa on)
    (hi : i < n) (hpc : pc = Host.addrOf kk)
    (hreg : (st.regs.getXReg r).toBitVec = a + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 o)
    (cont : ∀ st', Match (Env.ofMachine st [(a + BitVec.ofNat 64 (16 * i), 16)]) S' st'.data →
      PcOk (Env.ofMachine st [(a + BitVec.ofNat 64 (16 * i), 16)]) x (Host.addrOf (kk + ds.length)) st' →
      Body m0 F S slots oa on st'.data →
      (⟨st'.data.regs.getXReg lo, st'.data.regs.getXReg hi'⟩ : EW) =
        (ewsOf m0.dmem a n)[i]'(by simp; exact hi) →
      (∀ q ∈ rs, st'.data.regs.getXReg q = st.regs.getXReg q) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R ⟨st, pc⟩ := by
  obtain ⟨hmA, hnA⟩ := elem_mapped hr hb.kept hi
  have hwf := wf_one hmA hnA (m := st)
  have hm : Match (Env.ofMachine st [(a + BitVec.ofNat 64 (16 * i), 16)]) (ldS r o) st :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨hreg, trivial⟩ trivial trivial trivial
  refine exec_at (st := ⟨st, pc⟩) hk hx hwf hpc hm fun st' hm' hpc' ↦ cont st' hm' hpc'
    (hb.of_block hm hm' hwf rfl hkeep) ?_ (regs_eq_of hm hm' rs hrs)
  rw [ew_of_loads (off := 0) hm' hlo hhi, add_ofNat_zero]
  exact elem_of_apart hb.same hS hr.2 hst ho hno hi

/-! ## Entry and exit states -/

/-- The frame's base is 16-byte aligned. -/
theorem frame_aligned {m0 : MachineData} {S F : Nat} (hS : StackOk m0 S) (hF : F ≤ S)
    (h16 : F % 16 = 0) : (m0.regs.SP.toBitVec - BitVec.ofNat 64 F).toNat % 16 = 0 := by
  rw [(frame_ok hS hF).2.2]
  have : m0.regs.SP.toBitVec.toNat % 16 = 0 := hS.1
  have : F ≤ m0.regs.SP.toBitVec.toNat := Nat.le_trans hF hS.2.1
  omega

/-- The entry's environment: region 0 the `F`-byte frame below SP. -/
abbrev frameEnv (m0 st : MachineData) (F : Nat) : Env :=
  Env.ofMachine st [(m0.regs.SP.toBitVec - BitVec.ofNat 64 F, F)]

/-- At the entry: the frame (region 0), SP its top. -/
theorem entry_match [Labels] {m0 : MachineData} {S F : Nat} (hS : StackOk m0 S) (hF : F ≤ S)
    (h16 : F % 16 = 0) :
    (frameEnv m0 m0 F).WF ∧ Match (frameEnv m0 m0 F) (init [(F, true)] (.ptr 0 F)) m0 := by
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS hF
  refine ⟨wf_one hmap hnw, match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF h16, trivial⟩ ?_
    trivial trivial trivial trivial⟩
  show _ = (m0.regs.SP.toBitVec - BitVec.ofNat 64 F) + BitVec.ofInt 64 (F : Int)
  rw [ofInt_eq_ofNat, BitVec.sub_add_cancel]

/-- At the epilogue: the frame (region 0), SP its base. -/
theorem Body.exit_match [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hF : F ≤ S)
    (h16 : F % 16 = 0) :
    (frameEnv m0 st F).WF ∧ Match (frameEnv m0 st F) (init [(F, true)] (.ptr 0 0)) st := by
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS hF
  refine ⟨wf_one (fun i hi ↦ hb.kept _ (hmap i hi)) hnw,
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF h16, trivial⟩ ?_ trivial trivial trivial
      trivial⟩
  rw [hb.sp]; simp [Sym.eval]

/-- **A block writing only into region 0**, inside the outputs, keeps a body. -/
theorem Body.of_write [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × XReg)}
    {oa : BitVec 64} {on : Nat} {a : BitVec 64} {n : Nat} {S₀ S₁ : SState}
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S)
    (hm₀ : Match (Env.ofMachine st [(a, n)]) S₀ st) (hm : Match (Env.ofMachine st [(a, n)]) S₁ st')
    (hwf : (Env.ofMachine st [(a, n)]).WF) (hin : ∀ p, InRange a n p → InRange oa on p)
    (hk : keepsAll S₀ { S₁ with mem := [] } (calleeRegs.filter fun r ↦ !inSlots slots r) = true)
    (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ n) (hfr : Apart a n (stackBelow m0 S) S)
    (hF : F ≤ S) (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F) :
    Body m0 F S slots oa on st' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, -⟩ := hk
  have hnw : NoWrap a n := hwf.noWrap 0 a n rfl
  have hsame : ∀ p, ¬InRange a n p → st'.dmem.get? p = st.dmem.get? p := fun p hp ↦
    hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb', h1, h2⟩ ↦ hp (by
      obtain ⟨hr0, hoff⟩ := hw w hw'
      rw [hr0] at hb'
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      rw [inRange_iff hnw]
      omega)
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr' hn ↦ ?_, fun p hp ↦ ?_, fun p hp ↦ hm.kept hwf _ (hb.kept p hp)⟩
  · rw [Match.sp_eq hm₀ hm hsp]; exact hb.sp
  · rw [hsame _ ?_]
    · exact hb.frame p hp i hi
    · simp only [List.length_map, List.length_range] at hi
      have hSle : S ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
      have := hslots p hp
      have e : m0.regs.SP.toBitVec - BitVec.ofNat 64 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
          stackBelow m0 S + BitVec.ofNat 64 (S - F + p.1 + i) := by
        unfold stackBelow
        bv_omega
      rw [e]
      exact not_inRange_of_apart (Or.symm hfr) (stack_noWrap hS) hnw (by omega)
  · obtain ⟨hs, he⟩ := hr r (List.mem_filter.mpr ⟨mem_calleeRegs hr', by
      rw [inSlots_false hn]; rfl⟩)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    rw [Match.reg_eq hm₀ hm hv (he.trans hv)]
    exact hb.regs r hr' hn
  · rw [hsame p fun h ↦ hp (Or.inl (hin p h))]
    exact hb.same p hp

/-! ## Values -/

theorem min_toNat (a b : BitVec 64) :
    (if b.ult a then b else a).toNat = min a.toNat b.toNat := by
  split <;> rename_i h <;> simp only [BitVec.ult_iff_lt, BitVec.lt_def] at h <;> omega

theorem toBitVec_eq {a : UInt64} {b : BitVec 64} (h : a.toBitVec = b) : a = UInt64.ofBitVec b := by
  rw [← h]

/-- **Bit `y` of `x`** (`lsr`, `and #1`), for `y < 64`. -/
theorem bit_eval (x y : BitVec 64) (hy : y.toNat < 64) :
    BinOp.apply .and .W64 (BinOp.apply .lsrv .W64 x y) (BitVec.ofNat 64 1) =
      BitVec.ofNat 64 ((x.toNat >>> y.toNat) % 2) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [show y.toNat % RegWidth.W64.bits = y.toNat from Nat.mod_eq_of_lt hy]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  show (x >>> y.toNat).toNat &&& (1#64).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show 1 % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

/-- A branch on `x ≠ y` (`b.ne` after `cmp`), by the comparison. -/
theorem pc_ne {pc a b : Int64} {x y : BitVec 64} {inst : Decidable ((!(x == y)) = true)}
    (h : pc = @ite _ ((!(x == y)) = true) inst a b) : (x ≠ y → pc = a) ∧ (x = y → pc = b) := by
  constructor
  · intro hne; rw [h]; exact ite_eq_left (by simpa using hne)
  · intro he; rw [h]; exact ite_eq_right (by simp [he])

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `lsl #4` as rustc writes it (`ubfm #60, #59`): the product by `16`. -/
theorem lsl4 (x : BitVec 64) : UnOp.apply (.ubfm 60 59) .W64 x = BitVec.ofNat 64 (16 * x.toNat) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- A shifted register operand `lsl #4`: the product by `16`. -/
theorem shl4 (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem reg_of {env : Env} {S : SState} {m : MachineData} [Labels] (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) : m.regs.getXReg r = UInt64.ofBitVec (v.eval env) :=
  toBitVec_eq (hm.regs r v h)

/-- `1 + x` on the lanes `EW::mul`'s callers form (`eor #1`). -/
theorem one_add (x : EW) : (1 : EW) + x = ⟨x.c0 ^^^ 1, x.c1⟩ := by
  show (⟨1 ^^^ x.c0, 0 ^^^ x.c1⟩ : EW) = _
  rw [UInt64.xor_comm, UInt64.zero_xor]

theorem nbit_toNat (T : BitVec 64) :
    (BinOp.apply .and .W64 (BinOp.apply .orn .W32 (BitVec.ofNat 64 0)
      (UnOp.apply .trunc .W32 T)) (BitVec.ofNat 64 1)).toNat = 1 - T.toNat % 2 := by
  simp only [BinOp.apply, UnOp.apply, low_W64, ext_W64, low_W32, ext_W32]
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_not,
    BitVec.toNat_ofNat]
  rw [show 0 % 2 ^ 64 % 2 ^ 32 = 0 from rfl, Nat.zero_or, show 1 % 2 ^ 64 = 1 from rfl,
    Nat.and_one_is_mod]
  have := T.isLt
  omega

/-- **`1` minus bit `y` of `x`** (`lsr`, `mvn w`, `and #1`), for `y < 64`. -/
theorem nbit_eval (x y : BitVec 64) (hy : y.toNat < 64) :
    BinOp.apply .and .W64 (BinOp.apply .orn .W32 (BitVec.ofNat 64 0)
      (UnOp.apply .trunc .W32 (BinOp.apply .lsrv .W64 x y))) (BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (1 - (x.toNat >>> y.toNat) % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [nbit_toNat, BitVec.toNat_ofNat]
  have h : (BinOp.apply .lsrv .W64 x y).toNat = x.toNat >>> y.toNat := by
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [show y.toNat % RegWidth.W64.bits = y.toNat from Nat.mod_eq_of_lt hy]
    exact BitVec.toNat_ushiftRight _ _
  rw [h]
  omega

/-- `1 + b` for a bit `b`, as `1 - b` in limb `0`. -/
theorem one_add_bit (b : Nat) (hb : b < 2) :
    (⟨UInt64.ofBitVec (BitVec.ofNat 64 (1 - b)), 0⟩ : EW) = 1 + EW.ofNat b := by
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl

/-- `EW::mul`'s precondition from the caller's stack, SP restored. -/
theorem ewMulPre_of {m0 st : MachineData} {S : Nat} (hS : StackOk m0 S) (hle : ewMulStack ≤ S)
    (hsaved : Saved m0 st) : EWMulPre st := by
  obtain ⟨hal, hSle, hmap⟩ := hS
  have hsp := hsaved.2.1
  refine ⟨by rw [hsp]; exact hal, by rw [hsp]; omega, fun i hi ↦ ?_⟩
  have hS' : S ≤ m0.regs.SP.toBitVec.toNat := hSle
  have := hsaved.2.2 _ (hmap (S - ewMulStack + i) (by omega))
  rw [hsp]
  have e : m0.regs.SP.toBitVec - BitVec.ofNat 64 ewMulStack + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - ewMulStack + i) := by
    simp only [ewMulStack] at *
    bv_omega
  rw [e]
  exact this

/-- **A tail call of `EW::mul`** (`b`, SP and the callee-saved registers and X30 the entry's): the
callee returns to the entry's caller, the `S` bytes of stack its only other change. -/
theorem tail_mul [Host] (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {m0 st : MachineData}
    {S : Nat} {pc : Int64} {oa : BitVec 64} {on : Nat} (hS : StackOk m0 S) (hle : ewMulStack ≤ S)
    (hsaved : Saved m0 st) (hx30 : st.regs.X30 = m0.regs.X30) (hc : Changes m0 st S oa on)
    (hpc : pc = Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧
      (⟨s.data.regs.X0, s.data.regs.X1⟩ : EW) = EW.mul ⟨st.regs.X0, st.regs.X1⟩ ⟨st.regs.X2, st.regs.X3⟩ ∧
      Changes m0 s.data S oa on ∧ Saved m0 s.data) ⟨st, pc⟩ := by
  refine Eventually.mono (Spec.apply (s := ⟨st, pc⟩) hmul hpc (ewMulPre_of hS hle hsaved))
    fun s ⟨hpc', hpost⟩ ↦ ⟨?_, ?_, ?_, hsaved.trans hpost.2.2.2⟩
  · rw [hpc']; simp only [retOf, hx30]
  · rw [hpost.1, hpost.2.1]
  · intro p hp
    rw [hpost.2.2.1 p ?_]
    · exact hc p hp
    · intro h
      apply hp (Or.inr _)
      unfold stackBelow at h
      rw [hsaved.2.1] at h
      exact inRange_stack (F := 0) (n := ewMulStack) (by omega) hS.2.1 (by simpa using h)

/-! ## Stores -/

/-- A word's eight stored bytes are its `wordBytes`. -/
theorem byteOf_wordBytes (w : UInt64) :
    (List.range 8).map (byteOf w.toBitVec) = NativeRustcVm.wordBytes w := by
  rw [NativeRustcVm.wordBytes_eq]
  apply List.map_congr_left
  intro t _
  rfl

/-- Bytes kept where memory is unchanged. -/
theorem bytesAt_congr {d d' : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (he : ∀ j < bs.length, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)) :
    BytesAt d' a bs := fun j hj ↦ by rw [he j hj]; exact h j hj

/-- **A stored word**: a block's write of register `r`'s value at offset `o` of region 0. -/
theorem wordAt_of_write [Labels] {st m : MachineData} {a : BitVec 64} {n o : Nat}
    {rs : List (BitVec 64 × Nat)} {S : SState} {r : XReg}
    (hm : Match (Env.ofMachine st ((a, n) :: rs)) S m) (hle : o + 8 ≤ n)
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem = some (.reg r, i)) :
    NativeRustcVm.WordAt m.dmem (a + BitVec.ofNat 64 o) (st.regs.getXReg r) := by
  have := hm.bytesAt_write (r := 0) rfl hle hw
  simp only [Sym.eval, Env.ofMachine_regs] at this
  rw [byteOf_wordBytes] at this
  exact this

theorem inRange_add {a : BitVec 64} {n j : Nat} (hnw : NoWrap a n) (hj : j < n) :
    InRange a n (a + BitVec.ofNat 64 j) := by
  unfold NoWrap at hnw
  rw [inRange_iff hnw, toNat_add_ofNat' (by omega)]
  omega

/-- Bytes from `a` kept where memory is unchanged on the `n` bytes from `a`. -/
theorem bytesAt_keep {d d' : DataMem} {a : BitVec 64} {bs : List UInt8} {n : Nat}
    (h : BytesAt d a bs) (hn : bs.length ≤ n) (hnw : NoWrap a n)
    (he : ∀ p, InRange a n p → d'.get? p = d.get? p) : BytesAt d' a bs :=
  bytesAt_congr h fun j hj ↦ he _ (inRange_add hnw (by omega))

theorem length_flatMap_ewBytes (xs : List EW) : (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length := by
  rw [List.length_flatMap]
  simp [NativeRustcVm.length_ewBytes, Nat.mul_comm]

/-- Memory after a block whose writes are all in region 0 is the start's outside region 0. -/
theorem same_of_region0 [Labels] {st m : MachineData} {a : BitVec 64} {n : Nat}
    {rs : List (BitVec 64 × Nat)} {S : SState} (hm : Match (Env.ofMachine st ((a, n) :: rs)) S m)
    (hwf : (Env.ofMachine st ((a, n) :: rs)).WF) (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ n) :
    ∀ p, ¬InRange a n p → m.dmem.get? p = st.dmem.get? p := fun p hp ↦
  hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb', h1, h2⟩ ↦ hp (by
    obtain ⟨hr0, hoff⟩ := hw w hw'
    rw [hr0] at hb'
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    rw [inRange_iff (hwf.noWrap 0 _ _ rfl)]
    omega)

end

end NativeRustcVmArm.Arrays
