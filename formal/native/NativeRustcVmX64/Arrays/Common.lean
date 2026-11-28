module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Spec.Arrays
public import NativeRustcVmX64.Field.Leaf
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# The array functions' proofs: what they share (x86-64)

- Loads: the eight bytes the executor loads are `wordOf` of them (`load8_eq`), sixteen an `ewOf`
  (`ewOf_loads`, `ew_of_loads`).
- The frame (`Field.frameEnv m0 m F`, region 0): the `F` bytes below the entry's RSP, the last 8
  of them the slot a call pushes its return address in, and the return address. The state of a
  function's body (`Body`): RSP at the frame's offset `8`, the pushed registers in their slots,
  the other callee-saved registers the entry's, memory as at the entry but in the outputs and the
  `S` bytes of stack, every mapped byte still there. Made by the prologue (`Body.of_entry`), kept
  by a block that writes nothing (`Body.of_block`) and by a block ending in a call of `EW::mul`
  and the call (`Body.call_mul`); the epilogue returns with the entry's registers (`Body.done`).
- A slice's element read in a body (`elem_of_apart`), its region apart from the frame
  (`elem_apart_frame`), the two-region environment of a block (`wf_two`).
-/

namespace NativeRustcVmX64.Arrays

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model
open NativeRustcVm (wordOf ewOf ewsOf leNat)
open NativeRustcVmX64.Field (frameEnv frame_wf frame_noWrap frame_add frame_rsp load_ret
  stackBelow_toNat' frameS midS)

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

/-- Two blocks placed one after the other are placed together. -/
theorem isInfixAt_concat {a b P : List Directive} {k : Nat} (ha : a.IsInfixAt P k)
    (hb : b.IsInfixAt P (k + a.length)) : (a ++ b).IsInfixAt P k := by
  rw [List.isInfixAt_iff_getElem?] at *
  intro i hi
  rw [List.length_append] at hi
  by_cases h : i < a.length
  · rw [List.getElem_append_left h]; exact ha i h
  · rw [List.getElem_append_right (by omega)]
    have := hb (i - a.length) (by omega)
    rwa [show k + a.length + (i - a.length) = k + i by omega] at this

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
  unfold Env.load wordOf NativeRustcVm.bytesFrom
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

/-- **Sixteen bytes loaded as two words** are an `E` element. -/
theorem ewOf_loads (env : Env) (r off : Nat) :
    ewOf env.mem0 (env.base r + BitVec.ofNat 64 off) =
      ewArg (env.load r off 8) (env.load r (off + 8) 8) := by
  rw [load8_eq, load8_eq, ewArg, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec, ← addr_add]
  rfl

/-- **An element loaded into two registers** from region `r` of an environment. -/
theorem ew_of_loads [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {lo hi : Reg64} {r off : Nat} (hlo : S.reg lo = some (.load r off 8))
    (hhi : S.reg hi = some (.load r (off + 8) 8)) :
    ewArg (reg m lo) (reg m hi) = ewOf env.mem0 (env.base r + BitVec.ofNat 64 off) := by
  rw [ewOf_loads]
  show ewArg (m.regs.get64 lo) (m.regs.get64 hi) = _
  rw [hm.regs lo _ hlo, hm.regs hi _ hhi]
  rfl

/-! ## Addresses -/

theorem apart_mono {a b : BitVec 64} {n n' n'' : Nat} (h : Apart a n b n') (hle : n'' ≤ n') :
    Apart a n b n'' := by
  unfold Apart at *; omega

theorem apart_symm {a b : BitVec 64} {n n' : Nat} (h : Apart a n b n') : Apart b n' a n := by
  unfold Apart at *; omega

/-- A byte of a region apart from another is not one of the other's. -/
theorem not_inRange_of_apart {a b : BitVec 64} {n n' j : Nat} (hA : Apart a n b n')
    (hna : NoWrap a n) (hnb : NoWrap b n') (hj : j < n) : ¬InRange b n' (a + BitVec.ofNat 64 j) := by
  unfold Apart NoWrap at *
  rw [Sym.inRange_iff hnb, toNat_add_ofNat _ _ (by omega)]
  omega

theorem inRange_add {a : BitVec 64} {n j : Nat} (hnw : NoWrap a n) (hj : j < n) :
    InRange a n (a + BitVec.ofNat 64 j) := by
  unfold NoWrap at hnw
  rw [Sym.inRange_iff hnw, toNat_add_ofNat _ _ (by omega)]
  omega

/-- The stack below RSP as a number. -/
theorem stackBelow_toNat {m : MachineData} {n : Nat} (h : n ≤ (rspOf m).toNat) :
    (stackBelow m n).toNat = (rspOf m).toNat - n := stackBelow_toNat' h

/-- A smaller stack is a stack. -/
theorem stackOk_mono {m : MachineData} {F S : Nat} (h : StackOk m S) (hF : F ≤ S) :
    StackOk m F := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, h2, fun i hi ↦ ?_⟩
  have := h3 (S - F + i) (by omega)
  rwa [show rspOf m - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F + i) =
    rspOf m - BitVec.ofNat 64 F + BitVec.ofNat 64 i by
      apply BitVec.eq_of_toNat_eq
      have := (rspOf m).isLt
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega] at this

/-- The bytes `[rsp - F - n, rsp - F + k)` are among the `S` below RSP, for `F + n ≤ S` and
`k ≤ F`. -/
theorem inRange_stack {m : MachineData} {F S n k : Nat} {p : BitVec 64} (hS : S ≤ (rspOf m).toNat)
    (hle : F + n ≤ S) (hk : k ≤ F) (h : InRange (stackBelow m F - BitVec.ofNat 64 n) (n + k) p) :
    InRange (stackBelow m S) S p := by
  have hr := (rspOf m).isLt
  have e1 : (stackBelow m F - BitVec.ofNat 64 n).toNat = (rspOf m).toNat - F - n := by
    rw [toNat_sub_of_le _ _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      stackBelow_toNat (by omega)]; omega), stackBelow_toNat (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  rw [Sym.inRange_iff (by rw [e1]; omega), e1] at h
  rw [Sym.inRange_iff (by rw [stackBelow_toNat hS]; omega), stackBelow_toNat hS]
  omega

/-- The `16` bytes of element `i < n` of a readable slice are mapped in a state that kept them. -/
theorem elem_mapped {m0 st : MachineData} {a : BitVec 64} {n i : Nat} (h : Readable m0 a (16 * n))
    (hk : Kept m0.dmem st.dmem) (hi : i < n) :
    Readable st (a + BitVec.ofNat 64 (16 * i)) 16 := by
  obtain ⟨hm, hn⟩ := h
  unfold NoWrap at hn
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [addr_add]; exact hk _ (hm _ (by omega))
  · show (a + BitVec.ofNat 64 (16 * i)).toNat + 16 ≤ 2 ^ 64
    rw [toNat_add_ofNat _ _ (by omega)]; omega

/-- Element `i` of a slice off the stack is apart from the frame. -/
theorem elem_apart_frame {m0 : MachineData} {a : BitVec 64} {n i F S : Nat}
    (hS : StackOk m0 S) (hF : F ≤ S) (hr : Readable m0 a (16 * n)) (ho : OffStack m0 a (16 * n) S)
    (hi : i < n) : Apart (stackBelow m0 F) (F + 8) (a + BitVec.ofNat 64 (16 * i)) 16 := by
  obtain ⟨hS1, hS2, -⟩ := hS
  obtain ⟨-, hn⟩ := hr
  unfold OffStack Apart at ho
  unfold NoWrap at hn
  unfold Apart
  rw [stackBelow_toNat (by omega), toNat_add_ofNat _ _ (by omega)]
  rw [stackBelow_toNat hS1] at ho
  omega

/-! ## Regions -/

/-- The frame and one more region. -/
theorem wf_two {m0 st : MachineData} {F : Nat} {a : BitVec 64} {n : Nat}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hS : StackOk m0 F) (hk : Kept m0.dmem st.dmem)
    (ha : Readable st a n) (hap : Apart (stackBelow m0 F) (F + 8) a n) :
    (Env.ofMachine st [(stackBelow m0 F, F + 8), (a, n)] vars ret).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hk _ (hS.2.2 i hi), frame_noWrap hS⟩, ⟨ha.1, ha.2⟩, trivial⟩
    (List.pairwise_pair.mpr hap)

/-! ## The frame -/

/-- The pushed registers' slots: register `r`'s entry value at `fb + o` for each `(o, r)`. -/
@[expose] def SlotsAt (d : DataMem) (fb : BitVec 64) (m0 : MachineData)
    (slots : List (Nat × Reg64)) : Prop :=
  ∀ p ∈ slots, BytesAt d (fb + BitVec.ofNat 64 p.1) ((List.range 8).map (byteOf (reg m0 p.2)))

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
theorem slot_load {env : Env} {m0 : MachineData} {slots : List (Nat × Reg64)} {r : Nat}
    (h : SlotsAt env.mem0 (env.base r) m0 slots) {o : Nat} {x : Reg64} (hp : (o, x) ∈ slots) :
    env.load r o 8 = reg m0 x := by
  rw [Env.load_of_bytesAt (by simp) (h _ hp), ofInt_ofBytes_byteOf]

/-- **A function's body**: RSP at offset `8` of the frame, the pushed registers in their slots,
the other callee-saved registers the entry's, memory as at the entry but in the outputs (`oa`,
`on`) and the `S` bytes of stack, every mapped byte still there. -/
structure Body (m0 : MachineData) (F S : Nat) (slots : List (Nat × Reg64)) (oa : BitVec 64)
    (on : Nat) (st : MachineData) : Prop where
  rsp : rspOf st = stackBelow m0 F + BitVec.ofInt 64 8
  frame : SlotsAt st.dmem (stackBelow m0 F) m0 slots
  regs : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → reg st r = reg m0 r
  same : Changes m0 st S oa on
  kept : Kept m0.dmem st.dmem

/-- The callee-saved registers. -/
@[expose] def calleeRegs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

theorem mem_calleeRegs {r : Reg64} (h : calleeSaved r = true) : r ∈ calleeRegs := by
  cases r <;> simp_all [calleeSaved, calleeRegs]

/-- `r` is one of the slots' registers. -/
@[expose] def inSlots (slots : List (Nat × Reg64)) (r : Reg64) : Bool := slots.any (·.2 == r)

theorem inSlots_false {slots : List (Nat × Reg64)} {r : Reg64} (h : r ∉ slots.map (·.2)) :
    inSlots slots r = false := by
  unfold inSlots
  rw [List.any_eq_false]
  intro p hp he
  exact h (List.mem_map.mpr ⟨p, hp, Reg64.eq_of_beq he⟩)

/-- `S` keeps `S₀`'s registers `rs`. -/
@[expose] def keepsRegs (S₀ S : SState) (rs : List Reg64) : Bool :=
  rs.all fun r ↦ (S₀.reg r).isSome && S.reg r == S₀.reg r

/-- `S` keeps `S₀`'s RSP and registers `rs` and writes nothing. -/
@[expose] def keepsAll (S₀ S : SState) (rs : List Reg64) : Bool :=
  keepsRegs S₀ S (.rsp :: rs) && S.mem.isEmpty

/-- The callee-saved registers not in the slots. -/
@[expose] def freeRegs (slots : List (Nat × Reg64)) : List Reg64 :=
  calleeRegs.filter fun r ↦ !inSlots slots r

theorem regs_eq_of [Labels] {env : Env} {S₀ S₁ : SState} {m m' : MachineData}
    (hm : Match env S₀ m) (hm' : Match env S₁ m') {rs : List Reg64}
    (h : keepsRegs S₀ S₁ rs = true) : ∀ r ∈ rs, reg m' r = reg m r := by
  intro r hr
  unfold keepsRegs at h
  rw [List.all_eq_true] at h
  have := h r hr
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at this
  obtain ⟨⟨v, hv⟩, he⟩ := this
  exact Match.reg_eq hm hm' hv (he.trans hv)

theorem free_mem {slots : List (Nat × Reg64)} {r : Reg64} (hr : calleeSaved r = true)
    (hn : r ∉ slots.map (·.2)) : r ∈ freeRegs slots :=
  List.mem_filter.mpr ⟨mem_calleeRegs hr, by rw [inSlots_false hn]; rfl⟩

/-- **A block that writes nothing and keeps RSP and the free callee-saved registers** keeps a
body. -/
theorem Body.of_block [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {env : Env} {S₀ S₁ : SState} (hb : Body m0 F S slots oa on st)
    (hm₀ : Match env S₀ st) (hm : Match env S₁ st') (hwf : env.WF) (hd : st.dmem = env.mem0)
    (hk : keepsAll S₀ S₁ (freeRegs slots) = true) :
    Body m0 F S slots oa on st' := by
  unfold keepsAll at hk
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hk
  obtain ⟨hr, hmem⟩ := hk
  have he := regs_eq_of hm₀ hm hr
  have hdm : st'.dmem = st.dmem := (hm.dmem_eq hwf hmem).trans hd.symm
  refine ⟨?_, ?_, fun r hr' hn ↦ ?_, ?_, ?_⟩
  · show reg st' .rsp = _
    rw [he .rsp (by simp)]; exact hb.rsp
  · rw [hdm]; exact hb.frame
  · rw [he r (List.mem_cons_of_mem _ (free_mem hr' hn))]; exact hb.regs r hr' hn
  · intro p hp; rw [hdm]; exact hb.same p hp
  · rw [hdm]; exact hb.kept

/-- The bytes a block's writes cover, when all are in region 0 below `k`. -/
theorem written_region0 {env : Env} {S : SState} {b : BitVec 64} {n k : Nat}
    {rs : List (BitVec 64 × Nat)} (henv : env.regions = (b, n) :: rs) (hwf : env.WF) (hk : k ≤ n)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ k) {p : BitVec 64} (h : Written env S p) :
    InRange b k p := by
  obtain ⟨w, hw', b', sz, hb', h1, h2⟩ := h
  obtain ⟨hr0, hoff⟩ := hw w hw'
  rw [hr0, henv] at hb'
  simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨hb1, -⟩ := hb'
  have := hwf.noWrap 0 b n (by rw [henv]; rfl)
  rw [← hb1] at h1 h2
  rw [Sym.inRange_iff (by omega)]
  omega

/-- An address `j ≥ k` above `b` is not one of the `k` bytes from `b`. -/
theorem not_inRange_above {b : BitVec 64} {k j : Nat} (hkj : k ≤ j) (hj : b.toNat + j < 2 ^ 64) :
    ¬InRange b k (b + BitVec.ofNat 64 j) := by
  rw [Sym.inRange_iff (by omega), toNat_add_ofNat _ _ hj]
  omega

/-- An address at or above `b` is not one of the `n` bytes below `b`. -/
theorem not_inRange_below {b : BitVec 64} {n j : Nat} (hn : n ≤ b.toNat)
    (hj : b.toNat + j < 2 ^ 64) : ¬InRange (b - BitVec.ofNat 64 n) n (b + BitVec.ofNat 64 j) := by
  have e : (b - BitVec.ofNat 64 n).toNat = b.toNat - n := by
    rw [toNat_sub_of_le _ _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [Sym.inRange_iff (by rw [e]; omega), e, toNat_add_ofNat _ _ hj]
  omega

/-- **The entry block**: from the entry (`Field.frameS F`), the prologue's pushes in their slots,
the other callee-saved registers untouched, RSP at offset `8` make a body. -/
theorem Body.of_entry [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} {S' : SState}
    (hS : StackOk m0 S) (hF : F ≤ S) (hm : Match (frameEnv m0 m0 F vars ret) S' st)
    (hsp : S'.reg .rsp = some (.ptr 0 8))
    (hw : ∀ p ∈ slots, p.1 + 8 ≤ F ∧ ∀ i < 8, findWrite 0 (p.1 + i) S'.mem = some (.reg p.2, i))
    (hregs : ∀ r ∈ freeRegs slots, S'.reg r = some (.reg r))
    (hmem : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ F) : Body m0 F S slots oa on st := by
  have hSF := stackOk_mono hS hF
  have hwf := frame_wf (m := m0) (vars := vars) (ret := ret) hSF fun _ h ↦ h
  refine ⟨?_, fun p hp ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_, hm.kept hwf⟩
  · exact hm.regs .rsp _ hsp
  · exact hm.bytesAt_write (r := 0) rfl (by have := (hw p hp).1; omega) (hw p hp).2
  · exact hm.regs r _ (hregs r (free_mem hr hn))
  · refine hm.get?_mem0 hwf fun h ↦ hp (Or.inr ?_)
    have := written_region0 rfl hwf (Nat.le_add_right F 8) hmem h
    refine inRange_stack (n := 0) (k := F) hS.1 (by omega) le_rfl ?_
    simpa using this

/-- The frame's environment of a body is well formed. -/
theorem Body.wf {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)} {oa : BitVec 64}
    {on : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} (hb : Body m0 F S slots oa on st)
    (hS : StackOk m0 S) (hF : F ≤ S) : (frameEnv m0 st F vars ret).WF :=
  frame_wf (stackOk_mono hS hF) hb.kept

/-- A body in its frame environment, RSP at offset `8` (`Field.midS`). -/
theorem Body.mid_match [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hb : Body m0 F S slots oa on st) : Match (frameEnv m0 st F vars ret) (midS F) st :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial trivial

/-- **A block ending in a call of `EW::mul`, and the call**: from a body, a block that writes only
the frame (region 0) below offset `L` (the return address, locals below the pushed registers),
keeps the free callee-saved registers and leaves RSP at offset `0` calls `EW::mul`, which returns
to a body with the product of the block's RDI, RSI and RDX, RCX in RAX, RDX, the callee-saved
registers and the frame the block's. -/
theorem Body.call_mul [Host] (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 st : MachineData} {F S L : Nat} {slots : List (Nat × Reg64)} {oa : BitVec 64} {on : Nat}
    {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S₀ S₁ : SState} {st1 : MachineState} {next : Int64} {R : MachineState → Prop}
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hle : F + ewMulStack ≤ S)
    (hF8 : L ≤ F) (hslots : ∀ p ∈ slots, L ≤ p.1 ∧ p.1 + 8 ≤ F)
    (hwf : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).WF)
    (hm₀ : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₀ st)
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ st1.data)
    (hpc : PcOk (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) (.call NativeRustcVmX64.Vm.EWMul.entryLabel)
      next st1)
    (hk : keepsRegs S₀ S₁ (freeRegs slots) = true)
    (hsp : S₁.reg .rsp = some (.ptr 0 0)) (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ L)
    (cont : ∀ st2 : MachineState, st2.pc = next → Body m0 F S slots oa on st2.data →
      ewRet st2.data = EW.mul (ewArg (reg st1.data .rdi) (reg st1.data .rsi))
        (ewArg (reg st1.data .rdx) (reg st1.data .rcx)) →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st1.data r) →
      (∀ p, ¬InRange (stackBelow m0 S) S p → st2.data.dmem.get? p = st.dmem.get? p) →
      (∀ j < F + 8, st2.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) =
        st1.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j)) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st1 := by
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hr0 := (rspOf m0).isLt
  have hm144 : ewMulStack = 144 := rfl
  have hfb : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
  have hrsp1 : rspOf st1.data = stackBelow m0 F := by
    show st1.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    simp [Sym.eval]
  have hk1 : Kept m0.dmem st1.data.dmem := fun p h ↦ hm.kept hwf p (hb.kept p h)
  have hwr : ∀ p, Written (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ p →
      InRange (stackBelow m0 F) L p := fun p h ↦ written_region0 rfl hwf (by omega) hw h
  have hpre : EWMulPre st1.data := by
    refine ⟨by rw [hrsp1, hfb]; omega, by rw [hrsp1, hfb]; omega, fun i hi ↦ ?_⟩
    rw [hrsp1]
    have := hk1 _ (hS.2.2 (S - F - 144 + i) (by omega))
    rwa [show rspOf m0 - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - F - 144 + i) =
      stackBelow m0 F - BitVec.ofNat 64 ewMulStack + BitVec.ofNat 64 i by
        unfold stackBelow; rw [hm144]; bv_omega] at this
  refine call_then hpc hmul hpre fun st2 hpc2 hrsp2 hpost ↦ ?_
  obtain ⟨hax, hdx, hsame, hsaved⟩ := hpost
  have hcallee : ∀ p, InRange (stackBelow st1.data ewMulStack) ewMulStack p →
      InRange (stackBelow m0 S) S p := fun p h ↦ by
    unfold stackBelow at h
    rw [hrsp1] at h
    exact inRange_stack (n := ewMulStack) (k := 0) hS1 hle (Nat.zero_le _) (by simpa using h)
  have hblock : ∀ p, InRange (stackBelow m0 F) L p → InRange (stackBelow m0 S) S p := fun p h ↦
    inRange_stack (F := F) (n := 0) (k := L) hS1 (by omega) hF8 (by simpa using h)
  have hso : ∀ p, ¬InRange (stackBelow m0 S) S p → st2.data.dmem.get? p = st.dmem.get? p :=
    fun p hp ↦ by
      rw [hsame p fun h ↦ hp (hcallee p h), hm.get?_mem0 hwf fun h ↦ hp (hblock p (hwr p h))]
      rfl
  have hfr : ∀ j < F + 8, st2.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) =
      st1.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 j) := fun j hj ↦ by
    refine hsame _ ?_
    unfold stackBelow
    rw [hrsp1, hm144]
    exact not_inRange_below (by omega) (by omega)
  refine cont st2 hpc2 ⟨?_, fun p hp i hi ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_,
    fun p h ↦ hsaved.2 p (hk1 p h)⟩ ?_ hsaved.1 hso hfr
  · rw [hrsp2, hrsp1]; rfl
  · simp only [List.length_map, List.length_range] at hi
    obtain ⟨h8, hF⟩ := hslots p hp
    have hnw : (stackBelow m0 F).toNat + (F + 8) ≤ 2 ^ 64 := by rw [hfb]; omega
    show st2.data.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) = _
    rw [addr_add, hsame _ ?_, hm.get?_mem0 hwf ?_]
    · rw [← addr_add]; exact hb.frame p hp i hi
    · exact fun h ↦ not_inRange_above (k := L) (by omega) (by omega) (hwr _ h)
    · unfold stackBelow
      rw [hrsp1, hm144]
      exact not_inRange_below (by omega) (by omega)
  · exact (hsaved.1 r hr).trans ((regs_eq_of hm₀ hm hk r (free_mem hr hn)).trans
      (hb.regs r hr hn))
  · rw [hso p fun h ↦ hp (Or.inr h)]
    exact hb.same p hp
  · unfold ewRet ewArg
    rw [hax, hdx, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]

/-- The epilogue's callee-saved registers: each slot's register its load from the frame (region
0), the other callee-saved registers kept. -/
@[expose] def restoredRegs (slots : List (Nat × Reg64)) (S : SState) : Bool :=
  calleeRegs.all (fun r ↦ S.reg r == some (match slots.find? (·.2 == r) with
    | some p => .load 0 p.1 8
    | none => .reg r))

/-- The epilogue's registers: `restoredRegs`, RSP `8` above the return address' offset. -/
@[expose] def restores (slots : List (Nat × Reg64)) (F : Nat) (S : SState) : Bool :=
  restoredRegs slots S && S.reg .rsp == some (.ptr 0 ((F + 8 : Nat) : Int))

theorem find?_mem {slots : List (Nat × Reg64)} {r : Reg64} {p : Nat × Reg64}
    (h : slots.find? (·.2 == r) = some p) : p ∈ slots ∧ p.2 = r := by
  have h2 : (p.2 == r) = true := List.find?_some (p := fun x : Nat × Reg64 ↦ x.2 == r) h
  exact ⟨List.mem_of_find?_eq_some h, Reg64.eq_of_beq h2⟩

theorem find?_none {slots : List (Nat × Reg64)} {r : Reg64}
    (h : slots.find? (·.2 == r) = none) : r ∉ slots.map (·.2) := by
  intro hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  have := List.find?_eq_none.mp h p hp
  exact absurd this (by cases p.2 <;> decide)

/-- **The epilogue's registers**, run from a body in its frame environment: the entry's
callee-saved registers. -/
theorem Body.restored [Labels] {m0 st m : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} {S₁ : SState}
    (hb : Body m0 F S slots oa on st) (hm : Match (frameEnv m0 st F vars ret) S₁ m)
    (hr : restoredRegs slots S₁ = true) : ∀ r, calleeSaved r = true → reg m r = reg m0 r := by
  simp only [restoredRegs, List.all_eq_true, beq_iff_eq] at hr
  intro r hc
  have h := hm.regs r _ (hr r (mem_calleeRegs hc))
  cases hf : slots.find? (·.2 == r) with
  | some p =>
    obtain ⟨hp, rfl⟩ := find?_mem hf
    rw [hf] at h
    show m.regs.get64 p.2 = _
    rw [h]
    exact slot_load (r := 0) hb.frame hp
  | none =>
    rw [hf] at h
    show m.regs.get64 r = _
    rw [h]
    exact hb.regs r hc (find?_none hf)

/-- **The epilogue**: run from a body in its frame environment, it returns to the entry's return
address with RSP 8 above the entry's and the entry's callee-saved registers. -/
theorem Body.done [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {vars : Nat → BitVec 64} {ret : BitVec 64} {S₁ : SState}
    {st' : MachineState} {next : Int64} (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S)
    (hF : F ≤ S) (hm : Match (frameEnv m0 st F vars ret) S₁ st'.data)
    (hpc : PcOk (frameEnv m0 st F vars ret) (.ret (.load 0 F 8)) next st')
    (hr : restores slots F S₁ = true) (hmem : S₁.mem = [])
    (hret : ∀ j < 8, ¬InRange oa on (rspOf m0 + BitVec.ofNat 64 j)) :
    st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧ st'.data.dmem = st.dmem ∧
      Saved m0 st'.data := by
  have hwf := hb.wf (vars := vars) (ret := ret) hS hF
  simp only [restores, Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨hr, hsp⟩ := hr
  have hdm : st'.data.dmem = st.dmem := hm.dmem_eq hwf hmem
  refine ⟨?_, ?_, hdm, fun r hc ↦ ?_, fun p h ↦ ?_⟩
  · simp only [PcOk] at hpc
    rw [hpc]
    refine load_ret (stackOk_mono hS hF) fun j hj ↦ hb.same _ fun h ↦ h.elim (hret j hj) fun h ↦ ?_
    have hS1 := hS.1
    have := (rspOf m0).isLt
    rw [Sym.inRange_iff (by rw [stackBelow_toNat hS1]; omega), stackBelow_toNat hS1,
      toNat_add_ofNat _ _ (by have := hS.2.1; omega)] at h
    omega
  · show st'.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact frame_rsp F 8
  · exact hb.restored hm hr r hc
  · rw [hdm]; exact hb.kept p h

/-! ## Reading a slice in a body -/

/-- **Bytes of an argument a body did not change**: those of a region apart from the outputs and
the stack. -/
theorem same_of_apart {m0 st : MachineData} {S : Nat} {oa : BitVec 64} {on : Nat} {a : BitVec 64}
    {n : Nat} (hc : Changes m0 st S oa on) (hS : StackOk m0 S) (hna : NoWrap a n)
    (hst : OffStack m0 a n S) (ho : Apart a n oa on) (hno : NoWrap oa on) :
    ∀ j < n, st.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) := by
  have hnw : NoWrap (stackBelow m0 S) S := by
    have := hS.1
    unfold NoWrap; rw [stackBelow_toNat hS.1]; have := (rspOf m0).isLt; omega
  exact fun _ hj ↦ hc _ fun h ↦ h.elim (not_inRange_of_apart ho hna hno hj)
    (not_inRange_of_apart (apart_mono hst (Nat.le_add_right S 8)) hna hnw hj)

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

theorem add_ofNat_zero (a : BitVec 64) : a + BitVec.ofNat 64 0 = a := by simp

/-- A slice off the stack has fewer than `2 ^ 64` bytes. -/
theorem lt_of_offStack {m : MachineData} {a : BitVec 64} {n s : Nat} (hr : NoWrap a n)
    (ho : OffStack m a n s) : n < 2 ^ 64 := by
  unfold OffStack Apart at ho
  unfold NoWrap at hr
  have := (stackBelow m s).isLt
  omega

/-- A slice argument of a function whose body changes the outputs (`oa`, `on`) and `S` bytes of
stack: readable, off the stack, apart from the outputs. -/
structure SliceIn (m0 : MachineData) (S : Nat) (oa : BitVec 64) (on : Nat) (a : BitVec 64)
    (n : Nat) : Prop where
  rd : Readable m0 a (16 * n)
  off : OffStack m0 a (16 * n) S
  out : Apart a (16 * n) oa on
  nw : NoWrap oa on

/-- A slice argument of a function without outputs. -/
theorem SliceIn.of_ok {m0 : MachineData} {S : Nat} {a n : BitVec 64} (h : SliceOk m0 a n S) :
    SliceIn m0 S 0 0 a n.toNat :=
  ⟨h.1, h.2, apart_zero _ _, by unfold NoWrap; simp⟩

/-- The environment of a block reading element `i` of the slice at `a`: the frame (region 0), the
element (region 1). -/
abbrev elemEnv (m0 st : MachineData) (F : Nat) (a : BitVec 64) (i : Nat)
    (ret : BitVec 64 := 0) : Env :=
  Env.ofMachine st [(stackBelow m0 F, F + 8), (a + BitVec.ofNat 64 (16 * i), 16)] (fun _ ↦ 0) ret

/-- At such a block: the frame, RSP at its offset `8`, the element at `x - o`. -/
@[expose] def elemS (F : Nat) (x : Sym) (o : Nat) : SState :=
  init [F + 8, 16] [(.rsp, .ptr 0 8)] [] [] [(x, 1, (o : Int))]

/-- **A body at element `i`** of a region off the stack: the environment is well formed and the
body's state matches `elemS F x o` when `x` is the element's address plus `o`. -/
theorem Body.at_elem [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {a : BitVec 64} {n i : Nat} {ret : BitVec 64}
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hF : F ≤ S)
    (hr : Readable m0 a (16 * n)) (ho : OffStack m0 a (16 * n) S) (hi : i < n) {x : Sym} {o : Nat}
    (hx : x.eval (elemEnv m0 st F a i ret) = a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 o) :
    (elemEnv m0 st F a i ret).WF ∧ Match (elemEnv m0 st F a i ret) (elemS F x o) st :=
  ⟨wf_two (stackOk_mono hS hF) hb.kept (elem_mapped hr hb.kept hi)
      (elem_apart_frame hS hF hr ho hi),
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hb.rsp, trivial⟩ trivial trivial
      ⟨show x.eval (elemEnv m0 st F a i ret) = _ by
        rw [hx, BitVec.ofInt_natCast]; rfl, trivial⟩⟩

/-- **A body reading element `i`** of a slice argument: as `Body.at_elem`, and the element is the
two words the environment loads from region 1. -/
theorem Body.elem [Labels] {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {a : BitVec 64} {n i : Nat} {ret : BitVec 64}
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hF : F ≤ S)
    (hA : SliceIn m0 S oa on a n) (hi : i < n) {x : Sym} {o : Nat}
    (hx : x.eval (elemEnv m0 st F a i ret) = a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 o) :
    (elemEnv m0 st F a i ret).WF ∧ Match (elemEnv m0 st F a i ret) (elemS F x o) st ∧
      ewArg ((elemEnv m0 st F a i ret).load 1 0 8) ((elemEnv m0 st F a i ret).load 1 8 8) =
        (ewsOf m0.dmem a n)[i]'(by simp; exact hi) := by
  refine ⟨(hb.at_elem hS hF hA.rd hA.off hi hx).1, (hb.at_elem hS hF hA.rd hA.off hi hx).2, ?_⟩
  have he := elem_of_apart hb.same hS hA.rd.2 hA.off hA.out hA.nw hi
  rw [← add_ofNat_zero (a + BitVec.ofNat 64 (16 * i))] at he
  rw [← he]
  exact (ewOf_loads (elemEnv m0 st F a i ret) 1 0).symm

/-- Bytes of a sub-range are bytes of the range. -/
theorem inRange_sub {a p : BitVec 64} {n c m : Nat} (hnw : NoWrap a n) (hle : c + m ≤ n)
    (h : InRange (a + BitVec.ofNat 64 c) m p) : InRange a n p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact absurd h (by unfold InRange; omega)
  unfold NoWrap at hnw
  rw [Sym.inRange_iff (by rw [toNat_add_ofNat _ _ (by omega)]; omega),
    toNat_add_ofNat _ _ (by omega)] at h
  rw [Sym.inRange_iff hnw]
  omega

/-- The return address is not in a region off the stack. -/
theorem ret_not_in {m0 : MachineData} {a : BitVec 64} {n S : Nat} (hS : StackOk m0 S)
    (hr : NoWrap a n) (ho : OffStack m0 a n S) : ∀ j < 8, ¬InRange a n (rspOf m0 + BitVec.ofNat 64 j) := by
  intro j hj
  have hS1 := hS.1
  have hS2 := hS.2.1
  unfold OffStack Apart at ho
  unfold NoWrap at hr
  rw [stackBelow_toNat hS1] at ho
  rw [Sym.inRange_iff hr, toNat_add_ofNat _ _ (by omega)]
  omega

theorem beq_add_left (a x y : BitVec 64) : (a + x == a + y) = (x == y) := by
  by_cases h : x = y
  · simp [h]
  · have : a + x ≠ a + y := fun e ↦ h ((bv_add_left_cancel a x y).mp e)
    simp [h, this]

/-- Elements kept where memory is unchanged. -/
theorem ewsAt_congr {d d' : DataMem} {a : BitVec 64} {xs : List EW}
    (h : NativeRustcVm.EWsAt d a xs)
    (he : ∀ j < 16 * xs.length, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)) :
    NativeRustcVm.EWsAt d' a xs := fun j hj ↦ by
  have : (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length := by
    rw [List.length_flatMap]; simp [NativeRustcVm.length_ewBytes, Nat.mul_comm]
  rw [he j (by omega)]; exact h j hj

/-! ## Stores -/

/-- The bytes a block's writes cover, when all are in region `r` below `k`. -/
theorem written_region {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {n k : Nat}
    (hb : env.regions[r]? = some (b, n)) (hwf : env.WF) (hk : k ≤ n)
    (hw : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ k) {p : BitVec 64} (h : Written env S p) :
    InRange b k p := by
  obtain ⟨w, hw', b', sz, hb', h1, h2⟩ := h
  obtain ⟨hr0, hoff⟩ := hw w hw'
  rw [hr0, hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨hb1, -⟩ := hb'
  have := hwf.noWrap r b n hb
  rw [← hb1] at h1 h2
  rw [Sym.inRange_iff (by omega)]
  omega

/-- **A block storing into region 1** of a body's environment, inside the outputs, keeping RSP
and the free callee-saved registers, keeps the body. -/
theorem Body.of_store [Labels] {m0 st st' : MachineData} {F S : Nat} {slots : List (Nat × Reg64)}
    {oa : BitVec 64} {on : Nat} {b : BitVec 64} {n : Nat} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S₀ S₁ : SState} (hb : Body m0 F S slots oa on st)
    (hwf : (Env.ofMachine st [(stackBelow m0 F, F + 8), (b, n)] vars ret).WF)
    (hm₀ : Match (Env.ofMachine st [(stackBelow m0 F, F + 8), (b, n)] vars ret) S₀ st)
    (hm : Match (Env.ofMachine st [(stackBelow m0 F, F + 8), (b, n)] vars ret) S₁ st')
    (hk : keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true)
    (hw : ∀ w ∈ S₁.mem, w.r = 1 ∧ w.off + w.n ≤ n) (hin : ∀ p, InRange b n p → InRange oa on p)
    (hslots : ∀ p ∈ slots, p.1 + 8 ≤ F) : Body m0 F S slots oa on st' := by
  have he := regs_eq_of hm₀ hm hk
  have hwr : ∀ p, Written (Env.ofMachine st [(stackBelow m0 F, F + 8), (b, n)] vars ret) S₁ p →
      InRange b n p := fun p h ↦ written_region rfl hwf le_rfl hw h
  have hd := hwf.disjoint 0 1 _ _ _ _ (by decide) rfl rfl
  have hnw0 := hwf.noWrap 0 _ _ rfl
  have hnw1 := hwf.noWrap 1 _ _ rfl
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_, fun p h ↦ hm.kept hwf p (hb.kept p h)⟩
  · show reg st' .rsp = _
    rw [he .rsp (by simp)]; exact hb.rsp
  · simp only [List.length_map, List.length_range] at hi
    have := hslots p hp
    rw [addr_add, hm.get?_mem0 hwf fun h ↦ ?_, ← addr_add]
    · exact hb.frame p hp i hi
    · have h1 := hwr _ h
      rw [Sym.inRange_iff hnw1, toNat_add_ofNat _ _ (by omega)] at h1
      omega
  · rw [he r (List.mem_cons_of_mem _ (free_mem hr hn))]; exact hb.regs r hr hn
  · rw [hm.get?_mem0 hwf fun h ↦ hp (Or.inl (hin p (hwr p h)))]
    exact hb.same p hp

/-- **A block writing the frame below the pushed registers** (region 0, below offset `L`), keeping
RSP and the free callee-saved registers, keeps a body. -/
theorem Body.of_frame [Labels] {m0 st st' : MachineData} {F S L : Nat}
    {slots : List (Nat × Reg64)} {oa : BitVec 64} {on : Nat} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S₀ S₁ : SState} (hb : Body m0 F S slots oa on st)
    (hS : StackOk m0 S) (hF : F ≤ S)
    (hwf : (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret).WF)
    (hm₀ : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₀ st)
    (hm : Match (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ st')
    (hk : keepsRegs S₀ S₁ (.rsp :: freeRegs slots) = true)
    (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ L) (hL : L ≤ F)
    (hslots : ∀ p ∈ slots, L ≤ p.1 ∧ p.1 + 8 ≤ F) : Body m0 F S slots oa on st' := by
  have he := regs_eq_of hm₀ hm hk
  have hS1 := hS.1
  have hr0 := (rspOf m0).isLt
  have hfb : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
  have hwr : ∀ p, Written (Env.ofMachine st ((stackBelow m0 F, F + 8) :: rs) vars ret) S₁ p →
      InRange (stackBelow m0 F) L p := fun p h ↦ written_region0 rfl hwf (by omega) hw h
  refine ⟨?_, fun p hp i hi ↦ ?_, fun r hr hn ↦ ?_, fun p hp ↦ ?_,
    fun p h ↦ hm.kept hwf p (hb.kept p h)⟩
  · show reg st' .rsp = _
    rw [he .rsp (by simp)]; exact hb.rsp
  · simp only [List.length_map, List.length_range] at hi
    obtain ⟨h8, hF'⟩ := hslots p hp
    have hS2 := hS.2.1
    show st'.dmem.get? (stackBelow m0 F + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) = _
    rw [addr_add, hm.get?_mem0 hwf fun h ↦ not_inRange_above (k := L) (by omega) (by omega)
      (hwr _ h), ← addr_add]
    exact hb.frame p hp i hi
  · rw [he r (List.mem_cons_of_mem _ (free_mem hr hn))]; exact hb.regs r hr hn
  · rw [hm.get?_mem0 hwf fun h ↦ hp (Or.inr (inRange_stack (F := F) (n := 0) (k := L) hS1
      (by omega) hL (by simpa using hwr p h)))]
    exact hb.same p hp

/-- **A word in memory**, as an environment loads it. -/
theorem load_word {env : Env} {r o : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) w) :
    env.load r o 8 = w.toBitVec := by
  rw [load8_eq, NativeRustcVm.wordOf_of_wordAt h]

/-- The return address of states with the same RSP and the same bytes there. -/
theorem retOf_congr {m m' : MachineData} (hr : rspOf m' = rspOf m)
    (h : ∀ j < 8, m'.dmem.get? (rspOf m + BitVec.ofNat 64 j) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 j)) : retOf m' = retOf m := by
  unfold retOf
  rw [hr, loadInt_congr h]

/-- **The epilogue jumping to `EW::mul`** (a tail call): from a body, a block restoring the entry's
callee-saved registers and RSP, writing nothing, then `EW::mul` returns to the entry's caller with
the product of the block's RDI, RSI and RDX, RCX. -/
theorem Body.tail_mul [Host] (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 st : MachineData} {F S : Nat} {slots : List (Nat × Reg64)} {oa : BitVec 64} {on : Nat}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S₁ : SState} {st' : MachineState}
    (hb : Body m0 F S slots oa on st) (hS : StackOk m0 S) (hF : F ≤ S) (hle : ewMulStack ≤ S)
    (hm : Match (frameEnv m0 st F vars ret) S₁ st'.data) (hpc : st'.pc = Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel)
    (hr : restoredRegs slots S₁ = true) (hsp : S₁.reg .rsp = some (.ptr 0 F))
    (hmem : S₁.mem = []) (hret : ∀ j < 8, ¬InRange oa on (rspOf m0 + BitVec.ofNat 64 j)) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ rspOf s.data = rspOf m0 + 8#64 ∧
      ewRet s.data = EW.mul (ewArg (reg st'.data .rdi) (reg st'.data .rsi))
        (ewArg (reg st'.data .rdx) (reg st'.data .rcx)) ∧
      Changes m0 s.data S oa on ∧ Saved m0 s.data) st' := by
  have hwf := hb.wf (vars := vars) (ret := ret) hS hF
  have hdm : st'.data.dmem = st.dmem := hm.dmem_eq hwf hmem
  have hS1 := hS.1
  have hS2 := hS.2.1
  have hr0 := (rspOf m0).isLt
  have hm144 : ewMulStack = 144 := rfl
  have hrsp : rspOf st'.data = rspOf m0 := by
    show st'.data.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    show stackBelow m0 F + BitVec.ofInt 64 ((F : Nat) : Int) = rspOf m0
    rw [BitVec.ofInt_natCast]
    exact BitVec.sub_add_cancel _ _
  have hk : Kept m0.dmem st'.data.dmem := fun p h ↦ by rw [hdm]; exact hb.kept p h
  have hsaved : Saved m0 st'.data := ⟨hb.restored hm hr, hk⟩
  have hretb : ∀ j < 8, st'.data.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) := fun j hj ↦ by
    rw [hdm]
    refine hb.same _ fun h ↦ h.elim (hret j hj) fun h ↦ ?_
    rw [Sym.inRange_iff (by rw [stackBelow_toNat hS1]; omega), stackBelow_toNat hS1,
      toNat_add_ofNat _ _ (by omega)] at h
    omega
  have hpre : EWMulPre st'.data := by
    refine ⟨by rw [hrsp, hm144]; omega, by rw [hrsp]; exact hS2, fun i hi ↦ ?_⟩
    have := hk _ (hS.2.2 (S - 144 + i) (by omega))
    rw [hrsp]
    rwa [show rspOf m0 - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - 144 + i) =
      rspOf m0 - BitVec.ofNat 64 ewMulStack + BitVec.ofNat 64 i by rw [hm144]; bv_omega] at this
  refine Eventually.mono (Spec.apply hmul hpc hpre) fun s ⟨hpc', hrsp', hax, hdx, hsame, hsv⟩ ↦
    ⟨by rw [hpc', retOf_congr hrsp hretb], by rw [hrsp', hrsp], ?_, fun p hp ↦ ?_,
      hsaved.trans hsv⟩
  · unfold ewRet ewArg
    rw [hax, hdx, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
  · rw [hsame p fun h ↦ hp (Or.inr ?_), hdm]
    · exact hb.same p hp
    · unfold stackBelow at h ⊢
      rw [hrsp] at h
      refine inRange_stack (m := m0) (F := 0) (n := ewMulStack) (k := 0) hS1 (by omega) le_rfl ?_
      simpa [stackBelow] using h

/-- **A stored word**: where the newest writes of `v` cover the 8 bytes at `o` in region `r`, they
hold `v`'s value. -/
theorem wordAt_of_write [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := by
  have := hm.bytesAt_write hb hle hw
  unfold NativeRustcVm.WordAt
  rw [NativeRustcVm.wordBytes_eq]
  exact this

/-- **Bytes kept**: bytes in region `r` that no write of the block covers keep their values. -/
theorem bytesAt_keep [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) {bs : List UInt8}
    (hle : o + bs.length ≤ sz) (h : firstOverlap r o bs.length S.mem = none)
    (h0 : BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := by
  intro i hi
  rw [addr_add, hm.mem r b sz hb (o + i) (by omega)]
  unfold memByte
  rw [findWrite_none h (Nat.le_add_right o i) (by omega), ← addr_add]
  exact h0 i hi

/-- **A word kept** by a block whose writes miss it. -/
theorem wordAt_keep [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz)
    (h : firstOverlap r o 8 S.mem = none) {w : UInt64}
    (h0 : NativeRustcVm.WordAt env.mem0 (b + BitVec.ofNat 64 o) w) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) w :=
  bytesAt_keep hm hb (by rw [NativeRustcVm.length_wordBytes]; exact hle)
    (by rw [NativeRustcVm.length_wordBytes]; exact h) h0

/-- A word where memory is unchanged. -/
theorem wordAt_congr {d d' : DataMem} {a : BitVec 64} {w : UInt64}
    (h : NativeRustcVm.WordAt d a w)
    (he : ∀ j < 8, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)) :
    NativeRustcVm.WordAt d' a w := fun j hj ↦ by
  rw [he j (by rw [NativeRustcVm.length_wordBytes] at hj; exact hj)]; exact h j hj

/-- `E`'s sum commutes. -/
theorem ew_add_comm (a b : EW) : a + b = b + a := by
  show (⟨_, _⟩ : EW) = ⟨_, _⟩
  rw [UInt64.xor_comm a.c0, UInt64.xor_comm a.c1]

/-- **`1` minus bit `y` of `x`** (`shr %cl`, `notl`, `andl $1`), for `y < 64`. -/
theorem nbit_eval (x y : BitVec 64) (hy : y.toNat < 64) :
    BinOp.apply .and .W32 (UnOp.apply .not .W32 (BinOp.apply .shr .W64 x y)) (BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (1 - (x.toNat >>> y.toNat) % 2) := by
  have hc : shiftCount .W64 y = y.toNat := by
    unfold shiftCount shiftMask
    rw [toNat_low, show Width.W8.bits = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, UnOp.apply, hc, low_W64, ext_W64, toNat_ext, BitVec.toNat_and,
    BitVec.toNat_not, toNat_low, BitVec.toNat_ofNat]
  rw [show (x.ushiftRight y.toNat).toNat = x.toNat >>> y.toNat from BitVec.toNat_ushiftRight x _,
    show Width.W32.bits = 32 from rfl, show (1 : Nat) % 2 ^ 64 % 2 ^ 32 = 1 from rfl,
    Nat.and_one_is_mod]
  generalize x.toNat >>> y.toNat = z
  omega

/-- `1 - b` for a bit `b`, in limb `0`: `1 + b`. -/
theorem one_add_bit (b : Nat) (hb : b < 2) :
    ewArg (BitVec.ofNat 64 (1 - b)) (BitVec.ofNat 64 0) = 1 + EW.ofNat b := by
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl

/-- The carry of raw `bt`: bit `y` of `x`, for `y < 64`. -/
theorem bt_cf (x y : BitVec 64) (hy : y.toNat < 64) :
    CmpOp.apply .bit .W64 x y = decide ((x.toNat >>> y.toNat) % 2 = 1) := by
  simp only [CmpOp.apply, low_W64, show Width.W64.bits = 64 from rfl,
    Nat.mod_eq_of_lt hy, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq,
    Nat.shiftRight_eq_div_pow]

/-- `setb` into a zeroed register: the carry as `0` or `1`. -/
theorem setb_eval (c : Bool) :
    BinOp.apply .merge .W8 (BitVec.ofNat 64 0) (if c then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) =
      BitVec.ofNat 64 c.toNat := by
  cases c <;> decide

/-- A bit as `0` or `1`, in limb `0`. -/
theorem ewArg_bit (t : Nat) :
    ewArg (BitVec.ofNat 64 (decide (t % 2 = 1)).toNat) 0#64 = EW.ofNat (t % 2) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> rw [h] <;> rfl

/-- `xor` into limb `0`: the sum with an element of limb `1` zero. -/
theorem ewArg_xor_lo (a b c : BitVec 64) : ewArg (a ^^^ c) b = ewArg c 0#64 + ewArg a b := by
  show (⟨_, _⟩ : EW) = ⟨_, _⟩
  congr 1
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor]
    exact BitVec.xor_comm _ _
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor]
    show b = 0#64 ^^^ b
    rw [BitVec.zero_xor]

/-- **A stored element**: two words at `o`, `o + 8`. -/
theorem ewAt_of_writes [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r o sz : Nat} {b : BitVec 64} (hb : env.regions[r]? = some (b, sz)) (hle : o + 16 ≤ sz)
    {u v : Sym} (hu : ∀ i < 8, findWrite r (o + i) S.mem = some (u, i))
    (hv : ∀ i < 8, findWrite r (o + 8 + i) S.mem = some (v, i)) :
    NativeRustcVm.EWAt m.dmem (b + BitVec.ofNat 64 o) (ewArg (u.eval env) (v.eval env)) := by
  rw [NativeRustcVm.ewAt_iff]
  refine ⟨wordAt_of_write hm hb (by omega) hu, ?_⟩
  have := wordAt_of_write hm hb (by omega) hv
  rwa [← addr_add] at this

/-! ## Evaluating the executor's values -/

section
variable [Labels] {env : Env}

theorem eval_reg (r : Reg64) : (Sym.reg r).eval env = env.regs r := rfl

theorem eval_lit (n : Nat) : (Sym.lit n).eval env = BitVec.ofNat 64 n := rfl

theorem eval_load (r o n : Nat) : (Sym.load r o n).eval env = env.load r o n := rfl

theorem eval_add (a b : Sym) : (Sym.bin .add .W64 a b).eval env = a.eval env + b.eval env := by
  simp [Sym.eval, BinOp.apply]

theorem eval_xor (a b : Sym) : (Sym.bin .xor .W64 a b).eval env = a.eval env ^^^ b.eval env := by
  simp [Sym.eval, BinOp.apply]

theorem eval_shl_lit (a : Sym) {j : Nat} (hj : j < 64) :
    (Sym.bin .shl .W64 a (.lit j)).eval env = a.eval env <<< j := by
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask]
  congr 1
  simp only [low, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by
    show j < 2 ^ 8; omega)]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)

theorem eval_not (b : SBool) : (SBool.not b).eval env = !b.eval env := rfl

theorem eval_cmp_eq (a b : Sym) : (SBool.cmp .eq .W64 a b).eval env = (a.eval env == b.eval env) := by
  simp [SBool.eval, CmpOp.apply]

/-- `test v, v` for `je`. -/
theorem eval_test (v : Sym) :
    (SBool.cmp .eq .W64 (.bin .and .W64 v v) (.lit 0)).eval env =
      (v.eval env == BitVec.ofNat 64 0) := by
  simp [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply]

/-- `cmp`, `cmovb`: the smaller of two registers. -/
theorem eval_min (x y : Reg64) :
    (Sym.ite (.cmp .ult .W64 (.reg y) (.reg x)) (.reg y) (.reg x)).eval env =
      BitVec.ofNat 64 (min (env.regs x).toNat (env.regs y).toNat) := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  apply BitVec.eq_of_toNat_eq
  split <;> rename_i h <;> simp only [BitVec.ult_iff_lt, BitVec.lt_def] at h <;>
    simp only [BitVec.toNat_ofNat] <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega

end

theorem noWrap_zero : NoWrap 0 0 := by unfold NoWrap; simp

theorem not_inRange_zero (p : BitVec 64) : ¬InRange 0 0 p := by unfold InRange; omega

/-! ## Values -/

theorem add_eval (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp [BinOp.apply]

theorem xor_eval (x y : BitVec 64) : BinOp.apply .xor .W64 x y = x ^^^ y := by
  simp [BinOp.apply]

theorem toBitVec_eq {a : UInt64} {b : BitVec 64} (h : a.toBitVec = b) : a = UInt64.ofBitVec b := by
  rw [← h]

/-- `xor $1` on limb `0`: one plus the element. -/
theorem one_add_ewArg (x y : BitVec 64) : ewArg (x ^^^ BitVec.ofNat 64 1) y = 1 + ewArg x y := by
  show (⟨_, _⟩ : EW) = ⟨1 ^^^ _, 0 ^^^ _⟩
  congr 1
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor]
    exact BitVec.xor_comm _ _
  · apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_xor, UInt64.toBitVec_zero, BitVec.zero_xor]
    rfl

/-- The limbs' `xor`s: the sum. -/
theorem ewArg_xor (a b c d : BitVec 64) : ewArg (a ^^^ c) (b ^^^ d) = ewArg a b + ewArg c d := rfl

/-- The returned element's limbs. -/
theorem ewRet_eq (m : MachineData) : ewArg (reg m .rax) (reg m .rdx) = ewRet m := rfl

/-- `16 + (a + 16 i)`. -/
theorem add16 (a : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 16 + (a + BitVec.ofNat 64 (16 * i)) = a + BitVec.ofNat 64 (16 * (i + 1)) := by
  rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 16 * i + 16 = 16 * (i + 1) by omega]

/-- A conditional branch's target, by the condition, whatever its decidability instance. -/
theorem pc_cond {pc a b : Int64} {c : Prop} {inst : Decidable c} (h : pc = @ite _ c inst a b) :
    (c → pc = a) ∧ (¬c → pc = b) := by
  cases inst with
  | isTrue hc => exact ⟨fun _ ↦ h, fun hn ↦ absurd hc hn⟩
  | isFalse hc => exact ⟨fun hn ↦ absurd hn hc, fun _ ↦ h⟩

/-! ## Shared by the leaf functions -/

theorem low8_replaceLow (x : BitVec 64) (y : BitVec 8) : low .W8 (x.replaceLow y) = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi8 : i < 8 := hi
  simp only [low, BitVec.replaceLow, BitVec.getLsbD_setWidth]
  change (decide (i < 8) && (decide (i < 64) && ((x.drop 8) ++ y).getLsbD i)) = _
  rw [BitVec.getLsbD_append]
  simp [hi8, show i < 64 by omega]

/-- `movb $1, %al`: the low byte `1`. -/
theorem merge_one_mod (x : BitVec 64) :
    (BinOp.apply .merge .W8 x (BitVec.ofNat 64 1)).toNat % 256 = 1 := by
  have h := congrArg BitVec.toNat (low8_replaceLow x (low .W8 (BitVec.ofNat 64 1)))
  rw [toNat_low, toNat_low] at h
  exact h

theorem beq_ofNat (x : BitVec 64) {c : Nat} (hc : c < 2 ^ 64) :
    (x == BitVec.ofNat 64 c) = decide (x.toNat = c) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem neg_add_beq_one {a b : Nat} (ha : a + 1 < 2 ^ 64) (hb : b < 2 ^ 64) :
    (-BitVec.ofNat 64 a + BitVec.ofNat 64 b == BitVec.ofNat 64 1) = decide (b = a + 1) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq, BitVec.toNat_add,
    BitVec.toNat_neg, toNat_ofNat_lt (by omega), toNat_ofNat_lt hb, toNat_ofNat_lt (by decide)]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [h64] at ha hb ⊢
  omega

theorem sub8_beq_zero {a : Nat} (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 (2 ^ 64 - 8) + BitVec.ofNat 64 a == BitVec.ofNat 64 0) = decide (a = 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq, BitVec.toNat_add,
    toNat_ofNat_lt ha, toNat_ofNat_lt (by decide), toNat_ofNat_lt (by decide)]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [h64] at ha ⊢
  omega

/-- The bytes no write of a block covers, with writes only in region 0 below `k0` and region 1
below `k1`. -/
theorem same01 [Labels] {st m : MachineData} {a0 a1 : BitVec 64} {n0 n1 k0 k1 : Nat}
    {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine st ((a0, n0) :: (a1, n1) :: rs)) S m)
    (hwf : (Env.ofMachine st ((a0, n0) :: (a1, n1) :: rs)).WF) (hk0 : k0 ≤ n0) (hk1 : k1 ≤ n1)
    (hw : ∀ w ∈ S.mem, (w.r = 0 ∧ w.off + w.n ≤ k0) ∨ (w.r = 1 ∧ w.off + w.n ≤ k1)) :
    ∀ p, ¬InRange a0 k0 p → ¬InRange a1 k1 p → m.dmem.get? p = st.dmem.get? p :=
  fun p hp0 hp1 ↦ hm.get?_mem0 hwf fun ⟨w, hw', b, sz, hb', h1, h2⟩ ↦ by
    have hn0 := hwf.noWrap 0 _ _ rfl
    have hn1 := hwf.noWrap 1 _ _ rfl
    rcases hw w hw' with ⟨hr0, hoff⟩ | ⟨hr1, hoff⟩
    · rw [hr0] at hb'
      change some (a0, n0) = some (b, sz) at hb'
      cases hb'
      exact hp0 (by rw [Sym.inRange_iff (by omega)]; omega)
    · rw [hr1] at hb'
      change some (a1, n1) = some (b, sz) at hb'
      cases hb'
      exact hp1 (by rw [Sym.inRange_iff (by omega)]; omega)

/-- **The return address**, loaded from region 0 of an environment whose region 0 is the frame. -/
theorem load_ret2 {m0 m : MachineData} {F : Nat} {rs : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (h : StackOk m0 F)
    (hsame : ∀ j < 8, m.dmem.get? (rspOf m0 + BitVec.ofNat 64 j) =
      m0.dmem.get? (rspOf m0 + BitVec.ofNat 64 j)) :
    Int64.ofBitVec ((Env.ofMachine m ((stackBelow m0 F, F + 8) :: rs) vars ret).load 0 F 8) =
      retOf m0 :=
  load_ret (vars := vars) (ret := ret) h hsame

theorem addr_eq {a : BitVec 64} {x y : Nat} (h : x = y) :
    a + BitVec.ofNat 64 x = a + BitVec.ofNat 64 y := by rw [h]

end

end NativeRustcVmX64.Arrays
