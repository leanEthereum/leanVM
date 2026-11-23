module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Infix
public import NativeRustcArm.Hasher.Bytes
public import NativeRustcVm.MemLemmas
public import NativeRustcVmArm.Spec.Layout
public import NativeRustcVm.Layout.RepLemmas

/-!
# The layout's proofs: what they share

- Runs: the state a block ends in (`after`), to run the next block from (`exec_after`); a block of
  a placed function is in the program (`infix_of`).
- Loads: a word in memory at a region's offset is what the environment loads there (`load_word`).
- Writes: an 8-byte write of a block is the word in memory after it (`Match.wordAt_write`); a
  block whose writes stay inside its regions changes memory only there (`Match.sameOutside_regions`,
  `InRegions`).
- The stack: the `n` bytes below SP of a `StackOk m n` are a region (`stack_mapped`,
  `stack_noWrap`, `stack_aligned`).
- A return leaves the machine at the caller's address when X30 is kept (`retOf_of_x30`).
-/

namespace NativeRustcVmArm.Layout

open NativeRustcArm NativeRustcArm.Sym

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

/-- A block of a placed function in the program. -/
theorem infix_of [Host] {F b : List Directive} {k j : Nat} (hb : b.IsInfixAt F j) (hne : b ≠ [])
    (hp : Placed F k) : b.IsInfixAt Host.prog (k + j) :=
  List.IsInfixAt.trans hb hp.1 hne

/-! ## Loads -/

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (NativeRustcVm.wordBytes v)) = v.toBitVec := by
  have hw := Hasher.wordBytes_ofBitVec v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  rw [NativeRustcVm.wordBytes, hw, hb, BitVec.ofInt_natCast]
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

/-! ## Regions -/

/-- `p` is a byte of one of the regions. -/
@[expose] def InRegions (rs : List (BitVec 64 × Nat)) (p : BitVec 64) : Prop :=
  ∃ e ∈ rs, InRange e.1 e.2 p

/-- Every write of `S` is inside its region. -/
@[expose] def WritesIn (S : SState) : Bool :=
  S.mem.all fun w ↦ match S.regions[w.r]? with
    | some (sz, _) => decide (w.off + w.n ≤ sz)
    | none => false

/-- **Where a block wrote**: in its regions, when each write is inside its region (`WritesIn`,
by `decide` on the literal state). -/
theorem Match.sameOutside_regions [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) (hwf : env.WF) (hS : WritesIn S = true) :
    SameOutside env.mem0 m.dmem (InRegions env.regions) := by
  intro p hp
  refine hm.sameOutside hwf p fun hw0 ↦ hp ?_
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hw0
  have hw' := List.all_eq_true.mp hS w hw
  refine ⟨(b, sz), List.mem_of_getElem? hb, ?_⟩
  split at hw'
  · rename_i sz' al hr
    obtain ⟨b', hb', -⟩ := hm.regions _ _ _ hr
    rw [hb] at hb'
    cases hb'
    have hle : w.off + w.n ≤ sz := of_decide_eq_true hw'
    have hnw := hwf.noWrap _ _ _ hb
    exact (inRange_iff hnw).mpr ⟨by omega, by omega⟩
  · exact absurd hw' (by simp)

/-- **Bytes no write of a block touched**: the `len` bytes at `o` of region `r`, which no write
overlaps (`firstOverlap`, by `decide` on the literal state), are the environment's. -/
theorem Match.same_untouched [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o len : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + len ≤ sz)
    (h : firstOverlap r o len S.mem = none) :
    NativeRustcVm.Layout.Same env.mem0 m.dmem (b + BitVec.ofNat 64 o) len := fun j hj ↦ by
  rw [NativeRustcVm.addr_add_add, hm.mem r b sz hb (o + j) (by omega)]
  unfold memByte
  rw [findWrite_none h (by omega) (by omega)]

/-- `ptr r 0` is region `r`'s base. -/
theorem ofInt_zero : BitVec.ofInt 64 0 = 0#64 := by
  apply BitVec.eq_of_toNat_eq; simp

/-! ## The stack -/

theorem stack_mapped {m : MachineData} {n : Nat} (h : StackOk m n) :
    Mapped m.dmem (stackBelow m n) n := h.2.2

theorem stack_toNat {m : MachineData} {n : Nat} (h : StackOk m n) :
    (stackBelow m n).toNat = m.regs.SP.toNat - n :=
  NativeRustcVm.toNat_sub_ofNat h.2.1

theorem stack_noWrap {m : MachineData} {n : Nat} (h : StackOk m n) :
    NativeRustcVm.NoWrap (stackBelow m n) n := by
  unfold NativeRustcVm.NoWrap
  rw [stack_toNat h]
  have := m.regs.SP.toNat_lt
  have := h.2.1
  omega

theorem stack_aligned {m : MachineData} {n : Nat} (h : StackOk m n) (hn : n % 16 = 0) :
    (stackBelow m n).toNat % 16 = 0 := by
  rw [stack_toNat h]
  have := h.1
  have := h.2.1
  omega

/-- SP is the stack's base plus its size. -/
theorem sp_eq_stackBelow {m : MachineData} {n : Nat} :
    m.regs.SP.toBitVec = stackBelow m n + BitVec.ofInt 64 (n : Int) := by
  rw [stackBelow, BitVec.ofInt_natCast, BitVec.sub_add_cancel]

/-! ## Returns -/

/-- Where a block returns: the entry's return address, X30 kept. -/
theorem retOf_of_x30 [Labels] {env : Env} {S : SState} {m m' : MachineData}
    (hm : Match env S m') (hS : S.reg .X30 = some (.reg .X30))
    (henv : env.regs .X30 = m.regs.X30.toBitVec) : retOf m' = retOf m := by
  have := hm.regs .X30 _ hS
  simp only [Sym.eval] at this
  simp only [retOf]
  rw [show m'.regs.X30 = m.regs.X30 from UInt64.toBitVec_inj.mp (this.trans henv)]

end

end NativeRustcVmArm.Layout
