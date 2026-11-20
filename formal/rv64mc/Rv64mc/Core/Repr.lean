/-
  Rv64mc.Core.Repr

  How the guest's values sit in memory, and what a call keeps of them. Memory is riscv-zkvm's: a doubleword per
  address (`getMem`), loads and stores of a doubleword at 8-aligned addresses, and a byte at `a` is byte
  `byteOffset a` of the doubleword at `alignToDword a` (`getByte`). Every offset is a generated layout constant
  (`Rv64mc.Layouts`, `scripts/type-layouts.sh`), never a literal.

  * Footprints: `InRange a n` is `[a, a + n)` without wrapping; `Keeps m m' a n` says `m'` has `m`'s doublewords
    there. A call's frame (`Env.Frame`) keeps what it may not write (`Env.Frame.keeps`): an object of the caller's
    heap (`Live`, below `NEXT`) or of its frame (above the callee's stack top), outside the call's `out`.
  * The bump allocator never frees, so `NEXT` is a watermark: what lives is below it (`Live`), what a call allocates
    lies between `NEXT` before and after (`Fresh`), apart from every `Live` object (`Fresh.disjoint`).
  * Values: `WordsAt` (consecutive `u64`s), `EAt` and `EListAt` (an `E` is its limbs `c0`, `c1`), `BytesAt`,
    `DigestAt`, `VecAt` (a `Vec<T>`'s header and its elements at its pointer), `SliceArgs` (a slice passed as a
    pointer and a length). Each has a `keep` lemma: a value is read back from any state that keeps its footprint.
  * Bytes: `getByte` through a doubleword store (`getByte_setMem_ne`, `getByte_setMem_aligned`) and a byte store
    (`getByte_setByte_eq`, `getByte_setByte_ne`), and `ByteFrame`, the bytes a call keeps.
-/

import Rv64mc.Core.Holds
import Rv64mc.Gen.Layouts
import RiscvZkvm.Rv64.Logic.MemRegionWrite

namespace Rv64mc

open RiscvZkvm.Rv64

/-! ## Footprints -/

/-- `b` is in `[a, a + n)`, as numbers. -/
def InRange (a : Word) (n : Nat) (b : Word) : Prop := a.toNat ≤ b.toNat ∧ b.toNat < a.toNat + n

/-- `m'` has `m`'s doublewords in `[a, a + n)`. -/
def Keeps (m m' : MachineState) (a : Word) (n : Nat) : Prop := ∀ b, InRange a n b → m'.getMem b = m.getMem b

theorem Keeps.trans {m m1 m2 : MachineState} {a : Word} {n : Nat} (h1 : Keeps m m1 a n) (h2 : Keeps m1 m2 a n) :
    Keeps m m2 a n := fun b hb => (h2 b hb).trans (h1 b hb)

theorem Keeps.mono {m m' : MachineState} {a a' : Word} {n n' : Nat} (h : Keeps m m' a n)
    (hlo : a.toNat ≤ a'.toNat) (hhi : a'.toNat + n' ≤ a.toNat + n) : Keeps m m' a' n' :=
  fun b hb => h b ⟨by have := hb.1; omega, by have := hb.2; omega⟩

/-- A store outside the footprint keeps it. -/
theorem Keeps.setMem {m : MachineState} {a c v : Word} {n : Nat} (hc : ¬ InRange a n c) :
    Keeps m (m.setMem c v) a n := fun b hb => by
  have : b ≠ c := fun h => hc (h ▸ hb)
  simp [MachineState.getMem, MachineState.setMem, this]

/-- `a + k` as a number, without wrapping. -/
theorem toNat_add_ofNat {a : Word} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-! ## The heap's watermark, and what a call keeps -/

namespace Env

variable {env : Env}

/-- `[a, a + n)` lies below `NEXT`: allocated before. -/
def Live (env : Env) (m : MachineState) (a : Word) (n : Nat) : Prop := a.toNat + n ≤ (env.next m).toNat

/-- `[a, a + n)` lies between `NEXT` in `m` and in `m'`: allocated between them. -/
def Fresh (env : Env) (m m' : MachineState) (a : Word) (n : Nat) : Prop :=
  (env.next m).toNat ≤ a.toNat ∧ a.toNat + n ≤ (env.next m').toNat

theorem Live.frame {top : Word} {out : Word → Prop} {m m' : MachineState} {a : Word} {n : Nat}
    (h : env.Live m a n) (hf : env.Frame top out m m') : env.Live m' a n := by
  have := hf.1; unfold Live at *; omega

theorem Fresh.live {m m' : MachineState} {a : Word} {n : Nat} (h : env.Fresh m m' a n) : env.Live m' a n := h.2

/-- **What a call allocates is apart from what lived before it.** -/
theorem Fresh.disjoint {m m' : MachineState} {a b : Word} {n k : Nat} (h : env.Fresh m m' a n)
    (hb : env.Live m b k) (c : Word) (hc : InRange a n c) : ¬ InRange b k c := by
  have := h.1; unfold Live at hb; unfold InRange at *; omega

/-- **A call keeps what it may not write.** -/
theorem Frame.keeps {top : Word} {out : Word → Prop} {m m' : MachineState} {a : Word} {n : Nat}
    (h : env.Frame top out m m') (hw : ∀ b, InRange a n b → ¬ env.MayWrite top out m m' b) : Keeps m m' a n :=
  fun b hb => h.2.2 b (hw b hb)

/-- A call keeps the caller's heap objects outside its `out`. -/
theorem Frame.keeps_live {top : Word} {out : Word → Prop} {m m' : MachineState} {a : Word} {n : Nat}
    (h : env.Frame top out m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hl : env.Live m a n)
    (hout : ∀ b, InRange a n b → ¬ out b) : Keeps m m' a n :=
  fun b hb => h.getMem_below_next hnx (by have := hb.2; unfold Live at hl; omega) (hout b hb)

/-- A call keeps what lies at or above its stack top (the caller's frame) outside its `out`. -/
theorem Frame.keeps_above {top : Word} {out : Word → Prop} {m m' : MachineState} {a : Word} {n : Nat}
    (h : env.Frame top out m m') (hlim : env.stackLimit.toNat ≤ top.toNat) (ha : top.toNat ≤ a.toNat)
    (hout : ∀ b, InRange a n b → ¬ out b) : Keeps m m' a n :=
  fun b hb => h.getMem_above hlim (by have := hb.1; omega) (hout b hb)

end Env

/-! ## Values -/

section Values

variable {m m' : MachineState}

/-- **The `u64`s `ws` from `a`**, word `k` at `a + 8k`. -/
def WordsAt (m : MachineState) (a : Word) (ws : List Word) : Prop :=
  a.toNat + 8 * ws.length < 2 ^ 64 ∧ ∀ k (h : k < ws.length), m.getMem (a + BitVec.ofNat 64 (8 * k)) = ws[k]

theorem WordsAt.keep {a : Word} {ws : List Word} (h : WordsAt m a ws) (hk : Keeps m m' a (8 * ws.length)) :
    WordsAt m' a ws := by
  refine ⟨h.1, fun k hk' => ?_⟩
  rw [hk _ ⟨by rw [toNat_add_ofNat (by have := h.1; omega)]; omega,
    by rw [toNat_add_ofNat (by have := h.1; omega)]; omega⟩, h.2 k hk']

/-- **The `E` with limbs `e` at `a`**: `c0` and `c1` at their offsets. -/
def EAt (m : MachineState) (a : Word) (e : Word × Word) : Prop :=
  m.getMem (a + BitVec.ofNat 64 Layouts.E.c0) = e.1 ∧ m.getMem (a + BitVec.ofNat 64 Layouts.E.c1) = e.2

theorem EAt.keep {a : Word} {e : Word × Word} (h : EAt m a e) (ha : a.toNat + Layouts.E.byteSize < 2 ^ 64)
    (hk : Keeps m m' a Layouts.E.byteSize) : EAt m' a e := by
  simp only [EAt, Layouts.E.c0, Layouts.E.c1, Layouts.E.byteSize] at h ha hk ⊢
  have e : ∀ k, k < 16 → m'.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k) :=
    fun k hk' => hk _ ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
  rw [e 0 (by decide), e 8 (by decide)]; exact h

/-- **The `E`s `es` from `a`**, element `k` at `a + 16k`. -/
def EListAt (m : MachineState) (a : Word) (es : List (Word × Word)) : Prop :=
  a.toNat + Layouts.E.byteSize * es.length < 2 ^ 64 ∧
    ∀ k (h : k < es.length), EAt m (a + BitVec.ofNat 64 (Layouts.E.byteSize * k)) es[k]

theorem EListAt.keep {a : Word} {es : List (Word × Word)} (h : EListAt m a es)
    (hk : Keeps m m' a (Layouts.E.byteSize * es.length)) : EListAt m' a es := by
  have h1 := h.1
  simp only [Layouts.E.byteSize] at h1 hk ⊢
  have hlt : ∀ k, k < es.length → a.toNat + 16 * k + 16 ≤ a.toNat + 16 * es.length := fun k hk => by omega
  refine ⟨h.1, fun k hk' => (h.2 k hk').keep ?_ (hk.mono ?_ ?_)⟩ <;>
    have := hlt k hk' <;> simp only [Layouts.E.byteSize] <;>
    rw [toNat_add_ofNat (by omega)] <;> omega

/-- **The bytes `bs` from `a`.** -/
def BytesAt (m : MachineState) (a : Word) (bs : List (BitVec 8)) : Prop :=
  a.toNat + bs.length < 2 ^ 64 ∧ ∀ k (h : k < bs.length), m.getByte (a + BitVec.ofNat 64 k) = bs[k]

/-- **A `Digest`** (32 bytes) at `a`. -/
def DigestAt (m : MachineState) (a : Word) (d : List (BitVec 8)) : Prop :=
  d.length = Layouts.Digest.byteSize ∧ BytesAt m a d

/-- The capacity, pointer and length of the `Vec<T>` header at `a`. -/
def vecCap (m : MachineState) (a : Word) : Word := m.getMem (a + BitVec.ofNat 64 Layouts.Vec.cap)
def vecPtr (m : MachineState) (a : Word) : Word := m.getMem (a + BitVec.ofNat 64 Layouts.Vec.ptr)
def vecLen (m : MachineState) (a : Word) : Word := m.getMem (a + BitVec.ofNat 64 Layouts.Vec.len)

/-- **The `Vec<T>` at `a` holds `xs`**: its header says capacity `cap`, pointer `ptr`, length `|xs|`, and
    `Elems` reads `xs` at `ptr` (`WordsAt`, `EListAt`, ...). -/
structure VecAt {α : Type} (Elems : MachineState → Word → List α → Prop) (m : MachineState) (a ptr : Word)
    (cap : Nat) (xs : List α) : Prop where
  ptr_eq : vecPtr m a = ptr
  cap_eq : vecCap m a = BitVec.ofNat 64 cap
  len_eq : vecLen m a = BitVec.ofNat 64 xs.length
  len_le : xs.length ≤ cap
  cap_lt : cap < 2 ^ 63
  elems : Elems m ptr xs

theorem VecAt.keep {α : Type} {Elems : MachineState → Word → List α → Prop} {a ptr : Word} {cap : Nat}
    {xs : List α} (h : VecAt Elems m a ptr cap xs) (ha : a.toNat + Layouts.Vec.byteSize < 2 ^ 64)
    (hk : Keeps m m' a Layouts.Vec.byteSize) (he : Elems m ptr xs → Elems m' ptr xs) :
    VecAt Elems m' a ptr cap xs := by
  simp only [Layouts.Vec.byteSize] at ha hk
  have e : ∀ k, k < 24 → m'.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k) :=
    fun k hk' => hk _ ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩
  exact ⟨by rw [vecPtr, e _ (by decide)]; exact h.ptr_eq, by rw [vecCap, e _ (by decide)]; exact h.cap_eq,
    by rw [vecLen, e _ (by decide)]; exact h.len_eq, h.len_le, h.cap_lt, he h.elems⟩

/-- **A slice passed as a pointer and a length** holds `xs`. -/
def SliceArgs {α : Type} (Elems : MachineState → Word → List α → Prop) (m : MachineState) (ptr len : Word)
    (xs : List α) : Prop :=
  len = BitVec.ofNat 64 xs.length ∧ Elems m ptr xs

end Values

/-! ## Registers at a return -/

/-- A write to a register the calling convention does not keep leaves `AbiRegs` as it was: for `simp` over the
    register file a function returns with, its side condition by `decide`. -/
theorem AbiRegs.updReg_iff {top : Word} {regs R : Reg → Word} {r : Reg} {v : Word}
    (hr : r ∉ [.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]) :
    AbiRegs top regs (Lprog.updReg R r v) ↔ AbiRegs top regs R := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h2, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hr
  simp [AbiRegs, Lprog.updReg_apply, Ne.symm h2, Ne.symm h8, Ne.symm h9, Ne.symm h18, Ne.symm h19,
    Ne.symm h20, Ne.symm h21, Ne.symm h22, Ne.symm h23, Ne.symm h24, Ne.symm h25, Ne.symm h26, Ne.symm h27]

/-- A function that changed no kept register returns with `AbiRegs`. -/
theorem AbiRegs.refl {top : Word} {regs : Reg → Word} (h : regs .x2 = top) : AbiRegs top regs regs :=
  ⟨h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The precondition of a call through `Holds` from a caller with register file `R` and memory `m`, as `lsym`
    states it. -/
theorem Holds.pre_call {env : Env} {need : Nat} {Pre : (Reg → Word) → MachineState → Prop}
    {ret : Word} {R : Reg → Word} {m : MachineState} (hstk : env.stackLimit.toNat + need ≤ (R .x2).toNat)
    (hst : env.Static m) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hpre : Pre (Lprog.updReg R .x1 ret) m) :
    Holds.pre env need Pre ret (R .x2) (Lprog.updReg R .x1 ret) m :=
  ⟨⟨by simp [Lprog.updReg_apply], by simp [Lprog.updReg_apply]⟩, hstk, hst, hnx, hpre⟩

/-! ## Bytes in doublewords -/

section Bytes

variable {m m' : MachineState}

/-- A byte reads its doubleword only. -/
theorem getByte_congr {a : Word} (h : m'.getMem (alignToDword a) = m.getMem (alignToDword a)) :
    m'.getByte a = m.getByte a := by
  simp only [MachineState.getByte, h]

/-- A doubleword store elsewhere keeps a byte. -/
theorem getByte_setMem_ne {a b v : Word} (h : b ≠ alignToDword a) : (m.setMem b v).getByte a = m.getByte a :=
  getByte_congr (by simp [MachineState.getMem, MachineState.setMem, Ne.symm h])

theorem byteOffset_eq_toNat_mod (a : Word) : byteOffset a = a.toNat % 8 := by
  rw [byteOffset, BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod a.toNat 3

theorem toNat_alignToDword (a : Word) : (alignToDword a).toNat = a.toNat - a.toNat % 8 := by
  have h := congrArg BitVec.toNat (alignToDword_add_byteOffset a)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, byteOffset_eq_toNat_mod] at h
  have := (alignToDword a).isLt
  omega

theorem alignToDword_eq_iff {a b : Word} :
    alignToDword a = alignToDword b ↔ a.toNat / 8 = b.toNat / 8 := by
  rw [← BitVec.toNat_inj, toNat_alignToDword, toNat_alignToDword]; omega

/-- Byte `k` of a doubleword stored at the aligned `b`. -/
theorem getByte_setMem_aligned {b v : Word} (hb : b.toNat % 8 = 0) {k : Nat} (hk : k < 8) :
    (m.setMem b v).getByte (b + BitVec.ofNat 64 k) = extractByte v k := by
  have hn : (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := b.isLt
    have : b.toNat + k < 2 ^ 64 := by omega
    omega
  have ha : alignToDword (b + BitVec.ofNat 64 k) = b := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_alignToDword, hn]; omega
  simp [MachineState.getByte, ha, MachineState.getMem, MachineState.setMem, byteOffset_eq_toNat_mod, hn,
    Nat.add_mod, hb, Nat.mod_eq_of_lt hk]

theorem getByte_setByte_eq {a : Word} {c : BitVec 8} : (m.setByte a c).getByte a = c := by
  simp only [MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem, beq_self_eq_true,
    ite_true]
  exact extractByte_replaceByte_same _ ⟨_, byteOffset_lt_8⟩ c

theorem getByte_setByte_ne {a b : Word} {c : BitVec 8} (h : b ≠ a) : (m.setByte a c).getByte b = m.getByte b := by
  by_cases hd : alignToDword a = alignToDword b
  · simp only [MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem, hd,
      beq_self_eq_true, ite_true]
    refine extractByte_replaceByte_diff _ _ byteOffset_lt_8 byteOffset_lt_8 fun ho => h ?_
    rw [← alignToDword_add_byteOffset b, ← alignToDword_add_byteOffset a, hd, ho]
  · exact getByte_setMem_ne hd

/-- `m'` has `m`'s bytes outside `[a, a + n)`. -/
def ByteFrame (m m' : MachineState) (a : Word) (n : Nat) : Prop :=
  ∀ b, ¬ InRange a n b → m'.getByte b = m.getByte b

theorem BytesAt.keep {a : Word} {bs : List (BitVec 8)} (h : BytesAt m a bs)
    (hk : ∀ k, k < bs.length → m'.getByte (a + BitVec.ofNat 64 k) = m.getByte (a + BitVec.ofNat 64 k)) :
    BytesAt m' a bs :=
  ⟨h.1, fun k hk' => (hk k hk').trans (h.2 k hk')⟩

/-- The bytes of a footprint whose doublewords are kept are kept. -/
theorem Keeps.getByte {a b : Word} {n : Nat} (h : Keeps m m' (alignToDword a) (n + a.toNat % 8))
    (hb : InRange a n b) : m'.getByte b = m.getByte b :=
  getByte_congr (h _ ⟨by
    rw [toNat_alignToDword, toNat_alignToDword]
    have := hb.1; omega, by rw [toNat_alignToDword, toNat_alignToDword]; have := hb.2; omega⟩)

end Bytes

end Rv64mc
