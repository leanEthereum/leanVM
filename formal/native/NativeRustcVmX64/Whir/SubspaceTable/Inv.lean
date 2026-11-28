module

public import NativeRustcVmX64.Whir.SubspaceTable.Exec
public import NativeRustcVmX64.Whir.SubspaceAtTable.Leaf
public import NativeRustcVm.Whir.MathSubspaceRoots

/-!
# `subspace_table`'s states (x86-64)

From the entry `m0` (`μ` RSI, below 32 past `b1`), in the 848-byte frame at `fb` (`fbOf`): the
spilled output at `fb + 8`, `μ` and `8μ` at `fb + 16`, `fb + 24`, the table's length and the turn
at `fb + 32`, `fb + 40`, the table's `Buf` (`len` at `fb + 48`, the pairs from `fb + 56`), the
layer's 31 words from `fb + 552`.
- `Init i`: the layer's first `i` words set (`initL i`), the output spilled;
- `OInv t` at the turns' head (`b14`): the layer `layerAt μ t`, the table `tableAt μ t`, the
  last root in R15; `IInv t j` at the layer loop's head (`b15a`): words `t` to `t + j − 1`
  updated (`innerL`); `PInv t` after the layer loop (`b18a`): the layer `layerAt μ (t + 1)`;
- `Done` at the copy (`b21`): the whole table; `NoneAt` at `b23`.
-/

namespace NativeRustcVmX64.Whir.SubspaceTable

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Whir.Leaf
open NativeRustcVm (Region WordAt WordsAt)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := stackBelow m0 848
/-- `μ`. -/
def muOf (m0 : MachineData) : Nat := (reg m0 .rsi).toNat
/-- The output: the `Option<Buf<(u64, u64), 31>>`. -/
def outsOf (m0 : MachineData) : List Region := [⟨reg m0 .rdi, 8 + tableBytes⟩]

/-- A body of `subspace_table`. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 848 subspaceTableStack slots (outsOf m0) st

/-- The output spilled at `fb + 8`. -/
def OutAt (m0 st : MachineData) : Prop :=
  WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) (.ofBitVec (reg m0 .rdi))

/-- The layer's first `i` words set. -/
structure Init (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : OutAt m0 st
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 552) (initL i)
  r14 : reg st .r14 = reg m0 .rsi
  hmu : muOf m0 < 32

/-- What the turns keep: `μ`, `8μ` spilled. -/
structure Turn (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : OutAt m0 st
  mu : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (.ofBitVec (reg m0 .rsi))
  mu8 : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) (.ofNat (8 * muOf m0))
  hmu : muOf m0 < 32

/-- The turns' head after `t` turns. -/
structure OInv (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  tn : Turn m0 st
  ht : t < muOf m0
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 552) (layerAt (muOf m0) t)
  table : PairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 56) (tableAt (muOf m0) t)
  rbx : reg st .rbx = fbOf m0 + BitVec.ofNat 64 (552 + 8 * t)
  r12 : reg st .r12 = BitVec.ofNat 64 (t + 1)
  r13 : reg st .r13 = BitVec.ofNat 64 t
  r14 : reg st .r14 = reg m0 .rsi
  r15 : reg st .r15 = (lastAt (layerAt (muOf m0) t) t).toBitVec

/-- The layer loop's head: words `t` to `t + j − 1` updated. -/
structure IInv (m0 : MachineData) (t j : Nat) (st : MachineData) : Prop where
  tn : Turn m0 st
  ht : t + j < muOf m0
  tt : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 40) (.ofNat t)
  tl : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 32) (.ofNat (t + 1))
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 552)
    (innerL (layerAt (muOf m0) t) t (t + j))
  table : PairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 56) (tableAt (muOf m0) t)
  rbx : reg st .rbx = fbOf m0 + BitVec.ofNat 64 (552 + 8 * t)
  rbp : reg st .rbp = BitVec.ofNat 64 (8 * (muOf m0 - t))
  r14 : reg st .r14 = BitVec.ofNat 64 (8 * j)
  r15 : reg st .r15 = (lastAt (layerAt (muOf m0) t) t).toBitVec

/-- After the layer loop of turn `t`. -/
structure PInv (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  tn : Turn m0 st
  ht : t < muOf m0
  tt : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 40) (.ofNat t)
  tl : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 32) (.ofNat (t + 1))
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 552) (layerAt (muOf m0) (t + 1))
  table : PairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 56) (tableAt (muOf m0) t)
  rbx : reg st .rbx = fbOf m0 + BitVec.ofNat 64 (552 + 8 * t)

/-- At the copy: the whole table. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : OutAt m0 st
  hmu : muOf m0 ≤ 30
  table : PairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 56) (tableAt (muOf m0) (muOf m0))
  r12 : reg st .r12 = BitVec.ofNat 64 (muOf m0 + 1)

/-- At `None` (`b23`). -/
structure NoneAt (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : OutAt m0 st
  hmu : 30 < muOf m0

end

public section

theorem stack_le : 848 ≤ subspaceTableStack ∧ 848 + kinvStack ≤ subspaceTableStack ∧
    848 + kmulStack ≤ subspaceTableStack ∧ 848 + 0 ≤ subspaceTableStack := by decide

theorem layer_len (m0 : MachineData) (t : Nat) : (layerAt (muOf m0) t).length = muOf m0 :=
  layerAt_length _ _

/-- `2^m` shifted by `d`: `pow2 (d + m − 1)`. -/
theorem shl_pow2 {m d : Nat} (hm : 1 ≤ m) (hd : d + m ≤ 32) (x : BitVec 64) (hx : x.toNat = d) :
    BinOp.apply .shl .W64 (BitVec.ofNat 64 (2 ^ m)) (UnOp.apply .trunc .W32 x) =
      (pow2 (d + m - 1)).toBitVec := by
  have hc : shiftCount .W64 (UnOp.apply .trunc .W32 x) = d := by
    unfold shiftCount shiftMask
    simp only [UnOp.apply, toNat_low, toNat_ext]
    rw [show Width.W8.bits = 8 from rfl, show Width.W32.bits = 32 from rfl, hx,
      Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show d < 2 ^ 8 by omega)]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 6) (by omega)
  simp only [BinOp.apply, hc, low_W64, ext_W64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, pow2, Nat.toUInt64_eq, UInt64.toNat_toBitVec,
    UInt64.toNat_ofNat', Nat.shiftLeft_eq, show d + m - 1 + 1 = m + d by omega, Nat.pow_add,
    show Width.W64.bits = 64 from rfl,
    Nat.mod_eq_of_lt (show 2 ^ m < 2 ^ 64 from Nat.pow_lt_pow_right (by decide) (by omega))]

/-- **Words patched**: the words from `a`, words `c` to `c + n − 1` written (`f`), the others
kept. -/
theorem wordsAt_patch {d d' : DataMem} {a : BitVec 64} {L L' : List UInt64} {c n : Nat}
    {f : Nat → UInt64} (h : WordsAt d a L) (hnw : NoWrap a (8 * L.length))
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (8 * c)) (8 * n)))
    (hw : ∀ i < n, WordAt d' (a + BitVec.ofNat 64 (8 * (c + i))) (f (c + i)))
    (hcn : c + n ≤ L.length) (hlen : L'.length = L.length)
    (hL : ∀ k (hk : k < L.length), L'[k]'(by omega) =
      if c ≤ k ∧ k < c + n then f k else L[k]) : WordsAt d' a L' := by
  rw [NativeRustcVm.wordsAt_iff] at h ⊢
  intro k hk
  rw [hL k (by omega)]
  split
  · rename_i hck
    have := hw (k - c) (by omega)
    rwa [show c + (k - c) = k by omega] at this
  · rename_i hck
    unfold NoWrap at hnw
    refine NativeRustcVm.BytesAt.of_sameOutside (h k (by omega)) hs fun i hi ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at hi
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; intro hin; unfold InRange at hin; omega
    rw [addr_add, Sym.inRange_iff (by rw [toNat_add_ofNat _ _ (by omega)]; omega),
      toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
    omega

end

end NativeRustcVmX64.Whir.SubspaceTable
