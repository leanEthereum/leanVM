module

public import NativeRustcVmArm.Wire.RdRows.Exec
public import NativeRustcVmArm.Wire.Frame
public import NativeRustcVm.Wire.RowsFacts
public import NativeVm.Wire.Read

/-!
# `rd_rows`' places and states

The leaves at `lv` (`512` bytes each, `leaf i`), the output `W` of the `n` leaves; the frame
(`Frm`, 112 bytes, every callee-saved register in a slot). What a state keeps of the memory after
`i` rows (`Kept`: the rows read so far, the reader past them, their padded leaves); a block's
environment with one chunk of a leaf (`chEnv`); the bit tricks of the zero fills (`and_mask`,
`bic_sub`).
-/

namespace NativeRustcVmArm.Wire.RdRows

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.RdRows
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(16, .X29), (24, .X30), (32, .X28), (40, .X27), (48, .X26),
  (56, .X25), (64, .X24), (72, .X23), (80, .X22), (88, .X21), (96, .X20), (104, .X19)]

/-- The rows' count. -/
abbrev nr (m0 : MachineData) : Nat := m0.regs.X1.toNat
/-- The leaves' width. -/
abbrev lw (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- The rows' width. -/
abbrev rw (m0 : MachineData) : Nat := m0.regs.X3.toNat
/-- The leaves' address. -/
abbrev lv (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec
/-- The reader's address. -/
abbrev rdr (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- Leaf `i`'s address. -/
abbrev leaf (m0 : MachineData) (i : Nat) : BitVec 64 := lv m0 + BitVec.ofNat 64 (512 * i)
/-- The zeros before a row. -/
abbrev zc (m0 : MachineData) : Nat := lw m0 - rw m0
/-- `z` rounded down to a multiple of four. -/
abbrev q4 (z : Nat) : Nat := z / 4 * 4

/-- The leaves' bytes. -/
abbrev W (m0 : MachineData) : BitVec 64 → Prop := InRange (lv m0) (512 * nr m0)

/-- The state between the prologue and the epilogue. -/
abbrev Frm (m0 m : MachineData) : Prop := Fr m0 112 144 slots [] (outs (rdr m0) (W m0)) m

/-- Whether every row's first word is zero, as `rd_rows` returns it. -/
def flag (rows : List (List K)) : Nat := if ∀ x ∈ rows, x.getD 0 0 = 0 then 1 else 0

/-- What `rd_rows` reaches. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop := st.pc = retOf m0 ∧ RdRowsPost m0 st.data

/-- The environment of the frame. -/
abbrev frEnv (m0 m : MachineData) : Env := Env.ofMachine m [(base m0 112, 112)]

/-- The environment of the frame and `sz` bytes at `a`. -/
abbrev chEnv (m0 m : MachineData) (a : BitVec 64) (sz : Nat) : Env :=
  Env.ofMachine m [(base m0 112, 112), (a, sz)]

/-- **The memory after `i` rows**: the rows read, the reader past them, their padded leaves. -/
structure Kept (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c i : Nat)
    (rows : List (List K)) (ci : Nat) (d : Mem 64) : Prop where
  hrows : rdRows B (rw m0) i c = some (rows, ci)
  hrd : ReaderAt d (rdr m0) bp B ci
  hlvs : LeavesAt d (lv m0) (rows.map fun x ↦ paddedLeaf x (lw m0))

/-- The geometry: the stack, the reader, its bytes and the leaves apart, the leaves' bytes
mapped. -/
structure Geo (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) : Prop where
  g : RGeo m0 144 (rdr m0) bp B.length (W m0)
  lvMap : NativeRustcVm.Mapped m0.dmem (lv m0) (512 * nr m0)
  lvNw : (lv m0).toNat + 512 * nr m0 ≤ 2 ^ 64
  n0 : 0 < nr m0
  n256 : nr m0 ≤ 256
  lw64 : lw m0 ≤ 64
  rwlw : rw m0 ≤ lw m0
  aS : NativeRustcVm.Apart (lv m0) (512 * nr m0) (base m0 144) 144
  aR : NativeRustcVm.Apart (lv m0) (512 * nr m0) (rdr m0) 24
  aB : NativeRustcVm.Apart (lv m0) (512 * nr m0) bp B.length

end

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-! ## Bits -/

theorem testBit_mask (i : Nat) :
    Nat.testBit 4611686018427387900 i = (decide (2 ≤ i) && decide (i < 62)) := by
  rw [show (4611686018427387900 : Nat) = (2 ^ 60 - 1) <<< 2 by decide, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 2 ≤ i
  · simp only [ge_iff_le, h, decide_true, Bool.true_and]
    by_cases h' : i < 62
    · rw [decide_eq_true h', decide_eq_true (by omega)]
    · rw [decide_eq_false h', decide_eq_false (by omega)]
  · simp [h]

/-- `x & 0x3ffffffffffffffc`: `x` rounded down to a multiple of four. -/
theorem and_mask {x : BitVec 64} (h : x.toNat < 2 ^ 62) :
    (BinOp.apply .and .W64 x (BitVec.ofNat 64 4611686018427387900)).toNat = q4 x.toNat := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (4611686018427387900 : Nat) % 2 ^ 64 = 4611686018427387900 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_mask, q4, show x.toNat / 4 * 4 = (x.toNat >>> 2) <<< 2 by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow], Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h2 : 2 ≤ i
  · rw [show 2 + (i - 2) = i by omega]
    by_cases h62 : i < 62
    · simp [h2, h62]
    · have : x.toNat.testBit i = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [h2, h62, this]
  · simp [h2]

/-- `0x1fffffffffffffff & !(rw - lw)`: `lw - rw - 1` for `rw < lw`. -/
theorem bic_sub {a b : BitVec 64} (hab : b.toNat < a.toNat) (ha : a.toNat < 2 ^ 61) :
    (BinOp.apply .bic .W64 (BitVec.ofNat 64 2305843009213693951) (BinOp.apply .sub .W64 b a)).toNat =
      a.toNat - b.toNat - 1 := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
  have hs : (b - a) = ~~~(BitVec.ofNat 64 (a.toNat - b.toNat - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_ofNat]
    have := a.isLt
    rw [Nat.mod_eq_of_lt (by omega : a.toNat - b.toNat - 1 < 2 ^ 64)]
    omega
  rw [hs, BitVec.not_not, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2305843009213693951 : Nat) % 2 ^ 64 = 2 ^ 61 - 1 from rfl, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  have := a.isLt
  rw [Nat.mod_eq_of_lt (by omega : a.toNat - b.toNat - 1 < 2 ^ 64)]
  omega

theorem toNat_add_lit {x : BitVec 64} {c : Nat} (h : x.toNat + c < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat + c := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_sub_lit {x : BitVec 64} {c : Nat} (h : c ≤ x.toNat) (hc : c < 2 ^ 64) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat - c := by
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem lsl3 {x : BitVec 64} (h : 8 * x.toNat < 2 ^ 64) :
    (UnOp.apply (.ubfm 61 60) .W64 x).toNat = 8 * x.toNat := by
  rw [ubfm_lsl3, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  omega

theorem lsr3 (x : BitVec 64) : (UnOp.apply (.ubfm 3 63) .W64 x).toNat = x.toNat / 8 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  simp [evalUBFM, toNat_take', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem lsl9 {x : BitVec 64} (h : 512 * x.toNat < 2 ^ 64) :
    (UnOp.apply (.shift .LSL 9) .W64 x).toNat = 512 * x.toNat := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64, shiftW, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  omega

/-! ## Places -/

section Geo

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8}

theorem Geo.leaf_toNat (h : Geo m0 bp B) {i o : Nat} (hi : 512 * i + o < 512 * nr m0) :
    (leaf m0 i + BitVec.ofNat 64 o).toNat = (lv m0).toNat + 512 * i + o := by
  have := h.lvNw
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- Bytes `o` to `o + sz` of leaf `i` are outputs. -/
theorem Geo.out (h : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512) {j : Nat}
    (hj : j < sz) : W m0 (leaf m0 i + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  have := h.lvNw
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
  exact NativeRustcVm.inRange_add (by omega) (by omega)

/-- **A chunk of a leaf with the frame**: a well formed environment. -/
theorem Geo.chunk_wf (h : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hsz : 0 < sz) {m : MachineData} (hfr : Frm m0 m) :
    (chEnv m0 m (leaf m0 i + BitVec.ofNat 64 o) sz).WF := by
  have hst := h.g.st
  have := hst.2.1
  have hb := Ring.base_noWrap (m0 := m0) (F := 112) (by have := hst.2.1; omega)
  have hlt := h.leaf_toNat (i := i) (o := o) (by omega)
  have := h.lvNw
  refine Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped hst (by omega) j hj), hb⟩,
    ⟨fun j hj ↦ ?_, ?_⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  · rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]
    exact hfr.kept _ (h.lvMap _ (by omega))
  · show NativeRustcArm.NoWrap _ _
    unfold NativeRustcArm.NoWrap; rw [hlt]; omega
  · show NativeRustcArm.Apart _ _ _ _
    have hbN := Ring.base_noWrap (m0 := m0) (F := 144) hst.2.1
    unfold NativeRustcArm.Apart
    rw [Ring.base_toNat (by omega), hlt]
    by_contra hc
    obtain ⟨j, hj, he⟩ : ∃ j, j < sz ∧ (lv m0).toNat + 512 * i + o + j =
        max ((lv m0).toNat + 512 * i + o) (m0.regs.SP.toNat - 112) :=
      ⟨max ((lv m0).toNat + 512 * i + o) (m0.regs.SP.toNat - 112) - ((lv m0).toNat + 512 * i + o),
        by omega, by omega⟩
    have h1 := h.g.wS _ (h.out (o := o) (sz := sz) hi ho hj)
    rw [NativeRustcVm.addr_add_add, Sym.inRange_iff hbN, Ring.base_toNat hst.2.1,
      h.leaf_toNat (by omega)] at h1
    omega

theorem base_aligned (hst : StackOk m0 144) : (base m0 112).toNat % 16 = 0 := by
  rw [Ring.base_toNat (by have := hst.2.1; omega)]; have := hst.1; omega

theorem frEnv_wf (hst : StackOk m0 144) {m : MachineData} (hfr : Frm m0 m) : (frEnv m0 m).WF :=
  Env.wf_of ⟨⟨fun j hj ↦ hfr.kept _ (Ring.frame_mapped hst (by omega) j hj),
    Ring.base_noWrap (by have := hst.2.1; omega)⟩, trivial⟩ (List.pairwise_singleton _ _)

theorem frEnv_match [Labels] (hst : StackOk m0 144) {m : MachineData} (hfr : Frm m0 m) :
    Match (frEnv m0 m) frS m :=
  match_ofMachine ⟨rfl, fun _ ↦ base_aligned hst, trivial⟩ (by rw [hfr.sp]; simp [Sym.eval])
    trivial trivial trivial trivial

/-- A change of memory inside leaf `i` misses the stack, the reader and the other leaves. -/
theorem Geo.chunk_apart (h : Geo m0 bp B) {i o sz : Nat} (hi : i < nr m0) (ho : o + sz ≤ 512)
    (hsz : 0 < sz) {q : BitVec 64} (hq : InRange (leaf m0 i + BitVec.ofNat 64 o) sz q) :
    W m0 q ∧ ¬InRange (lv m0) (512 * i) q := by
  have := h.lvNw
  have hlt := h.leaf_toNat (i := i) (o := o) (by omega)
  have hnw : NoWrap (leaf m0 i + BitVec.ofNat 64 o) sz := by unfold NoWrap; rw [hlt]; omega
  rw [Sym.inRange_iff hnw, hlt] at hq
  refine ⟨?_, ?_⟩
  · show InRange _ _ _
    rw [Sym.inRange_iff (by omega)]; omega
  · rw [Sym.inRange_iff (by omega)]; omega

/-- A sub-range of the leaves is apart from what they are apart from. -/
theorem Geo.sub_apart (h : Geo m0 bp B) {i o sz : Nat} (hle : 512 * i + o + sz ≤ 512 * nr m0)
    {b : BitVec 64} {n : Nat} (hA : NativeRustcVm.Apart (lv m0) (512 * nr m0) b n) :
    NativeRustcVm.Apart (leaf m0 i + BitVec.ofNat 64 o) sz b n := by
  have := h.lvNw
  rw [NativeRustcVm.addr_add_add]
  unfold NativeRustcVm.Apart at *
  rcases NativeRustcVm.toNat_add_ofNat_le (a := lv m0) (i := 512 * i + o) (by omega) with
    h1 | ⟨h1, h2⟩ <;> rw [h1] <;> omega

end Geo

end

end NativeRustcVmArm.Wire.RdRows
