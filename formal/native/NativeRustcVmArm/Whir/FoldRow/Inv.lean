module

public import NativeRustcVmArm.Whir.FoldRow.Exec
public import NativeRustcVm.Whir.MathFold

/-!
# `fold_row`'s states

The lanes in memory as a function (`LanesAt`), the spilled arguments (`Spills`: `x`, `n`, the
rounds' count, `values` from SP), and per round `r` (from `1`):
- `Head r` before round `r + 1`'s head: the lanes after `r` rounds (`memOf r`);
- `Loop r i` at round `r`'s loop head after `i` turns (rounds `1` to `5`; `Loop6` round 6's,
  its registers renamed);
- `Chk r` after round `r`'s turns;
- `Fin` at the end block: the lanes after every round, X26 zero iff no lane is left.
-/

namespace NativeRustcVmArm.Whir.FoldRow

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (Region wordOf ewOf ewsOf)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 128
/-- The lanes. -/
def vOf (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The lanes' count. -/
def nOf (m0 : MachineData) : Nat := m0.regs.X1.toNat
/-- The rounds' count. -/
def rnOf (m0 : MachineData) : Nat := m0.regs.X4.toNat
/-- The rounds. -/
def rdsOf (m0 : MachineData) : Array FoldRoundW :=
  (roundsOf m0.dmem m0.regs.X3.toBitVec (rnOf m0)).toArray
/-- Round `r` (from `0`). -/
def rdOf (m0 : MachineData) (r : Nat) : FoldRoundW := (rdsOf m0).getD r default
/-- The lanes at the entry. -/
def v0Of (m0 : MachineData) : Nat → EW := fun j ↦ ewOf m0.dmem (vOf m0 + BitVec.ofNat 64 (16 * j))
/-- The lanes after `r` rounds. -/
def memOf (m0 : MachineData) (r : Nat) : Nat → EW :=
  foldMem m0.regs.X2 (rdsOf m0) (nOf m0) (v0Of m0) r
/-- The output: the lanes. -/
def outsOf (m0 : MachineData) : List Region := [⟨vOf m0, lanesBytes⟩]

/-- The 64 lanes from `v` are `f`'s. -/
def LanesAt (d : DataMem) (v : BitVec 64) (f : Nat → EW) : Prop :=
  ∀ j < 64, ewOf d (v + BitVec.ofNat 64 (16 * j)) = f j

/-- The body's frame. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 128 foldRowStack slots (outsOf m0) st

/-- The spilled arguments. -/
def Spills (m0 st : MachineData) : Prop :=
  NativeRustcVm.WordsAt st.dmem (fbOf m0) [m0.regs.X2, m0.regs.X1, m0.regs.X4, m0.regs.X0]

/-- Before round `r + 1`'s head. -/
structure Head (m0 : MachineData) (r : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  x22 : st.regs.X22 = m0.regs.X3
  lanes : LanesAt st.dmem (vOf m0) (memOf m0 r)
  hr : r < rnOf m0

/-- Round `r`'s loop head (`r ≤ 5`) after `i` turns. -/
structure Loop (m0 : MachineData) (r i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  x22 : st.regs.X22 = m0.regs.X3
  fac : (⟨st.regs.X24 ^^^ st.regs.X27, st.regs.X25 ^^^ st.regs.X28⟩ : EW) =
    foldFactor m0.regs.X2 (rdOf m0 (r - 1))
  x26 : st.regs.X26.toNat = nOf m0 >>> r
  x29 : st.regs.X29.toNat = i
  hi : i < nOf m0 >>> r
  x20 : st.regs.X20.toBitVec = vOf m0 + BitVec.ofNat 64 (16 * i + 8)
  x23 : st.regs.X23.toBitVec = vOf m0 + BitVec.ofNat 64 (32 * i + 16)
  lanes : LanesAt st.dmem (vOf m0) (foldPart m0.regs.X2 (rdOf m0 (r - 1)) i (memOf m0 (r - 1)))
  hr : r ≤ rnOf m0

/-- Round 6's loop head after `i` turns. -/
structure Loop6 (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  fac : (⟨st.regs.X22 ^^^ st.regs.X24, st.regs.X20 ^^^ st.regs.X25⟩ : EW) =
    foldFactor m0.regs.X2 (rdOf m0 5)
  x21 : st.regs.X21.toNat = nOf m0 >>> 6
  x26 : st.regs.X26 = 1
  x23 : st.regs.X23.toNat = i
  hi : i < nOf m0 >>> 6
  x27 : st.regs.X27.toBitVec = vOf m0 + BitVec.ofNat 64 (16 * i + 8)
  x28 : st.regs.X28.toBitVec = vOf m0 + BitVec.ofNat 64 (32 * i + 16)
  lanes : LanesAt st.dmem (vOf m0) (foldPart m0.regs.X2 (rdOf m0 5) i (memOf m0 5))
  hr : 6 ≤ rnOf m0

/-- After round `r`'s turns. -/
structure Chk (m0 : MachineData) (r : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  x22 : st.regs.X22 = m0.regs.X3
  x26 : st.regs.X26.toNat = nOf m0 >>> r
  lanes : LanesAt st.dmem (vOf m0) (memOf m0 r)
  hr : r ≤ rnOf m0

/-- At the end block. -/
structure Fin (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  v : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) m0.regs.X0
  x26 : st.regs.X26 = 0 ↔ nOf m0 >>> rnOf m0 = 0
  lanes : LanesAt st.dmem (vOf m0) (memOf m0 (rnOf m0))

end

public section

theorem stack_eq : foldRowStack = 720 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 128 := by decide

theorem slots_ge : ∀ p ∈ slots, 32 ≤ p.1 := by decide

theorem x30_mem : XReg.X30 ∈ slots.map (·.2) :=
  List.mem_map.mpr ⟨(40, .X30), by simp [slots], rfl⟩

/-- `lsr x, x, #r`. -/
theorem lsr_toNat (x : BitVec 64) {r : Nat} (hr : r < 64) :
    (evalUBFM (w := RegWidth.W64) x r 63).toNat = x.toNat >>> r := by
  have hx := x.isLt
  have hlt : x.toNat >>> r < 2 ^ (63 - r + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos r), ← Nat.pow_add,
      show 63 - r + 1 + r = 64 by omega]
    exact hx
  simp [evalUBFM, RegWidth.bits, Nat.mod_eq_of_lt hr, show r ≤ 63 by omega, BitVec.take,
    Nat.mod_eq_of_lt hlt]
  exact lt_of_le_of_lt (Nat.shiftRight_le _ _) hx

theorem fac_eq {x : UInt64} {rd : FoldRoundW} {a b : UInt64}
    (ha : a = kmul x rd.beta.c0) (hb : b = kmul x rd.beta.c1) :
    (⟨a ^^^ rd.alpha.c0, b ^^^ rd.alpha.c1⟩ : EW) = foldFactor x rd := by
  rw [ha, hb, foldFactor]
  show _ = (⟨rd.alpha.c0 ^^^ kmul x rd.beta.c0, rd.alpha.c1 ^^^ kmul x rd.beta.c1⟩ : EW)
  rw [UInt64.xor_comm (kmul x rd.beta.c0), UInt64.xor_comm (kmul x rd.beta.c1)]

/-- Round `r`'s words in memory. -/
theorem rdOf_eq (m0 : MachineData) {r : Nat} (hr : r < rnOf m0) :
    rdOf m0 r = ⟨ewOf m0.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * r)),
      ewOf m0.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (32 * r + 16))⟩ := by
  simp [rdOf, rdsOf, roundsOf, Array.getD_eq_getD_getElem?, hr]

theorem memOf_succ (m0 : MachineData) (r : Nat) :
    memOf m0 (r + 1) = foldPart m0.regs.X2 (rdOf m0 r) (nOf m0 >>> (r + 1)) (memOf m0 r) := rfl

/-- Lanes kept where memory is. -/
theorem LanesAt.of_same {d d' : DataMem} {v : BitVec 64} {f : Nat → EW}
    {R : BitVec 64 → Prop} (h : LanesAt d v f) (hs : SameOutside d d' R)
    (hR : ∀ i < 1024, ¬R (v + BitVec.ofNat 64 i)) : LanesAt d' v f := by
  intro j hj
  rw [← h j hj]
  refine NativeRustcVm.ewOf_congr fun i hi ↦ ?_
  rw [addr_add]
  exact hs _ (hR _ (by omega))

/-- A lane stored. -/
theorem LanesAt.store {d d' : DataMem} {v : BitVec 64} {f : Nat → EW} {i : Nat} {e : EW}
    (h : LanesAt d v f) (hnw : NoWrap v 1024) (hi : i < 64)
    (hs : SameOutside d d' (InRange (v + BitVec.ofNat 64 (16 * i)) 16))
    (he : NativeRustcVm.EWAt d' (v + BitVec.ofNat 64 (16 * i)) e) :
    LanesAt d' v (Function.update f i e) := by
  intro j hj
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self]
    exact NativeRustcVm.ewOf_of_ewAt he
  · rw [Function.update_of_ne hji, ← h j hj]
    refine NativeRustcVm.ewOf_congr fun b hb ↦ ?_
    refine hs _ fun hin ↦ ?_
    unfold NoWrap at hnw
    rw [addr_add, Sym.inRange_iff (NativeRustcVm.NoWrap.sub hnw (by omega)),
      toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)] at hin
    omega

end

end NativeRustcVmArm.Whir.FoldRow
