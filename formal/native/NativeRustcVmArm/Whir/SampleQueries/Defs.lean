module

public import NativeRustcVmArm.Whir.SampleQueries.Exec
public import NativeRustcVmArm.Whir.Frame
public import NativeRustcVmArm.Spec.Whir
public import NativeRustcVm.Whir.Sample
public import NativeRustcVm.Transcript.Update

/-!
# `sample_queries`: its frame, its loops' invariants

`m1` is the entry's state: the function's frame (`SFr`, 112 bytes, X19 to X30 saved) is relative
to it. The outer loop's head `.LSampleQueries_8` (`b9`) after
`j` challenges (`Outer`), the inner loop's head `.LSampleQueries_11` (`b13`) after `i` positions of
the `j`th (`Inner`); with a depth above `128`, the squeezes' loop head `.LSampleQueries_3` (`b3`)
(`Big`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt)
open NativeRustcVm.Whir (sq chunk auxP queryCap queryBufBytes)

@[expose] public section

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(16, .X29), (24, .X30), (32, .X28), (40, .X27), (48, .X26), (56, .X25), (64, .X24), (72, .X23),
    (80, .X22), (88, .X21), (96, .X20), (104, .X19)]

/-- The outputs: the positions' buffer and the `TState`. -/
def outs (m1 : MachineData) (q : BitVec 64) : Prop :=
  InRange m1.regs.X3.toBitVec queryBufBytes q ∨ InRange m1.regs.X0.toBitVec tstateBytes q

/-- The frame. -/
abbrev SFr (m1 st : MachineData) : Prop := Fr m1 112 sampleQueriesStack slots [] (outs m1) st

/-- The depth. -/
abbrev dep (m1 : MachineData) : Nat := m1.regs.X1.toNat
/-- The count. -/
abbrev cnt (m1 : MachineData) : Nat := m1.regs.X2.toNat
/-- The `TState`. -/
abbrev tA (m1 : MachineData) : BitVec 64 := m1.regs.X0.toBitVec
/-- The buffer. -/
abbrev oA (m1 : MachineData) : BitVec 64 := m1.regs.X3.toBitVec

section
variable [Labels]

/-- **The outer loop's head**, after `j` challenges, `r` positions left, the transcript's state
`s`, the positions `qs`. -/
structure Outer (a : DecArea) (s0 : TState) (m1 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (st : MachineData) : Prop where
  fr : SFr m1 st
  x19 : st.regs.X19 = m1.regs.X2
  x20 : st.regs.X20 = m1.regs.X0
  x21 : st.regs.X21 = m1.regs.X3
  x22 : st.regs.X22 = m1.regs.X1
  x25 : st.regs.X25.toNat = j
  x26 : st.regs.X26 = 230
  x27 : st.regs.X27.toBitVec = rodataAddr .perChallenge
  x28 : st.regs.X28.toNat = qs.length
  x29 : st.regs.X29.toNat = r
  jlt : j < cnt m1
  len : qs.length + r = cnt m1
  dlt : dep m1 < 129
  ts : TStateAt st.dmem (tA m1) a s
  buf : BufWordsAt st.dmem (oA m1) queryCap qs
  model : auxP (dep m1) (cnt m1) (cnt m1) s0 =
    (qs.toArray ++ (auxP (dep m1) (cnt m1 - j) r s).1, (auxP (dep m1) (cnt m1 - j) r s).2)

/-- **The inner loop's head**: the `j`th challenge `(sq s).1` squeezed from `s`, `i` of its `n`
positions pushed after `qs`. -/
structure Inner (a : DecArea) (s0 : TState) (m1 : MachineData) (j r : Nat) (s : TState)
    (qs : List UInt64) (n i : Nat) (st : MachineData) : Prop where
  fr : SFr m1 st
  x19 : st.regs.X19 = m1.regs.X2
  x20 : st.regs.X20 = m1.regs.X0
  x21 : st.regs.X21 = m1.regs.X3
  x22 : st.regs.X22 = m1.regs.X1
  x23 : st.regs.X23 = (sq s).1.c0
  x24 : st.regs.X24 = (sq s).1.c1
  x25 : st.regs.X25.toNat = i * dep m1
  x26 : st.regs.X26.toNat = qs.length + i + 1
  x27 : st.regs.X27.toBitVec = BitVec.ofNat 64 (qs.length + i) - 230#64
  x28 : st.regs.X28.toNat = n - i
  x29 : st.regs.X29.toNat = r
  words : WordsAt st.dmem (base m1 112) [n.toUInt64, j.toUInt64]
  jlt : j < cnt m1
  len : qs.length + r = cnt m1
  r0 : r ≠ 0
  dpos : 0 < dep m1
  dle : dep m1 ≤ 128
  hn : n = min (128 / dep m1) r
  ilt : i < n
  ts : TStateAt st.dmem (tA m1) a (sq s).2
  buf : BufWordsAt st.dmem (oA m1) queryCap (qs ++ ((chunk (dep m1) (sq s).1 n).toList.take i))
  model : auxP (dep m1) (cnt m1) (cnt m1) s0 =
    (qs.toArray ++ (auxP (dep m1) (cnt m1 - j) r s).1, (auxP (dep m1) (cnt m1 - j) r s).2)

/-- **The squeezes' loop head** (depth above `128`), `j` challenges squeezed. -/
structure Big (a : DecArea) (s0 : TState) (m1 : MachineData) (j : Nat) (s : TState)
    (st : MachineData) : Prop where
  fr : SFr m1 st
  x19 : st.regs.X19.toNat = cnt m1 - j
  x20 : st.regs.X20 = m1.regs.X0
  jlt : j < cnt m1
  ts : TStateAt st.dmem (tA m1) a s
  buf : WordAt st.dmem (oA m1) 0
  model : auxP (dep m1) (cnt m1) (cnt m1) s0 = auxP (dep m1) (cnt m1 - j) (cnt m1) s

end

end

end NativeRustcVmArm.Whir.SampleQueries
