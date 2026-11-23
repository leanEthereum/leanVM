module

public import NativeRustcVmArm.Ring.Track
public import NativeRustcVmArm.Ring.Loc
public import NativeRustcVmArm.Ring.Target.Exec
public import NativeRustcVmArm.Spec.Ring
public import NativeRustcVm.Ring.Math
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `ring_target`: its frame, its values

From the entry state `m0` (`s` at X0, `f` at X1, `g` at X2): the frame (`TFr`: 2352 bytes, X19
to X30 saved from byte `2256`), the entry's facts (`P`), the arrays as read at the entry (`sl`,
`fl`, `gl`) and the images `Ψ(s_i)` (`imgs`); the values the code computes after the images
loop, as a table (`tv`, indices `fI`, `zI`, `pI`, `tI`, `mI`): `f`'s words, the turn's point
`Z_p`, `P_p = Σ_i Z_p^i Ψ(s_i)`, `T_p = P_p^(2^(8p))`, `M_p = f_p · T_p`.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(2256, .X29), (2264, .X30), (2272, .X28), (2280, .X27), (2288, .X26), (2296, .X25),
    (2304, .X24), (2312, .X23), (2320, .X22), (2328, .X21), (2336, .X20), (2344, .X19)]

/-- `s`'s address. -/
def sA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- `f`'s address. -/
def fA (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- `g`'s address. -/
def gA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec

/-- The frame. -/
abbrev TFr (m0 m : MachineData) : Prop := Fr m0 2352 ringTargetStack slots [] (fun _ ↦ False) m

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 2352

/-- `s`, `f`, `g` as read at the entry. -/
def sl (m0 : MachineData) : Array EW := arr m0 m0.regs.X0 coeffCount
def fl (m0 : MachineData) : Array EW := arr m0 m0.regs.X1 ringWidth
def gl (m0 : MachineData) : Array EW := arr m0 m0.regs.X2 ringWidth

/-- The images `Ψ(s_i)`. -/
def imgs (m0 : MachineData) : Array EW := (sl m0).map (ringPsi · (gl m0))

/-- `Z_p`, the point of turn `p` (`7` first). -/
def zV (p : Nat) : EW := zz (8 - p)
/-- `P_p = Σ_i Z_p^i Ψ(s_i)`. -/
def pV (m0 : MachineData) (p : Nat) : EW := polyEval (imgs m0) (zV p)
/-- `T_p = P_p^(2^(8p))`. -/
def tV (m0 : MachineData) (p : Nat) : EW := EW.sqIter (8 * p) (pV m0 p)
/-- `M_p = f_p · T_p`. -/
def mV (m0 : MachineData) (p : Nat) : EW := (fl m0).getD p 0 * tV m0 p
/-- `M_1 + … + M_7`, as the code sums them. -/
def sV (m0 : MachineData) : EW :=
  mV m0 1 + (mV m0 2 + (mV m0 3 + (mV m0 4 + (mV m0 5 + (mV m0 6 + mV m0 7)))))

/-- Limb `c` of `x`. -/
def limb (x : EW) (c : Nat) : UInt64 := if c = 0 then x.c0 else x.c1

/-- The table's indices: `f_p`'s words, `Z_p`, `P_p`, `T_p`, `M_p`, the generator, the sum,
`f`'s address. -/
def fI (p : Nat) : Nat := 2 * p
def zI (p : Nat) : Nat := 16 + 2 * (7 - p)
def pI (p : Nat) : Nat := 32 + 2 * (7 - p)
def tI (p : Nat) : Nat := 48 + 2 * (7 - p)
def mI (p : Nat) : Nat := 64 + 2 * (7 - p)
def gI : Nat := 96
def sI : Nat := 98
def fPtr : Nat := 100

/-- **The table.** -/
def tv (m0 : MachineData) (n : Nat) : UInt64 :=
  if n < 16 then limb ((fl m0).getD (n / 2) 0) (n % 2)
  else if n < 32 then limb (zV (7 - (n - 16) / 2)) (n % 2)
  else if n < 48 then limb (pV m0 (7 - (n - 32) / 2)) (n % 2)
  else if n < 64 then limb (tV m0 (7 - (n - 48) / 2)) (n % 2)
  else if n < 80 then limb (mV m0 (7 - (n - 64) / 2)) (n % 2)
  else if n < 96 then 0
  else if n < 98 then limb gen (n % 2)
  else if n < 100 then limb (sV m0) (n % 2)
  else UInt64.ofBitVec (fA m0)

/-- The regions of the code after the images loop: the frame, `f`. -/
abbrev rsT (m0 : MachineData) : List (BitVec 64 × Nat) := [(fb m0, 2352), (fA m0, 128)]

/-- Their sizes. -/
def szT : List Nat := [2352, 128]

end

end NativeRustcVmArm.Ring.Target
