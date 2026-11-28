module

public import NativeRustcVmX64.Ring.Target.Exec
public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVmX64.Field.LinSound
public import NativeRustcVm.Ring.Math
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `ring_target`: its layout, its values (x86-64)

From the entry state `m0` (`s` RDI, `f` RSI, `g` RDX): the frame (`2352` bytes, `NT` of stack),
the arrays `s`, `f`, `g` (regions `1` to `3`), the images `Ψ(s_i)` (`imgs`), and a table `E` of the
values the code computes after the images (`Good`): `f`'s elements (`0` to `7`), the points
`zz n` (`8 + n`), `P_p = Σ_i Z_p^i Ψ(s_i)` (`20 + p`), `T_p = P_p^(2^(8p))` (`30 + p`),
`M_p = f_p · T_p` (`40 + p`). The templates' values are stated over an abstract table, so that the
kernel never computes a Frobenius power.
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring

@[expose] public section

abbrev NT : Nat := ringTargetStack

abbrev sA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev fA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
abbrev gA (m0 : MachineData) : BitVec 64 := reg m0 .rdx

/-- Nothing is written outside the stack. -/
abbrev noWr : Nat → Bool := fun _ ↦ false

def sl (m0 : MachineData) : Array EW := arr m0 (sA m0) coeffCount
def fl (m0 : MachineData) : Array EW := arr m0 (fA m0) ringWidth
def gl (m0 : MachineData) : Array EW := arr m0 (gA m0) ringWidth

/-- Element `i` of `s`, of `f`. -/
def sE (m0 : MachineData) (i : Nat) : EW := NativeRustcVm.ewOf m0.dmem (sA m0 + BitVec.ofNat 64 (16 * i))
def fE (m0 : MachineData) (p : Nat) : EW := NativeRustcVm.ewOf m0.dmem (fA m0 + BitVec.ofNat 64 (16 * p))

/-- The images `Ψ(s_i)`. -/
def imgs (m0 : MachineData) : Array EW := (sl m0).map (ringPsi · (gl m0))

abbrev c0 (x : EW) : BitVec 64 := x.c0.toBitVec
abbrev c1 (x : EW) : BitVec 64 := x.c1.toBitVec

/-- **The table's facts.** -/
structure Good (m0 : MachineData) (E : Nat → EW) : Prop where
  f : ∀ p < 8, E p = fE m0 p
  z1 : E 9 = EW.sqIter 8 ⟨2, 0⟩
  z : ∀ n, 1 ≤ n → n < 8 → E (9 + n) = EW.sqIter 8 (E (8 + n))
  pv : ∀ p < 8, E (20 + p) = polyEval (imgs m0) (E (16 - p))
  tv : ∀ p < 8, E (30 + p) = EW.sqIter (8 * p) (E (20 + p))
  mv : ∀ p < 8, E (40 + p) = E p * E (30 + p)

/-- Values updated at the listed variables. -/
def upd (f : Nat → BitVec 64) (l : List (Nat × BitVec 64)) : Nat → BitVec 64 :=
  fun i ↦ (l.lookup i).getD (f i)

/-- The pushed registers' values: the variables `0` to `5`. -/
def pv0 (m0 : MachineData) : Nat → BitVec 64 :=
  upd (fun _ ↦ 0) [(0, reg m0 .rbp), (1, reg m0 .r15), (2, reg m0 .r14), (3, reg m0 .r13),
    (4, reg m0 .r12), (5, reg m0 .rbx)]

end

public section

variable {m0 : MachineData}

theorem nt_eq : NT = 2576 := rfl

/-- The images loop's layout: `s`. -/
theorem layL [Labels] (hpre : RingTargetPre m0) : Lay m0 2352 NT [(sA m0, 1024)] :=
  ⟨hpre.1, by decide, by decide, ⟨⟨hpre.2.1.1.1, hpre.2.1.1.2, hpre.2.1.2⟩, trivial⟩,
    List.pairwise_singleton _ _⟩

/-- The turns' layout: `f`. -/
theorem layC [Labels] (hpre : RingTargetPre m0) : Lay m0 2352 NT [(fA m0, 128)] :=
  ⟨hpre.1, by decide, by decide, ⟨⟨hpre.2.2.1.1.1, hpre.2.2.1.1.2, hpre.2.2.1.2⟩, trivial⟩,
    List.pairwise_singleton _ _⟩

end

end NativeRustcVmX64.Ring.Target
