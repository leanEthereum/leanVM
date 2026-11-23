module

public import NativeRustcVmX64.Ring.Psi.Exec
public import NativeRustcVmX64.Spec.Ring
public import NativeRustcVmX64.Field.LinSound
public import NativeRustcVm.Ring.Math

/-!
# `ring_psi`: its values between the calls (x86-64)

From the entry state `m0` (`value` in RDI, RSI, `g` at RDX): `g`'s elements (`gE`), the powers
`v^(2^j)` (`W`), the products `g_j · v^(2^j)` (`P`), the partial sums rustc keeps (`s01`, `s03`,
`s45`, `s06`), and after call `j` the values of the template `t<j>`'s variables (`v<j>`, through
`vB`: the pushed registers, then RAX, RDX, RBP, R12 to R15, the spills at `8`, `16`, `24`).
`psi_eq`: `ringPsi` is the sum of the products.
-/

namespace NativeRustcVmX64.Ring.Psi

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Field (Geo inRange_N stackBelow_toNat')

@[expose] public section

/-- `g`'s address. -/
abbrev gA (m0 : MachineData) : BitVec 64 := reg m0 .rdx

/-- The arrays: `g`. -/
abbrev rsOf (m0 : MachineData) : List (BitVec 64 × Nat) := [(gA m0, 128)]

/-- Nothing is written outside the stack. -/
abbrev noWr : Nat → Bool := fun _ ↦ false

/-- Element `j` of `g`. -/
def gE (m0 : MachineData) (j : Nat) : EW :=
  NativeRustcVm.ewOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * j))

/-- The value. -/
def vE (m0 : MachineData) : EW := ewArg (reg m0 .rdi) (reg m0 .rsi)

/-- `v^(2^j)`. -/
def W (m0 : MachineData) : Nat → EW
  | 0 => vE m0
  | n + 1 => EW.mul (W m0 n) (W m0 n)

/-- `g_j · v^(2^j)`. -/
def P (m0 : MachineData) (j : Nat) : EW := EW.mul (gE m0 j) (W m0 j)

/-- A limb's bits. -/
abbrev c0 (x : EW) : BitVec 64 := x.c0.toBitVec
/-- A limb's bits. -/
abbrev c1 (x : EW) : BitVec 64 := x.c1.toBitVec

def s01c0 (m0 : MachineData) : BitVec 64 := c0 (P m0 1) ^^^ c0 (P m0 0)
def s01c1 (m0 : MachineData) : BitVec 64 := c1 (P m0 1) ^^^ c1 (P m0 0)
def s03c0 (m0 : MachineData) : BitVec 64 := (c0 (P m0 3) ^^^ c0 (P m0 2)) ^^^ s01c0 m0
def s03c1 (m0 : MachineData) : BitVec 64 := (c1 (P m0 3) ^^^ c1 (P m0 2)) ^^^ s01c1 m0
def s45c0 (m0 : MachineData) : BitVec 64 := c0 (P m0 5) ^^^ c0 (P m0 4)
def s45c1 (m0 : MachineData) : BitVec 64 := c1 (P m0 5) ^^^ c1 (P m0 4)
def s06c0 (m0 : MachineData) : BitVec 64 := (c0 (P m0 6) ^^^ s45c0 m0) ^^^ s03c0 m0
def s06c1 (m0 : MachineData) : BitVec 64 := (c1 (P m0 6) ^^^ s45c1 m0) ^^^ s03c1 m0

/-- The variables' values: the pushed registers, then RAX, RDX, RBP, R12 to R15, the spills. -/
def vB (m0 : MachineData) (rax rdx rbp r12 r13 r14 r15 s8 s16 s24 : BitVec 64) :
    Nat → BitVec 64 := fun i ↦
  ([reg m0 .rbp, reg m0 .r15, reg m0 .r14, reg m0 .r13, reg m0 .r12, reg m0 .rbx, rax, rdx, rbp,
    r12, r13, r14, r15, s8, s16, s24] : List (BitVec 64)).getD i 0

section
variable (m0 : MachineData)

def v1 := vB m0 (c0 (P m0 0)) (c1 (P m0 0)) 0 0 0 (c1 (W m0 0)) (c0 (W m0 0)) 0 0 0
def v2 := vB m0 (c0 (W m0 1)) (c1 (W m0 1)) (c0 (P m0 0)) (c1 (P m0 0)) 0 0 0 0 0 0
def v3 := vB m0 (c0 (P m0 1)) (c1 (P m0 1)) (c0 (P m0 0)) (c1 (P m0 0)) 0 (c0 (W m0 1))
  (c1 (W m0 1)) 0 0 0
def v4 := vB m0 (c0 (W m0 2)) (c1 (W m0 2)) 0 0 (s01c0 m0) 0 0 0 0 (s01c1 m0)
def v5 := vB m0 (c0 (P m0 2)) (c1 (P m0 2)) 0 0 (s01c0 m0) (c0 (W m0 2)) (c1 (W m0 2)) 0 0
  (s01c1 m0)
def v6 := vB m0 (c0 (W m0 3)) (c1 (W m0 3)) 0 0 (s01c0 m0) 0 0 (c1 (P m0 2)) (c0 (P m0 2))
  (s01c1 m0)
def v7 := vB m0 (c0 (P m0 3)) (c1 (P m0 3)) (c0 (W m0 3)) (c1 (W m0 3)) (s01c0 m0) 0 0
  (c1 (P m0 2)) (c0 (P m0 2)) (s01c1 m0)
def v8 := vB m0 (c0 (W m0 4)) (c1 (W m0 4)) 0 0 0 0 0 (c1 (P m0 2)) (s03c0 m0) (s03c1 m0)
def v9 := vB m0 (c0 (P m0 4)) (c1 (P m0 4)) 0 (c0 (W m0 4)) (c1 (W m0 4)) 0 0 (c1 (P m0 2))
  (s03c0 m0) (s03c1 m0)
def v10 := vB m0 (c0 (W m0 5)) (c1 (W m0 5)) 0 0 0 (c1 (P m0 4)) (c0 (P m0 4)) (c1 (P m0 2))
  (s03c0 m0) (s03c1 m0)
def v11 := vB m0 (c0 (P m0 5)) (c1 (P m0 5)) 0 (c0 (W m0 5)) (c1 (W m0 5)) (c1 (P m0 4))
  (c0 (P m0 4)) (c1 (P m0 2)) (s03c0 m0) (s03c1 m0)
def v12 := vB m0 (c0 (W m0 6)) (c1 (W m0 6)) (s45c0 m0) 0 0 0 0 (s45c1 m0) (s03c0 m0) (s03c1 m0)
def v13 := vB m0 (c0 (P m0 6)) (c1 (P m0 6)) (s45c0 m0) 0 0 (c1 (W m0 6)) (c0 (W m0 6))
  (s45c1 m0) (s03c0 m0) (s03c1 m0)
def v14 := vB m0 (c0 (W m0 7)) (c1 (W m0 7)) 0 (s06c1 m0) (s06c0 m0) 0 0 (s45c1 m0) (s03c0 m0)
  (s03c1 m0)
def v15 := vB m0 (c0 (P m0 7)) (c1 (P m0 7)) 0 (s06c1 m0) (s06c0 m0) 0 0 (s45c1 m0) (s03c0 m0)
  (s03c1 m0)

end

end

public section

variable {m0 : MachineData}

theorem lay (hpre : RingPsiPre m0) : Lay m0 80 ringPsiStack (rsOf m0) :=
  ⟨hpre.1, by decide, by decide, ⟨⟨hpre.2.1.1, hpre.2.1.2, hpre.2.2⟩, trivial⟩,
    List.pairwise_singleton _ _⟩

/-- `g`'s words are the entry's in every state between blocks. -/
theorem gload [Labels] (hpre : RingPsiPre m0) {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 80 ringPsiStack (rsOf m0) noWr T vals m) {o : Nat}
    (ho : o + 8 ≤ 128) (ret : BitVec 64) :
    (Sym.load 1 o 8).eval (envS m0 m 80 (rsOf m0) vals ret) =
      (NativeRustcVm.wordOf m0.dmem (gA m0 + BitVec.ofNat 64 o)).toBitVec := by
  simp only [Sym.eval]
  rw [load_eq_wordOf]
  refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun i hi ↦ ?_)
  refine hB.same _ fun hin ↦ hin.elim (fun h1 ↦ ?_) fun ⟨j, e, he, _⟩ ↦ by cases he
  have hnw : NoWrap (gA m0) 128 := hpre.2.1.2
  have hap : Apart (gA m0) 128 (stackBelow m0 ringPsiStack) (ringPsiStack + 8) := hpre.2.2
  show False
  rw [show (envS m0 m 80 (rsOf m0) vals ret).base 1 = gA m0 from rfl, addr_add] at h1
  have := (lay hpre).geo
  rw [inRange_N this, toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)] at h1
  unfold Apart at hap
  rw [stackBelow_toNat' this.sp] at hap
  unfold NoWrap at hnw
  have := this.sp
  omega

theorem gl0 [Labels] (hpre : RingPsiPre m0) {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 80 ringPsiStack (rsOf m0) noWr T vals m) {j : Nat}
    (hj : j < 8) (ret : BitVec 64) :
    (Sym.load 1 (16 * j) 8).eval (envS m0 m 80 (rsOf m0) vals ret) = c0 (gE m0 j) :=
  gload hpre hB (by omega) ret

theorem gl1 [Labels] (hpre : RingPsiPre m0) {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 80 ringPsiStack (rsOf m0) noWr T vals m) {j : Nat}
    (hj : j < 8) (ret : BitVec 64) :
    (Sym.load 1 (16 * j + 8) 8).eval (envS m0 m 80 (rsOf m0) vals ret) = c1 (gE m0 j) := by
  rw [gload hpre hB (by omega) ret, ← addr_add]
  rfl

/-- **`ringPsi` is the sum of the products.** -/
theorem psi_eq : ringPsi (vE m0) (arr m0 (gA m0) ringWidth) =
    0 + P m0 0 + P m0 1 + P m0 2 + P m0 3 + P m0 4 + P m0 5 + P m0 6 + P m0 7 := by
  rw [arr, ringPsi_toArray]
  rfl

end

end NativeRustcVmX64.Ring.Psi
