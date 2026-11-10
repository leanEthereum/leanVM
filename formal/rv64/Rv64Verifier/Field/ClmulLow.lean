import Rv64Verifier.Sym.Api
import Rv64Verifier.Image
import Rv64Verifier.Model.Clmul

/-!
# `field::clmul_low`, whole function

The image's `clmul_low` (64 instructions at `0x80010804`: it saves `s0` and `s1`, computes, restores
them and returns with `jalr zero, 0(ra)`) computes `clmulLowMirror`, a transcription of the Rust:

```rust
const fn clmul_low(a: u64, b: u64) -> u64 {
    const M0: u64 = 0x1111_1111_1111_1111;
    const M1: u64 = M0 << 1;
    const M2: u64 = M0 << 2;
    const M3: u64 = M0 << 3;
    let (x0, x1, x2, x3) = (a & M0, a & M1, a & M2, a & M3);
    let (y0, y1, y2, y3) = (b & M0, b & M1, b & M2, b & M3);
    let z0 = x0.wrapping_mul(y0) ^ x1.wrapping_mul(y3) ^ x2.wrapping_mul(y2) ^ x3.wrapping_mul(y1);
    let z1 = x0.wrapping_mul(y1) ^ x1.wrapping_mul(y0) ^ x2.wrapping_mul(y3) ^ x3.wrapping_mul(y2);
    let z2 = x0.wrapping_mul(y2) ^ x1.wrapping_mul(y1) ^ x2.wrapping_mul(y0) ^ x3.wrapping_mul(y3);
    let z3 = x0.wrapping_mul(y3) ^ x1.wrapping_mul(y2) ^ x2.wrapping_mul(y1) ^ x3.wrapping_mul(y0);
    z0 & M0 | z1 & M1 | z2 & M2 | z3 & M3
}
```

The compiler builds `M0`, `M1` and `M2` with `lui`/`addi`/`slli`/`add` but loads `M3` from the
image's data at `0xa0000008`, so the entry condition asks for that word, and for the frame not to
cover it. The products stay opaque: the run's `a0` equals the mirror up to the associativity and
commutativity of `&&&`, `|||`, `^^^` and `*` (`E.acEq`), checked with the run by one
`decide +kernel` (`run_meets`).
-/

namespace Rv64Verifier.Field.ClmulLow
open RiscvZkvm.Rv64 Rv64Verifier.Sym

def M0 : BitVec 64 := 0x1111111111111111
def M1 : BitVec 64 := M0 <<< 1
def M2 : BitVec 64 := M0 <<< 2
def M3 : BitVec 64 := M0 <<< 3

/-- The Rust `clmul_low`. -/
def clmulLowMirror (a b : BitVec 64) : BitVec 64 :=
  let x0 := a &&& M0
  let x1 := a &&& M1
  let x2 := a &&& M2
  let x3 := a &&& M3
  let y0 := b &&& M0
  let y1 := b &&& M1
  let y2 := b &&& M2
  let y3 := b &&& M3
  let z0 := x0 * y0 ^^^ x1 * y3 ^^^ x2 * y2 ^^^ x3 * y1
  let z1 := x0 * y1 ^^^ x1 * y0 ^^^ x2 * y3 ^^^ x3 * y2
  let z2 := x0 * y2 ^^^ x1 * y1 ^^^ x2 * y0 ^^^ x3 * y3
  let z3 := x0 * y3 ^^^ x1 * y2 ^^^ x2 * y1 ^^^ x3 * y0
  (z0 &&& M0) ||| (z1 &&& M1) ||| (z2 &&& M2) ||| (z3 &&& M3)

/-- `clmulLowMirror` as a symbolic expression, with `M3` given as `m3`. -/
def clmulLowE (a b m3 : E) : E :=
  let and := fun x y => E.bin .and x y
  let mul := fun x y => E.bin .mul x y
  let xor := fun x y => E.bin .xor x y
  let or := fun x y => E.bin .or x y
  let x0 := and a (.c M0)
  let x1 := and a (.c M1)
  let x2 := and a (.c M2)
  let x3 := and a m3
  let y0 := and b (.c M0)
  let y1 := and b (.c M1)
  let y2 := and b (.c M2)
  let y3 := and b m3
  let z0 := xor (xor (xor (mul x0 y0) (mul x1 y3)) (mul x2 y2)) (mul x3 y1)
  let z1 := xor (xor (xor (mul x0 y1) (mul x1 y0)) (mul x2 y3)) (mul x3 y2)
  let z2 := xor (xor (xor (mul x0 y2) (mul x1 y1)) (mul x2 y0)) (mul x3 y3)
  let z3 := xor (xor (xor (mul x0 y3) (mul x1 y2)) (mul x2 y1)) (mul x3 y0)
  or (or (or (and z0 (.c M0)) (and z1 (.c M1))) (and z2 (.c M2))) (and z3 m3)

/-- The address of the image's data word the compiler reads `M3` from. -/
def poolAddr : Word := 0xa0000008

theorem clmulLowE_eval (s : MachineState) (h : s.getMem poolAddr = M3) :
    (clmulLowE (.reg .x10) (.reg .x11) (.ld (.c poolAddr))).eval s =
      clmulLowMirror (s.getReg .x10) (s.getReg .x11) := by
  simp only [clmulLowE, clmulLowMirror, E.eval, BinOp.eval, h]

def entry : Word := 0x80010804

theorem entry_listed :
    ("verifier[312c7e26d4ca39a]::field::clmul_low", entry, 256) ∈ Image.functions := by
  decide +kernel

/-- The function's 64 instructions. -/
def words : List (BitVec 32) := (Image.code.words.drop 16897).take 64

theorem codeAt : CodeAt Image.code entry words :=
  CodeAt.slice Image.code 16897 64 entry (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- `ra`, `sp` and `s0`..`s11`. -/
def calleeSaved : List Reg :=
  [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The frame's doubleword `i`, from the bottom: `sp - 16 + 8 * i`. -/
def slot (i : Nat) : Addr := ⟨some (.reg .x2), BitVec.ofNat 64 (2 ^ 64 - 16 + 8 * i)⟩

def cfg : Config := { noAlias := true }

def expect : Expect where
  steps := 64
  pc := .bin .and (.reg .x1) (.c (~~~1#64))
  regs := (.x10, clmulLowE (.reg .x10) (.reg .x11) (.ld (.c poolAddr))) ::
    calleeSaved.map fun r => (r, .reg r)
  mem := []
  writes := (List.range 2).map slot
  obl := (List.range 2).map (fun i => .valid (slot i) 8) ++
    (List.range 2).map (fun i => .ne ⟨none, poolAddr⟩ (slot i))

/-- The kernel runs the symbolic executor over the function and checks `expect`. -/
theorem run_meets : (symRun cfg words entry 64).any (·.meets cfg expect) = true := by
  decide +kernel

/-- The entry condition: the frame's two doublewords below `sp` are valid riscv-zkvm memory
(`ValidMemRange` includes their alignment), `M3` is at `poolAddr`, and the frame does not cover
`poolAddr`. -/
def Pre (s : MachineState) : Prop :=
  ValidMemRange (s.getReg .x2 - 16) 2 ∧ s.getMem poolAddr = M3 ∧
    ((s.getReg .x2).toNat ≤ poolAddr.toNat ∨ poolAddr.toNat + 24 ≤ (s.getReg .x2).toNat)

/-- At the return: `pc` is the entry's `ra` as `JALR` masks it, `a0` is `clmulLowMirror a0 a1`,
`ra`, `sp` and `s0`..`s11` are unchanged, and so is all memory outside the frame. -/
def Post (s t : MachineState) : Prop :=
  t.pc = s.getReg .x1 &&& ~~~1#64 ∧
    t.getReg .x10 = clmulLowMirror (s.getReg .x10) (s.getReg .x11) ∧
    (∀ r ∈ calleeSaved, t.getReg r = s.getReg r) ∧
    ∀ a, (∀ i < 2, a ≠ s.getReg .x2 - 16 + BitVec.ofNat 64 (8 * i)) → t.getMem a = s.getMem a

theorem slot_eval (s : MachineState) (i : Nat) :
    (slot i).eval s = s.getReg .x2 - 16 + BitVec.ofNat 64 (8 * i) := by
  show s.getReg .x2 + BitVec.ofNat 64 (2 ^ 64 - 16 + 8 * i) = _
  bv_omega

theorem clmul_low_spec : BlockSpec Image.code entry 64 Pre Post := by
  refine BlockSpec.of_expect (x := expect) run_meets codeAt ?_ ?_
  · rintro s ⟨hv, -, hd⟩
    rw [Oblig.all_iff]
    intro o ho
    simp only [expect, List.mem_append, List.mem_map, List.mem_range] at ho
    rcases ho with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · show validAccess 8 ((slot i).eval s) = true
      rw [slot_eval]
      exact hv.get hi
    · show poolAddr ≠ (slot i).eval s
      rw [slot_eval]
      simp only [poolAddr] at hd ⊢
      bv_omega
  · rintro s t ⟨-, hm, -⟩ ⟨hpc, hregs, -, hframe⟩
    refine ⟨hpc, ?_, ?_, ?_⟩
    · rw [hregs _ (List.mem_cons_self ..)]
      exact clmulLowE_eval s hm
    · intro r hr
      exact hregs (r, .reg r) (List.mem_cons_of_mem _ (List.mem_map_of_mem hr))
    · intro a ha
      apply hframe
      intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      rw [slot_eval]
      exact ha i (List.mem_range.mp hi)

/-! ## The carry-less product -/

theorem clmulLowMirror_eq (a b : BitVec 64) : clmulLowMirror a b = Model.clmulLow a b := by
  have h0 : Model.classMask 0 = M0 := by decide
  simp only [clmulLowMirror, Model.clmulLow, h0]
  rfl

theorem clmul_low_correct : BlockSpec Image.code entry 64 Pre fun s t ↦
    t.pc = s.getReg .x1 &&& ~~~1#64 ∧
      t.getReg .x10 =
        (BinaryField.carryLessMul (w := 128) (s.getReg .x10) (s.getReg .x11)).truncate 64 :=
  clmul_low_spec.mono (fun _ h ↦ h) fun s t _ ⟨hpc, ha0, _⟩ ↦
    ⟨hpc, by rw [ha0, clmulLowMirror_eq, Model.clmulLow_eq]⟩

end Rv64Verifier.Field.ClmulLow
