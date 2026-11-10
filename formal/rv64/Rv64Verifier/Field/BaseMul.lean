import Rv64Verifier.Sym.Code
import Rv64Verifier.Field.ClmulLow
import Rv64Verifier.Model.Field
import Rv64Verifier.Frame
import Mathlib.Tactic.IntervalCases

/-!
# `field::base_mul`, with its calls, as one run

`base_mul` (18 instructions at `0x80011128`) calls `clmul` (157 instructions), which calls
`clmul_low` (64 instructions) on the operands and on their bit reversals, which `clmul` computes
inline; `base_mul` then reduces the 128-bit product. `symRunCode` follows the calls and the
returns, 303 steps from `base_mul`'s entry to its own return, and one `decide +kernel`
(`run_meets`) checks that the run's `a0` is `baseMulE` up to associativity and commutativity.
`baseMulE` mirrors the compiled code: `bswapE` and `swapE` are its byte swap and its three swap
stages (`revE_eval`: together the bit reversal), and `reduceE` is its reduction, which leaves out
the `hi >>> 63` term of the Rust's `reduce` because `clmul`'s high word is shifted right by one
(`reduceE_eval`). The frames of the three functions are the 112 bytes below `sp`.
-/

namespace Rv64Verifier.Field.BaseMul
open RiscvZkvm.Rv64 Rv64Verifier.Sym

def orE (a b : E) : E := .bin .or a b
def andC (a : E) (m : Word) : E := .bin .and a (.c m)
def srlC (a : E) (k : Word) : E := .bin .srl a (.c k)
def sllC (a : E) (k : Word) : E := .bin .sll a (.c k)

/-- The compiled byte swap. -/
def bswapE (x : E) : E :=
  orE (orE (orE (andC (srlC x 24) 0xff0000) (andC (srlC x 8) 0xff000000))
    (orE (andC (srlC x 40) 0xff00) (srlC x 56)))
  (orE (orE (sllC (andC x 0xff0000) 24) (sllC (.bin (.w .srl) x (.c 24)) 32))
    (orE (sllC x 56) (sllC (andC x 0xff00) 40)))

/-- One swap stage of the bit reversal. -/
def swapE (x : E) (k m : Word) : E := orE (andC (srlC x k) m) (sllC (andC x m) k)

/-- The compiled bit reversal. -/
def revE (x : E) : E :=
  swapE (swapE (swapE (bswapE x) 4 0x0f0f0f0f0f0f0f0f) 2 0x3333333333333333) 1 0x5555555555555555

/-- The compiled reduction of the 128-bit product `hi`, `lo`. -/
def reduceE (hi lo : E) : E :=
  let v := .bin .xor (.bin .xor hi (srlC hi 61)) (srlC hi 60)
  .bin .xor (.bin .xor (.bin .xor (.bin .xor lo (sllC v 1)) (sllC v 3)) (sllC v 4)) v

/-- The value `base_mul` computes, with `M3` given as `m3`. -/
def baseMulE (a b m3 : E) : E :=
  reduceE (srlC (revE (ClmulLow.clmulLowE (revE a) (revE b) m3)) 1) (ClmulLow.clmulLowE a b m3)

/-! ## Meaning -/

theorem revE_eval (s : MachineState) (x : E) : (revE x).eval s = (x.eval s).reverse := by
  simp only [revE, swapE, bswapE, orE, andC, srlC, sllC, E.eval, BinOp.eval, wordResult]
  generalize x.eval s = v
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getElem_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getElem_signExtend, BitVec.getElem_setWidth, BitVec.getElem_ushiftRight]

theorem reduceE_eval (s : MachineState) (hi lo : E) (h : hi.eval s >>> 63 = 0) :
    (reduceE hi lo).eval s = Model.reduceWords (hi.eval s) (lo.eval s) := by
  simp only [reduceE, srlC, sllC, E.eval, BinOp.eval, Model.reduceWords, h, BitVec.xor_assoc]
  ac_rfl

theorem srlC_one_eval (s : MachineState) (x : E) : (srlC x 1).eval s = x.eval s >>> 1 := by
  simp [srlC, E.eval, BinOp.eval]

theorem clmulLowE_eval (s : MachineState) (a b : E)
    (h : s.getMem ClmulLow.poolAddr = ClmulLow.M3) :
    (ClmulLow.clmulLowE a b (.ld (.c ClmulLow.poolAddr))).eval s =
      Model.clmulLow (a.eval s) (b.eval s) := by
  rw [← ClmulLow.clmulLowMirror_eq]
  simp only [ClmulLow.clmulLowE, ClmulLow.clmulLowMirror, E.eval, BinOp.eval, h]

theorem baseMulE_eval (s : MachineState) (h : s.getMem ClmulLow.poolAddr = ClmulLow.M3) :
    (baseMulE (.reg .x10) (.reg .x11) (.ld (.c ClmulLow.poolAddr))).eval s =
      Model.baseMul (s.getReg .x10) (s.getReg .x11) := by
  unfold baseMulE
  rw [reduceE_eval _ _ _ (by rw [srlC_one_eval]; bv_omega), srlC_one_eval, revE_eval,
    clmulLowE_eval _ _ _ h, revE_eval, revE_eval, clmulLowE_eval _ _ _ h]
  rfl

/-! ## The run -/

def entry : Word := 0x80011128

theorem entry_listed :
    ("verifier[72855cb32e92cc4d]::field::base_mul", entry, 72) ∈ Image.functions := by
  decide +kernel

/-- `clmul`, `base_mul` and `clmul_low`, the image's words from `0x80010d84` to `0x80011270`. -/
def window : Code := codeWindow Image.code 17249 315

theorem window_sub : CodeSub window Image.code :=
  codeWindow_sub Image.code 17249 315 (by decide +kernel)

/-- `ra`, `sp` and `s0`..`s11`. -/
def calleeSaved : List Reg :=
  [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The frames' doubleword `i`, from the bottom: `sp - 112 + 8 * i`. -/
def slot (i : Nat) : Addr := ⟨some (.reg .x2), BitVec.ofNat 64 (2 ^ 64 - 112 + 8 * i)⟩

def cfg : Config := { noAlias := true }

def expect : Expect where
  steps := 303
  pc := .bin .and (.reg .x1) (.c (~~~1#64))
  regs := (.x10, baseMulE (.reg .x10) (.reg .x11) (.ld (.c ClmulLow.poolAddr))) ::
    calleeSaved.map fun r => (r, .reg r)
  mem := []
  writes := (List.range 14).map slot
  obl := (List.range 14).map (fun i => .valid (slot i) 8) ++
    (List.range 14).map (fun i => .ne ⟨none, ClmulLow.poolAddr⟩ (slot i))

/-- The kernel runs the symbolic executor through `base_mul`, `clmul` and both `clmul_low` calls,
and checks `expect`. -/
theorem run_meets : (symRunCode cfg window entry 400).any (·.meets cfg expect) = true := by
  decide +kernel

/-- The entry condition: the frames' fourteen doublewords below `sp` are valid riscv-zkvm memory,
`M3` is at `poolAddr`, and the frames do not cover `poolAddr`. -/
def Pre (s : MachineState) : Prop :=
  ValidMemRange (s.getReg .x2 - 112) 14 ∧ s.getMem ClmulLow.poolAddr = ClmulLow.M3 ∧
    ((s.getReg .x2).toNat ≤ ClmulLow.poolAddr.toNat ∨
      ClmulLow.poolAddr.toNat + 120 ≤ (s.getReg .x2).toNat)

/-- Memory outside the frames below `sp` is unchanged. -/
def FrameOnly (s t : MachineState) : Prop :=
  ∀ a, (∀ i < 14, a ≠ s.getReg .x2 - 112 + BitVec.ofNat 64 (8 * i)) → t.getMem a = s.getMem a

/-- At the return: `pc` is the entry's `ra` as `JALR` masks it, `a0` is `Model.baseMul a0 a1`,
`ra`, `sp` and `s0`..`s11` are unchanged, and so is all memory outside the frames. -/
def Post (s t : MachineState) : Prop :=
  t.pc = s.getReg .x1 &&& ~~~1#64 ∧
    t.getReg .x10 = Model.baseMul (s.getReg .x10) (s.getReg .x11) ∧
    (∀ r ∈ calleeSaved, t.getReg r = s.getReg r) ∧ FrameOnly s t

theorem slot_eval (s : MachineState) (i : Nat) :
    (slot i).eval s = s.getReg .x2 - 112 + BitVec.ofNat 64 (8 * i) := by
  show s.getReg .x2 + BitVec.ofNat 64 (2 ^ 64 - 112 + 8 * i) = _
  bv_omega

theorem base_mul_spec : BlockSpec Image.code entry 303 Pre Post := by
  refine BlockSpec.of_expectCode (x := expect) run_meets window_sub ?_ ?_
  · rintro s ⟨hv, -, hd⟩
    rw [Oblig.all_iff]
    intro o ho
    simp only [expect, List.mem_append, List.mem_map, List.mem_range] at ho
    rcases ho with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · show validAccess 8 ((slot i).eval s) = true
      rw [slot_eval]
      exact hv.get hi
    · show ClmulLow.poolAddr ≠ (slot i).eval s
      rw [slot_eval]
      simp only [ClmulLow.poolAddr] at hd ⊢
      bv_omega
  · rintro s t ⟨-, hm, -⟩ ⟨hpc, hregs, -, hframe⟩
    refine ⟨hpc, ?_, ?_, ?_⟩
    · rw [hregs _ (List.mem_cons_self ..)]
      exact baseMulE_eval s hm
    · intro r hr
      exact hregs (r, .reg r) (List.mem_cons_of_mem _ (List.mem_map_of_mem hr))
    · intro a ha
      apply hframe
      intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      rw [slot_eval]
      exact ha i (List.mem_range.mp hi)

/-- `base_mul`'s contract, in `Frame.lean`'s terms. -/
theorem base_mul_funSpec : FunSpec Image.code entry Pre fun s t ↦
    t.getReg .x10 = Model.baseMul (s.getReg .x10) (s.getReg .x11) ∧ FrameOnly s t := by
  intro s hpc hP
  obtain ⟨t, hst, hpc', ha0, hregs, hframe⟩ := base_mul_spec s hpc hP
  exact ⟨t, ⟨_, hst⟩, Or.inl ⟨hpc', fun r hr ↦ hregs r (List.mem_cons_of_mem _ hr), ha0, hframe⟩⟩

/-- **`base_mul` multiplies in `GF(2^64)`.** -/
theorem base_mul_correct : BlockSpec Image.code entry 303 Pre fun s t ↦
    t.pc = s.getReg .x1 &&& ~~~1#64 ∧
      t.getReg .x10 = (BF64.ofBitVec (s.getReg .x10) * BF64.ofBitVec (s.getReg .x11)).toBitVec :=
  base_mul_spec.mono (fun _ h ↦ h) fun s t _ ⟨hpc, ha0, _⟩ ↦
    ⟨hpc, by rw [ha0, ← Model.baseMul_eq]; rfl⟩

end Rv64Verifier.Field.BaseMul
