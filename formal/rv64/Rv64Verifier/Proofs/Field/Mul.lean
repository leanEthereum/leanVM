import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Field.BaseMul

/-!
# `<E as Mul>::mul`, with its six `clmul` calls, as one run

`mul` (123 instructions at `0x80008c48`) loads both operands, calls `clmul` (which calls
`clmul_low` twice) six times, and folds the six products into three limbs, each reduced as
`base_mul` reduces (`BaseMul.reduceE`). One `symRunCode` run follows all twelve calls (1833
steps), and one `decide +kernel` (`run_meets`) checks the three limbs it writes at `a0` against
`limbE`. `limbE` evaluates to the Rust's Karatsuba with each 128-bit word split into its high and
low words (`limbE_eval`); `emul_split` puts `Model.emul` in the same form, and `Model.emul_eq` is
the `E` product. The frames are the 224 bytes below `sp`.
-/

namespace Rv64Verifier.Proofs.Field.Mul
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.FieldContracts Rv64Verifier.Field
  Rv64Verifier.Contracts

/-! ## The expressions -/

def m3 : E := .ld (.c ClmulLow.poolAddr)

def xorE (a b : E) : E := .bin .xor a b

/-- `clmul`'s low word. -/
def loE (a b : E) : E := ClmulLow.clmulLowE a b m3

/-- `clmul`'s high word. -/
def hiE (a b : E) : E :=
  BaseMul.srlC (BaseMul.revE (ClmulLow.clmulLowE (BaseMul.revE a) (BaseMul.revE b) m3)) 1

/-- Limb `k` of the operand at `r`. -/
def opE (r : Reg) (k : Word) : E := .ld (if k = 0 then .reg r else .bin .add (.reg r) (.c k))

/-- The four products a limb sums, as `(lhs, rhs)` pairs: a pair of limb sets, each summed. -/
def prods : Nat → List (List Word × List Word)
  | 0 => [([0], [0]), ([8], [8]), ([16], [16]), ([8, 16], [8, 16])]
  | 1 => [([0], [0]), ([0, 8], [0, 8]), ([8, 16], [8, 16])]
  | _ => [([0], [0]), ([8], [8]), ([0, 16], [0, 16])]

def sumE (r : Reg) : List Word → E
  | [] => .c 0
  | [k] => opE r k
  | k :: ks => xorE (opE r k) (sumE r ks)

def foldXor (f : List Word × List Word → E) : List (List Word × List Word) → E
  | [] => .c 0
  | [p] => f p
  | p :: ps => xorE (f p) (foldXor f ps)

/-- Limb `i` of the product, as `mul` computes it. -/
def limbE (i : Nat) : E :=
  BaseMul.reduceE (foldXor (fun p ↦ hiE (sumE .x11 p.1) (sumE .x12 p.2)) (prods i))
    (foldXor (fun p ↦ loE (sumE .x11 p.1) (sumE .x12 p.2)) (prods i))

/-! ## The run -/

def entry : Word := 0x80008c48

/-- `mul` through `clmul_low`, the image's words from `0x80008c48` to `0x8000df24`. -/
def window : Code := codeWindow Image.code 8978 5303

theorem window_sub : CodeSub window Image.code :=
  codeWindow_sub Image.code 8978 5303 (by decide +kernel)

/-- `ra`, `sp` and `s0`..`s11`. -/
def kept : List Reg :=
  [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The frames' doubleword `i`, from the bottom: `sp - 224 + 8 * i`. -/
def slot (i : Nat) : Addr := ⟨some (.reg .x2), BitVec.ofNat 64 (2 ^ 64 - 224 + 8 * i)⟩

/-- Limb `k` of the operand or result at `r`. -/
def limb (r : Reg) (k : Nat) : Addr := ⟨some (.reg r), BitVec.ofNat 64 (8 * k)⟩

/-- The addresses that must not meet the frames. -/
def others : List Addr :=
  ⟨none, ClmulLow.poolAddr⟩ :: [Reg.x10, .x11, .x12].flatMap fun r ↦ (List.range 3).map (limb r)

def cfg : Config := { noAlias := true }

def expect : Expect where
  steps := 1833
  pc := .bin .and (.reg .x1) (.c (~~~1#64))
  regs := kept.map fun r => (r, .reg r)
  mem := (List.range 3).map fun i ↦ (limb .x10 i, limbE i)
  writes := (List.range 3).map (limb .x10) ++ (List.range 28).map slot
  obl := (List.range 28).map (fun i ↦ .valid (slot i) 8) ++
    ([Reg.x10, .x11, .x12].flatMap fun r ↦ (List.range 3).map fun k ↦ .valid (limb r k) 8) ++
    others.flatMap fun o ↦ (List.range 28).flatMap fun i ↦ [.ne o (slot i), .ne (slot i) o]

theorem run_meets : (symRunCode cfg window entry 3000).any (·.meets cfg expect) = true := by
  decide +kernel

/-! ## Meaning -/

section
variable (s : MachineState) (hw : s.getMem ClmulLow.poolAddr = ClmulLow.M3)
include hw

theorem loE_eval (a b : E) : (loE a b).eval s = (Model.clmul (a.eval s) (b.eval s)).2 :=
  BaseMul.clmulLowE_eval s a b hw

theorem hiE_eval (a b : E) : (hiE a b).eval s = (Model.clmul (a.eval s) (b.eval s)).1 := by
  rw [hiE, BaseMul.srlC_one_eval, BaseMul.revE_eval, m3, BaseMul.clmulLowE_eval _ _ _ hw,
    BaseMul.revE_eval, BaseMul.revE_eval]
  rfl

end

theorem clmul_hi_top (a b : BitVec 64) : (Model.clmul a b).1 >>> 63 = 0 := by
  simp only [Model.clmul]
  bv_omega

theorem append_xor (a b c d : BitVec 64) : (a ^^^ b) ++ (c ^^^ d) = (a ++ c) ^^^ (b ++ d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor]
  split <;> rfl

theorem cl_eq (a b : BitVec 64) : (Model.clmul a b).1 ++ (Model.clmul a b).2 = Model.cl a b :=
  Model.clmul_eq a b

set_option maxRecDepth 20000 in
/-- The value of the three limbs, given the operands' limbs in memory. -/
theorem limbE_eval (s : MachineState) (hw : s.getMem ClmulLow.poolAddr = ClmulLow.M3) :
    ((limbE 0).eval s, (limbE 1).eval s, (limbE 2).eval s) =
      Model.emul (s.getMem (s.getReg .x11)) (s.getMem (s.getReg .x11 + 8))
        (s.getMem (s.getReg .x11 + 16)) (s.getMem (s.getReg .x12))
        (s.getMem (s.getReg .x12 + 8)) (s.getMem (s.getReg .x12 + 16)) := by
  simp only [limbE, prods]
  rw [BaseMul.reduceE_eval _ _ _ ?t0, BaseMul.reduceE_eval _ _ _ ?t1,
    BaseMul.reduceE_eval _ _ _ ?t2]
  case t0 | t1 | t2 =>
    simp only [foldXor, xorE, E.eval, BinOp.eval, BitVec.ushiftRight_xor_distrib, hiE_eval s hw,
      clmul_hi_top]
    rfl
  simp only [foldXor, sumE, opE, xorE, E.eval, BinOp.eval, hiE_eval s hw, loE_eval s hw,
    ite_true, show ((8 : Word) = 0) = False by decide, show ((16 : Word) = 0) = False by decide,
    ite_false, Model.emul, Model.reduceWords_eq, append_xor, cl_eq, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> xor_cancel

/-! ## The contract -/

theorem slot_eval (s : MachineState) (i : Nat) :
    (slot i).eval s = s.getReg .x2 - 224 + BitVec.ofNat 64 (8 * i) := by
  show s.getReg .x2 + BitVec.ofNat 64 (2 ^ 64 - 224 + 8 * i) = _
  bv_omega

theorem limb_eval (s : MachineState) (r : Reg) (k : Nat) :
    (limb r k).eval s = s.getReg r + BitVec.ofNat 64 (8 * k) := rfl

theorem pool_eq : ClmulLow.poolAddr = poolAddr := rfl

theorem pool_addr_eval (s : MachineState) :
    (⟨none, ClmulLow.poolAddr⟩ : Addr).eval s = poolAddr := rfl

/-- **`mul` multiplies in `E`**, given `M3` in place. -/
theorem mul_spec : EMulSpec := by
  intro s hpc ⟨hpre, hpool⟩
  have hsp := hpre.stack.bounds (by decide) (by decide)
  have hpa := hpool.apart
  have hO := ValidMemRange.bounds hpre.out (by decide)
  have hL := ValidMemRange.bounds hpre.lhs (by decide)
  have hR := ValidMemRange.bounds hpre.rhs (by decide)
  have hOs := hpre.outStack
  have hLs := hpre.lhsStack
  have hRs := hpre.rhsStack
  have hw : s.getMem ClmulLow.poolAddr = ClmulLow.M3 := by
    rw [pool_eq, show ClmulLow.M3 = poolWord by decide]; exact hpool.word
  have hb := BlockSpec.of_expectCode (x := expect) run_meets window_sub
    (P := (· = s)) (Q := fun s t ↦ expect.Holds s t) ?_ (fun _ _ _ hx ↦ hx)
  · obtain ⟨t, ht, hx⟩ := hb s hpc rfl
    obtain ⟨hpc', hregs, hmem, hframe⟩ := hx
    have hreg : ∀ p ∈ expect.regs, t.getReg p.1 = p.2.eval s := hregs
    have hm : ∀ i < 3, t.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * i)) = (limbE i).eval s :=
      fun i hi ↦ hmem (limb .x10 i, limbE i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    refine ⟨t, ⟨_, ht⟩, Or.inl ⟨hpc', fun r hr ↦ ?_, ⟨?_, ?_⟩⟩⟩
    · exact hreg (r, .reg r) (List.mem_map_of_mem
        (by simp only [Rv64Verifier.calleeSaved, kept, List.mem_cons] at hr ⊢; tauto))
    · apply eq_of_limbs
      rw [← Model.emul_eq, limbs_eAt, limbs_eAt, limbs_eAt, ← limbE_eval s hw]
      have h0 : t.getMem (s.getReg .x10) = (limbE 0).eval s := by simpa using hm 0 (by decide)
      have h1 : t.getMem (s.getReg .x10 + 8) = (limbE 1).eval s := hm 1 (by decide)
      have h2 : t.getMem (s.getReg .x10 + 16) = (limbE 2).eval s := hm 2 (by decide)
      rw [h0, h1, h2]
    · intro a hout hstk
      apply hframe
      intro k hk
      simp only [expect, List.mem_append, List.mem_map, List.mem_range] at hk
      rcases hk with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · rw [limb_eval]
        intro heq; apply hout; rw [heq]; addr_omega [hi, hO]
      · rw [slot_eval]
        intro heq; apply hstk; rw [heq]; addr_omega [hi, hsp]
  · intro s' hs
    rw [hs, Oblig.all_iff]
    intro o ho
    simp only [expect, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with (⟨i, hi, rfl⟩ | ⟨r, hr, k, hk, rfl⟩) | ⟨o, ho, i, hi, rfl | rfl⟩
    · show validAccess 8 ((slot i).eval s) = true
      rw [slot_eval]
      valid_access hpre.stack.valid [hsp, hi]
    · show validAccess 8 ((limb r k).eval s) = true
      rw [limb_eval]
      rcases hr with rfl | rfl | rfl
      · valid_access hpre.out [hO, hk]
      · valid_access hpre.lhs [hL, hk]
      · valid_access hpre.rhs [hR, hk]
    all_goals
      show Addr.eval s _ ≠ Addr.eval s _
      rw [slot_eval]
      simp only [others, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range] at ho
      rcases ho with rfl | ⟨r, hr, k, hk, rfl⟩
      · rw [pool_addr_eval]
        addr_omega [hsp, hi, hpa]
      · rw [limb_eval]
        simp only [List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · addr_omega [hsp, hi, hk, hO, hOs]
        · addr_omega [hsp, hi, hk, hL, hLs]
        · addr_omega [hsp, hi, hk, hR, hRs]

end Rv64Verifier.Proofs.Field.Mul
