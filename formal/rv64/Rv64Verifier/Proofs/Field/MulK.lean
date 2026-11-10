import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Field.BaseMul

/-!
# `<E as Mul<K>>::mul`, with its three `base_mul` calls, as one run

`mul` (36 instructions at `0x8000ce64`) multiplies each limb of `self` by `rhs` with `base_mul`;
one `symRunCode` run follows the three calls (945 steps), and one `decide +kernel` (`run_meets`)
checks the three limbs it writes against `BaseMul.baseMulE`. `limbs_mul_ofK`: the limbs of
`x * ofK c` are the `base_mul`s of `x`'s limbs by `c`. The frames are the 160 bytes below `sp`.
-/

namespace Rv64Verifier.Proofs.Field.MulK
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.FieldContracts Rv64Verifier.Field

def m3 : E := .ld (.c ClmulLow.poolAddr)

/-- Limb `k` of `self`. -/
def opE (k : Word) : E := .ld (if k = 0 then .reg .x11 else .bin .add (.reg .x11) (.c k))

def limbE (i : Nat) : E := BaseMul.baseMulE (opE (BitVec.ofNat 64 (8 * i))) (.reg .x12) m3

def entry : Word := 0x8000ce64

/-- `mul` through `clmul_low`, the image's words from `0x8000ce64` to `0x8000df24`. -/
def window : Code := codeWindow Image.code 13209 1072

theorem window_sub : CodeSub window Image.code :=
  codeWindow_sub Image.code 13209 1072 (by decide +kernel)

/-- `ra`, `sp` and `s0`..`s11`. -/
def kept : List Reg :=
  [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The frames' doubleword `i`, from the bottom: `sp - 160 + 8 * i`. -/
def slot (i : Nat) : Addr := ⟨some (.reg .x2), BitVec.ofNat 64 (2 ^ 64 - 160 + 8 * i)⟩

/-- Limb `k` of the operand or result at `r`. -/
def limb (r : Reg) (k : Nat) : Addr := ⟨some (.reg r), BitVec.ofNat 64 (8 * k)⟩

/-- The addresses that must not meet the frames. -/
def others : List Addr :=
  ⟨none, ClmulLow.poolAddr⟩ :: [Reg.x10, .x11].flatMap fun r ↦ (List.range 3).map (limb r)

def cfg : Config := { noAlias := true }

def expect : Expect where
  steps := 945
  pc := .bin .and (.reg .x1) (.c (~~~1#64))
  regs := kept.map fun r => (r, .reg r)
  mem := (List.range 3).map fun i ↦ (limb .x10 i, limbE i)
  writes := (List.range 3).map (limb .x10) ++ (List.range 20).map slot
  obl := (List.range 20).map (fun i ↦ .valid (slot i) 8) ++
    ([Reg.x10, .x11].flatMap fun r ↦ (List.range 3).map fun k ↦ .valid (limb r k) 8) ++
    others.flatMap fun o ↦ (List.range 20).flatMap fun i ↦ [.ne o (slot i), .ne (slot i) o]

theorem run_meets : (symRunCode cfg window entry 1200).any (·.meets cfg expect) = true := by
  decide +kernel

/-! ## Meaning -/

theorem baseMulE_eval (s : MachineState) (hw : s.getMem ClmulLow.poolAddr = ClmulLow.M3)
    (a b : E) : (BaseMul.baseMulE a b m3).eval s = Model.baseMul (a.eval s) (b.eval s) := by
  unfold BaseMul.baseMulE
  rw [BaseMul.reduceE_eval _ _ _ (by rw [BaseMul.srlC_one_eval]; bv_omega),
    BaseMul.srlC_one_eval, BaseMul.revE_eval, m3, BaseMul.clmulLowE_eval _ _ _ hw,
    BaseMul.revE_eval, BaseMul.revE_eval, BaseMul.clmulLowE_eval _ _ _ hw]
  rfl

open LeanVM.Parameters in
theorem reduce_cl_zero (u : BitVec 64) : BF64.reduce (Model.cl u 0#64) = 0#64 := by
  have h := Model.reduce_cl (BF64.ofBitVec u) 0
  rw [mul_zero] at h
  exact h

theorem baseMul_cl (a b : BitVec 64) : Model.baseMul a b = BF64.reduce (Model.cl a b) := by
  rw [Model.baseMul, Model.reduceWords_eq, Model.clmul_eq]
  rfl

open LeanVM.Parameters in
/-- The limbs of `x * ofK c`: each limb of `x` times `c`. -/
theorem limbs_mul_ofK (x : LeanVM.Parameters.E) (c : K) : Model.limbs (x * ofK c) =
    (Model.baseMul (Model.limbs x).1 c.toBitVec, Model.baseMul (Model.limbs x).2.1 c.toBitVec,
      Model.baseMul (Model.limbs x).2.2 c.toBitVec) := by
  rw [← Model.emul_eq, Model.limbs_ofK]
  simp only [Model.emul, BitVec.xor_zero, Model.cl_xor_left, Model.reduce_xor, reduce_cl_zero,
    baseMul_cl, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩ <;>
    rw [BitVec.xor_comm, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-! ## The contract -/

theorem slot_eval (s : MachineState) (i : Nat) :
    (slot i).eval s = s.getReg .x2 - 160 + BitVec.ofNat 64 (8 * i) := by
  show s.getReg .x2 + BitVec.ofNat 64 (2 ^ 64 - 160 + 8 * i) = _
  bv_omega

theorem limb_eval (s : MachineState) (r : Reg) (k : Nat) :
    (limb r k).eval s = s.getReg r + BitVec.ofNat 64 (8 * k) := rfl

theorem pool_addr_eval (s : MachineState) :
    (⟨none, ClmulLow.poolAddr⟩ : Addr).eval s = poolAddr := rfl

theorem opE_eval (s : MachineState) (k : Word) :
    (opE k).eval s = s.getMem (if k = 0 then s.getReg .x11 else s.getReg .x11 + k) := by
  unfold opE; split <;> simp [E.eval, BinOp.eval, *]

/-- **`mul` multiplies `E` by `K`.** -/
theorem mul_k_spec : MulKSpec := by
  intro s hpc hpre
  have hsp := hpre.stack.bounds (by decide) (by decide)
  have hpa := hpre.pool.apart
  have hO := ValidMemRange.bounds hpre.out (by decide)
  have hL := ValidMemRange.bounds hpre.lhs (by decide)
  have hOs := hpre.outStack
  have hLs := hpre.lhsStack
  have hw : s.getMem ClmulLow.poolAddr = ClmulLow.M3 := by
    rw [show ClmulLow.M3 = poolWord by decide]; exact hpre.pool.word
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
      have h0 : t.getMem (s.getReg .x10) = (limbE 0).eval s := by simpa using hm 0 (by decide)
      have h1 : t.getMem (s.getReg .x10 + 8) = (limbE 1).eval s := hm 1 (by decide)
      have h2 : t.getMem (s.getReg .x10 + 16) = (limbE 2).eval s := hm 2 (by decide)
      rw [limbs_mul_ofK, limbs_eAt, limbs_eAt, h0, h1, h2]
      simp only [limbE, baseMulE_eval s hw, opE_eval, E.eval]
      rfl
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
      rcases hr with rfl | rfl
      · valid_access hpre.out [hO, hk]
      · valid_access hpre.lhs [hL, hk]
    all_goals
      show Addr.eval s _ ≠ Addr.eval s _
      rw [slot_eval]
      simp only [others, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range] at ho
      rcases ho with rfl | ⟨r, hr, k, hk, rfl⟩
      · rw [pool_addr_eval]
        addr_omega [hsp, hi, hpa]
      · rw [limb_eval]
        simp only [List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · addr_omega [hsp, hi, hk, hO, hOs]
        · addr_omega [hsp, hi, hk, hL, hLs]

end Rv64Verifier.Proofs.Field.MulK
