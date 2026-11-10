import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Field.BaseMul

/-!
# `field::clmul`, with its two `clmul_low` calls, as one run

`clmul` (157 instructions at `0x8000dbb0`) calls `clmul_low` on the operands and on their bit
reversals; one `symRunCode` run follows both calls, and one `decide +kernel` (`run_meets`) checks
its `a0` and `a1` against `Field/BaseMul.lean`'s expressions. The frames are the 96 bytes below
`sp`.
-/

namespace Rv64Verifier.Proofs.Field.Clmul
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.FieldContracts Rv64Verifier.Field

def entry : Word := 0x8000dbb0

/-- `clmul` and `clmul_low`, the image's words from `0x8000dbb0` to `0x8000df24`. -/
def window : Code := codeWindow Image.code 14060 221

theorem window_sub : CodeSub window Image.code :=
  codeWindow_sub Image.code 14060 221 (by decide +kernel)

/-- `ra`, `sp` and `s0`..`s11`. -/
def kept : List Reg :=
  [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The frames' doubleword `i`, from the bottom: `sp - 96 + 8 * i`. -/
def slot (i : Nat) : Addr := ⟨some (.reg .x2), BitVec.ofNat 64 (2 ^ 64 - 96 + 8 * i)⟩

def m3 : E := .ld (.c ClmulLow.poolAddr)

/-- The high word: the low word of the reversed operands' product, reversed, shifted by one. -/
def hiE : E :=
  BaseMul.srlC (BaseMul.revE (ClmulLow.clmulLowE (BaseMul.revE (.reg .x10))
    (BaseMul.revE (.reg .x11)) m3)) 1

def cfg : Config := { noAlias := true }

def expect : Expect where
  steps := 285
  pc := .bin .and (.reg .x1) (.c (~~~1#64))
  regs := (.x10, ClmulLow.clmulLowE (.reg .x10) (.reg .x11) m3) :: (.x11, hiE) ::
    kept.map fun r => (r, .reg r)
  mem := []
  writes := (List.range 12).map slot
  obl := (List.range 12).map (fun i => .valid (slot i) 8) ++
    (List.range 12).map (fun i => .ne ⟨none, ClmulLow.poolAddr⟩ (slot i))

theorem run_meets : (symRunCode cfg window entry 400).any (·.meets cfg expect) = true := by
  decide +kernel

theorem slot_eval (s : MachineState) (i : Nat) :
    (slot i).eval s = s.getReg .x2 - 96 + BitVec.ofNat 64 (8 * i) := by
  show s.getReg .x2 + BitVec.ofNat 64 (2 ^ 64 - 96 + 8 * i) = _
  bv_omega

theorem pool_eq : ClmulLow.poolAddr = poolAddr := rfl

theorem m3_eq : ClmulLow.M3 = poolWord := by decide

theorem hiE_eval (s : MachineState) (h : s.getMem ClmulLow.poolAddr = ClmulLow.M3) :
    hiE.eval s = (Model.clmul (s.getReg .x10) (s.getReg .x11)).1 := by
  rw [hiE, BaseMul.srlC_one_eval, BaseMul.revE_eval, m3, BaseMul.clmulLowE_eval _ _ _ h,
    BaseMul.revE_eval, BaseMul.revE_eval]
  rfl

/-- **`clmul` meets its contract.** -/
theorem clmul_spec : ClmulSpec := by
  intro s hpc hpre
  have hsp := hpre.stack.bounds (by decide) (by decide)
  have hpool := hpre.pool.apart
  have hw : s.getMem ClmulLow.poolAddr = ClmulLow.M3 := by
    rw [pool_eq, m3_eq]; exact hpre.pool.word
  have hb := BlockSpec.of_expectCode (x := expect) run_meets window_sub
    (P := (· = s)) (Q := fun s t ↦ expect.Holds s t) ?_ (fun _ _ _ hx ↦ hx)
  · obtain ⟨t, ht, hx⟩ := hb s hpc rfl
    obtain ⟨hpc', hregs, -, hframe⟩ := hx
    have hreg : ∀ p ∈ expect.regs, t.getReg p.1 = p.2.eval s := hregs
    refine ⟨t, ⟨_, ht⟩, Or.inl ⟨hpc', fun r hr ↦ ?_, ?_, ?_, ?_⟩⟩
    · exact hreg (r, .reg r) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_map_of_mem (by simp only [Rv64Verifier.calleeSaved, kept, List.mem_cons] at hr ⊢; tauto))))
    · rw [hreg _ (List.mem_cons_self ..), m3]
      exact BaseMul.clmulLowE_eval s _ _ hw
    · rw [hreg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]
      exact hiE_eval s hw
    · intro a ha
      apply hframe
      intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      rw [slot_eval]
      have hi' := List.mem_range.mp hi
      intro heq
      apply ha
      rw [heq]
      addr_omega [hsp, hi']
  · intro s' hs
    rw [hs, Oblig.all_iff]
    intro o ho
    simp only [expect, List.mem_append, List.mem_map, List.mem_range] at ho
    rcases ho with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · show validAccess 8 ((slot i).eval s) = true
      rw [slot_eval]
      valid_access hpre.stack.valid [hsp, hi]
    · show ClmulLow.poolAddr ≠ (slot i).eval s
      rw [slot_eval, pool_eq]
      addr_omega [hsp, hi, hpool]

end Rv64Verifier.Proofs.Field.Clmul
