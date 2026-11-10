import Rv64Verifier.Proofs.Field.Spread

/-!
# `K::square` and `E::square`, each one run

Both are leaves: `K::square` (65 instructions at `0x8000d670`) squares `a0` in place;
`E::square` (160 instructions at `0x8000e2a0`) loads `self`'s three limbs, spreads each, and
writes `reduce(s0)`, `reduce(s2)`, `reduce(s1 ^ s2)` to the return slot. Each is one `symRun`,
checked by one `decide +kernel` against `Spread.lean`'s expressions, which `Model.kSquare` and
`Model.esquare` mirror.
-/

namespace Rv64Verifier.Proofs.Field.Square
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.FieldContracts Rv64Verifier.Field
  Rv64Verifier.Proofs.Field.Spread

/-- `ra`, `sp` and `s0`..`s11`. -/
def kept : List Reg :=
  [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

def cfg : Config := { noAlias := true }

theorem kept_of {r : Reg} (hr : r ∈ Rv64Verifier.calleeSaved) : r ∈ kept := by
  simp only [Rv64Verifier.calleeSaved, kept, List.mem_cons] at hr ⊢; tauto

/-! ## `K::square` -/

def kWords : List (BitVec 32) := (Image.code.words.drop 13724).take 65

theorem kCodeAt : CodeAt Image.code 0x8000d670 kWords :=
  CodeAt.slice Image.code 13724 65 0x8000d670 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

def kExpect : Expect where
  steps := 65
  pc := .bin .and (.reg .x1) (.c (~~~1#64))
  regs := (.x10, sqE (.reg .x10)) :: kept.map fun r => (r, .reg r)
  mem := []
  writes := []
  obl := []

theorem k_run_meets : (symRun cfg kWords 0x8000d670 65).any (·.meets cfg kExpect) = true := by
  decide +kernel

/-- **`K::square` squares.** -/
theorem k_square_spec : KSquareSpec := by
  intro s hpc _
  obtain ⟨t, ht, hpc', hregs, -, hframe⟩ :=
    BlockSpec.of_expect (x := kExpect) k_run_meets kCodeAt (P := fun _ ↦ True)
      (Q := fun s t ↦ kExpect.Holds s t) (fun _ _ ↦ trivial) (fun _ _ _ hx ↦ hx) s hpc trivial
  have hreg : ∀ p ∈ kExpect.regs, t.getReg p.1 = p.2.eval s := hregs
  refine ⟨t, ⟨_, ht⟩, Or.inl ⟨hpc', fun r hr ↦ ?_, ?_, fun a ↦ hframe a (by simp [kExpect])⟩⟩
  · exact hreg (r, .reg r) (List.mem_cons_of_mem _ (List.mem_map_of_mem (kept_of hr)))
  · rw [hreg _ (List.mem_cons_self ..), sqE_eval, ← Model.kSquare_eq]
    rfl

/-! ## `E::square` -/

/-- Limb `k` of the operand at `a1`. -/
def opE (k : Word) : E := .ld (if k = 0 then .reg .x11 else .bin .add (.reg .x11) (.c k))

/-- The three limbs of the square. -/
def eLimbE : Nat → E
  | 0 => sqE' (opE 0)
  | 1 => sqE' (opE 16)
  | _ => sqSumE (opE 8) (opE 16)

def eWords : List (BitVec 32) := (Image.code.words.drop 14504).take 160

theorem eCodeAt : CodeAt Image.code 0x8000e2a0 eWords :=
  CodeAt.slice Image.code 14504 160 0x8000e2a0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Limb `k` of the result or the operand at `r`. -/
def limb (r : Reg) (k : Nat) : Addr := ⟨some (.reg r), BitVec.ofNat 64 (8 * k)⟩

def eExpect : Expect where
  steps := 160
  pc := .bin .and (.reg .x1) (.c (~~~1#64))
  regs := kept.map fun r => (r, .reg r)
  mem := (List.range 3).map fun i ↦ (limb .x10 i, eLimbE i)
  writes := (List.range 3).map (limb .x10)
  obl := [Reg.x10, .x11].flatMap fun r ↦ (List.range 3).map fun k ↦ .valid (limb r k) 8

theorem e_run_meets : (symRun cfg eWords 0x8000e2a0 160).any (·.meets cfg eExpect) = true := by
  decide +kernel

theorem limb_eval (s : MachineState) (r : Reg) (k : Nat) :
    (limb r k).eval s = s.getReg r + BitVec.ofNat 64 (8 * k) := rfl

theorem opE_eval (s : MachineState) (k : Word) :
    (opE k).eval s = s.getMem (if k = 0 then s.getReg .x11 else s.getReg .x11 + k) := by
  unfold opE; split <;> simp [E.eval, BinOp.eval, *]

/-- **`E::square` squares.** -/
theorem e_square_spec : ESquareSpec := by
  intro s hpc hpre
  have hO := ValidMemRange.bounds hpre.out (by decide)
  have hA := ValidMemRange.bounds hpre.arg (by decide)
  have hb := BlockSpec.of_expect (x := eExpect) e_run_meets eCodeAt (P := (· = s))
    (Q := fun s t ↦ eExpect.Holds s t) ?_ (fun _ _ _ hx ↦ hx)
  · obtain ⟨t, ht, hpc', hregs, hmem, hframe⟩ := hb s hpc rfl
    have hreg : ∀ p ∈ eExpect.regs, t.getReg p.1 = p.2.eval s := hregs
    have hm : ∀ i < 3, t.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * i)) = (eLimbE i).eval s :=
      fun i hi ↦ hmem (limb .x10 i, eLimbE i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    refine ⟨t, ⟨_, ht⟩, Or.inl ⟨hpc', fun r hr ↦ ?_, ⟨?_, ?_⟩⟩⟩
    · exact hreg (r, .reg r) (List.mem_map_of_mem (kept_of hr))
    · apply eq_of_limbs
      have h0 : t.getMem (s.getReg .x10) = (eLimbE 0).eval s := by simpa using hm 0 (by decide)
      have h1 : t.getMem (s.getReg .x10 + 8) = (eLimbE 1).eval s := hm 1 (by decide)
      have h2 : t.getMem (s.getReg .x10 + 16) = (eLimbE 2).eval s := hm 2 (by decide)
      rw [← Model.esquare_eq, limbs_eAt, limbs_eAt, h0, h1, h2]
      simp only [eLimbE, sqE'_eval, sqSumE_eval, opE_eval, Model.esquare]
      rfl
    · intro a hout
      apply hframe
      intro k hk
      simp only [eExpect, List.mem_map, List.mem_range] at hk
      obtain ⟨i, hi, rfl⟩ := hk
      rw [limb_eval]
      intro heq; apply hout; rw [heq]; addr_omega [hi, hO]
  · intro s' hs
    rw [hs, Oblig.all_iff]
    intro o ho
    simp only [eExpect, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at ho
    obtain ⟨r, hr, k, hk, rfl⟩ := ho
    show validAccess 8 ((limb r k).eval s) = true
    rw [limb_eval]
    rcases hr with rfl | rfl
    · valid_access hpre.out [hO, hk]
    · valid_access hpre.arg [hA, hk]

end Rv64Verifier.Proofs.Field.Square
