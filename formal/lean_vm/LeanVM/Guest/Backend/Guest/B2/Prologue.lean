/-
  LeanVM.Guest.Backend.Guest.B2.Prologue

  The residual values' cells hold what the residual table says, at every frame where the run
  from the function's entry halts: each is written in the function's code before its first jump.
-/

module

public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.Backend.Guest.Facts
public import LeanVM.Guest.Backend.Guest.B2.Locs

/-!
# The residual facts

The residual table (`Residual.lean`) lists 72 values whose certificate cell the core semantics
does not justify against the back end's place: dead constants (`.konst c0 c1`) and pointers placed
at `fp[n]·g^e` (`.addr n e`). Each such cell is written by the function's code before its first
jump (`prologue`): a constant's by `SET` of exactly that constant, a pointer's by the `MUL` of
`fp[n]` with a cell an earlier `SET` gives `g^e`.

* `prologue_holds`: a run from a function's entry at `fp` that halts executes its prologue there,
  so each of its instructions `Holds` at `fp` (`Safe.fallThrough`, iterated);
* `resEntryOk_sound`: the decidable test of an entry against the prologue gives `ResFact`;
* `residual_ok`: the kernel's evaluation of the test over the table;
* `residualFacts : ResidualFacts`.
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The residual values' cells hold what the residual table says**, at every frame where the run
from the function's entry halts. -/
def ResidualFacts : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ) (j k : ℕ) (fp : K), 1 ≤ j → j < nFns →
    Safe guestProgram L k ⟨addressOfIndex (fnOf j).entryPc, fp⟩ →
    ∀ p ∈ resOf (coreOf j).name, ResFact L fp ((certOf j).locs.getD p.1.idx 0) p.2

/-! ## The prologue -/

/-- A function's code before its first jump. -/
def prologue (f : CompiledFunction) : List OffsetInstruction := f.code.takeWhile (fun i => !i.isJump)

section

variable {κ : ℕ} {L : MemoryImage κ}

/-- **A halting run from a function's entry executes its prologue** at that frame. -/
theorem prologue_holds {f : CompiledFunction} (hf : f ∈ Data.functions) {k : ℕ} {fp : K}
    (hs : Safe guestProgram L k ⟨addressOfIndex f.entryPc, fp⟩) :
    ∀ ins ∈ prologue f, ∃ pc, Holds L pc fp ins := by
  have hw := CompiledFunction.wellChunked_of_mem hf
  have hwalk : ∀ i ≤ (prologue f).length,
      (∀ m (hm : m < i) (hm' : m < (prologue f).length), Holds L (f.entryPc + m) fp (prologue f)[m]) ∧
        ∃ k', Safe guestProgram L k' ⟨addressOfIndex (f.entryPc + i), fp⟩ := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨fun _ hm => absurd hm (Nat.not_lt_zero _), k, hs⟩
    | succ i ih =>
      intro hi
      obtain ⟨hh, k', hk'⟩ := ih (by omega)
      have hiP : i < (prologue f).length := by omega
      obtain ⟨t, ht⟩ := List.takeWhile_prefix (l := f.code) (fun i => !i.isJump)
      have hlen := congrArg List.length ht
      rw [List.length_append] at hlen
      have hic : i < f.code.length := by
        have : i < (f.code.takeWhile fun i => !i.isJump).length := hiP
        omega
      have hin : i < f.instructionCount := CompiledFunction.length_code hw ▸ hic
      have hget : (prologue f)[i] = f.instructionAt i := by
        have h1 := CompiledFunction.getElem?_code hw hin
        have h2 : (f.code.takeWhile fun i => !i.isJump)[i]? = f.code[i]? := by
          conv_rhs => rw [← ht]
          rw [List.getElem?_append_left (show i < (f.code.takeWhile fun i => !i.isJump).length from hiP)]
        have h3 : (prologue f)[i]? = some (f.instructionAt i) := h2.trans h1
        rw [List.getElem?_eq_getElem hiP] at h3
        exact Option.some.inj h3
      have hj : (f.instructionAt i).isJump = false := by
        have := List.all_eq_true.mp (List.all_takeWhile (l := f.code) (p := fun i => !i.isJump))
          _ (hget ▸ List.getElem_mem hiP)
        simpa using this
      obtain ⟨k'', -, hH, hs'⟩ := hk'.fallThrough (guest_fetch hf hin) (guest_pc_lt hf hin) hj
      refine ⟨fun m hm hm' => ?_, k'', hs'⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
      · exact hh m hm hm'
      · rw [hget]; exact hH
  intro ins hins
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hins
  exact ⟨_, (hwalk _ le_rfl).1 m hm hm⟩

end

/-! ## The test -/

/-- A `SET` of cell `c` to `word k0 k1`. -/
def isSet (c k0 k1 : ℕ) : OffsetInstruction → Bool
  | .set o a b => o == c && a == k0 && b == k1
  | _ => false

/-- A `MUL` writing cell `c` with `fp[n]` times a cell the prologue `P` sets to `g^e`. -/
def mulFrom (P : List OffsetInstruction) (c n e : ℕ) : OffsetInstruction → Bool
  | .mul a b c' => c' == c &&
      ((a == n && P.any (isSet b (gpowLimbs e).1 (gpowLimbs e).2)) ||
        (b == n && P.any (isSet a (gpowLimbs e).1 (gpowLimbs e).2)))
  | _ => false

/-- **The test of a residual entry** of cell `c` against the prologue `P`. -/
def resEntryOk (P : List OffsetInstruction) (c : ℕ) : Res → Bool
  | .konst c0 c1 => P.any (isSet c c0 c1)
  | .addr n e => decide (e < 2 ^ 128) && P.any (mulFrom P c n e)

/-- The test of function `j`'s residual entries. -/
noncomputable def resOk (j : ℕ) (es : List (V × Res)) : Bool :=
  es.all fun p => resEntryOk (prologue (fnOf j)) ((certOf j).locs.getD p.1.idx 0) p.2

/-- The test of the residual table: each row names function `j` by its name, and its entries pass. -/
noncomputable def residualOk : Bool :=
  residual.all fun x => decide (1 ≤ x.2.1) && decide (x.2.1 < nFns) && (fnOf x.2.1).name == x.1 &&
    resOk x.2.1 x.2.2

section

variable {κ : ℕ} {L : MemoryImage κ} {fp : K}

theorem holds_set {pc c k0 k1 : ℕ} (h : Holds L pc fp (.set c k0 k1)) : wd L fp c = word k0 k1 :=
  wd_of_read h

theorem set_of_any {P : List OffsetInstruction} (hP : ∀ ins ∈ P, ∃ pc, Holds L pc fp ins)
    {c k0 k1 : ℕ} (h : P.any (isSet c k0 k1) = true) : wd L fp c = word k0 k1 := by
  obtain ⟨ins, hins, hs⟩ := List.any_eq_true.mp h
  obtain ⟨pc, hH⟩ := hP ins hins
  cases ins with
  | set o a b =>
      simp only [isSet, Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
      exact holds_set hH
  | _ => simp [isSet] at hs

/-- **A residual entry the prologue passes holds** at a frame where the prologue was executed. -/
theorem resEntryOk_sound {P : List OffsetInstruction} (hP : ∀ ins ∈ P, ∃ pc, Holds L pc fp ins)
    {c : ℕ} {r : Res} (h : resEntryOk P c r = true) : ResFact L fp c r := by
  cases r with
  | konst c0 c1 => exact set_of_any hP h
  | addr n e =>
      simp only [resEntryOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨he, h⟩ := h
      obtain ⟨ins, hins, hm⟩ := List.any_eq_true.mp h
      obtain ⟨pc, hH⟩ := hP ins hins
      have hg : word (gpowLimbs e).1 (gpowLimbs e).2 = ofK (addressOfIndex e) := word_gpow he
      cases ins with
      | mul a b c' =>
          simp only [mulFrom, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hm
          obtain ⟨rfl, ⟨rfl, hb⟩ | ⟨rfl, ha⟩⟩ := hm
          · obtain ⟨vA, vB, hA, hB, hC⟩ := hH
            have hb' := set_of_any hP hb
            simp only [ResFact]
            rw [wd_of_read hC, ← wd_of_read hA, ← wd_of_read hB, hb', hg]
          · obtain ⟨vA, vB, hA, hB, hC⟩ := hH
            have ha' := set_of_any hP ha
            simp only [ResFact]
            rw [wd_of_read hC, ← wd_of_read hA, ← wd_of_read hB, ha', hg, mul_comm]
      | _ => simp [mulFrom] at hm

end

end
end LeanVM.Guest.Backend.B2
