import Rv64Verifier.Proofs.Walk.R9B
import Rv64Verifier.Proofs.Walk.AtR10

/-!
# `walk`: `tables()` returned, the six tables in their buffer (R9)

From `AtR9`: the six `memcpy`s of the tables' 72 bytes into `Bb + 80 i` with the opcodes stored
between them, to `0x80002e40`, where `AtR10` holds (`r9`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-- The registers R9 keeps. -/
structure R9R (s u : MachineState) (Bb : Word) : Prop where
  x8 : u.getReg .x8 = 5
  x9 : u.getReg .x9 = 8
  x18 : u.getReg .x18 = Bb
  x19 : u.getReg .x19 = 1
  x20 : u.getReg .x20 = s.getReg .x2 - 512
  x21 : u.getReg .x21 = 6
  x22 : u.getReg .x22 = 2
  x27 : u.getReg .x27 = 6

theorem R9R.keeps {s u t : MachineState} {Bb : Word} {l : List Reg} (h : R9R s u Bb)
    (hk : ∀ r ∈ l, t.getReg r = u.getReg r)
    (hl : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x27] : List Reg), r ∈ l := by decide) :
    R9R s t Bb :=
  ⟨by rw [hk .x8 (hl _ (by decide))]; exact h.x8, by rw [hk .x9 (hl _ (by decide))]; exact h.x9,
    by rw [hk .x18 (hl _ (by decide))]; exact h.x18, by rw [hk .x19 (hl _ (by decide))]; exact h.x19,
    by rw [hk .x20 (hl _ (by decide))]; exact h.x20, by rw [hk .x21 (hl _ (by decide))]; exact h.x21,
    by rw [hk .x22 (hl _ (by decide))]; exact h.x22, by rw [hk .x27 (hl _ (by decide))]; exact h.x27⟩

theorem R9R.pres {s u t : MachineState} {Bb : Word} (h : R9R s u Bb) (hp : Preserves u t) : R9R s t Bb :=
  h.keeps hp

theorem tl_zero : tl 0 = xorT := by simp only [tl, tablesRust_zero, Option.getD_some]
theorem tl_one : tl 1 = mulT := by simp only [tl, tablesRust_one, Option.getD_some]
theorem tl_two : tl 2 = setT := by simp only [tl, tablesRust_two, Option.getD_some]
theorem tl_three : tl 3 = derefT := by simp only [tl, tablesRust_three, Option.getD_some]
theorem tl_four : tl 4 = jumpT := by simp only [tl, tablesRust_four, Option.getD_some]
theorem tl_five : tl 5 = kTable := by simp only [tl, tablesRust_five, Option.getD_some]

/-- `AtR10` from the six copies made, the five opcodes stored. -/
theorem atR10_of {OI : MachineState → Word → List (List Opening) → Prop} {s t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)}
    (M : M8 OI s t A k R Q B Bb W L) (c : Cp t B W Bb 6 5) (r : R9R s t Bb)
    (hpc : t.pc = 0x80002e40) : AtR10 OI s t A k R Q Bb := by
  obtain ⟨r1, r2, r3⟩ := M.m.bufR
  obtain ⟨q1, q2, q3, q4⟩ := M.m.bufQ
  obtain ⟨b1, b2, b3, b4⟩ := M.bb
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := M.m.spills
  have hl := rows_len M.m.rate.1
  refine {
    pc := hpc
    inv := M.m.inv
    proofPtr := M.m.proofPtr
    checked := M.m.checked
    ok := M.m.ok
    rate := M.m.rate
    tracks := M.m.tracks
    x8 := r.x8
    x9 := r.x9
    x18 := r.x18
    x20 := r.x20
    x21 := r.x21
    x27 := r.x27
    spills := ⟨p1, p2, p3, p4, p5, p6, p7, M.m.lb, p8⟩
    slots := ⟨M.m.cap, M.lens.1, M.lens.2, p9, M.m.ptr, M.slot⟩
    bufR := ⟨r1, r2, by omega⟩
    bufQ := ⟨q2, q1, by omega⟩
    bufB := ⟨by omega, b2, by omega⟩
    apartB := ⟨by simp only [Apart]; omega, by simp only [Apart]; omega⟩
    rows := ?_
    heights := M.m.heights
    tables := fun i tb hi ↦ ?_
    opcodes := c.op
    sep := fun i hi x hx ↦ ((c.tab i hi).2 x hx).2.2 }
  · apply List.ext_getElem (by simp [hl])
    intro i h1 _
    simp only [List.length_cons, List.length_nil] at h1
    have := M.m.rows i h1
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    interval_cases i <;> first | (rw [← this]; rfl) | simpa using this
  · have hi6 : i < 6 := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simpa [LayoutMirror.tablesRust] using this
    have e : tl i = tb := by simp only [tl, hi, Option.getD_some]
    rw [← e]; exact (c.tab i hi6).1

end Rv64Verifier.Proofs.Walk
