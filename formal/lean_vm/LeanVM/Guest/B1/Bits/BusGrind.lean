/-
  LeanVM.Guest.B1.Bits.BusGrind

  `bus_grind_check__L{d}`: the bus's grind at a push depth of `BUS_MIN_MU + d`, `grind_check`
  inlined, returning `0`.
-/

module

public import LeanVM.Guest.B1.Bits.Grind
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L0»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L1»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L10»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L11»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L12»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L13»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L2»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L3»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L4»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L5»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L6»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L7»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L8»
import LeanVM.Guest.Data.ValNames.«bus_grind_check__L9»

/-!
# `bus_grind_check`

`bus_grind_check(word, tabs, d)` (`lean_ethereum.py`) inlines `grind_check(word, tabs,
BUS_GRIND_BITS[BUS_MIN_MU + d])` and returns `0`; one specialization per `d < 14`, the push
depths from `busMinMu` below `SIZE_BITS`. Its bits are `busGrindingBits (busMinMu + d)`, which
is `17 + d` (`busGrindBits_eq`), a deployed `grind_check` (`busGrindBits_mem`).

`bus_grind_check_found`: every specialization is `bgBody d` (a kernel check each), `gcPre` then
`0` returned. `bus_grind_check_holds`: its relation is its meaning (`MeaningBusGrindCheck`), from
`gc_sound` and `gcPre_complete_of`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The deployed `bus_grind_check__L{d}`. -/
def busGrindDeployed : List ℕ := List.range 14

/-- `bus_grind_check__L{d}` (a table: `toString`'s body is not exposed to a `module`'s kernel). -/
def busGrindName (d : ℕ) : String :=
  ["bus_grind_check__L0", "bus_grind_check__L1", "bus_grind_check__L2", "bus_grind_check__L3", "bus_grind_check__L4", "bus_grind_check__L5", "bus_grind_check__L6", "bus_grind_check__L7", "bus_grind_check__L8", "bus_grind_check__L9", "bus_grind_check__L10", "bus_grind_check__L11", "bus_grind_check__L12", "bus_grind_check__L13"].getD d ""

/-- `BUS_MIN_MU`: the least push depth of an execution of the guest's bytecode, where the bus
grind's arms start (`placeholders.rs`). -/
abbrev busMinMu : ℕ := 20

/-- `BUS_GRIND_BITS[BUS_MIN_MU + d]`: the protocol's grind at push depth `busMinMu + d`. -/
def busGrindBits (d : ℕ) : ℕ := busGrindingBits (busMinMu + d)

/-- From a depth of `4`, a bus grind is three bits short of it. -/
theorem busGrindingBits_of {mu : ℕ} (h : 4 ≤ mu) : busGrindingBits mu = mu - 3 := by
  unfold busGrindingBits grindingBits securityBits
  have h1 : 1 ≤ 2 ^ (mu - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ mu = 2 * 2 ^ (mu - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [ite_eq_right (by omega)]
  have hlt : Nat.log2 (2 ^ mu - 1) < mu := (Nat.log2_lt (by omega)).2 (by omega)
  have hle : mu - 1 ≤ Nat.log2 (2 ^ mu - 1) := (Nat.le_log2 (by omega)).2 (by omega)
  omega

theorem busGrindBits_eq (d : ℕ) : busGrindBits d = 17 + d := by
  rw [busGrindBits, busGrindingBits_of (by simp only [busMinMu]; omega)]
  simp only [busMinMu]
  omega

theorem busGrindBits_mem : ∀ d ∈ busGrindDeployed, busGrindBits d ∈ grindBitsDeployed := by
  intro d hd
  rw [busGrindBits_eq]
  simp only [busGrindDeployed, List.mem_range] at hd
  interval_cases d <;> decide

/-- The value `bus_grind_check__L{d}` returns, past the grind's. -/
def bgZero (d : ℕ) : ℕ := gcLen (busGrindBits d)

/-- `bus_grind_check__L{d}`'s statements before its return: the grind, then the `0` it returns. -/
def bgPre (d : ℕ) : List Stmt := gcPre (busGrindBits d) ++ [.atom (.const (.n (bgZero d)) (word 0 0))]

/-- `bus_grind_check__L{d}`'s expansion: the grind, then `0` returned. -/
def bgBody (d : ℕ) : List Stmt := bgPre d ++ [.ret [.n (bgZero d)]]

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_0 : coreProgram.find? (busGrindName 0) = some
    fn% «bus_grind_check__L0» ∧
    (fn% «bus_grind_check__L0»).params = [.n (val% «bus_grind_check__L0» "word"), .n (val% «bus_grind_check__L0» "tabs")] ∧ (fn% «bus_grind_check__L0»).body = bgBody 0
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L0») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_1 : coreProgram.find? (busGrindName 1) = some
    fn% «bus_grind_check__L1» ∧
    (fn% «bus_grind_check__L1»).params = [.n (val% «bus_grind_check__L1» "word"), .n (val% «bus_grind_check__L1» "tabs")] ∧ (fn% «bus_grind_check__L1»).body = bgBody 1
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L1») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_2 : coreProgram.find? (busGrindName 2) = some
    fn% «bus_grind_check__L2» ∧
    (fn% «bus_grind_check__L2»).params = [.n (val% «bus_grind_check__L2» "word"), .n (val% «bus_grind_check__L2» "tabs")] ∧ (fn% «bus_grind_check__L2»).body = bgBody 2
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L2») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_3 : coreProgram.find? (busGrindName 3) = some
    fn% «bus_grind_check__L3» ∧
    (fn% «bus_grind_check__L3»).params = [.n (val% «bus_grind_check__L3» "word"), .n (val% «bus_grind_check__L3» "tabs")] ∧ (fn% «bus_grind_check__L3»).body = bgBody 3
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L3») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_4 : coreProgram.find? (busGrindName 4) = some
    fn% «bus_grind_check__L4» ∧
    (fn% «bus_grind_check__L4»).params = [.n (val% «bus_grind_check__L4» "word"), .n (val% «bus_grind_check__L4» "tabs")] ∧ (fn% «bus_grind_check__L4»).body = bgBody 4
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L4») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_5 : coreProgram.find? (busGrindName 5) = some
    fn% «bus_grind_check__L5» ∧
    (fn% «bus_grind_check__L5»).params = [.n (val% «bus_grind_check__L5» "word"), .n (val% «bus_grind_check__L5» "tabs")] ∧ (fn% «bus_grind_check__L5»).body = bgBody 5
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L5») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_6 : coreProgram.find? (busGrindName 6) = some
    fn% «bus_grind_check__L6» ∧
    (fn% «bus_grind_check__L6»).params = [.n (val% «bus_grind_check__L6» "word"), .n (val% «bus_grind_check__L6» "tabs")] ∧ (fn% «bus_grind_check__L6»).body = bgBody 6
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L6») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_7 : coreProgram.find? (busGrindName 7) = some
    fn% «bus_grind_check__L7» ∧
    (fn% «bus_grind_check__L7»).params = [.n (val% «bus_grind_check__L7» "word"), .n (val% «bus_grind_check__L7» "tabs")] ∧ (fn% «bus_grind_check__L7»).body = bgBody 7
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L7») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_8 : coreProgram.find? (busGrindName 8) = some
    fn% «bus_grind_check__L8» ∧
    (fn% «bus_grind_check__L8»).params = [.n (val% «bus_grind_check__L8» "word"), .n (val% «bus_grind_check__L8» "tabs")] ∧ (fn% «bus_grind_check__L8»).body = bgBody 8
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L8») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_9 : coreProgram.find? (busGrindName 9) = some
    fn% «bus_grind_check__L9» ∧
    (fn% «bus_grind_check__L9»).params = [.n (val% «bus_grind_check__L9» "word"), .n (val% «bus_grind_check__L9» "tabs")] ∧ (fn% «bus_grind_check__L9»).body = bgBody 9
        :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L9») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_10 : coreProgram.find? (busGrindName 10) = some
    fn% «bus_grind_check__L10» ∧
    (fn% «bus_grind_check__L10»).params = [.n (val% «bus_grind_check__L10» "word"), .n (val% «bus_grind_check__L10» "tabs")] ∧ (fn% «bus_grind_check__L10»).body = bgBody
        10 :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L10») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_11 : coreProgram.find? (busGrindName 11) = some
    fn% «bus_grind_check__L11» ∧
    (fn% «bus_grind_check__L11»).params = [.n (val% «bus_grind_check__L11» "word"), .n (val% «bus_grind_check__L11» "tabs")] ∧ (fn% «bus_grind_check__L11»).body = bgBody
        11 :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L11») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_12 : coreProgram.find? (busGrindName 12) = some
    fn% «bus_grind_check__L12» ∧
    (fn% «bus_grind_check__L12»).params = [.n (val% «bus_grind_check__L12» "word"), .n (val% «bus_grind_check__L12» "tabs")] ∧ (fn% «bus_grind_check__L12»).body = bgBody
        12 :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L12») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_13 : coreProgram.find? (busGrindName 13) = some
    fn% «bus_grind_check__L13» ∧
    (fn% «bus_grind_check__L13»).params = [.n (val% «bus_grind_check__L13» "word"), .n (val% «bus_grind_check__L13» "tabs")] ∧ (fn% «bus_grind_check__L13»).body = bgBody
        13 :=
  ⟨coreProgram_find?_at (j := idx% «bus_grind_check__L13») rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed `bus_grind_check` is the template.** -/
theorem bus_grind_check_found : ∀ d ∈ busGrindDeployed, ∃ fn : Fn,
    coreProgram.find? (busGrindName d) = some fn ∧ fn.params = [.n (valf% «bus_grind_check» "word"), .n (valf% «bus_grind_check» "tabs")] ∧
      fn.body = bgBody d := by
  intro d hd
  simp only [busGrindDeployed, List.mem_range] at hd
  interval_cases d
  · exact ⟨_, bus_grind_check_found_0⟩
  · exact ⟨_, bus_grind_check_found_1⟩
  · exact ⟨_, bus_grind_check_found_2⟩
  · exact ⟨_, bus_grind_check_found_3⟩
  · exact ⟨_, bus_grind_check_found_4⟩
  · exact ⟨_, bus_grind_check_found_5⟩
  · exact ⟨_, bus_grind_check_found_6⟩
  · exact ⟨_, bus_grind_check_found_7⟩
  · exact ⟨_, bus_grind_check_found_8⟩
  · exact ⟨_, bus_grind_check_found_9⟩
  · exact ⟨_, bus_grind_check_found_10⟩
  · exact ⟨_, bus_grind_check_found_11⟩
  · exact ⟨_, bus_grind_check_found_12⟩
  · exact ⟨_, bus_grind_check_found_13⟩

/-- **`bus_grind_check__L{d}`**: the word's low limb passes the proof of work of
`busGrindBits d` bits; it returns `0`. -/
def MeaningBusGrindCheck (d : ℕ) : List E → List E → Prop
  | [w, _], rets => rets = [0] ∧ (w.limb 0).lane.toNat % 2 ^ busGrindBits d = 0
  | _, _ => False

/-- `bus_grind_check__L{d}`'s core IR is its meaning, on a memory image of `2^κ` words,
`11 ≤ κ ≤ 32`, whose `tabs` holds the bit windows. -/
def bus_grind_check_Spec (d : ℕ) : Prop :=
  ∀ {κ : ℕ}, κ ≤ 32 → winTabBits ≤ κ → ∀ (L : MemoryImage κ) (w tabs : E), WinTabs L.read tabs →
    ∀ rets : List E, coreProgram.Rel L.read (busGrindName d) [w, tabs] rets ↔
      MeaningBusGrindCheck d [w, tabs] rets

/-- **Every deployed `bus_grind_check` is its meaning.** -/
theorem bus_grind_check_holds : ∀ d ∈ busGrindDeployed, bus_grind_check_Spec d := by
  intro d hd κ hκ h11 L w tabs ht rets
  obtain ⟨fn, hf, hpar, hbody⟩ := bus_grind_check_found d hd
  have hb := busGrindBits_mem d hd
  rw [rel_iff_sem hf, hpar, hbody, bgBody, bgPre]
  simp only [List.append_assoc, List.cons_append, List.nil_append, holdsList_append,
    List.map_cons, List.map_nil, MeaningBusGrindCheck]
  constructor
  · rintro ⟨σ, hp, h⟩
    obtain ⟨hh, hi, htl, hrest⟩ := (holds_gcPre _ _ _).mp h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hrest
    obtain ⟨h2, hr⟩ := hrest
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨h0, h1⟩ := hp
    refine ⟨by rw [← hr, h2, word_zero], ?_⟩
    rw [← h0]
    exact gc_sound hκ h11 L (gc_shape _ hb) (by rw [h1]; exact ht) hh hi htl
  · rintro ⟨rfl, hlow⟩
    have h11' : 11 ≤ κ := h11
    refine ⟨fun v => gcVals L.read (busGrindBits d) w tabs v.idx, ?_, ?_⟩
    · show [gcVals L.read (busGrindBits d) w tabs 0, gcVals L.read (busGrindBits d) w tabs 1] = [w, tabs]
      unfold gcVals
      simp
    · refine gcPre_complete_of (fun _ hv _ he => rc_complete hκ L hv (by omega) he) hb ht hlow
        (fun k _ => rfl) ?_
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
      refine ⟨?_, ?_⟩
      · show gcVals L.read (busGrindBits d) w tabs (bgZero d) = word 0 0
        rw [bgZero, gcVals_len, word_zero]
      · show [gcVals L.read (busGrindBits d) w tabs (bgZero d)] = [0]
        rw [bgZero, gcVals_len]

end
end LeanVM.Guest.B1
