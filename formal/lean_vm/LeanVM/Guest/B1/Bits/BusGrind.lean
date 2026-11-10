/-
  LeanVM.Guest.B1.Bits.BusGrind

  `bus_grind_check__L{d}`: the bus's grind at a push depth of `MIN_LOG_MEM + d`, a call of
  `grind_check` returning `0`.
-/

module

public import LeanVM.Guest.B1.Bits.Grind

/-!
# `bus_grind_check`

`bus_grind_check(word, tabs, d)` (`lean_ethereum.py`) calls `grind_check(word, tabs,
BUS_GRIND_BITS[MIN_LOG_MEM + d])` and returns `0`; one specialization per `d < 18`, the push
depths from `minLogMem` below `SIZE_BITS`. Its bits are `busGrindingBits (minLogMem + d)`, which
is `13 + d` (`busGrindBits_eq`), a deployed `grind_check` (`busGrindBits_mem`).

`bus_grind_check_found`: every specialization is `bgBody d` (a kernel check each).
`bus_grind_check_holds`: its relation is its meaning (`MeaningBusGrindCheck`), from
`grind_check_holds`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The deployed `bus_grind_check__L{d}`. -/
def busGrindDeployed : List ℕ := List.range 18

/-- `bus_grind_check__L{d}` (a table: `toString`'s body is not exposed to a `module`'s kernel). -/
def busGrindName (d : ℕ) : String :=
  ["bus_grind_check__L0", "bus_grind_check__L1", "bus_grind_check__L2", "bus_grind_check__L3", "bus_grind_check__L4", "bus_grind_check__L5", "bus_grind_check__L6", "bus_grind_check__L7", "bus_grind_check__L8", "bus_grind_check__L9", "bus_grind_check__L10", "bus_grind_check__L11", "bus_grind_check__L12", "bus_grind_check__L13", "bus_grind_check__L14", "bus_grind_check__L15", "bus_grind_check__L16", "bus_grind_check__L17"].getD d ""

/-- `BUS_GRIND_BITS[MIN_LOG_MEM + d]`: the protocol's grind at push depth `minLogMem + d`. -/
def busGrindBits (d : ℕ) : ℕ := busGrindingBits (minLogMem + d)

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

theorem busGrindBits_eq (d : ℕ) : busGrindBits d = 13 + d := by
  rw [busGrindBits, busGrindingBits_of (by simp only [minLogMem]; omega)]
  simp only [minLogMem]
  omega

theorem busGrindBits_mem : ∀ d ∈ busGrindDeployed, busGrindBits d ∈ grindBitsDeployed := by
  intro d hd
  rw [busGrindBits_eq]
  simp only [busGrindDeployed, List.mem_range] at hd
  interval_cases d <;> decide

/-- `bus_grind_check__L{d}`'s expansion: the grind, then `0` returned. -/
def bgBody (d : ℕ) : List Stmt :=
  [.call (grindCheckName (busGrindBits d)) [.n 0, .n 1] [], .atom (.const (.n 2) (word 0 0)),
    .ret [.n 2]]

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_0 : coreProgram.find? (busGrindName 0) = some Data.core312 ∧
    Data.core312.params = [.n 0, .n 1] ∧ Data.core312.body = bgBody 0 :=
  ⟨Program.find?_of_indexOf? (j := 312) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_1 : coreProgram.find? (busGrindName 1) = some Data.core313 ∧
    Data.core313.params = [.n 0, .n 1] ∧ Data.core313.body = bgBody 1 :=
  ⟨Program.find?_of_indexOf? (j := 313) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_2 : coreProgram.find? (busGrindName 2) = some Data.core314 ∧
    Data.core314.params = [.n 0, .n 1] ∧ Data.core314.body = bgBody 2 :=
  ⟨Program.find?_of_indexOf? (j := 314) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_3 : coreProgram.find? (busGrindName 3) = some Data.core315 ∧
    Data.core315.params = [.n 0, .n 1] ∧ Data.core315.body = bgBody 3 :=
  ⟨Program.find?_of_indexOf? (j := 315) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_4 : coreProgram.find? (busGrindName 4) = some Data.core316 ∧
    Data.core316.params = [.n 0, .n 1] ∧ Data.core316.body = bgBody 4 :=
  ⟨Program.find?_of_indexOf? (j := 316) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_5 : coreProgram.find? (busGrindName 5) = some Data.core317 ∧
    Data.core317.params = [.n 0, .n 1] ∧ Data.core317.body = bgBody 5 :=
  ⟨Program.find?_of_indexOf? (j := 317) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_6 : coreProgram.find? (busGrindName 6) = some Data.core318 ∧
    Data.core318.params = [.n 0, .n 1] ∧ Data.core318.body = bgBody 6 :=
  ⟨Program.find?_of_indexOf? (j := 318) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_7 : coreProgram.find? (busGrindName 7) = some Data.core319 ∧
    Data.core319.params = [.n 0, .n 1] ∧ Data.core319.body = bgBody 7 :=
  ⟨Program.find?_of_indexOf? (j := 319) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_8 : coreProgram.find? (busGrindName 8) = some Data.core320 ∧
    Data.core320.params = [.n 0, .n 1] ∧ Data.core320.body = bgBody 8 :=
  ⟨Program.find?_of_indexOf? (j := 320) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_9 : coreProgram.find? (busGrindName 9) = some Data.core321 ∧
    Data.core321.params = [.n 0, .n 1] ∧ Data.core321.body = bgBody 9 :=
  ⟨Program.find?_of_indexOf? (j := 321) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_10 : coreProgram.find? (busGrindName 10) = some Data.core322 ∧
    Data.core322.params = [.n 0, .n 1] ∧ Data.core322.body = bgBody 10 :=
  ⟨Program.find?_of_indexOf? (j := 322) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_11 : coreProgram.find? (busGrindName 11) = some Data.core323 ∧
    Data.core323.params = [.n 0, .n 1] ∧ Data.core323.body = bgBody 11 :=
  ⟨Program.find?_of_indexOf? (j := 323) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_12 : coreProgram.find? (busGrindName 12) = some Data.core324 ∧
    Data.core324.params = [.n 0, .n 1] ∧ Data.core324.body = bgBody 12 :=
  ⟨Program.find?_of_indexOf? (j := 324) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_13 : coreProgram.find? (busGrindName 13) = some Data.core325 ∧
    Data.core325.params = [.n 0, .n 1] ∧ Data.core325.body = bgBody 13 :=
  ⟨Program.find?_of_indexOf? (j := 325) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_14 : coreProgram.find? (busGrindName 14) = some Data.core326 ∧
    Data.core326.params = [.n 0, .n 1] ∧ Data.core326.body = bgBody 14 :=
  ⟨Program.find?_of_indexOf? (j := 326) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_15 : coreProgram.find? (busGrindName 15) = some Data.core327 ∧
    Data.core327.params = [.n 0, .n 1] ∧ Data.core327.body = bgBody 15 :=
  ⟨Program.find?_of_indexOf? (j := 327) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_16 : coreProgram.find? (busGrindName 16) = some Data.core328 ∧
    Data.core328.params = [.n 0, .n 1] ∧ Data.core328.body = bgBody 16 :=
  ⟨Program.find?_of_indexOf? (j := 328) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem bus_grind_check_found_17 : coreProgram.find? (busGrindName 17) = some Data.core329 ∧
    Data.core329.params = [.n 0, .n 1] ∧ Data.core329.body = bgBody 17 :=
  ⟨Program.find?_of_indexOf? (j := 329) (by decide +kernel) rfl, rfl,
    stmtsEqb_sound (by decide +kernel)⟩

/-- **Every deployed `bus_grind_check` is the template.** -/
theorem bus_grind_check_found : ∀ d ∈ busGrindDeployed, ∃ fn : Fn,
    coreProgram.find? (busGrindName d) = some fn ∧ fn.params = [.n 0, .n 1] ∧
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
  · exact ⟨_, bus_grind_check_found_14⟩
  · exact ⟨_, bus_grind_check_found_15⟩
  · exact ⟨_, bus_grind_check_found_16⟩
  · exact ⟨_, bus_grind_check_found_17⟩

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
  have hg := grind_check_holds _ (busGrindBits_mem d hd) hκ h11 L w tabs ht []
  rw [rel_iff_sem hf, hpar, hbody]
  simp only [bgBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    MeaningBusGrindCheck]
  constructor
  · rintro ⟨σ, hp, hc, ⟨h2, hr⟩⟩
    simp only [List.cons.injEq, and_true] at hp
    rw [hp.1, hp.2, hg] at hc
    refine ⟨?_, hc.2⟩
    rw [← hr, h2, word_zero]
  · rintro ⟨rfl, hlow⟩
    refine ⟨fun v => [w, tabs, 0].getD v.idx 0, rfl, hg.mpr ⟨rfl, hlow⟩, ?_, ?_⟩
    · show (0 : E) = word 0 0
      rw [word_zero]
    · rfl

end
end LeanVM.Guest.B1
