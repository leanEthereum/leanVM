/-
  LeanVM.Semantics.Executable

  The computable carrier of the fixed-image leanISA semantics: address search, the checked
  step, and the exact and fuel-bounded checkers, each proved equal to the reference.
-/

module

public import LeanVM.Semantics.Lemmas

/-!
# The executable carrier

Against leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`.
The reference semantics (`gLog?`, `MemImage.read`, `Program.fetch`, `execute`, `step`, `run`,
`ValidExecution`) is noncomputable and is what a reader audits. This module is its computable
carrier: one address search, `addressIndex`, replaces the chosen logarithm `gLog?`; the checked
step `stepChecked` is `executeWith` (the reference's six arms, `LeanVM.Semantics`) at the
carrier's reader; `checkWithinFuel` searches for the halting time within a budget and
`checkTrace` checks an announced one.

**What is trusted here is the statements of the equivalence theorems**, not the bodies:
`addressIndex_eq_gLog`, `readImage_eq_read`, `fetchInstruction_eq_fetch`,
`executeChecked_eq_execute`, `stepChecked_eq_step`, `runToHalt_eq_ok_iff`,
`checkBoundary_eq_true_iff`, `checkWithinFuel_eq_ok_iff`, `checkTrace_eq_true_iff`. Each says
that a carrier function agrees with the reference on every input (within the address bound
`κ < 64`, which every public entry point discharges from the caps `κ ≤ 32` and
`logSize ≤ 32`). The bodies may hold any speedup that keeps those theorems true.

**Hints.** Every carrier function takes an untrusted list of suggested cell indices. A hint
is used only after `gpow i = a` has been checked, and a miss falls back to the exhaustive
scan, so `addressIndex_eq_gLog` holds for every hint list: hints buy speed, never trust. The
scan carries `g ^ i` as a running product, one multiplication per candidate.

This is fixed-image validation of the reference ISA; it constructs no witness and says
nothing about a Rust executor's success domain.
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-! ## Address search -/

/-- Retain only hint indices inside the address space, without truncation or modular
reduction. -/
def hintIndices (κ : ℕ) (hints : List ℕ) : List (Fin (2 ^ κ)) :=
  hints.filterMap fun i ↦ if h : i < 2 ^ κ then some ⟨i, h⟩ else none

/-- The exhaustive fallback: from index `i` with `cur = g ^ i`, compare `cur` with `a` and
advance by one multiplication, for at most `fuel` candidates; `none` past the address space. -/
def scan (κ : ℕ) (a : K) : ℕ → ℕ → K → Option (Fin (2 ^ κ))
  | 0, _, _ => none
  | fuel + 1, i, cur =>
    if h : i < 2 ^ κ then
      if cur = a then some ⟨i, h⟩ else scan κ a fuel (i + 1) (g * cur)
    else none

/-- The index of address `a`: the first hint `i` with `g ^ i = a`, else the scan from index
`0` over the whole address space. -/
def addressIndex (κ : ℕ) (hints : List (Fin (2 ^ κ))) (a : K) : Option (Fin (2 ^ κ)) :=
  match hints.find? (fun i : Fin (2 ^ κ) ↦ decide (gpow i = a)) with
  | some i => some i
  | none => scan κ a (2 ^ κ) 0 1

/-- Read a fixed image through `addressIndex`. -/
def readImage {κ : ℕ} (image : MemImage κ) (hints : List ℕ) (a : K) : Option E :=
  (addressIndex κ (hintIndices κ hints) a).map image

/-- Fetch the typed instruction at a bounded program address; the hints are range-checked
again against the program size. -/
def fetchInstruction (prog : Program) (hints : List ℕ) (pc : K) : Option Instr :=
  (addressIndex prog.logSize (hintIndices prog.logSize hints) pc).map prog.code

/-! ## The checked step -/

/-- One instruction at the carrier's reader: the reference arms `executeWith`, nothing else. -/
def executeChecked {κ : ℕ} (image : MemImage κ) (hints : List ℕ) (r : Regs K) :
    Instr → Option (Regs K) :=
  executeWith (readImage image hints) r

/-- Fetch and check one step. Halting remains the responsibility of the loop. -/
def stepChecked {κ : ℕ} (prog : Program) (image : MemImage κ) (hints : List ℕ) (r : Regs K) :
    Option (Regs K) :=
  fetchInstruction prog hints r.pc >>= executeChecked image hints r

/-! ## Bounded checking -/

/-- Failure modes of bounded execution checking. Exhausting fuel makes no claim that a
longer run is invalid; the other cases identify failed semantic or public-boundary checks. -/
inductive CheckError
  | publicBoundary
  | invalidStep
  | finalFrame
  | fuelExhausted
  deriving DecidableEq, Repr

/-- Run to the sentinel in at most `fuel` transitions. The result counts only main-run
steps; no filler rows are appended. At zero fuel an already halted state
succeeds, while a nonterminal state reports exhaustion. -/
def runToHalt {κ : ℕ} (prog : Program) (image : MemImage κ) (hints : List ℕ) :
    ℕ → Regs K → Except CheckError ℕ
  | fuel, r =>
    if r.pc = prog.finalPc then
      if r.fp = 1 then .ok 0 else .error .finalFrame
    else match fuel with
      | 0 => .error .fuelExhausted
      | fuel + 1 => match stepChecked prog image hints r with
        | none => .error .invalidStep
        | some next => (runToHalt prog image hints fuel next).map (· + 1)

/-- The executable checks of the memory-size window and the two public words. -/
def checkBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Bool :=
  decide (minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem) &&
    decide (readImage t.image [] (gpow 0) = some input.word0 ∧
      readImage t.image [] (gpow 1) = some input.word1)

/-- Check public memory and find a valid exact main-run length within the supplied fuel.
The image is preserved verbatim; the returned count can be used in `Trace`. -/
def checkWithinFuel {κ : ℕ} (prog : Program) (input : PublicInput) (image : MemImage κ)
    (fuel : ℕ) (hints : List ℕ := []) : Except CheckError ℕ :=
  if checkBoundary input (⟨κ, image, 0⟩ : Trace prog) then
    runToHalt prog image hints fuel Regs.initial
  else .error .publicBoundary

/-- Validate a claimed exact-length execution, including its public memory and final frame:
the bounded search with the announced count as its budget must halt at exactly that count.
A successful witness generator must still establish that its output passes this check. -/
def checkTrace (prog : Program) (input : PublicInput) (t : Trace prog)
    (hints : List ℕ := []) : Bool :=
  decide (checkWithinFuel prog input t.image t.steps hints = .ok t.steps)

/-! ## Refinement to the reference semantics -/

/-- A hit of the scan is genuine: from `cur = g ^ i`, `some j` means `a = g ^ j`. -/
theorem scan_eq_some {κ : ℕ} {a : K} (fuel i : ℕ) {j : Fin (2 ^ κ)}
    (h : scan κ a fuel i (gpow i) = some j) : a = gpow j := by
  induction fuel generalizing i with
  | zero => exact nomatch h
  | succ fuel ih =>
    unfold scan at h
    by_cases hi : i < 2 ^ κ
    · rw [dite_eq_left hi] at h
      by_cases ha : gpow i = a
      · rw [ite_eq_left ha] at h
        cases h
        exact ha.symm
      · rw [ite_eq_right ha, ← gpow_succ] at h
        exact ih (i + 1) h
    · rw [dite_eq_right hi] at h
      exact nomatch h

/-- A miss of the scan is genuine: from `cur = g ^ i`, `none` means no index in the window
`[i, i + fuel)` addresses `a`. -/
theorem scan_eq_none {κ : ℕ} {a : K} (fuel i : ℕ) (h : scan κ a fuel i (gpow i) = none)
    (j : Fin (2 ^ κ)) (hij : i ≤ j) (hj : (j : ℕ) < i + fuel) : a ≠ gpow j := by
  induction fuel generalizing i with
  | zero => intro _; omega
  | succ fuel ih =>
    unfold scan at h
    by_cases hi : i < 2 ^ κ
    · rw [dite_eq_left hi] at h
      by_cases ha : gpow i = a
      · rw [ite_eq_left ha] at h
        exact nomatch h
      · rw [ite_eq_right ha, ← gpow_succ] at h
        intro haj
        rcases Nat.eq_or_lt_of_le hij with hij' | hij'
        · apply ha
          rw [hij']
          exact haj.symm
        · exact ih (i + 1) h hij' (by omega) haj
    · exact absurd (lt_of_le_of_lt hij j.isLt) hi

/-- The address search agrees with the reference logarithm for every hint list, whenever the
address representation is injective on the selected domain. -/
theorem addressIndex_eq_gLog {κ : ℕ} (hκ : κ < 64) (hints : List (Fin (2 ^ κ))) (a : K) :
    addressIndex κ hints a = gLog? κ a := by
  unfold addressIndex
  cases hf : hints.find? (fun i : Fin (2 ^ κ) ↦ decide (gpow i = a)) with
  | some i =>
    have hgi : decide (gpow (i : ℕ) = a) = true :=
      List.find?_some (p := fun j : Fin (2 ^ κ) ↦ decide (gpow j = a)) hf
    exact ((gLog?_spec hκ).mpr (of_decide_eq_true hgi).symm).symm
  | none =>
    have h1 : (1: K) = gpow 0 := (pow_zero g).symm
    cases hs : scan κ a (2 ^ κ) 0 1 with
    | some j =>
      rw [h1] at hs
      exact ((gLog?_spec hκ).mpr (scan_eq_some _ _ hs)).symm
    | none =>
      rw [h1] at hs
      symm
      rw [gLog?_eq_none_iff]
      intro j
      exact scan_eq_none _ _ hs j (Nat.zero_le _) (by have := j.isLt; omega)

/-- Executable reads preserve success, failure, and the exact word returned. -/
theorem readImage_eq_read {κ : ℕ} (hκ : κ < 64) (image : MemImage κ) (hints : List ℕ)
    (a : K) : readImage image hints a = image.read a := by
  rw [readImage, MemImage.read, addressIndex_eq_gLog hκ]

/-- Executable fetch agrees with typed reference fetch on every field address. -/
theorem fetchInstruction_eq_fetch (prog : Program) (hints : List ℕ) (pc : K) :
    fetchInstruction prog hints pc = prog.fetch pc := by
  have hκ : prog.logSize < 64 := lt_of_le_of_lt prog.logSize_le (by decide)
  rw [fetchInstruction, Program.fetch, addressIndex_eq_gLog hκ]

/-- The checked instruction is the reference instruction: the same arms, an equal reader. -/
theorem executeChecked_eq_execute {κ : ℕ} (hκ : κ < 64) (image : MemImage κ) (hints : List ℕ)
    (r : Regs K) : executeChecked image hints r = execute image r := by
  unfold executeChecked execute
  rw [show readImage image hints = image.read from funext (readImage_eq_read hκ image hints)]

/-- The checked program step has exactly the reference step's behavior. -/
theorem stepChecked_eq_step {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (hints : List ℕ) (r : Regs K) : stepChecked prog image hints r = step prog image r := by
  unfold stepChecked step
  rw [fetchInstruction_eq_fetch, executeChecked_eq_execute hκ]

/-- Every successful bounded check gives an exact reference execution of the reported
length, and every such execution within the budget is found. -/
theorem runToHalt_eq_ok_iff {κ : ℕ} (hκ : κ < 64) (prog : Program) (image : MemImage κ)
    (hints : List ℕ) (fuel n : ℕ) (r : Regs K) :
    runToHalt prog image hints fuel r = .ok n ↔
      n ≤ fuel ∧ run prog image n r = some (Regs.final prog) := by
  induction fuel generalizing r n with
  | zero =>
    rw [runToHalt]
    split_ifs with hpc hfp
    · have hr : r = Regs.final prog := by cases r; cases hpc; cases hfp; rfl
      subst r
      cases n <;> simp
    · have hr : r ≠ Regs.final prog := fun h ↦ hfp (congrArg Regs.fp h)
      cases n <;> simp [hr]
    · have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
      cases n <;> simp [hr]
  | succ fuel ih =>
    rw [runToHalt]
    split_ifs with hpc hfp
    · have hr : r = Regs.final prog := by cases r; cases hpc; cases hfp; rfl
      subst r
      cases n with
      | zero => simp
      | succ n => simp [run_succ_of_eq hpc]
    · cases n with
      | zero =>
        have hr : r ≠ Regs.final prog := fun h ↦ hfp (congrArg Regs.fp h)
        simp [hr]
      | succ n => simp [run_succ_of_eq hpc]
    · rw [stepChecked_eq_step hκ]
      cases hs : step prog image r with
      | none =>
        cases n with
        | zero =>
          have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
          simp [hr]
        | succ n => simp [run_succ_of_ne hpc, hs]
      | some next =>
        cases n with
        | zero =>
          have hr : r ≠ Regs.final prog := fun h ↦ hpc (congrArg Regs.pc h)
          cases he : runToHalt prog image hints fuel next <;> simp [he, Except.map, hr]
        | succ n =>
          have hm : (runToHalt prog image hints fuel next).map (· + 1) = .ok (n + 1) ↔
              runToHalt prog image hints fuel next = .ok n := by
            cases runToHalt prog image hints fuel next <;> simp [Except.map]
          rw [hm, ih]
          simp only [Nat.add_le_add_iff_right, run_succ_of_ne hpc, hs, Option.bind_eq_bind,
            Option.bind_some]

/-- Boundary checking is equivalent to the reference public boundary, including size caps. -/
theorem checkBoundary_eq_true_iff {prog : Program} (input : PublicInput) (t : Trace prog) :
    checkBoundary input t = true ↔ HasPublicBoundary input t := by
  simp only [checkBoundary, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hmin, hmax⟩, hwords⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hmax (by decide)
    rw [readImage_eq_read hκ, readImage_eq_read hκ] at hwords
    exact ⟨hmin, hmax, hwords⟩
  · rintro ⟨hmin, hmax, hwords⟩
    have hκ : t.κ < 64 := lt_of_le_of_lt hmax (by decide)
    rw [readImage_eq_read hκ, readImage_eq_read hκ]
    exact ⟨⟨hmin, hmax⟩, hwords⟩

/-- The public bounded checker accepts exactly valid executions whose length fits the
budget, for every hint list. This theorem also excludes oversized images and wrong public
words. -/
theorem checkWithinFuel_eq_ok_iff {κ : ℕ} (prog : Program) (input : PublicInput)
    (image : MemImage κ) (fuel n : ℕ) (hints : List ℕ) :
    checkWithinFuel prog input image fuel hints = .ok n ↔
      n ≤ fuel ∧ ValidExecution prog input ⟨κ, image, n⟩ := by
  unfold checkWithinFuel
  split_ifs with hb
  · have hb' := (checkBoundary_eq_true_iff input _).mp hb
    have hκ : κ < 64 := lt_of_le_of_lt hb'.2.1 (by decide)
    rw [runToHalt_eq_ok_iff hκ]
    simp only [ValidExecution, show HasPublicBoundary input (⟨κ, image, n⟩ : Trace prog)
      from hb', true_and]
  · have hb' : ¬ HasPublicBoundary input (⟨κ, image, n⟩ : Trace prog) := by
      intro h
      exact hb ((checkBoundary_eq_true_iff input _).mpr h)
    simp [ValidExecution, hb']

/-- Exact checking accepts precisely the valid reference executions, for every hint list.
The equivalence is unconditional: the checker itself rejects sizes outside the public
boundary. -/
theorem checkTrace_eq_true_iff (prog : Program) (input : PublicInput) (t : Trace prog)
    (hints : List ℕ) : checkTrace prog input t hints = true ↔ ValidExecution prog input t := by
  rw [checkTrace, decide_eq_true_iff, checkWithinFuel_eq_ok_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨le_rfl, h⟩⟩

end
end LeanVM.Semantics
