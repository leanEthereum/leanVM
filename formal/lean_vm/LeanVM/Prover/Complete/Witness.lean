/-
  LeanVM.Prover.Complete.Witness

  The honest prover's witness exists on every execution `LeanVM.Completeness` admits.
-/

module

public import LeanVM.Prover.Complete.End
public import LeanVM.Prover.Complete.Prefix
import LeanVM.Semantics.Lemmas
import LeanVM.Parameters.Generator
import LeanVM.Facts.Stack

/-!
# The witness exists

`witness?` (`Statement/Prover/Witness.lean`) runs the trace through the address indices
(`powIndex`, a hash map from the lane of `g^i` to `i`), counts each table's rows, builds the
layout and the chunks. On a valid execution within the cap, of pointer width at most `24`:

* the boundary holds (`boundaryOK_of_holds`);
* the indices are `addressIndex?` (`gLogIn_powIndex`, restored from the bus era's
  `Extraction/Run.lean`), so the run through them is `run` (`stepsFrom_eq`, restored from
  `Prover/WitnessRun.lean`), and its row counts are the execution's (`rowCounts_traceSteps`);
* the layout exists (`buildLayout`'s checks: the program's length a power of two, the sizes within
  their caps, the row counts below `2^24` by the pointer width), its stack within `2^30` words by the
  committed size (`Execution.committedSize_le_iff_stackLog_le`), and the chunks exist by the
  pointer width.

Hence `witnessExists : WitnessExists`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction LeanVM.Protocol.Verifier

/-! ## The address indices -/

/-- The lanes of the powers `g^j`, `j < 2^64 − 1`, are distinct. -/
theorem lane_gpow_inj {i j : ℕ} (hi : i < 2 ^ 64 - 1) (hj : j < 2 ^ 64 - 1)
    (h : (addressOfIndex i).lane = (addressOfIndex j).lane) : i = j :=
  gpow_injOn hi hj (K.lane_injective h)

/-- An index built from `g^i` past the indices whose lane is `k` reads `k` from where it started. -/
theorem powIndexFrom_of_not {k : UInt64} :
    ∀ (n i : ℕ) (m : Std.HashMap UInt64 ℕ),
      (∀ j, i ≤ j → j < i + n → (addressOfIndex j).lane ≠ k) →
      (powIndexFrom n i (addressOfIndex i) m)[k]? = m[k]?
  | 0, _, _, _ => rfl
  | n + 1, i, m, h => by
    rw [powIndexFrom, show addressOfIndex i * g = addressOfIndex (i + 1) from (pow_succ g i).symm,
      powIndexFrom_of_not n (i + 1) _ fun j hj hj' ↦ h j (by omega) (by omega),
      Std.HashMap.getElem?_insert]
    split
    · rename_i hk
      exact absurd (beq_iff_eq.mp hk) (h i le_rfl (by omega))
    · rfl

/-- An index built over `[i, i + n)`, below `2^64 − 1`, maps the lane of `g^j` to `j`. -/
theorem powIndexFrom_of_mem :
    ∀ (n i : ℕ) (m : Std.HashMap UInt64 ℕ) {j : ℕ}, i + n ≤ 2 ^ 64 - 1 → i ≤ j → j < i + n →
      (powIndexFrom n i (addressOfIndex i) m)[(addressOfIndex j).lane]? = some j
  | 0, _, _, _, _, h₁, h₂ => absurd h₂ (by omega)
  | n + 1, i, m, j, hn, h₁, h₂ => by
    rw [powIndexFrom, show addressOfIndex i * g = addressOfIndex (i + 1) from (pow_succ g i).symm]
    rcases h₁.lt_or_eq with h₁ | rfl
    · exact powIndexFrom_of_mem n (i + 1) _ (by omega) (by omega) (by omega)
    · rw [powIndexFrom_of_not n (i + 1) _ fun j' hj hj' hl ↦ by
          have := lane_gpow_inj (by omega) (by omega) hl; omega,
        Std.HashMap.getElem?_insert_self]

/-- **The index lookup is `addressIndex?`** on at most `2^63` words. -/
theorem gLogIn_powIndex {κ : ℕ} (hκ : κ < 64) (a : K) :
    gLogIn (powIndex κ) κ a = addressIndex? κ a := by
  have hb : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases h : ∃ i : Fin (2 ^ κ), a = addressOfIndex i
  · obtain ⟨i, rfl⟩ := h
    rw [(gLog?_spec hκ).mpr rfl, gLogIn, powIndex,
      show (1 : K) = addressOfIndex 0 from (pow_zero g).symm,
      powIndexFrom_of_mem _ 0 _ (by omega) (Nat.zero_le _) (by omega)]
    simp [i.isLt]
  · rw [gLog?_eq_none_iff.mpr fun i hi ↦ h ⟨i, hi⟩, gLogIn, powIndex,
      show (1 : K) = addressOfIndex 0 from (pow_zero g).symm,
      powIndexFrom_of_not _ 0 _ fun j _ hj hl ↦ h ⟨⟨j, by omega⟩, (K.lane_injective hl).symm⟩,
      Std.HashMap.getElem?_empty]

theorem logSize_lt (prog : LeanIsaProgram) : prog.logSize < 64 :=
  lt_of_le_of_lt prog.logSize_le (by decide)

/-- **The boundary holds** of an execution that holds the public input. -/
theorem boundaryOK_of_holds {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (h : HoldsPublicInput input t) : boundaryOK input t = true := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hκ : t.logMemorySize < 64 := by unfold maxLogMem at h2; omega
  have hlt : 1 < 2 ^ t.logMemorySize := Nat.one_lt_two_pow (by unfold minLogMem at h1; omega)
  unfold boundaryOK
  rw [dite_eq_left ⟨h1, h2⟩]
  rw [show addressOfIndex 0 = addressOfIndex
      ((⟨0, Nat.two_pow_pos t.logMemorySize⟩ : Fin (2 ^ t.logMemorySize)) : ℕ) from rfl,
    MemoryImage.read_gpow hκ] at h3
  rw [show addressOfIndex 1 = addressOfIndex
      ((⟨1, hlt⟩ : Fin (2 ^ t.logMemorySize)) : ℕ) from rfl, MemoryImage.read_gpow hκ] at h4
  simp only [Option.some.injEq] at h3 h4
  have h3' : t.memory 0 = input.word0 := by rw [← h3]; rfl
  simp [h3', h4]

/-! ## The run -/

/-- The step taken from the state `r`: its registers, the bytecode slot of its counter (`0` if
none) and the instruction fetched there. -/
noncomputable def stepOf (prog : LeanIsaProgram) (r : Registers K) : Step :=
  ⟨r.pc, r.fp, ((addressIndex? prog.logSize r.pc).map Fin.val).getD 0,
    (prog.fetch r.pc).getD (.setConstant 0 0)⟩

/-- The run through the indices is `run`, the steps recorded those of the states it passes
through. -/
theorem stepsFrom_eq {prog : LeanIsaProgram} {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) :
    ∀ (n : ℕ) (r : Registers K) (acc : Array Step),
      stepsFrom (powIndex κ) (powIndex prog.logSize) prog (Vector.ofFn prog.instructions) img n
          r acc =
        (run prog img n r).map fun rf ↦
          (acc ++ ((List.range n).map fun k ↦
            stepOf prog ((run prog img k r).getD Registers.initial)).toArray, rf)
  | 0, r, acc => by simp [stepsFrom]
  | n + 1, r, acc => by
    by_cases hr : r = Registers.final prog
    · simp [stepsFrom, hr, run_succ_of_eq rfl]
    · rw [stepsFrom, ite_eq_right hr, run_succ_of_ne_final hr, gLogIn_powIndex (logSize_lt prog)]
      have hread : readIn (powIndex κ) img = img.read := by
        funext a
        unfold readIn MemoryImage.read
        rw [gLogIn_powIndex hκ]
      cases hg : addressIndex? prog.logSize r.pc with
      | none =>
        simp [step, LeanIsaProgram.fetch, hg]
      | some i =>
        have hstep : step prog img r = execute img r (prog.instructions i) := by
          simp [step, LeanIsaProgram.fetch, hg]
        rw [hstep]
        have hci : (Vector.ofFn prog.instructions)[i] = prog.instructions i := by simp
        simp only [hread, hci]
        cases he : execute img r (prog.instructions i) with
        | none =>
          have he' : executeWith img.read r (prog.instructions i) = none := he
          simp [he']
        | some r' =>
          have he' : executeWith img.read r (prog.instructions i) = some r' := he
          simp only [he']
          rw [stepsFrom_eq hκ img n r' _]
          refine Option.map_congr fun rf _ ↦ ?_
          congr 1
          rw [List.range_succ_eq_map, List.map_cons, List.map_map]
          have h0 : stepOf prog ((run prog img 0 r).getD Registers.initial) =
              ⟨r.pc, r.fp, i.val, prog.instructions i⟩ := by
            simp [stepOf, hg, LeanIsaProgram.fetch]
          have hk : ∀ k, (run prog img (k + 1) r) = run prog img k r' := fun k ↦ by
            rw [run_succ_of_ne_final hr]
            simp [step, LeanIsaProgram.fetch, hg, execute, he']
          simp only [h0, Function.comp_def, hk]
          rw [List.toArray_cons, ← Array.append_assoc]
          rfl

/-- The steps of a trace: the steps taken from its first `t.stepCount` states. -/
noncomputable def traceSteps {prog : LeanIsaProgram} (t : Execution prog) : List Step :=
  (List.range t.stepCount).map fun k ↦
    stepOf prog ((run prog t.memory k Registers.initial).getD Registers.initial)

/-- **The run of a valid trace** through the indices: its steps. -/
theorem runSteps_eq {prog : LeanIsaProgram} (t : Execution prog) (hκ : t.logMemorySize < 64)
    (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    runSteps (powIndex t.logMemorySize) (powIndex prog.logSize) prog t =
      some (traceSteps t).toArray := by
  unfold runSteps
  rw [stepsFrom_eq hκ, hv]
  simp [traceSteps]

/-! ## The row counts -/

/-- The opcodes in the tables' order. -/
def tableOpcodes : List Opcode := [.xor, .mulNative, .setConstant, .deref, .jump, .keccak]

theorem opTableIdx_eq_iff (o : Opcode) {t : ℕ} (ht : t < nTables) :
    opTableIdx o = t ↔ o = tableOpcodes.getD t .xor := by
  have : nTables = 6 := by decide
  rw [this] at ht
  interval_cases t <;> cases o <;> decide

/-- The steps of a halting run count each opcode as `opcodeCountInRun` does. -/
theorem countP_steps {prog : LeanIsaProgram} {κ : ℕ} {L : MemoryImage κ} (op : Opcode) :
    ∀ (n : ℕ) (r : Registers K), run prog L n r = some (Registers.final prog) →
      ((List.range n).map fun k ↦ stepOf prog ((run prog L k r).getD Registers.initial)).countP
          (fun st ↦ decide (st.ins.opcode = op)) = opcodeCountInRun prog L op n r
  | 0, _, _ => rfl
  | n + 1, r, h => by
    have hr : r ≠ Registers.final prog := fun he ↦ by rw [run_succ_of_eq he] at h; cases h
    rw [run_succ_of_ne_final hr] at h
    obtain ⟨r', hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ins, hf, he⟩ := Option.bind_eq_some_iff.mp hs
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.countP_cons]
    have hk : ∀ k, (run prog L (k + 1) r) = run prog L k r' := fun k ↦ by
      rw [run_succ_of_ne_final hr, hs]; rfl
    simp only [Function.comp_def, hk]
    rw [countP_steps op n r' h, opcodeCountInRun]
    have hfs : step prog L r = some r' := hs
    simp only [hf, hfs]
    simp [stepOf, hf, add_comm]

/-- **The row counts of a valid trace are the execution's.** -/
theorem rowCounts_traceSteps {prog : LeanIsaProgram} {t : Execution prog}
    (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    rowCounts (traceSteps t).toArray = t.tableRows := by
  unfold rowCounts Execution.tableRows
  have : nTables = 6 := by decide
  rw [this]
  refine List.ext_getElem (by simp) fun t' h1 h2 ↦ ?_
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.countP_toArray]
  have ht' : t' < nTables := by rw [this]; omega
  have hiff := fun o ↦ opTableIdx_eq_iff o ht'
  rw [show (fun st : Step ↦ decide (opTableIdx st.ins.opcode = t')) =
      fun st ↦ decide (st.ins.opcode = tableOpcodes.getD t' .xor) from
    funext fun st ↦ by simp [hiff]]
  rw [traceSteps, countP_steps _ _ _ hv]
  interval_cases t' <;> rfl

/-! ## The witness -/

theorem log2Strict_two_pow (k : ℕ) : log2Strict (2 ^ k) = some k := by
  unfold log2Strict bitLength
  rw [ite_eq_left ⟨Nat.two_pow_pos k, by rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]⟩,
    ite_eq_right (Nat.two_pow_pos k).ne', Nat.log2_two_pow, Nat.add_sub_cancel]

theorem bitLength_lt {n w : ℕ} (h : bitLength n ≤ w) : n < 2 ^ w := by
  unfold bitLength at h
  split at h
  · subst_vars; exact Nat.two_pow_pos w
  · have := Nat.lt_log2_self (n := n)
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The witness exists** on every execution `LeanVM.Completeness` admits. -/
theorem witnessExists : WitnessExists := by
  intro prog input t hv hs hpw _
  have hκ : t.logMemorySize < 64 := by have := hv.1.2.1; unfold maxLogMem at this; omega
  have hsteps := runSteps_eq t hκ hv.2
  have hrows := rowCounts_traceSteps hv.2
  -- the pointer width bounds the program, the memory and the cycles
  have hpw' : pointerWidth t.logMemorySize prog.logSize t.tableRows.sum ≤ 24 := hpw
  unfold pointerWidth at hpw'
  have hcyc : t.tableRows.sum < 2 ^ 24 := bitLength_lt (by omega)
  have hrowle : ∀ r ∈ t.tableRows, r ≤ 2 ^ maxTableLog := fun r hr ↦ by
    have := List.le_sum_of_mem hr
    have : 2 ^ 24 ≤ 2 ^ maxTableLog := Nat.pow_le_pow_right (by norm_num) (by decide)
    omega
  -- the layout
  have hlen : (bytecodeWords prog).length = 2 ^ (prog.logSize + bytecodeSlotBits) := by
    rw [LeanVM.Rpm.bytecodeWords_length, pow_add, mul_comm]; rfl
  obtain ⟨layout, hl⟩ : ∃ layout, buildLayout (bytecodeWords prog) t.logMemorySize t.tableRows =
      some layout := by
    unfold buildLayout
    rw [hlen, log2Strict_two_pow]
    simp only
    rw [ite_eq_left]
    · exact ⟨_, rfl⟩
    · refine ⟨hv.1.1, hv.1.2.1, ?_, by omega, ?_, by simp [Execution.tableRows]; decide⟩
      · simpa using hrowle
      · have : prog.logSize ≤ 24 := by omega
        unfold Protocol.Verifier.maxLogBytecode; omega
  have hstack : layout.stackLog ≤ Whir.maxLogStack := by
    have := (Execution.committedSize_le_iff_stackLog_le t).mp hs
    unfold buildLayout at hl
    rw [hlen, log2Strict_two_pow] at hl
    simp only at hl
    split at hl
    · cases hl
      exact this
    · cases hl
  obtain ⟨chunks, hc⟩ : ∃ chunks,
      Chunks.new (pointerWidth t.logMemorySize prog.logSize t.tableRows.sum) = some chunks := by
    unfold Chunks.new
    rw [ite_eq_left ⟨by unfold pointerWidth; omega, hpw⟩]
    exact ⟨_, rfl⟩
  unfold witness?
  simp only [boundaryOK_of_holds hv.1, hsteps, hrows, hl, hstack, ↓reduceIte, hc]
  exact ⟨_, rfl⟩

end LeanVM.Prover

end
