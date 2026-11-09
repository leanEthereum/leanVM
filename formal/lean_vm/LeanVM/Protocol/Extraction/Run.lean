/-
  LeanVM.Protocol.Extraction.Run

  The extractor's computable halting search (`LeanVM/Protocol/Extraction/Extractor.lean`, §7) against the
  specification: its addresses, step and run are the specification's, it finds the specification's
  halting run whenever that run fits the cap, and what it returns for any stack is a valid
  execution. A halting run never repeats a state.
-/

module

public import LeanVM.Protocol.Extraction.Defs
public import LeanVM.Semantics.Lemmas

/-!
# The halting search, proved

* `gLogIn_powIndex`, `gLogC_eq`: on at most `2^63` words (`κ < 64`), the index lookup is `addressIndex?`
  (the powers `g^i`, `i < 2^κ < 2^64 − 1`, are distinct, and so are their lanes).
* `stepIn_powIndex`, `stepC_eq`, `runC_eq`: the step and the run through the indices are `step`
  and `run`.
* `haltLoop_eq_some_iff`: the search from `r` returns `m` exactly when the run reaches the final
  state from `r` in `m − n ≤ fuel` steps.
* `run_final_unique`: a run reaches the final state after at most one number of steps (it halts
  there). `haltingRun_eq_some_iff`: so `haltingRun` returns that number.
* **`haltingRunC_eq_haltingRun`**: when every halting run fits the cap, the capped search is
  `haltingRun`. `haltingRunC_sound`: what the capped search returns, `haltingRun` returns.
* `boundaryOK_iff`: the Boolean boundary is `HoldsPublicInput`. **`candidateExecution_valid`**,
  **`candidateExecutionIn_valid`**: what a stack's execution is, is a valid execution, for every
  stack and every layout.
* `run_injective`: a halting run never repeats a state (from the repeat it would reach the final
  state before its end, and halt there).

The index is reasoned about through Lean core's `Std.HashMap` lemmas (`getElem?_insert`,
`getElem?_insert_self`, `getElem?_empty`; Lean FRO, Apache-2.0).
-/

namespace LeanVM.Protocol.Halting

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Extraction

@[expose] public section

/-! ## 1. Addresses -/

/-- The lanes of the powers `g^j`, `j < 2^64 − 1`, are distinct. -/
theorem lane_gpow_inj {i j : ℕ} (hi : i < 2 ^ 64 - 1) (hj : j < 2 ^ 64 - 1)
    (h : (addressOfIndex i).lane = (addressOfIndex j).lane) : i = j :=
  gpow_injOn hi hj (K.lane_injective h)

/-- An index built from `g^i` past the indices whose lane is `k` reads `k` from where it started. -/
theorem powIndexFrom_of_not {k : UInt64} :
    ∀ (n i : ℕ) (m : Std.HashMap UInt64 ℕ), (∀ j, i ≤ j → j < i + n → (addressOfIndex j).lane ≠ k) →
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
theorem gLogIn_powIndex {κ : ℕ} (hκ : κ < 64) (a : K) : gLogIn (powIndex κ) κ a = addressIndex? κ a := by
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

/-! ## 2. The step and the run -/

/-- The bytecode's address space is within `addressIndex?`'s. -/
theorem logSize_lt (prog : LeanIsaProgram) : prog.logSize < 64 :=
  lt_of_le_of_lt prog.logSize_le (by decide)

/-- **The step through the indices is `step`.** -/
theorem stepIn_powIndex {prog : LeanIsaProgram} {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) (r : Registers K) :
    stepIn (powIndex κ) (powIndex prog.logSize) prog L r = step prog L r := by
  have hread : (fun a ↦ (gLogIn (powIndex κ) κ a).map L) = L.read :=
    funext fun a ↦ by rw [gLogIn_powIndex hκ]; rfl
  rw [stepIn, hread, gLogIn_powIndex (logSize_lt prog)]
  rfl

/-! ## 3. The search -/

section Search

variable {prog : LeanIsaProgram} {κ : ℕ} {L : MemoryImage κ}

/-- From the final state, a run reaches the final state only in zero steps. -/
theorem run_final_eq_iff {d : ℕ} :
    run prog L d (Registers.final prog) = some (Registers.final prog) ↔ d = 0 := by
  rcases d with _ | d
  · simp
  · simp [run_succ_of_eq rfl]

/-- **The search** from `r`, after `n` steps and with `fuel` more, returns `m` exactly when the run
reaches the final state from `r` in `m − n ≤ fuel` steps. -/
theorem haltLoop_eq_some_iff {memIdx codeIdx : Std.HashMap UInt64 ℕ}
    (hS : ∀ r, stepIn memIdx codeIdx prog L r = step prog L r) :
    ∀ (fuel n : ℕ) (r : Registers K) (m : ℕ),
      haltLoop memIdx codeIdx prog L fuel n r = some m ↔
        ∃ d, m = n + d ∧ d ≤ fuel ∧ run prog L d r = some (Registers.final prog)
  | 0, n, r, m => by
    rw [haltLoop]
    by_cases hr : r = Registers.final prog
    · simp only [hr, ↓reduceIte]
      constructor
      · intro h
        exact ⟨0, (Option.some.inj h).symm, le_rfl, rfl⟩
      · rintro ⟨d, rfl, hd, -⟩
        obtain rfl : d = 0 := by omega
        rfl
    · simp only [hr, ↓reduceIte]
      refine ⟨fun h ↦ by simp at h, ?_⟩
      rintro ⟨d, -, hd, h⟩
      obtain rfl : d = 0 := by omega
      exact absurd (Option.some.inj h) hr
  | fuel + 1, n, r, m => by
    rw [haltLoop]
    by_cases hr : r = Registers.final prog
    · simp only [hr, ↓reduceIte]
      subst hr
      constructor
      · intro h
        exact ⟨0, (Option.some.inj h).symm, Nat.zero_le _, rfl⟩
      · rintro ⟨d, rfl, -, h⟩
        rw [run_final_eq_iff.mp h]
        rfl
    · simp only [hr, ↓reduceIte, hS]
      have hrun : ∀ d, run prog L (d + 1) r = step prog L r >>= run prog L d :=
        run_succ_of_ne_final hr
      rcases hs : step prog L r with _ | r'
      · refine ⟨fun h ↦ by simp at h, ?_⟩
        rintro ⟨d, -, -, h⟩
        rcases d with _ | d
        · exact absurd (Option.some.inj h) hr
        · rw [hrun, hs] at h
          exact nomatch h
      · dsimp only
        rw [haltLoop_eq_some_iff hS fuel (n + 1) r' m]
        constructor
        · rintro ⟨d, rfl, hd, h⟩
          exact ⟨d + 1, by omega, by omega, by rw [hrun, hs]; exact h⟩
        · rintro ⟨d, rfl, hd, h⟩
          rcases d with _ | d
          · exact absurd (Option.some.inj h) hr
          · rw [hrun, hs] at h
            exact ⟨d, by omega, by omega, h⟩

/-- **A run reaches the final state after at most one number of steps**: it halts there. -/
theorem run_final_unique {r : Registers K} {m n : ℕ}
    (hm : run prog L m r = some (Registers.final prog)) (hn : run prog L n r = some (Registers.final prog)) :
    m = n := by
  have key : ∀ {a b : ℕ}, a < b → run prog L a r = some (Registers.final prog) →
      run prog L b r ≠ some (Registers.final prog) := fun {a b} hab ha hb ↦ by
    obtain ⟨d, rfl⟩ : ∃ d, b = a + (d + 1) := ⟨b - a - 1, by omega⟩
    rw [run_add, ha] at hb
    exact absurd (run_final_eq_iff.mp hb) (Nat.succ_ne_zero d)
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact absurd hn (key h hm)
  · exact h
  · exact absurd hm (key h hn)

/-- **`haltingRun` returns the number of steps after which the run halts**, if there is one. -/
theorem haltingRun_eq_some_iff {t : Execution prog} :
    haltingRun prog L = some t ↔
      ∃ n, t = ⟨κ, L, n⟩ ∧ run prog L n Registers.initial = some (Registers.final prog) := by
  unfold haltingRun
  split_ifs with h
  · constructor
    · intro ht
      exact ⟨_, (Option.some.inj ht).symm, Nat.find_spec h⟩
    · rintro ⟨n, rfl, hn⟩
      rw [run_final_unique (Nat.find_spec h) hn]
  · refine ⟨fun ht ↦ by simp at ht, ?_⟩
    rintro ⟨n, -, hn⟩
    exact absurd ⟨n, hn⟩ h

/-- The steps of `haltingRun`'s execution are those of any halting run. -/
theorem haltingRun_steps {t : Execution prog} (ht : haltingRun prog L = some t) {n : ℕ}
    (hn : run prog L n Registers.initial = some (Registers.final prog)) : t.stepCount = n := by
  obtain ⟨m, rfl, hm⟩ := haltingRun_eq_some_iff.mp ht
  exact run_final_unique hm hn

/-- What the capped search returns is the image, with the number of steps it found. -/
theorem haltingRunC_eq_some {cap : ℕ} {t : Execution prog} (h : haltingRunC prog L cap = some t) :
    t = ⟨κ, L, t.stepCount⟩ ∧
      haltLoop (powIndex κ) (powIndex prog.logSize) prog L cap 0 Registers.initial = some t.stepCount := by
  dsimp only [haltingRunC, haltingRunIn] at h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, hn⟩

/-- **The capped search returns the halting run of at most `cap` steps.** -/
theorem haltingRunC_eq_some_iff (hκ : κ < 64) {cap : ℕ} {t : Execution prog} :
    haltingRunC prog L cap = some t ↔
      ∃ n, t = ⟨κ, L, n⟩ ∧ n ≤ cap ∧ run prog L n Registers.initial = some (Registers.final prog) := by
  have hS := stepIn_powIndex (prog := prog) hκ L
  constructor
  · intro h
    obtain ⟨ht, hl⟩ := haltingRunC_eq_some h
    obtain ⟨d, hd, hcap, hrun⟩ := (haltLoop_eq_some_iff hS cap 0 _ _).mp hl
    rw [Nat.zero_add] at hd
    exact ⟨t.stepCount, ht, hd ▸ hcap, hd ▸ hrun⟩
  · rintro ⟨n, rfl, hcap, hrun⟩
    dsimp only [haltingRunC, haltingRunIn]
    rw [(haltLoop_eq_some_iff hS cap 0 _ n).mpr ⟨n, (Nat.zero_add n).symm, hcap, hrun⟩]
    rfl

/-- **The capped search is `haltingRun` whenever every halting run fits the cap.** -/
theorem haltingRunC_eq_haltingRun (hκ : κ < 64) {cap : ℕ}
    (hcap : ∀ n, run prog L n Registers.initial = some (Registers.final prog) → n ≤ cap) :
    haltingRunC prog L cap = haltingRun prog L := by
  refine Option.ext fun t ↦ ?_
  rw [haltingRunC_eq_some_iff hκ, haltingRun_eq_some_iff]
  exact ⟨fun ⟨n, h, _, h'⟩ ↦ ⟨n, h, h'⟩, fun ⟨n, h, h'⟩ ↦ ⟨n, h, hcap n h', h'⟩⟩

end Search

/-! ## 4. The boundary and a candidate's execution -/

/-- **The Boolean boundary is `HoldsPublicInput`.** -/
theorem boundaryOK_iff {prog : LeanIsaProgram} (input : PublicInput) (t : Execution prog) :
    boundaryOK input t = true ↔ HoldsPublicInput input t := by
  unfold boundaryOK HoldsPublicInput
  split_ifs with h
  · have hκ : t.logMemorySize < 64 := by have := h.2; unfold maxLogMem at this; omega
    have h1 : 1 < 2 ^ t.logMemorySize := Nat.one_lt_two_pow (by unfold minLogMem at h; omega)
    rw [show addressOfIndex 0 = addressOfIndex ((⟨0, Nat.two_pow_pos t.logMemorySize⟩ : Fin (2 ^ t.logMemorySize)) : ℕ) from rfl,
      show addressOfIndex 1 = addressOfIndex ((⟨1, h1⟩ : Fin (2 ^ t.logMemorySize)) : ℕ) from rfl,
      MemoryImage.read_gpow hκ, MemoryImage.read_gpow hκ]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq]
    exact ⟨fun h' ↦ ⟨h.1, h.2, h'⟩, fun h' ↦ h'.2.2⟩
  · simp only [false_iff]
    exact fun h' ↦ h ⟨h'.1, h'.2.1⟩

/-- A candidate's execution is the capped halting run of its memory image, filtered by the
boundary. -/
theorem candidateExecution_eq {prog : LeanIsaProgram} (input : PublicInput) (layout :
    Verifier.Layout)
    {μ : ℕ} (q : Vector K (2 ^ μ)) :
    candidateExecution prog input layout q =
      (haltingRunC prog (memoryImage layout q) (stepCap layout)).filter (boundaryOK input) :=
  rfl

/-- **A candidate's execution is valid**, for every candidate: the boundary bounds the memory, so
the search's addresses and run are the specification's. -/
theorem candidateExecution_valid {prog : LeanIsaProgram} {input : PublicInput} {layout :
    Verifier.Layout}
    {μ : ℕ} {q : Vector K (2 ^ μ)} {t : Execution prog}
    (h : candidateExecution prog input layout q = some t) :
    ValidExecution prog input t := by
  rw [candidateExecution_eq] at h
  obtain ⟨hr, hb⟩ := Option.filter_eq_some_iff.mp h
  have hB := (boundaryOK_iff input t).mp hb
  obtain ⟨ht, -⟩ := haltingRunC_eq_some hr
  have hκ : layout.logMemory < 64 := by
    have h2 := hB.2.1
    rw [ht] at h2
    unfold maxLogMem at h2
    exact lt_of_le_of_lt h2 (by norm_num)
  obtain ⟨n, rfl, -, hn⟩ := (haltingRunC_eq_some_iff hκ).mp hr
  exact ⟨hB, hn⟩

/-- **A stack's execution, with the extractor's indices, is valid**: with the indices of the
memory's and the bytecode's address spaces, it is `candidateExecution`. -/
theorem candidateExecutionIn_valid {prog : LeanIsaProgram} {input : PublicInput}
    {layout : Verifier.Layout} {μ : ℕ} {q : Vector K (2 ^ μ)} {t : Execution prog}
    (h : candidateExecutionIn (powIndex layout.logMemory) (powIndex prog.logSize) prog input
      layout q = some t) :
    ValidExecution prog input t :=
  candidateExecution_valid h

/-! ## 5. A halting run never repeats a state -/

section Repeat

variable {prog : LeanIsaProgram}

/-- **A halting run never repeats a state**: from a repeated state the run would reach the final
state before its end, where it halts. -/
theorem run_injective {κ : ℕ} {L : MemoryImage κ} {N : ℕ}
    (hv : run prog L N Registers.initial = some (Registers.final prog)) {i j : ℕ} (hij : i < j)
    (hj : j ≤ N) {r : Registers K} (hi : run prog L i Registers.initial = some r)
    (hj' : run prog L j Registers.initial = some r) : False := by
  obtain ⟨e, rfl⟩ : ∃ e, N = j + e := ⟨N - j, by omega⟩
  have hre : run prog L e r = some (Registers.final prog) := by
    have h := hv
    rw [run_add, hj'] at h
    exact h
  have h1 : run prog L (i + e) Registers.initial = some (Registers.final prog) := by
    rw [run_add, hi]
    exact hre
  obtain ⟨r₁, h₁, hne⟩ := run_intermediate hv (show i + e < j + e by omega)
  rw [h₁] at h1
  exact hne (Option.some.inj h1)

/-- Registers are equal when their components are. -/
theorem regs_ext {r r' : Registers K} (h₁ : r.pc = r'.pc) (h₂ : r.fp = r'.fp) : r = r' := by
  cases r
  cases r'
  simp only at h₁ h₂
  rw [h₁, h₂]

end Repeat

end
end LeanVM.Protocol.Halting
