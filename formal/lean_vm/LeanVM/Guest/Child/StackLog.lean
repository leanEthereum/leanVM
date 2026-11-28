/-
  LeanVM.Guest.Child.StackLog

  Every layout a proof stream announces has a stack log at least `min_execution_stacked_log`, the
  least the guest program has an opening arm for (`Coverage.minChildStackLog`).
-/

module

public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.Verifier.Deferred
public import LeanVM.Facts.Stack
public import LeanVM.Guest.AcceptableChild

/-!
# The announced stack log

The layout a stream announces (`announcedLayoutAndRate`) is one `buildLayout` gives
(`built_of_announced`): the stack of the columns' log-sizes at the announced memory and table
heights (`stack`). Its log-size grows with every block's log-size (`stack_snd_mono`), and each
column's log-size grows with the memory's and the tables' heights (`columnKappas_forall₂`). The
announced memory is at least `MIN_LOG_MEMORY` and every table's height at least its floor
(`buildLayout`), the sizes `min_execution_stacked_log` stacks, so every announced stack log is at
least it (`minExecutionStackedLog_le_of_buildLayout`), on every bytecode
(`stackLog_ge_of_announced`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The stack grows with its blocks -/

/-- `log2_ceil` is monotone. -/
theorem log2Ceil_mono {a b : ℕ} (h : a ≤ b) : log2Ceil a ≤ log2Ceil b :=
  (log2Ceil_le_iff a _).mpr (h.trans ((log2Ceil_le_iff b _).mp le_rfl))

/-- **The stack's log-size grows with its blocks' log-sizes.** -/
theorem stack_snd_mono {kappas kappas' : List ℕ}
    (h : ∀ b ∈ stackBlocks, kappas.getD b.column 0 ≤ kappas'.getD b.column 0) :
    (stack kappas).2 ≤ (stack kappas').2 := by
  simp only [stack, stackOffsets_snd, List.map_map]
  refine max_le_max le_rfl (log2Ceil_mono (List.sum_le_sum fun b hb ↦ ?_))
  exact Nat.pow_le_pow_right (by norm_num) (h b hb)

theorem forall₂_getD {l l' : List ℕ} (h : List.Forall₂ (· ≤ ·) l l') (i : ℕ) :
    l.getD i 0 ≤ l'.getD i 0 := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem forall₂_append {a b c d : List ℕ} (h1 : List.Forall₂ (· ≤ ·) a c)
    (h2 : List.Forall₂ (· ≤ ·) b d) : List.Forall₂ (· ≤ ·) (a ++ b) (c ++ d) := by
  induction h1 with
  | nil => simpa using h2
  | cons h _ ih => exact .cons h ih

theorem forall₂_replicate {x y : ℕ} (h : x ≤ y) :
    ∀ n, List.Forall₂ (· ≤ ·) (List.replicate n x) (List.replicate n y)
  | 0 => .nil
  | n + 1 => by
    simp only [List.replicate_succ]
    exact .cons h (forall₂_replicate h n)

/-- **Each column's log-size grows with the memory's and the tables' heights.** -/
theorem columnKappas_forall₂ (tl : List Table) {logMemory logMemory' : ℕ}
    {heights heights' : List ℕ} (hm : logMemory ≤ logMemory')
    (hh : ∀ i, heights.getD i 0 ≤ heights'.getD i 0) :
    List.Forall₂ (· ≤ ·) (columnKappas tl logMemory heights) (columnKappas tl logMemory' heights') := by
  unfold columnKappas
  refine forall₂_append (.cons hm (.cons hm (.cons (by have := hh opKeccak; omega) .nil))) ?_
  induction tl with
  | nil => exact .nil
  | cons t ts ih =>
    simp only [List.flatMap_cons]
    exact forall₂_append (forall₂_replicate (hh _) _) ih

/-- Every table's height `buildLayout` takes is at least its floor. -/
theorem floors_getD_le : ∀ {rows floors : List ℕ}, floors.length ≤ rows.length → ∀ i,
    floors.getD i 0 ≤ (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows floors).getD i 0
  | _, [], _, i => by simp
  | [], _ :: _, hl, _ => by simp at hl
  | r :: rs, f :: fs, hl, i => by
    cases i with
    | zero => simp
    | succ i =>
      simpa using floors_getD_le (rows := rs) (floors := fs) (by simpa using hl) i

/-! ## The announced layout -/

/-- What `buildLayout` stacks: the columns' log-sizes at the memory, at least `MIN_LOG_MEMORY`,
and at the tables' heights, each the least fitting its rows and at least its floor. -/
theorem buildLayout_stackLog {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout) :
    minLogMemory ≤ logMemory ∧ tableRows.length = nTables ∧
      layout.stackLog = (stack (columnKappas tables logMemory
        (List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows tableLogFloors))).2 := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hc.1, hc.2.2.2.2.2, rfl⟩
    · cases h

/-- **A layout `buildLayout` gives stacks at least `min_execution_stacked_log`**: its memory and
its tables' heights are at least the smallest execution's. -/
theorem minExecutionStackedLog_le_of_buildLayout {bytecode : List K} {logMemory : ℕ}
    {tableRows : List ℕ} {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout)
    (logBytecode : ℕ) : minExecutionStackedLog logBytecode ≤ layout.stackLog := by
  obtain ⟨hm, hlen, he⟩ := buildLayout_stackLog h
  rw [he]
  unfold minExecutionStackedLog
  have hfl : tableLogFloors.length ≤ tableRows.length := by rw [hlen]; decide
  exact stack_snd_mono fun b _ ↦ forall₂_getD
    (columnKappas_forall₂ tables hm (floors_getD_le hfl)) b.column

/-- **The layout a stream announces is one `buildLayout` gives.** -/
theorem built_of_announced {bytecode : List K} {stream : List E} {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate bytecode stream = some (layout, r)) :
    ∃ logMemory tableRows, buildLayout bytecode logMemory tableRows = some layout := by
  unfold announcedLayoutAndRate at h
  obtain ⟨⟨x, s'⟩, hrun, hx⟩ := Option.map_eq_some_iff.mp h
  simp only at hx
  subst hx
  rw [runPure_eq_withHash] at hrun
  have hr := VerifierProgram.returns_of_run _ _ hrun
  unfold readAnnouncedSizes at hr
  obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨layout', hl, hr⟩ := VerifierProgram.returns_bind hr
  obtain ⟨_, -, hr⟩ := VerifierProgram.returns_bind hr
  have he := congrArg Prod.fst (VerifierProgram.returns_ret hr)
  simp only at he
  subst he
  exact ⟨_, _, returns_liftOption hl⟩

/-- **Every layout a stream announces has a stack log at least `minChildStackLog`**
(`min_execution_stacked_log`), on every bytecode: `AcceptableChild`'s `stackLogAtLeastMinimum`. -/
theorem stackLog_ge_of_announced {bytecode : List K} {stream : List E} {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate bytecode stream = some (layout, r)) :
    Coverage.minChildStackLog ≤ layout.stackLog :=
  let ⟨_, _, hb⟩ := built_of_announced h
  minExecutionStackedLog_le_of_buildLayout hb 19

end

end LeanVM.Guest.Child
