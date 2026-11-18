/-
  LeanVM.Protocol.Extraction.AS.Lite

  The agreement-set extractor on the layout's fields it reads.
-/

module

public import LeanVM.Protocol.Extraction.AS.TopC
public import LeanVM.Protocol.Extraction.Fast.RunVec
public import LeanVM.Protocol.EndToEnd.Complete.Flushes

/-!
# The extractor on the lite layout

The opcode tables carry their constraints as functions, which the cost machine does not hold, so
the full layout is not built: the body's skeleton depends on the layout only through its sizes,
the tables' log-heights and the push side's depth, computed from the tables' widths and push
counts as constants (`tableWidthsL`, `pushCountsL`). `extractL` is `extractP` on the lite layout
(`Fast.LayoutLite`), its candidate run the indexed runner (`Fast.candidateRunner`); it is
`extractP` (`extractL_eq`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Whir.Params
open LeanVM.Extraction.Fast Common
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest refNConstraints)

@[expose] public section

attribute [local instance] lexOrd

/-- The tables' widths. -/
def tableWidthsL : List ℕ := [13, 13, 7, 14, 14, 92]

/-- The tables' push counts. -/
def pushCountsL : List ℕ := [5, 5, 3, 5, 5, 28]

theorem tableWidthsL_eq : tables.map Table.width = tableWidthsL := by decide +kernel

theorem pushCountsL_eq : tables.map (fun t ↦ t.flushes.push.length) = pushCountsL := by
  decide +kernel

/-- The skeleton of the first `k` tables' reads. -/
def skTablesL (k : ℕ) : List Op := (tableWidthsL.take k).flatMap fun w ↦ List.replicate w .read

theorem skTables_take (k : ℕ) : skTables (tables.take k) = skTablesL k := by
  unfold skTables skTablesL
  rw [← tableWidthsL_eq, ← List.map_take, List.flatMap_map]

/-- The table phase's skeleton. -/
def skTablePhaseL (heights : List ℕ) : List Op :=
  skGrind (grindingBits (2 + nTrees - 1)) ++ [.sample] ++
    (skSum 4 (List.replicate (heights.foldl max 0) false) ++ skTablesL (min heights.length 6))

theorem skTablePhase_eq (heights : List ℕ) : skTablePhase heights = skTablePhaseL heights := by
  unfold skTablePhase skTablePhaseL skTableSumcheck
  rw [refNConstraints, skTables_take]
  rfl

/-- The push side's depth. -/
def pushDepthL (lm lb : ℕ) (heights : List ℕ) : ℕ :=
  (stackOffsets ([0, lm, lb] ++ (heights.zip pushCountsL).flatMap fun x ↦ List.replicate x.2 x.1)).2

theorem logRows_pushBlocks : ∀ (ts : List Table) (hs ns : List ℕ), hs.length ≤ ns.length →
    ((ts.zip (hs.zip ns)).flatMap fun x ↦ x.1.flushes.push.map fun c ↦
      (⟨x.2.1, x.2.2, c, x.1.opcode⟩ : BusBlock)).map (·.logRows) =
      (hs.zip (ts.map fun t ↦ t.flushes.push.length)).flatMap fun x ↦ List.replicate x.2 x.1
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | _ :: _, _ :: _, [], h => by simp at h
  | t :: ts, h :: hs, n :: ns, hl => by
    simp only [List.zip_cons_cons, List.flatMap_cons, List.map_append, List.map_cons]
    rw [logRows_pushBlocks ts hs ns (by simpa using hl), List.map_map]
    congr 1
    simp [Function.comp_def, List.map_const']

/-- The body's skeleton on the lite layout. -/
def skBodyL (lay : LayoutLite) (ρ : ℕ) : List Op :=
  skCommitStack lay.stackLog ρ ++ skOod lay.stackLog ++
    (skBus (pushDepthL lay.logMemory lay.logBytecode lay.tableLogHeights) ++
      skTablePhaseL lay.tableLogHeights ++ [.sample] ++ skKeccak (kLen lay.tableLogHeights)) ++
    skRing ++ ([.sample] ++ skWhir lay.stackLog ρ)

/-- The body's skeleton before the opening's trace, on the lite layout. -/
def skBodyHeadL (lay : LayoutLite) (ρ : ℕ) : List Op :=
  skCommitStack lay.stackLog ρ ++ skOod lay.stackLog ++
    (skBus (pushDepthL lay.logMemory lay.logBytecode lay.tableLogHeights) ++
      skTablePhaseL lay.tableLogHeights ++ [.sample] ++ skKeccak (kLen lay.tableLogHeights)) ++
    skRing ++ [.sample]

/-- A layout built by `buildLayout`: its push side is its blocks'. -/
theorem skFront_built {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) :
    skFront layout = skBus (pushDepthL layout.logMemory layout.logBytecode layout.tableLogHeights) ++
      skTablePhaseL layout.tableLogHeights ++ [.sample] ++ skKeccak (kLen layout.tableLogHeights) := by
  unfold buildLayout at h
  split at h
  · exact absurd h (by simp)
  · split_ifs at h with hc
    · rw [Option.some.injEq] at h
      subst h
      unfold skFront
      rw [skTablePhase_eq]
      congr 3
      unfold busLayout pushDepthL busBlocks
      dsimp only
      rw [logRows_pushBlocks _ _ _ (by
        simp only [List.length_zipWith, tableLogFloors]
        omega), pushCountsL_eq]

/-- The announced sizes' checks, on the lite layout. -/
def sizesOfL (bytecode : List K) (announced : List E) : Option (LayoutLite × ℕ) :=
  if (announced.all fun value ↦ value.limb 1 = 0) then
    let logMemory := kToNat ((announced.headD 0).limb 0)
    let tableRows := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
    let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
    if 1 ≤ logInverseRate ∧ logInverseRate ≤ 4 then
      (buildLayoutLite bytecode logMemory tableRows).bind fun layout ↦
        if Whir.minLogStack ≤ layout.stackLog ∧ layout.stackLog ≤ Whir.maxLogStack then
          some (layout, logInverseRate)
        else none
    else none
  else none

theorem sizesOfL_eq (bytecode : List K) (announced : List E) :
    sizesOfL bytecode announced = (sizesOf bytecode announced).map fun a ↦ (layoutLite a.1, a.2) := by
  unfold sizesOfL sizesOf
  dsimp only
  rw [buildLayoutLite_eq]
  split_ifs
  · rcases buildLayout bytecode _ _ with _ | layout
    · rfl
    · simp only [Option.map_some, Option.bind_some]
      split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  · rfl
  · rfl

theorem built_of_sizesOf {bytecode : List K} {announced : List E} {a : Layout × ℕ}
    (h : sizesOf bytecode announced = some a) :
    ∃ lm rows, buildLayout bytecode lm rows = some a.1 := by
  unfold sizesOf at h
  dsimp only at h
  split_ifs at h
  obtain ⟨layout, hl, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h
  rw [Option.some.injEq] at h
  subst h
  exact ⟨_, _, hl⟩

/-- The announced sizes, on the lite layout. -/
def decSizesL (bytecode : List K) (h : List EvP) : Option (LayoutLite × ℕ) :=
  (h.mapM (fun p : EvP ↦ p.1)).bind (sizesOfL bytecode)

theorem decSizesL_eq (bytecode : List K) (h : List EvP) :
    decSizesL bytecode h = (decSizesP bytecode h).map fun a ↦ (layoutLite a.1, a.2) := by
  unfold decSizesL decSizesP
  rcases h.mapM (fun p : EvP ↦ p.1) with _ | ann
  · rfl
  · exact sizesOfL_eq bytecode ann

/-- The body's trace, on the lite layout. -/
def decBodyL (lay : LayoutLite) (ρ : ℕ) (h : List EvP) : Option WhirTrace :=
  decWhirCutP lay.stackLog ρ (h.drop (skBodyHeadL lay ρ).length)

theorem skBody_built {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) (ρ : ℕ) :
    skBody layout ρ = skBodyL (layoutLite layout) ρ := by
  unfold skBody skBodyL
  rw [skFront_built h]
  rfl

theorem decBodyP_built {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) (ρ : ℕ) (hist : List EvP) :
    decBodyP layout ρ hist = decBodyL (layoutLite layout) ρ hist := by
  unfold decBodyP decBodyL skBodyHead skBodyHeadL
  rw [skFront_built h]
  rfl

/-- Column `v`'s lanes of commitment `i`, from its leaves. -/
def laneRow (i : ℕ) (lv : Array (List K)) (h w v : ℕ) : Array E :=
  (lanesOf i (leafAt lv h w v)).toArray

/-- The `n` columns' lanes of commitment `i`, from its leaves. -/
def laneRows (n i : ℕ) (lv : Array (List K)) (h w : ℕ) : AV :=
  Array.ofFn fun v : Fin n ↦ laneRow i lv h w v

/-- The longest lookup of the roots' leaves: a node's `64` bytes, a leaf's `8w`. -/
def capOf : List (Digest × ℕ × ℕ) → ℕ
  | [] => 64
  | x :: xs =>
    let c := capOf xs
    max (8 * x.2.2) c

theorem le_capOf : ∀ (roots : List (Digest × ℕ × ℕ)) (x : Digest × ℕ × ℕ), x ∈ roots →
    max 64 (8 * x.2.2) ≤ capOf roots
  | [], _, h => absurd h List.not_mem_nil
  | y :: ys, x, h => by
    have h64 : 64 ≤ capOf ys := by
      cases ys with
      | nil => exact le_rfl
      | cons z zs => exact le_trans (le_max_left _ _) (le_capOf (z :: zs) z List.mem_cons_self)
    rcases List.mem_cons.1 h with rfl | h
    · simp only [capOf]; omega
    · have := le_capOf ys x h; simp only [capOf]; omega

/-- A root's leaves, read through the roots' shared index `I`. -/
def leavesAt (I : SortedMap (List UInt64 × ℕ) Hits) (x : Digest × ℕ × ℕ) : Array (List K) :=
  Fast.leavesIn I x.2.2 x.2.1 x.1

/-- Root `i`'s word, column by column. -/
def wordArrOf (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) (i : ℕ) (x : Digest × ℕ × ℕ) : AV :=
  laneRows (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) i (leavesAt I x) x.2.1 x.2.2

/-- Every root's word from root `i` on. -/
def wordsGo (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) :
    ℕ → List (Digest × ℕ × ℕ) → List AV
  | _, [] => []
  | i, x :: xs => wordArrOf μ R I i x :: wordsGo μ R I (i + 1) xs

theorem wordsGo_eq (μ R : ℕ) (I : SortedMap (List UInt64 × ℕ) Hits) :
    ∀ (roots : List (Digest × ℕ × ℕ)) (i : ℕ),
      wordsGo μ R I i roots = roots.mapIdx fun j x ↦ wordArrOf μ R I (j + i) x
  | [], _ => rfl
  | x :: xs, i => by
    rw [wordsGo, List.mapIdx_cons, wordsGo_eq μ R I xs (i + 1), Nat.zero_add]
    congr 1
    refine List.mapIdx_eq_mapIdx_iff.mpr fun j _ ↦ ?_
    rw [Nat.add_right_comm, Nat.add_assoc]

/-- **One index for every root**: at the roots' longest lookup, the words are the per-root ones. -/
theorem wordsGo_zero (μ R : ℕ) (qs : List (PermutationQuery KeccakState × KeccakState))
    (roots : List (Digest × ℕ × ℕ)) :
    wordsGo μ R (transcriptIndex qs (capOf roots)) 0 roots = wordsC μ R qs roots := by
  rw [wordsGo_eq]
  unfold wordsC
  refine List.mapIdx_eq_mapIdx_iff.mpr fun i hi ↦ ?_
  have hl : leavesAt (transcriptIndex qs (capOf roots)) roots[i] =
      Fast.leavesOf qs roots[i].2.2 roots[i].2.1 roots[i].1 :=
    leavesIn_transcriptIndex qs _ _ (le_capOf roots _ (List.getElem_mem hi)) _
  unfold wordArrOf laneRows laneRow
  rw [hl, Nat.add_zero]

/-- **The extractor's finish on the lite layout**, its candidate run the indexed runner. -/
def finishL (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState))
    (r : (Bool × ((LayoutLite × ℕ) × WhirTrace)) × VerifierProgramState) :
    Option (Execution prog) :=
  if laneBits ≤ r.1.2.1.1.stackLog ∧ 2 ^ (r.1.2.1.1.stackLog - laneBits) ≤
      2 ^ ((lvC r.1.2.1.1.stackLog r.1.2.1.2 0).1 + (lvC r.1.2.1.1.stackLog r.1.2.1.2 0).2.1) then
    (descendTraceC r.1.2.1.1.stackLog r.1.2.1.2
      (wordsGo r.1.2.1.1.stackLog r.1.2.1.2 (transcriptIndex qs (capOf r.2.roots)) 0 r.2.roots)
      r.1.2.2 0).bind fun T ↦
    if T.1 = laneBits then
      candidateRunner prog input r.1.2.1.1 (stackA r.1.2.1.1.stackLog T.2)
    else none
  else none

theorem finishL_eq (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (L : Layout) (ρ : ℕ) (tr : WhirTrace)
    (s : VerifierProgramState) :
    finishL prog input qs ((true, ((layoutLite L, ρ), tr)), s) =
      finishC prog input qs ((true, ((L, ρ), tr)), s) := by
  unfold finishL finishC
  dsimp only
  rw [candidateRunner_eq, candidateExecutionFast_eq, wordsGo_zero]
  rfl

/-- **The agreement-set extractor on the lite layout.** -/
def extractL (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) :=
  let M := fwdIndex qs
  let F := fwdF M
  (seedWithHash (KeccakHash.keccak256With F) F (bytecodeWords prog)
    (publicInputDigest input)).bind fun seed ↦
  (skelReplayP F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizesL (bytecodeWords prog) r₁.1).bind fun a ↦
  (skelReplayP F (skBodyL a.1 a.2) r₁.2).bind fun r₂ ↦
  (decBodyL a.1 a.2 r₂.1).bind fun tr ↦
  finishL prog input qs ((true, (a, tr)), r₂.2)

theorem extractL_eq (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    extractL prog input qs π = extractP prog input qs π := by
  unfold extractL extractP
  dsimp only
  refine congrArg _ (funext fun seed ↦ congrArg _ (funext fun r₁ ↦ ?_))
  rw [decSizesL_eq]
  rcases ha : decSizesP (bytecodeWords prog) r₁.1 with _ | a
  · rfl
  · obtain ⟨lm, rows, hb⟩ := built_of_sizesOf (Option.bind_eq_some_iff.mp ha).choose_spec.2
    simp only [Option.map_some, Option.bind_some]
    rw [← skBody_built hb]
    refine congrArg _ (funext fun r₂ ↦ ?_)
    rw [← decBodyP_built hb]
    refine congrArg _ (funext fun tr ↦ ?_)
    exact finishL_eq _ _ _ _ _ _ _

/-- **The agreement-set extractor on the lite layout**, on the adversary's transcript. -/
def transcriptExtractorL : StraightLineExtractor :=
  fun prog input T π ↦ extractL prog input (permutationQueries T) π

end
end LeanVM.Extraction.AS
