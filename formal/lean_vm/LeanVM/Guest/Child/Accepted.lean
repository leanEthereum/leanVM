/-
  LeanVM.Guest.Child.Accepted

  A child the deferring verifier accepts, free of a collision in the caps and of a zero challenge,
  is one the guest program accepts: its stack log and its stream follow from the acceptance.
-/

module

public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Child.Reads
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Protocol.Verifier.Phases
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.Limits

/-!
# Children the verifier accepts

`acceptableChild_of_accepted`: a child whose proof the deferring verifier accepts, with a deferred
claim of the bytecode's shape (`NodeRelation`'s `ChildrenProven`), is a child the guest program
accepts (`AcceptableChild`) wherever it is `ChildWithoutCollisionOrZero`:

* its stack log is at least `20` (`stackLog_ge_of_buildLayout`): every layout the verifier reads
  for a bytecode of `2^23` words (`built_of_announced`) stacks the memory's three columns and the
  bytecode's `2^19`-word column, more than `2^19` words;
* its stream is at most `STREAM_CAP` scalars (`stream_le_of_verifyDeferred`);
* every query step of its verifier's run opens one phase of its proof, each opening at its leaf's
  position, every path of the step's height (`queryStepsOf_phase`), so the phases agreeing gives
  the steps agreeing.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Guest.Completeness LeanVM.Protocol.Verifier.Claims

@[expose] public section

/-! ## The announced layout -/

/-- **Every value a program returns, run, satisfies what every value it can return does.** -/
theorem run_of_allRet {α : Type} {P : α → Prop} (π : KeccakState → Id KeccakState)
    {p : VerifierProgram α} (hp : AllRet p P) :
    ∀ {s : VerifierProgramState} {a : α} {s' : VerifierProgramState},
      run (m := Id) π p s = some (a, s') → P a := by
  induction hp with
  | ret h =>
    intro s a s' e
    simp only [run, pure, Option.some.injEq, Prod.mk.injEq] at e
    exact e.1 ▸ h
  | fail =>
    intro s a s' e
    cases e
  | read _ ih =>
    intro s a s' e
    simp only [run] at e
    split at e
    · exact ih _ e
    · cases e
  | sample _ ih =>
    intro s a s' e
    exact ih _ e
  | grind _ ih =>
    intro s a s' e
    simp only [run] at e
    split at e
    · split at e
      · exact ih e
      · cases e
    · cases e
  | commit _ ih =>
    intro s a s' e
    simp only [run] at e
    split at e
    · exact ih e
    · cases e
  | query _ ih =>
    intro s a s' e
    simp only [run] at e
    split at e
    · split at e
      · exact ih _ e
      · cases e
    · cases e

/-- Every value `readAnnouncedSizes` returns has a layout `buildLayout` gives. -/
theorem allRet_readSizes_built (bytecode : List K) :
    AllRet (readAnnouncedSizes bytecode) fun x ↦
      ∃ logMemory tableRows, buildLayout bytecode logMemory tableRows = some x.1 := by
  rw [readAnnouncedSizes_eq]
  refine AllRet.bind (fun _ _ ↦ ?_) _ (allRet_true _)
  exact AllRet.mono (fun _ hx ↦ ⟨_, _, (sizesOf_spec hx).layout⟩) (allRet_liftOption _)

/-- **The layout a stream announces is one `buildLayout` gives.** -/
theorem built_of_announced {bytecode : List K} {stream : List E} {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate bytecode stream = some (layout, r)) :
    ∃ logMemory tableRows, buildLayout bytecode logMemory tableRows = some layout := by
  unfold announcedLayoutAndRate at h
  obtain ⟨⟨x, s'⟩, hrun, hx⟩ := Option.map_eq_some_iff.mp h
  subst hx
  exact run_of_allRet _ (allRet_readSizes_built bytecode) hrun

/-- The guest's first four columns are committed: the memory's three and the bytecode's. -/
theorem committedCols_take : (B1.Tables.committedCols 158).take 4 = [0, 1, 2, 3] := by
  decide +kernel

/-- **A layout of a bytecode of `2^23` words stacks more than `2^19` words**, so its stack log is
at least `20`: its bytecode column alone has `2^19`. -/
theorem stackLog_ge_of_buildLayout {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {logMemory : ℕ} {tableRows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode logMemory tableRows = some layout) :
    Coverage.minChildStackLog ≤ layout.stackLog := by
  have hls : log2Strict bytecode.length = some 23 := by rw [hbl]; decide
  have hc : 1 ≤ logMemory ∧ logMemory ≤ 30 ∧ tableRows.all (· ≤ 2 ^ 30) ∧
      tableRows.length = tables.length := by
    have h' := h
    unfold buildLayout at h'
    rw [hls] at h'
    simp only at h'
    split_ifs at h' with hc
    · exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.2⟩
  obtain ⟨hlm1, hlm30, hrows, hlen⟩ := hc
  rw [B1.VerifySub.buildLayout_eq hbl hlm1 hlm30 (by rw [hlen]; rfl) (by simpa using hrows),
    Option.some.injEq] at h
  subst h
  rw [B1.VerifySub.stackLog_eq hbl]
  refine le_trans ?_ (le_max_right _ _)
  generalize B1.Tables.tableHeightsOf tableRows = hs
  have hlen' : (columnKappas logMemory 19 hs).length = 158 := by
    simp only [columnKappas, List.length_append, List.length_cons, List.length_nil,
      List.length_flatMap, List.length_replicate]
    decide +kernel
  have hcols : B1.Tables.committedCols 158 = [0, 1, 2, 3] ++ (B1.Tables.committedCols 158).drop 4 := by
    conv_lhs => rw [← List.take_append_drop 4 (B1.Tables.committedCols 158)]
    rw [committedCols_take]
  have htot : 2 ^ 19 < B1.Tables.stackTotal (columnKappas logMemory 19 hs) := by
    unfold B1.Tables.stackTotal B1.Tables.committedKappas
    rw [hlen', hcols]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, columnKappas, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]
    have := Nat.two_pow_pos logMemory
    omega
  by_contra hlt
  have hle := B1.VerifySub.le_pow_of_log2Ceil
    (r := B1.Tables.stackTotal (columnKappas logMemory 19 hs)) (k := 19)
    (by unfold Coverage.minChildStackLog at hlt; omega)
  omega

/-! ## The query steps -/

theorem zip_map_self {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map f).zip l = l.map fun a ↦ (f a, a)
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.map_cons, List.zip_cons_cons, zip_map_self f l]

/-- An opened phase has its positions and every path the tree's height. -/
theorem openPhase_some {root : Digest} {height width : ℕ} {positions : List ℕ}
    {phase : List Opening} {rows : List (List K)}
    (h : openPhase (m := Id) keccakF1600 root height width positions phase = some rows) :
    (∀ opening ∈ phase, opening.path.length = height) ∧
      positions.zip phase = phase.map fun opening ↦ (opening.leafIndex, opening) := by
  unfold openPhase at h
  split_ifs at h with hc
  · refine ⟨fun o ho ↦ (hc.1 o ho).2, ?_⟩
    rw [← hc.2]
    exact zip_map_self _ phase

/-- **Every query step opens a phase of the state's openings**, each opening at its leaf's
position, every path the step's height. -/
theorem queryStepsOf_phase {α : Type} (p : VerifierProgram α) :
    ∀ (state : VerifierProgramState), ∀ step ∈ Limits.queryStepsOf p state,
      ∃ phase ∈ state.openings, (∀ opening ∈ phase, opening.path.length = step.1) ∧
        step.2 = phase.map fun opening ↦ (opening.leafIndex, opening) := by
  induction p with
  | ret _ => intro state step h; simp [Limits.queryStepsOf] at h
  | fail => intro state step h; simp [Limits.queryStepsOf] at h
  | read k ih =>
    intro state step h
    simp only [Limits.queryStepsOf] at h
    split at h
    · exact ih _ _ step h
    · simp at h
  | sample k ih =>
    intro state step h
    exact ih _ _ step h
  | grind bits k ih =>
    intro state step h
    simp only [Limits.queryStepsOf] at h
    split at h
    · split at h
      · exact ih _ step h
      · simp at h
    · simp at h
  | commit height width k ih =>
    intro state step h
    simp only [Limits.queryStepsOf] at h
    split at h
    · exact ih _ step h
    · simp at h
  | query i ps k ih =>
    intro state step h
    simp only [Limits.queryStepsOf] at h
    split at h
    · rename_i root height width phase rest hroot hopen
      split at h
      · rename_i rows hrows
        obtain ⟨hlen, hzip⟩ := openPhase_some hrows
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨phase, by rw [hopen]; exact List.mem_cons_self .., hlen, hzip⟩
        · obtain ⟨phase', hmem, h'⟩ := ih rows _ step h
          exact ⟨phase', by rw [hopen]; exact List.mem_cons_of_mem _ hmem, h'⟩
      · simp at h
    · simp at h

/-! ## Acceptable children -/

/-- **A child the deferring verifier accepts, free of a collision in the caps and of a zero
challenge, is one the guest program accepts**, for a bytecode of `2^23` words. -/
theorem acceptableChild_of_accepted {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {seed : Digest} {child : Child}
    (hshape : child.statement.deferredClaim.HasBytecodeShape bytecode)
    (hv : verifyDeferred bytecode seed (statementDigest seed child.statement) child.freshClaim
      child.proof = true)
    (hc : ChildWithoutCollisionOrZero bytecode seed child) :
    AcceptableChild bytecode seed child where
  deferredClaimShaped := hshape
  verifies := hv
  stackLogAtLeastMinimum layout _ h :=
    let ⟨_, _, hb⟩ := built_of_announced h
    stackLog_ge_of_buildLayout hbl hb
  streamWithinCap := stream_le_of_verifyDeferred hv
  capsAgree step hstep := by
    obtain ⟨phase, hphase, hlen, heq⟩ := queryStepsOf_phase _ _ step hstep
    rw [heq]
    exact hc.openingsAgree phase hphase step.1 hlen
  noZeroChallenge := hc.noZeroChallenge

/-- **The children of a node `NodeRelation` admits, each free of a collision in the caps and of a
zero challenge, are children the guest program accepts**, for a bytecode of `2^23` words. -/
theorem acceptableChildren_of_accepted {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {seed : Digest} {statement : NodeStatement} {witness : NodeWitness}
    (hrel : NodeRelation bytecode seed statement witness)
    (hc : ∀ child ∈ witness.children, ChildWithoutCollisionOrZero bytecode seed child) :
    ChildrenOk bytecode seed witness := by
  intro child hchild
  unfold NodeRelation at hrel
  obtain ⟨hshape, hv⟩ := hrel.2.2.1 child hchild
  exact acceptableChild_of_accepted hbl hshape hv (hc child hchild)

end
end LeanVM.Guest.Child
