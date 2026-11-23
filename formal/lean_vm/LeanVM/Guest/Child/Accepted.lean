/-
  LeanVM.Guest.Child.Accepted

  A child the deferring verifier accepts, its openings agreeing in the caps, is one the guest
  program accepts: its stack log and its stream follow from the acceptance.
-/

module

public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Child.Reads
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Protocol.Verifier.Phases
public import LeanVM.Protocol.Verifier.Claims

/-!
# Children the verifier accepts

`acceptableChild_of_accepted`: a child whose proof the deferring verifier accepts, with a deferred
claim of the bytecode's shape (`NodeRelation`'s `ChildrenProven`), is a child the guest program
accepts (`AcceptableChild`) wherever its openings agree at every query step of its verifier's run
(which fails only on a Keccak-256 collision, `Child/Collision.lean`):

* its stack log is at least `20` (`stackLog_ge_of_buildLayout`): every layout the verifier reads
  for a bytecode of `2^23` words (`built_of_announced`) stacks the memory's three columns and the
  bytecode's `2^19`-word column, more than `2^19` words;
* its stream is at most `STREAM_CAP` scalars (`stream_le_of_verifyDeferred`).
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
      Compile.run (m := Id) π p s = some (a, s') → P a := by
  induction hp with
  | ret h =>
    intro s a s' e
    simp only [Compile.run, pure] at e
    cases e
    exact h
  | fail =>
    intro s a s' e
    cases e
  | read _ ih =>
    intro s a s' e
    simp only [Compile.run] at e
    split at e
    · exact ih _ e
    · cases e
  | @sample k _ ih =>
    intro s a s' e
    have e2 : Compile.run (m := Id) π (VerifierProgram.sample k) s =
        Compile.run π (k (Id.run (squeeze π s.sponge)).1)
          { s with sponge := (Id.run (squeeze π s.sponge)).2 } := rfl
    rw [e2] at e
    exact ih _ e
  | grind _ ih =>
    intro s a s' e
    simp only [Compile.run] at e
    split at e
    · rename_i _ _ n _ _ _
      generalize absorbNonce π s.sponge n = N at e
      obtain ⟨pw, sp'⟩ := N
      change (if powOk _ pw = true then _ else _) = _ at e
      split at e
      · exact ih e
      · cases e
    · cases e
  | commit _ ih =>
    intro s a s' e
    simp only [Compile.run] at e
    split at e
    · exact ih e
    · cases e
  | query _ ih =>
    intro s a s' e
    simp only [Compile.run] at e
    split at e
    · rename_i root height width phase rest _ _
      generalize openPhase π root height width _ phase = O at e
      cases O with
      | some rows => exact ih rows e
      | none => cases e
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

/-! ## Acceptable children -/

/-- **A child the deferring verifier accepts, its openings agreeing at every query step, is one the
guest program accepts**, for a bytecode of `2^23` words. -/
theorem acceptableChild_of_accepted {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {seed : Digest} {child : Child}
    (hshape : child.statement.deferredClaim.HasBytecodeShape bytecode)
    (hv : verifyDeferred bytecode seed (statementDigest seed child.statement) child.freshClaim
      child.proof = true)
    (hcaps : ∀ step ∈ Limits.queryStepsOf
      (deferringVerifierProgram child.freshClaim bytecode (statementDigest seed child.statement))
        (Coverage.childVerifierStart seed child),
      Limits.OpeningsAgree step.1 step.2) :
    AcceptableChild bytecode seed child where
  deferredClaimShaped := hshape
  verifies := hv
  stackLogAtLeastMinimum _ _ h :=
    let ⟨_, _, hb⟩ := built_of_announced h
    stackLog_ge_of_buildLayout hbl hb
  streamWithinCap := stream_le_of_verifyDeferred hv
  capsAgree := hcaps

end
end LeanVM.Guest.Child
