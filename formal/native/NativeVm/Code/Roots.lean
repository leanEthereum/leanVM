module

public import NativeVm.Code.Chain

/-!
# The roots each phase reads

Only commitments add roots. Phase 1 and phases 3 to 6 read none (`KeepsRoots`: their runs end with
the roots they start with), phase 2 reads the stack's (`phase2M_roots`), so phase 2 starts with
none and phase 7 with one (`phases_roots`). Each is proved from its steps' (`KeepsRoots.bind`,
the transcript's operations, the loops), by `keeps`.
-/

@[expose] public section

namespace NativeVm.Code

open NativeVm.Model LeanVM.Parameters

/-- A step that leaves the roots read as they were (a structure, so that no tactic unfolds it). -/
structure KeepsRoots {α : Type} (m : VM α) : Prop where
  keeps : ∀ t x t', m.run t = some (x, t') → t'.roots = t.roots

theorem KeepsRoots.bind {α β : Type} {m : VM α} {f : α → VM β} (hm : KeepsRoots m)
    (hf : ∀ a, KeepsRoots (f a)) : KeepsRoots (m >>= f) := by
  refine ⟨fun t x t' h ↦ ?_⟩
  simp only [StateT.run_bind, Option.bind_eq_bind] at h
  cases hr : m.run t with
  | none => rw [hr] at h; cases h
  | some p =>
    rw [hr, Option.bind_some] at h
    rw [(hf p.1).keeps _ _ _ h, hm.keeps t p.1 p.2 hr]

theorem KeepsRoots.pure {α : Type} (a : α) : KeepsRoots (pure a : VM α) := by
  refine ⟨fun t x t' h ↦ ?_⟩
  cases h; rfl

theorem run_reject {α : Type} (t : TState) : (reject : VM α).run t = none := rfl

theorem KeepsRoots.reject {α : Type} : KeepsRoots (reject : VM α) := ⟨fun _ _ _ h ↦ by cases h⟩

theorem KeepsRoots.require (c : Bool) : KeepsRoots (Model.require c) := by
  refine ⟨fun t x t' h ↦ ?_⟩
  unfold Model.require at h
  split at h
  · cases h; rfl
  · cases h

theorem KeepsRoots.liftOpt {α : Type} (o : Option α) : KeepsRoots (liftOpt o) := by
  refine ⟨fun t x t' h ↦ ?_⟩
  cases o with
  | some a => cases h; rfl
  | none => cases h

theorem KeepsRoots.nextScalar : KeepsRoots Model.nextScalar := by
  refine ⟨fun t x t' h ↦ ?_⟩
  by_cases hg : t.sponge.ground.isSome = true
  · simp [Model.nextScalar, hg, run_reject] at h
  · cases hs : t.stream[t.cursor]? with
    | none => simp [Model.nextScalar, hg, hs, run_reject] at h
    | some y =>
      simp [Model.nextScalar, hg, hs] at h
      obtain ⟨-, rfl⟩ := h
      rfl

theorem KeepsRoots.readScalar : KeepsRoots Model.readScalar := by
  refine KeepsRoots.bind KeepsRoots.nextScalar fun x ↦ ⟨fun t y t' h ↦ ?_⟩
  simp at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem KeepsRoots.sampleChallenge : KeepsRoots Model.sampleChallenge := by
  refine ⟨fun t x t' h ↦ ?_⟩
  simp [Model.sampleChallenge] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem KeepsRoots.grind (bits : Nat) : KeepsRoots (Model.grind bits) := by
  unfold Model.grind
  split
  · exact KeepsRoots.pure _
  · refine KeepsRoots.bind KeepsRoots.nextScalar fun nonce ↦ ?_
    refine ⟨fun t x t' h ↦ ?_⟩
    simp only [StateT.run_bind, StateT.run_get, Option.bind_eq_bind, Option.pure_def,
      Option.bind_some, StateT.run_set] at h
    have := (KeepsRoots.require _).keeps _ _ _ h
    rw [this]

theorem KeepsRoots.foldlM {α β : Type} {f : β → α → VM β} (hf : ∀ b a, KeepsRoots (f b a)) :
    ∀ (l : List α) (b : β), KeepsRoots (l.foldlM f b)
  | [], _ => KeepsRoots.pure _
  | a :: l, b => by
    simp only [List.foldlM_cons]
    exact KeepsRoots.bind (hf b a) fun b' ↦ KeepsRoots.foldlM hf l b'

theorem KeepsRoots.arrayFoldlM {α β : Type} {f : β → α → VM β} (hf : ∀ b a, KeepsRoots (f b a))
    (xs : Array α) (b : β) : KeepsRoots (xs.foldlM f b) := by
  rw [← Array.foldlM_toList]
  exact KeepsRoots.foldlM hf _ _

/-- A goal `KeepsRoots m`, `m` a program of the transcript's operations: split into its steps. -/
theorem KeepsRoots.readScalars (n : Nat) : KeepsRoots (Model.readScalars n) := by
  unfold Model.readScalars
  exact KeepsRoots.foldlM (fun _ _ ↦ KeepsRoots.bind KeepsRoots.readScalar fun _ ↦ KeepsRoots.pure _)
    _ _

theorem KeepsRoots.sampleChallenges (n : Nat) : KeepsRoots (Model.sampleChallenges n) := by
  unfold Model.sampleChallenges
  exact KeepsRoots.foldlM
    (fun _ _ ↦ KeepsRoots.bind KeepsRoots.sampleChallenge fun _ ↦ KeepsRoots.pure _) _ _

theorem KeepsRoots.sumcheckRoundPoly (count : Nat) (claim : EW) (eq : Option EW) :
    KeepsRoots (Model.sumcheckRoundPoly count claim eq) := by
  cases eq with
  | none =>
    exact KeepsRoots.bind KeepsRoots.readScalar fun _ ↦ KeepsRoots.bind (KeepsRoots.readScalars _)
      fun _ ↦ KeepsRoots.bind (KeepsRoots.grind _) fun _ ↦ KeepsRoots.pure _
  | some e =>
    exact KeepsRoots.bind (KeepsRoots.readScalars _) fun _ ↦ KeepsRoots.bind (KeepsRoots.grind _)
      fun _ ↦ KeepsRoots.pure _

theorem KeepsRoots.sumcheck (claim : EW) (count : Nat) (eqs : Array (Option EW)) :
    KeepsRoots (Model.sumcheck claim count eqs) := by
  unfold Model.sumcheck
  exact KeepsRoots.arrayFoldlM (fun _ _ ↦ KeepsRoots.bind (KeepsRoots.sumcheckRoundPoly _ _ _)
    fun _ ↦ KeepsRoots.bind KeepsRoots.sampleChallenge fun _ ↦ KeepsRoots.pure _) _ _

theorem KeepsRoots.sumcheckPlain (claim : EW) (count rounds : Nat) :
    KeepsRoots (Model.sumcheckPlain claim count rounds) := KeepsRoots.sumcheck _ _ _

macro "keeps" : tactic => `(tactic| repeat' (first
  | with_reducible exact KeepsRoots.pure _
  | with_reducible exact KeepsRoots.reject
  | with_reducible exact KeepsRoots.require _
  | with_reducible exact KeepsRoots.liftOpt _
  | with_reducible exact KeepsRoots.readScalar
  | with_reducible exact KeepsRoots.sampleChallenge
  | with_reducible exact KeepsRoots.grind _
  | with_reducible exact KeepsRoots.readScalars _
  | with_reducible exact KeepsRoots.sampleChallenges _
  | with_reducible exact KeepsRoots.sumcheck _ _ _
  | with_reducible exact KeepsRoots.sumcheckPlain _ _ _
  | with_reducible apply KeepsRoots.bind
  | with_reducible apply KeepsRoots.foldlM
  | with_reducible apply KeepsRoots.arrayFoldlM
  | (intro)
  | split
  | (dsimp only)))

theorem readAnnouncedSizes_roots (bc : Array UInt64) : KeepsRoots (readAnnouncedSizes bc) := by
  unfold readAnnouncedSizes; keeps

theorem publicInputPhase_roots (layout : LayoutW) (pub : Vector UInt64 4) :
    KeepsRoots (publicInputPhase layout pub) := by
  unfold publicInputPhase; keeps

theorem gkrStep_roots (step : Nat) (last : Bool) (st : GkrStateW) : KeepsRoots (gkrStep step last st) := by
  unfold gkrStep; keeps

theorem gkrLayers_roots : ∀ n st, KeepsRoots (gkrLayers n st)
  | 0, _ => by rw [gkrLayers]; exact KeepsRoots.pure _
  | 1, _ => by
    rw [gkrLayers]
    exact KeepsRoots.bind (gkrStep_roots _ _ _) fun _ ↦ gkrLayers_roots 0 _
  | n + 2, _ => by
    rw [gkrLayers]
    split
    · exact KeepsRoots.bind (gkrStep_roots _ _ _) fun _ ↦ gkrLayers_roots (n + 1) _
    · exact KeepsRoots.bind (gkrStep_roots _ _ _) fun _ ↦ gkrLayers_roots n _

theorem verifyBusBalance_roots (layout : LayoutW) : KeepsRoots (verifyBusBalance layout) := by
  unfold verifyBusBalance verifyGkrGrandProducts bytecodeShare computedBytecodeValue
  keeps
  all_goals exact gkrLayers_roots _ _

theorem tablePhase_roots (layout : LayoutW) (bus : BusResultW) :
    KeepsRoots (tablePhase layout bus) := by
  unfold tablePhase tableSumcheck tableTerms tableTermsStep
  keeps

theorem keccakPhase_roots (layout : LayoutW) (ev : Array (Array EW × Array EW)) :
    KeepsRoots (keccakPhase layout ev) := by
  unfold keccakPhase verifyKeccak keccakLayers verifyKeccakLayer keccakOpen
  keeps

/-- A step that adds at most `k` roots. -/
structure GrowsRoots {α : Type} (k : Nat) (m : VM α) : Prop where
  grows : ∀ t x t', m.run t = some (x, t') → t'.roots.size ≤ t.roots.size + k

theorem KeepsRoots.grows {α : Type} {m : VM α} (h : KeepsRoots m) : GrowsRoots 0 m :=
  ⟨fun t x t' hr ↦ by rw [h.keeps t x t' hr]; omega⟩

theorem GrowsRoots.mono {α : Type} {m : VM α} {a b : Nat} (h : GrowsRoots a m) (hab : a ≤ b) :
    GrowsRoots b m := ⟨fun t x t' hr ↦ by have := h.grows t x t' hr; omega⟩

theorem GrowsRoots.bind {α β : Type} {m : VM α} {f : α → VM β} {a b : Nat} (hm : GrowsRoots a m)
    (hf : ∀ x, GrowsRoots b (f x)) : GrowsRoots (a + b) (m >>= f) := by
  refine ⟨fun t x t' h ↦ ?_⟩
  simp only [StateT.run_bind, Option.bind_eq_bind] at h
  cases hr : m.run t with
  | none => rw [hr] at h; cases h
  | some p =>
    rw [hr, Option.bind_some] at h
    have h1 := (hf p.1).grows _ _ _ h
    have h2 := hm.grows t p.1 p.2 hr
    omega

theorem readCommitment_roots (height width : Nat) : GrowsRoots 1 (readCommitment height width) := by
  unfold readCommitment
  refine (GrowsRoots.bind KeepsRoots.readScalar.grows fun _ ↦ GrowsRoots.bind (b := 1)
    KeepsRoots.readScalar.grows fun _ ↦ ⟨fun t x t' h ↦ ?_⟩).mono (by omega)
  simp at h
  obtain ⟨-, rfl⟩ := h
  simp

theorem readOod_roots (stackLog : Nat) : KeepsRoots (readOod stackLog) := by
  unfold readOod; keeps

/-- **Phase 2 reads one root**, the stack's. -/
theorem phase2M_roots (layout : LayoutW) (rate : Nat) : GrowsRoots 1 (phase2M layout rate) := by
  unfold phase2M commitStack
  refine (GrowsRoots.bind (GrowsRoots.bind (b := 1) (KeepsRoots.liftOpt _).grows fun config ↦ ?_)
    fun _ ↦ (readOod_roots _).grows).mono (by omega)
  split
  · exact KeepsRoots.reject.grows.mono (by omega)
  · exact readCommitment_roots _ _

end NativeVm.Code
