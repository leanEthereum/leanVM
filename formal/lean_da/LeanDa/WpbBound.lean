module

public import LeanDa.ForkBound
public import LeanDa.WithHash

@[expose] public section

/-!
# The collision term of Wagner's weak-position-binding reduction, bounded

Benedikt Wagner's weak-position-binding reduction (`wpbReduction`) runs the code-binding adversary
once, extracts a vector from its proof, and opens it honestly at a position where an opening of
the adversary disagrees; `wpbCollExpH` is the probability that the two openings' climbs collide
under the hash of a uniformly random table `h`. With `H` left as queries (`wpbX`), the experiment
for `h` is this computation answered by `h` (`wpbCollExpH_le_col`). The adversary makes at most
`Q + 1` queries of `H`, the honest opening at most `256 · nPad r`, and the climbs, the adversary's
cut at the honest climb's height (`findCollision_take`), and the search at most `4 d + 7`
(`d = 7 + logPad r`). So the term is at most `(N + 2)² / 2^256` for
`N = Q + 256 · nPad r + 4 d + 8` (`wpbColl_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: it bounds his
weak-position-binding collision term.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex LeanDa.Fork PFunctor PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-! ## Cutting a climb at a height -/

theorem hashInputs_take (H : List UInt8 → Common.DigestBytes) (path : List Common.DigestBytes) :
    ∀ (k idx : ℕ) (a : List UInt8),
      (hashInputs H idx a path).take (k + 1) = (hashInputs H idx a (path.take k)).take (k + 1) := by
  induction path with
  | nil => intro k idx a; simp
  | cons s rest ih =>
    intro k idx a
    rcases k with _ | k
    · simp [hashInputs]
    · simp only [hashInputs, List.take_succ_cons]
      rw [ih k]

theorem findCollision_take (H : List UInt8 → Common.DigestBytes) (l₁ : List (List UInt8)) :
    ∀ (l₂ : List (List UInt8)) (n : ℕ), l₂.length ≤ n →
      findCollision H l₁ l₂ = findCollision H (l₁.take n) l₂ := by
  induction l₁ with
  | nil => intro l₂ n _; simp
  | cons a as ih =>
    intro l₂ n hn
    cases l₂ with
    | nil => cases n <;> rfl
    | cons b bs =>
      rcases n with _ | n
      · simp at hn
      · simp only [findCollision, List.take_succ_cons]
        rw [ih bs n (by simpa using hn)]

/-- **The adversary's climb cut at the honest climb's height** finds the same collision. -/
theorem openingsCollision_take {r : ℕ} (H : List UInt8 → Common.DigestBytes) (i : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) (c : Fin (r * 128) → Cell) :
    openingsCollision H r i x ⟨τ.path.take (7 + logPaddedRowCount r)⟩ (c i) (openCellWithHash H c i) =
      openingsCollision H r i x τ (c i) (openCellWithHash H c i) := by
  have hl : (hashInputs H i (cellBytes (c i)) (openCellWithHash H c i).path).length =
      8 + logPaddedRowCount r := by
    rw [length_hashInputs]
    simp only [openCellWithHash, List.length_append, length_merklePath]
    omega
  simp only [openingsCollision]
  rw [findCollision_take H _ _ (8 + logPaddedRowCount r) hl.le,
    findCollision_take H (hashInputs H i (cellBytes x) τ.path) _ (8 + logPaddedRowCount r)
      hl.le, show 8 + logPaddedRowCount r = (7 + logPaddedRowCount r) + 1 by omega,
    hashInputs_take H τ.path (7 + logPaddedRowCount r)]

theorem shortP_openingsCollision {r : ℕ} (H : List UInt8 → Common.DigestBytes) (i : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) (x' : Cell) (τ' : CellOpening)
    (hne : (openingsCollision H r i x τ x' τ').1 ≠ (openingsCollision H r i x τ x' τ').2) :
    shortP (openingsCollision H r i x τ x' τ').1 ∧ shortP (openingsCollision H r i x τ x' τ').2 := by
  obtain ⟨h1, h2⟩ := findCollision_mem H _ _ hne
  exact ⟨shortP_of_mem_hashInputs H _ _ _ _ h1, shortP_of_mem_hashInputs H _ _ _ _ h2⟩

/-- The climbs of an opening and of the honest one, with `H` as queries, the opening's cut. -/
def wpbColX (r : ℕ) (c : Fin (r * 128) → Cell) (i : Fin (r * 128)) (x : Cell) (τ : CellOpening) :
    OracleComp (unifSpec + XS) (List UInt8 × List UInt8) := do
  let τ' ← openCellM hS c i
  let l₁ ← hashInputsM hS i (cellBytes x) (τ.path.take (7 + logPaddedRowCount r))
  let l₂ ← hashInputsM hS i (cellBytes (c i)) (τ'.path.take (7 + logPaddedRowCount r))
  findCollisionM hS l₁ (l₂.take (8 + logPaddedRowCount r))

theorem wpbColX_eval (r : ℕ) (h : HTab) (c : Fin (r * 128) → Cell) (i : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) :
    simulateQ (col h) (wpbColX r c i x τ) = pure (openingsCollision (Hh h) r i x τ (c i) (openCellWithHash (Hh h) c i)) := by
  have hp : ∀ {α} (a : α), simulateQ (col (Ψ := unifSpec) h) (pure a) = pure a := fun _ ↦ rfl
  have hb : ∀ {α β} (x : OracleComp (unifSpec + XS) α) (f : α → OracleComp (unifSpec + XS) β),
      simulateQ (col h) (x >>= f) = simulateQ (col h) x >>= fun a ↦ simulateQ (col h) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  simp only [wpbColX, hb, openCellM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
    hashInputsM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
    findCollisionM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h), pure_bind]
  rw [← openingsCollision_take]
  congr 1
  have e1 : (openCellWithHash (Hh h) c i).path.take (7 + logPaddedRowCount r) = (openCellWithHash (Hh h) c i).path :=
    List.take_of_length_le (by simp [openCellWithHash, length_merklePath])
  have e2 : (hashInputs (Hh h) i (cellBytes (c i)) (openCellWithHash (Hh h) c i).path).take
      (8 + logPaddedRowCount r) = hashInputs (Hh h) i (cellBytes (c i)) (openCellWithHash (Hh h) c i).path :=
    List.take_of_length_le (by
      rw [length_hashInputs]
      simp only [openCellWithHash, List.length_append, length_merklePath]
      omega)
  simp only [openingsCollision, e1, e2]

theorem isWeightBound_wpbColX (r : ℕ) (c : Fin (r * 128) → Cell) (i : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) :
    QueryCostAtMost (wpbColX r c i x τ) xCalls
      (openCalls r + (8 + logPaddedRowCount r + 1) + (7 + logPaddedRowCount r + 1) + 2 * (9 + logPaddedRowCount r)) := by
  unfold wpbColX
  have hI : ∀ k idx a (path : List Common.DigestBytes), QueryCostAtMost
      (hashInputsM (hS (Ψ := unifSpec)) idx a (path.take k)) xCalls (k + 1) :=
    fun k idx a path ↦ (isWeightBound_hashInputsM (hS (Ψ := unifSpec)) xCalls
      (fun _ ↦ isWeightBound_hS _) _ idx a).mono (by simp only [List.length_take]; omega)
  have hF : ∀ l₁ (l₂ : List (List UInt8)), QueryCostAtMost
      (findCollisionM (hS (Ψ := unifSpec)) l₁ (l₂.take (8 + logPaddedRowCount r))) xCalls (2 * (9 + logPaddedRowCount r)) :=
    fun l₁ l₂ ↦ (isWeightBound_findCollisionM (hS (Ψ := unifSpec)) xCalls
      (fun _ ↦ isWeightBound_hS _) l₁ _).mono (by simp only [List.length_take]; omega)
  exact ((isWeightBound_openCellM_hS r c i).bind fun _ ↦ (hI _ _ _ _).bind fun _ ↦
    (hI _ _ _ _).bind fun _ ↦ hF _ _).mono (by omega)

section Wpb

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- The adversary then the challenges of its root (`runWithChallenge`), `H` as queries. -/
noncomputable def rwcX (ck : Unit × Crs) :
    OracleComp (WSpec + XS) (((Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) × MembershipChallenge) := do
  let out ← advX r ps A ck
  let l ← liftL (HasQuery.query (spec := (Common.DigestBytes →ₒ MembershipChallenge)) (m := OracleComp WSpec) out.1.1)
  pure (out, l)

theorem simulateRom_runWithChallenge_eq (h : HTab) (ck : Unit × Crs) :
    simulateRom (runWithChallenge (advH r ps A h) ck) =
      simulateQ (col h) ((simulateQ (extImpl ((Common.DigestBytes →ₒ MembershipChallenge).romImpl)) (rwcX r ps A ck)).run' ∅) := by
  have e : runWithChallenge (advH r ps A h) ck = simulateQ (col h) (rwcX r ps A ck) := by
    simp only [rwcX, simulateQ_bind, simulateQ_col_liftL, ← advH_eq]
    rfl
  rw [simulateRom, simulateRomWithCache, e, StateT.run'_eq, StateT.run'_eq, run_simulateQ_col_ext,
    simulateQ_map]
  rfl

/-- The vector, position, cell and opening of Wagner's weak-position-binding reduction from a run. -/
def wTup [NeZero r] (crs : Crs)
    (p : ((Common.DigestBytes × Proof) × List (Fin (r * 128) × Cell × CellOpening)) ×
        MembershipChallenge) :
    (Fin (r * 128) → Cell) × Fin (r * 128) × Cell × CellOpening :=
  match p.1.2.find? (fun q ↦ decide (q.2.1 ≠ ext crs ((), p.1.1.1, p.2) p.1.1.2 q.1)) with
  | some q => (ext crs ((), p.1.1.1, p.2) p.1.1.2, q.1, q.2.1, q.2.2)
  | none => (ext crs ((), p.1.1.1, p.2) p.1.1.2, 0, ext crs ((), p.1.1.1, p.2) p.1.1.2 0, default)

theorem wpbReduction_eq [NeZero r] (h : HTab) :
    wpbReduction (argH r ps (Hh h)) ext (advH r ps A h) () = (ps.setup >>= fun crs ↦
      simulateRom (runWithChallenge (advH r ps A h) ((), crs)) >>= fun p ↦
        pure (wTup r ext crs p)) := by
  simp only [wpbReduction, argH]
  congr 1
  funext crs
  congr 1
  funext p
  obtain ⟨⟨com, ops⟩, l⟩ := p
  simp only [wTup]
  split <;> next heq => simp only [heq]

/-- **Wagner's weak-position-binding collision search with `H` as queries.** -/
noncomputable def wpbX [NeZero r] : OracleComp (unifSpec + XS) (List UInt8 × List UInt8) := do
  let crs ← liftL ps.setup
  let p ← (simulateQ (extImpl ((Common.DigestBytes →ₒ MembershipChallenge).romImpl)) (rwcX r ps A ((), crs))).run' ∅
  let t := wTup r ext crs p
  wpbColX r t.1 t.2.1 t.2.2.1 t.2.2.2

/-- Its hash calls. -/
abbrev wpbCalls (r Q : ℕ) : ℕ :=
  Q + 1 + (openCalls r + (8 + logPaddedRowCount r + 1) + (7 + logPaddedRowCount r + 1) + 2 * (9 + logPaddedRowCount r))

theorem isWeightBound_wpbX [NeZero r] (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (wpbX r ps ext A) xCalls (wpbCalls r Q) := by
  refine ((isWeightBound_liftL _).bind fun crs ↦
    (?_ : QueryCostAtMost _ xCalls (wpbCalls r Q))).mono (by omega)
  have hr : QueryCostAtMost (rwcX r ps A ((), crs)) xCalls (Q + 1) :=
    ((isWeightBound_advX r ps A Q hQ _).bind fun _ ↦ (isWeightBound_liftL _).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (by omega)
  have hrun := isWeightBound_run_simulateQ
    (extImpl (Ψ := unifSpec) ((Common.DigestBytes →ₒ MembershipChallenge).romImpl)) xCalls xCalls
    (isWeightBound_extImpl _) hr (∅ : (Common.DigestBytes →ₒ MembershipChallenge).QueryCache)
  rw [StateT.run'_eq]
  exact (isWeightBound_map _ hrun).bind fun p ↦ isWeightBound_wpbColX r _ _ _ _

theorem prEvent_pure_le {x y : Bool} (h : x = true → y = true) :
    Pr{let b ← (pure x : ProbComp Bool)}[b = true] ≤ Pr{let b ← (pure y : ProbComp Bool)}[b = true] := by
  simp only [prEvent_pure]
  split_ifs <;> simp_all

/-- The pair Wagner's weak-position-binding reduction compares. -/
def wpbPair (H : List UInt8 → Common.DigestBytes) (t : (Fin (r * 128) → Cell) × Fin (r * 128) × Cell × CellOpening) :
    List UInt8 × List UInt8 :=
  openingsCollision H r t.2.1 t.2.2.1 t.2.2.2 (t.1 t.2.1) (openCellWithHash H t.1 t.2.1)

/-- **Wagner's weak-position-binding collision term is a birthday bound**: at most
`(N + 2)² / 2^256` for the `N = wpbCalls r Q` hash calls of the search, for an RPM adversary of
`Q` permutation calls. -/
theorem wpbColl_le [NeZero r] (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= wpbCollExpH r ps ext A}[b = true] ≤
      ((wpbCalls r Q + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  have hpt : ∀ h : HTab, Pr{let b ← wpbCollExpH r ps ext A h}[b = true] ≤
      Pr{let b ← simulateQ (col h) (wpbX r ps ext A >>= finalCheck)}[b = true] := by
    intro h
    have hL : wpbCollExpH r ps ext A h = (ps.setup >>= fun crs ↦
        simulateRom (runWithChallenge (advH r ps A h) ((), crs)) >>= fun p ↦
          pure (decide ((wpbPair r (Hh h) (wTup r ext crs p)).1 ≠ (wpbPair r (Hh h) (wTup r ext crs p)).2) &&
            decide (Hh h (wpbPair r (Hh h) (wTup r ext crs p)).1 =
              Hh h (wpbPair r (Hh h) (wTup r ext crs p)).2))) := by
      simp only [wpbCollExpH, hashCollisionExp, merkleCollider,
        VectorCommitment.WeakPosBindingAdv.toPosBindingAdv, wpbReduction_eq, bind_assoc, pure_bind]
      rfl
    have hR : simulateQ (col h) (wpbX r ps ext A >>= finalCheck) = (ps.setup >>= fun crs ↦
        simulateRom (runWithChallenge (advH r ps A h) ((), crs)) >>= fun p ↦
          pure (decide (shortP (wpbPair r (Hh h) (wTup r ext crs p)).1 ∧
              shortP (wpbPair r (Hh h) (wTup r ext crs p)).2) &&
            (decide ((wpbPair r (Hh h) (wTup r ext crs p)).1 ≠ (wpbPair r (Hh h) (wTup r ext crs p)).2) &&
              decide (Hh h (wpbPair r (Hh h) (wTup r ext crs p)).1 =
                Hh h (wpbPair r (Hh h) (wTup r ext crs p)).2)))) := by
      simp only [wpbX, bind_assoc, simulateQ_bind, simulateQ_col_liftL,
        simulateRom_runWithChallenge_eq]
      congr 1
      funext crs
      congr 1
      funext p
      rw [wpbColX_eval, pure_bind, simulateQ_col_finalCheck]
      rfl
    rw [hL, hR]
    refine prEvent_bind_mono' _ _ _ _ fun crs ↦ prEvent_bind_mono' _ _ _ _ fun p ↦ ?_
    refine prEvent_pure_le fun hc ↦ ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
    exact ⟨shortP_openingsCollision _ _ _ _ _ _ hc.1, hc⟩
  exact (prEvent_bind_mono' _ _ _ _ hpt).trans
    (prob_collision_le _ _ (isWeightBound_wpbX r ps ext A Q hQ))

end Wpb

end LeanDa
