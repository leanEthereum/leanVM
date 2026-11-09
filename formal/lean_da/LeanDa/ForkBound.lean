module

public import LeanDa.AdvX
public import LeanDa.WithHash

@[expose] public section

/-!
# The collision term of Wagner's forking reduction, bounded

Benedikt Wagner's forking reduction (`forkCollisionReduction`) runs the committed-soundness
adversary twice by the replay fork and, when the two runs extract different vectors committing to
one root, opens both at a position where they differ; `forkCollExpH` is the probability that the
two openings' climbs collide under the hash of a uniformly random table `h`. With `H` left as
queries (`forkX`, `Z₂`), the experiment for `h` is this computation answered by `h`
(`forkCollExpH_le_col`): the fork commutes with answering `H` by `h` (`contextFork_collapse`), so
both runs see the same `h`. The fork makes at most twice the queries of one run
(`isQueryBoundP_contextFork`), each run at most `Q + 1` for the adversary and `256 · nPad r`
for the commitment its win checks, and the openings and climbs at most `512 · nPad r + 4 d + 6`
more (`d = 7 + logPad r`). So the term is at most `(N + 2)² / 2^256` for
`N = 2 Q + 1024 · nPad r + 4 d + 8` (`forkColl_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: it bounds his
forking collision term.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex LeanDa.Fork PFunctor PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open PqDas.CommittedSoundness
open scoped ENNReal

namespace LeanDa

section Fork

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- Wagner's reduction to committed soundness (`csReduction`) with `H` as queries. -/
noncomputable def csX (ckVC : Unit) : OracleComp (WSpec + XS) (Common.DigestBytes × (Fin (r * 128) → Cell)) := do
  let crs ← liftL (liftM ps.setup : OracleComp WSpec Crs)
  let out ← advX r ps A (ckVC, crs)
  let l ← liftL (HasQuery.query (spec := (Common.DigestBytes →ₒ MembershipChallenge)) (m := OracleComp WSpec) out.1.1)
  pure (out.1.1, ext crs (ckVC, out.1.1, l) out.1.2)

theorem csReduction_eq (h : HTab) (ckVC : Unit) :
    csReduction (argH r ps (Hh h)) ext (advH r ps A h) ckVC = simulateQ (col h) (csX r ps ext A ckVC) := by
  simp only [csX, simulateQ_bind, simulateQ_col_liftL, ← advH_eq]
  rfl

/-- The wrapped adversary of the fork (`wrappedAdv`) with `H` as queries. -/
noncomputable def wrX : OracleComp (WSpec + XS) (Common.DigestBytes × (Fin (r * 128) → Cell) × MembershipChallenge) := do
  let out ← csX r ps ext A ()
  let l ← liftL (HasQuery.query (spec := (Common.DigestBytes →ₒ MembershipChallenge)) (m := OracleComp WSpec) out.1)
  pure (out.1, out.2, l)

theorem wrappedAdv_eq (h : HTab) :
    wrappedAdv (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) () =
      simulateQ (col h) (wrX r ps ext A) := by
  simp only [wrX, simulateQ_bind, simulateQ_col_liftL, ← csReduction_eq]
  rfl

/-- The win of a run of the fork (`winOn`) with `H` as queries. -/
noncomputable def winX (out : Common.DigestBytes × (Fin (r * 128) → Cell) × MembershipChallenge) :
    OracleComp (wrappedSpec MembershipChallenge + XS) Bool := do
  let root ← commitCellsMWithHash hS out.2.1
  pure (decide (out.2.1 ∉ (leanDaErasureCode r).code) && (checker r).check out.2.2 out.2.1 && decide (root = out.1))

theorem winX_eval (h : HTab) (out : Common.DigestBytes × (Fin (r * 128) → Cell) ×
    MembershipChallenge) :
    simulateQ (col h) (winX r out) = pure (winOn (leanDaErasureCode r) (merkleVC r (Hh h)) (checker r) () out) := by
  rw [winX, simulateQ_bind, commitCellsM_eval (fun x ↦ simulateQ (col h) x) (fun a ↦ rfl)
    (fun x f ↦ simulateQ_bind _ x f) hS (Hh h) (simulateQ_col_hS h), pure_bind]
  rfl

/-- **A run of the fork** (`runTrace`) with `H` as queries. -/
noncomputable def mainX : OracleComp (wrappedSpec MembershipChallenge + XS) (Trace Cell (r * 128) Common.DigestBytes MembershipChallenge) := do
  let p ← (simulateQ (extImpl (unifForward Common.DigestBytes MembershipChallenge + roImpl Common.DigestBytes MembershipChallenge))
    (wrX r ps ext A)).run (∅, [])
  let w ← winX r p.1
  pure { com := p.1.1, vec := p.1.2.1, chal := p.1.2.2, roCache := p.2.1, queryLog := p.2.2, win := w }

theorem runTrace_eq (h : HTab) :
    runTrace (leanDaErasureCode r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) () = simulateQ (col h) (mainX r ps ext A) := by
  rw [runTrace, wrappedAdv_eq, run_simulateQ_col_ext, mainX, simulateQ_bind]
  congr 1
  funext p
  rw [simulateQ_bind, winX_eval, pure_bind]
  rfl

/-- The fork's query budgets, with no budget for `XS`. -/
def qbX (Q : ℕ) : ((ℕ ⊕ Unit) ⊕ HDom) → ℕ
  | .inl (.inl _) => 0
  | .inl (.inr ()) => Q + 1
  | .inr _ => 0

/-- **The fork and its two vectors** (`forkVecPair`) with `H` as queries. -/
noncomputable def forkX (Q : ℕ) :
    OracleComp (wrappedSpec MembershipChallenge + XS) ((Fin (r * 128) → Cell) × (Fin (r * 128) →
        Cell)) :=
  contextFork (mainX r ps ext A) (qbX Q) (.inl (.inr ())) (forkPoint (Q + 1)) >>= fun o ↦
    match o with
    | some (x₁, x₂) => pure (x₁.vec, x₂.vec)
    | none => pure (fun _ ↦ default, fun _ ↦ default)

theorem forkVecPair_eq (h : HTab) (Q : ℕ) :
    forkVecPair (leanDaErasureCode r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1) () =
      simulateQ (col h) (forkX r ps ext A Q) := by
  rw [forkVecPair, runTrace_eq, forkX, simulateQ_bind]
  change contextFork (simulateQ (col h) (mainX r ps ext A)) (fun i ↦ qbX Q (.inl i)) (Sum.inr ())
    (forkPoint (Q + 1)) >>= _ = _
  erw [contextFork_collapse h (mainX r ps ext A) (qbX Q) (Sum.inr ()) (forkPoint (Q + 1))]
  congr 1
  funext o
  rcases o with _ | ⟨x₁, x₂⟩ <;> rfl

/-- The fork's oracles answered by uniform sampling. -/
noncomputable abbrev forkI : QueryImpl (wrappedSpec MembershipChallenge) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    uniformSampleImpl (spec := ((Unit →ₒ MembershipChallenge) : OracleSpec Unit))

theorem forkCollisionReduction_eq (h : HTab) (Q : ℕ) :
    forkCollisionReduction (leanDaErasureCode r) (merkleVC r (Hh h)) (checker r)
      (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1) () =
      simulateQ (col h) (simulateQ (extI forkI) (forkX r ps ext A Q)) := by
  rw [forkCollisionReduction, forkVecPair_eq, simulateQ_col_extI]

end Fork

/-! ## The openings of two different vectors and their collision -/

theorem findCollision_self (H : List UInt8 → Common.DigestBytes) (l : List (List UInt8)) :
    findCollision H l l = ([], []) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [findCollision, ih]

/-- The two climbs Wagner's forking reduction compares, from two vectors. -/
def colPair (r : ℕ) [NeZero r] (H : List UInt8 → Common.DigestBytes)
    (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) : List UInt8 × List UInt8 :=
  if hv : vv.1 = vv.2 then ([], [])
  else
    let i := Fin.find (fun j ↦ vv.1 j ≠ vv.2 j) (Function.ne_iff.mp hv)
    openingsCollision H r i (vv.1 i) (openCellWithHash H vv.1 i) (vv.2 i) (openCellWithHash H vv.2 i)

/-- The climbs of two vectors' honest openings at a position, with `H` as queries. -/
def colPairAt (r : ℕ) (c c' : Fin (r * 128) → Cell) (i : Fin (r * 128)) :
    OracleComp (unifSpec + XS) (List UInt8 × List UInt8) := do
  let τ ← openCellM hS c i
  let τ' ← openCellM hS c' i
  let l₁ ← hashInputsM hS i (cellBytes (c i)) (τ.path.take (7 + logPaddedRowCount r))
  let l₂ ← hashInputsM hS i (cellBytes (c' i)) (τ'.path.take (7 + logPaddedRowCount r))
  findCollisionM hS l₁ (l₂.take (8 + logPaddedRowCount r))

/-- The same with `H` as queries. -/
def colPairX (r : ℕ) [NeZero r] (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) :
    OracleComp (unifSpec + XS) (List UInt8 × List UInt8) :=
  if hv : vv.1 = vv.2 then pure ([], [])
  else colPairAt r vv.1 vv.2 (Fin.find (fun j ↦ vv.1 j ≠ vv.2 j) (Function.ne_iff.mp hv))

theorem length_hashInputs (H : List UInt8 → Common.DigestBytes) (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (a : List UInt8), (hashInputs H idx a path).length = path.length + 1 := by
  induction path with
  | nil => intro idx a; rfl
  | cons s rest ih => intro idx a; simp [hashInputs, ih]

theorem mem_hashInputs (H : List UInt8 → Common.DigestBytes) (path : List Common.DigestBytes) :
    ∀ (idx : ℕ) (a : List UInt8) (x : List UInt8), x ∈ hashInputs H idx a path →
      x = a ∨ ∃ d₁ d₂, x = pairBytes d₁ d₂ := by
  induction path with
  | nil =>
    intro idx a x hx
    simp only [hashInputs, List.mem_cons, List.not_mem_nil, or_false] at hx
    exact Or.inl hx
  | cons s rest ih =>
    intro idx a x hx
    simp only [hashInputs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases ih _ _ x hx with rfl | h
      · split <;> exact Or.inr ⟨_, _, rfl⟩
      · exact Or.inr h

theorem shortP_of_mem_hashInputs (H : List UInt8 → Common.DigestBytes) (path : List Common.DigestBytes) (idx : ℕ)
    (x : Cell) (y : List UInt8) (hy : y ∈ hashInputs H idx (cellBytes x) path) :
    shortP y := by
  rcases mem_hashInputs H path idx _ y hy with rfl | ⟨d₁, d₂, rfl⟩
  · simp [shortP, length_cellBytes]
  · simp [shortP, length_pairBytes]

/-- **The climbs' colliding inputs are short.** -/
theorem shortP_colPair (r : ℕ) [NeZero r] (H : List UInt8 → Common.DigestBytes)
    (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell))
    (hne : (colPair r H vv).1 ≠ (colPair r H vv).2) :
    shortP (colPair r H vv).1 ∧ shortP (colPair r H vv).2 := by
  unfold colPair at hne ⊢
  split at hne
  · exact absurd rfl hne
  · next hv =>
    simp only [hv, ↓reduceDIte] at hne ⊢
    obtain ⟨h1, h2⟩ := findCollision_mem H _ _ hne
    exact ⟨shortP_of_mem_hashInputs H _ _ _ _ h1, shortP_of_mem_hashInputs H _ _ _ _ h2⟩

theorem colPairX_eval (r : ℕ) [NeZero r] (h : HTab)
    (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) :
    simulateQ (col h) (colPairX r vv) = pure (colPair r (Hh h) vv) := by
  have hp : ∀ {α} (a : α), simulateQ (col (Ψ := unifSpec) h) (pure a) = pure a := fun _ ↦ rfl
  have hb : ∀ {α β} (x : OracleComp (unifSpec + XS) α) (f : α → OracleComp (unifSpec + XS) β),
      simulateQ (col h) (x >>= f) = simulateQ (col h) x >>= fun a ↦ simulateQ (col h) (f a) :=
    fun x f ↦ simulateQ_bind _ x f
  unfold colPairX colPair
  split
  · rfl
  · simp only [colPairAt, hb, openCellM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
      hashInputsM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
      findCollisionM_eval (fun x ↦ simulateQ (col h) x) hp hb hS (Hh h) (simulateQ_col_hS h),
      pure_bind]
    congr 1
    have e1 : ∀ (c : Fin (r * 128) → Cell) (i : Fin (r * 128)),
        (openCellWithHash (Hh h) c i).path.take (7 + logPaddedRowCount r) = (openCellWithHash (Hh h) c i).path := fun c i ↦
      List.take_of_length_le (by simp [openCellWithHash, length_merklePath])
    simp only [openingsCollision, e1]
    rw [List.take_of_length_le (by rw [length_hashInputs]; simp [openCellWithHash, length_merklePath])]

section Fork2

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- **Wagner's forking collision experiment for the table `h`, as a function of the two vectors.** -/
theorem forkCollExpH_eq [NeZero r] (h : HTab) (Q : ℕ) :
    forkCollExpH r ps ext A Q h = (fun vv ↦ decide ((colPair r (Hh h) vv).1 ≠ (colPair r (Hh h) vv).2) &&
      decide (Hh h (colPair r (Hh h) vv).1 = Hh h (colPair r (Hh h) vv).2)) <$>
        forkCollisionReduction (leanDaErasureCode r) (merkleVC r (Hh h)) (checker r)
          (csReduction (argH r ps (Hh h)) ext (advH r ps A h)) (Q + 1) () := by
  simp only [forkCollExpH, hashCollisionExp, merkleCollider,
    VectorCommitment.CollisionAdv.toPosBindingAdv, bind_assoc, map_eq_bind_pure_comp]
  congr 1
  funext vv
  obtain ⟨v, v'⟩ := vv
  simp only [colPair]
  by_cases hv : v = v'
  · subst hv
    simp [merkleVC, openingsCollision, findCollision_self]
  · simp [merkleVC, hv]

end Fork2


/-! ## Queries of `H` -/

section Weight

variable {ι κ ιs : Type} {Ψ : OracleSpec ι} {spec : OracleSpec ιs} {σ α : Type}

theorem isWeightBound_extImpl (impl : QueryImpl spec (StateT σ (OracleComp Ψ)))
    (t : (spec + XS).Domain) (s : σ) :
    QueryCostAtMost (((extImpl impl) t).run s) xCalls (xCalls t) := by
  rcases t with t | x
  · exact isWeightBound_liftL _
  · exact isWeightBound_map _ (isWeightBound_query (spec := Ψ + XS) xCalls (.inr x))

theorem isWeightBound_extI (I : QueryImpl spec (OracleComp Ψ)) (t : (spec + XS).Domain) :
    QueryCostAtMost ((extI I) t) xCalls (xCalls t) := by
  rcases t with t | x
  · exact isWeightBound_liftL _
  · exact isWeightBound_query (spec := Ψ + XS) xCalls (.inr x)

theorem isWeightBound_iff_isQueryBoundP {oa : OracleComp (Ψ + XS) α} {N : ℕ} :
    QueryCostAtMost oa xCalls N ↔ IsQueryBoundP oa (fun j ↦ j.isRight = true) N :=
  isQueryBound_congr (fun t b ↦ by rcases t with t | x <;> simp [xCalls]; omega)
    (fun t b ↦ by rcases t with t | x <;> simp [xCalls])

end Weight

section Fork3

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)
  (A : CodeBindingAdvB r Crs Proof)

/-- The hash calls of an honest opening over `H` as queries (at most). -/
abbrev openCalls (r : ℕ) : ℕ := 256 * paddedRowCount r

/-- The hash calls of the commitment over `H` as queries (at most). -/
abbrev commitCalls (r : ℕ) : ℕ := 256 * paddedRowCount r

set_option maxRecDepth 4000 in
theorem isWeightBound_commitCellsM_hS {ι : Type} {Ψ : OracleSpec ι} (c : Fin (r * 128) → Cell) :
    QueryCostAtMost (commitCellsMWithHash (hS (Ψ := Ψ)) c) xCalls (commitCalls r) := by
  have := isWeightBound_commitCellsM (hS (Ψ := Ψ)) xCalls 1 1
    (fun a b ↦ isWeightBound_hS (Ψ := Ψ) (pairBytes a b))
    (fun x ↦ isWeightBound_hS (Ψ := Ψ) (cellBytes x)) c
  exact this.mono (le_of_eq (by ring))

set_option maxRecDepth 4000 in
theorem isWeightBound_openCellM_hS {ι : Type} {Ψ : OracleSpec ι} (c : Fin (r * 128) → Cell)
    (i : Fin (r * 128)) : QueryCostAtMost (openCellM (hS (Ψ := Ψ)) c i) xCalls (openCalls r) := by
  have := isWeightBound_openCellM (hS (Ψ := Ψ)) xCalls 1 1
    (fun a b ↦ isWeightBound_hS (Ψ := Ψ) (pairBytes a b))
    (fun x ↦ isWeightBound_hS (Ψ := Ψ) (cellBytes x)) c i
  rwa [show paddedRowCount r * (128 * 1 + 128 * 1) = openCalls r by unfold openCalls; ring] at this

theorem isWeightBound_winX (out : Common.DigestBytes × (Fin (r * 128) → Cell) ×
    MembershipChallenge) :
    QueryCostAtMost (winX r out) xCalls (commitCalls r) := by
  have := (isWeightBound_commitCellsM_hS r (Ψ := wrappedSpec MembershipChallenge) out.2.1).bind
    fun root ↦ isWeightBound_pure (spec := wrappedSpec MembershipChallenge + XS)
      (decide (out.2.1 ∉ (leanDaErasureCode r).code) && (checker r).check out.2.2 out.2.1 &&
        decide (root = out.1)) xCalls 0
  exact this

theorem isWeightBound_mainX (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (mainX r ps ext A) xCalls (Q + 1 + commitCalls r) := by
  have hcs : QueryCostAtMost (csX r ps ext A ()) xCalls (Q + 1) :=
    ((isWeightBound_liftL _).bind fun _ ↦ (isWeightBound_advX r ps A Q hQ _).bind fun _ ↦
      (isWeightBound_liftL _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by omega)
  have hwr : QueryCostAtMost (wrX r ps ext A) xCalls (Q + 1) :=
    (hcs.bind fun _ ↦ (isWeightBound_liftL _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by omega)
  have hrun := isWeightBound_run_simulateQ
    (extImpl (Ψ := wrappedSpec MembershipChallenge) (unifForward Common.DigestBytes MembershipChallenge + roImpl Common.DigestBytes MembershipChallenge))
    xCalls xCalls (isWeightBound_extImpl _) hwr
    (((∅ : (Common.DigestBytes →ₒ MembershipChallenge).QueryCache), ([] : List Common.DigestBytes)) : SimState Common.DigestBytes MembershipChallenge)
  exact (hrun.bind fun p ↦ ((isWeightBound_winX r p.1).bind fun w ↦
    isWeightBound_pure _ _ 0)).mono le_rfl

theorem isWeightBound_colPairAt (c c' : Fin (r * 128) → Cell) (i : Fin (r * 128)) :
    QueryCostAtMost (colPairAt r c c' i) xCalls
      (2 * openCalls r + 2 * (7 + logPaddedRowCount r + 1) + 2 * (9 + logPaddedRowCount r)) := by
  have hI : ∀ idx a (path : List Common.DigestBytes), QueryCostAtMost
      (hashInputsM (hS (Ψ := unifSpec)) idx a (path.take (7 + logPaddedRowCount r))) xCalls
        (7 + logPaddedRowCount r + 1) :=
    fun idx a path ↦ (isWeightBound_hashInputsM (hS (Ψ := unifSpec)) xCalls
      (fun _ ↦ isWeightBound_hS _) _ idx a).mono (by simp only [List.length_take]; omega)
  have hF : ∀ l₁ (l₂ : List (List UInt8)), QueryCostAtMost
      (findCollisionM (hS (Ψ := unifSpec)) l₁ (l₂.take (8 + logPaddedRowCount r)))
        xCalls (2 * (9 + logPaddedRowCount r)) :=
    fun l₁ l₂ ↦ (isWeightBound_findCollisionM (hS (Ψ := unifSpec)) xCalls
      (fun _ ↦ isWeightBound_hS _) l₁ _).mono (by simp only [List.length_take]; omega)
  unfold colPairAt
  exact ((isWeightBound_openCellM_hS r c i).bind fun _ ↦ (isWeightBound_openCellM_hS r c' i).bind
    fun _ ↦ (hI _ _ _).bind fun _ ↦ (hI _ _ _).bind fun _ ↦ hF _ _).mono (by omega)

theorem isWeightBound_colPairX [NeZero r] (vv : (Fin (r * 128) → Cell) × (Fin (r * 128) → Cell)) :
    QueryCostAtMost (colPairX r vv) xCalls
      (2 * openCalls r + 2 * (7 + logPaddedRowCount r + 1) + 2 * (9 + logPaddedRowCount r)) := by
  unfold colPairX
  split
  · exact isWeightBound_pure _ _ _
  · exact isWeightBound_colPairAt r _ _ _

/-- **The forking reduction's collision search with `H` as queries.** -/
noncomputable def forkZ [NeZero r] (Q : ℕ) :
    OracleComp (unifSpec + XS) (List UInt8 × List UInt8) :=
  simulateQ (extI forkI) (forkX r ps ext A Q) >>= colPairX r

/-- Its hash calls. -/
abbrev forkCalls (r Q : ℕ) : ℕ :=
  2 * (Q + 1 + commitCalls r) + (2 * openCalls r + 2 * (7 + logPaddedRowCount r + 1) + 2 * (9 + logPaddedRowCount r))

theorem isWeightBound_forkZ [NeZero r] (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    QueryCostAtMost (forkZ r ps ext A Q) xCalls (forkCalls r Q) := by
  have hm := isWeightBound_iff_isQueryBoundP.mp (isWeightBound_mainX r ps ext A Q hQ)
  have hf := isWeightBound_iff_isQueryBoundP.mpr
    (isQueryBoundP_contextFork _ (mainX r ps ext A) (qbX Q) (.inl (.inr ())) (forkPoint (Q + 1)) _ hm)
  have hX : QueryCostAtMost (forkX r ps ext A Q) xCalls (2 * (Q + 1 + commitCalls r)) := by
    refine (hf.bind fun o ↦ (?_ : QueryCostAtMost _ xCalls 0)).mono (by omega)
    rcases o with _ | ⟨x₁, x₂⟩ <;> exact isWeightBound_pure _ _ _
  exact (isWeightBound_simulateQ _ xCalls xCalls (isWeightBound_extI forkI) hX).bind fun vv ↦
    isWeightBound_colPairX r vv

theorem prEvent_bind_mono' {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β) (P : β → Prop)
    (h : ∀ x, Pr{let y ← f x}[P y] ≤ Pr{let y ← g x}[P y]) :
    Pr{let y ← mx >>= f}[P y] ≤ Pr{let y ← mx >>= g}[P y] := by
  simpa using Common.prEvent_bind_le_add_const mx f g P P 0 (fun x ↦ by simpa using h x)

/-- **Wagner's forking collision term is a birthday bound**: at most `(N + 2)² / 2^256` for the
`N = forkCalls r Q` hash calls of the forked search, for an RPM adversary of `Q` permutation
calls. -/
theorem forkColl_le [NeZero r] (Q : ℕ) (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) :
    Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= forkCollExpH r ps ext A Q}[b = true] ≤
      ((forkCalls r Q + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  have hpt : ∀ h : HTab, Pr{let b ← forkCollExpH r ps ext A Q h}[b = true] ≤
      Pr{let b ← simulateQ (col h) (forkZ r ps ext A Q >>= finalCheck)}[b = true] := by
    intro h
    have e : ∀ vv, simulateQ (col h) (colPairX r vv >>= finalCheck) =
        pure (decide (shortP (colPair r (Hh h) vv).1 ∧ shortP (colPair r (Hh h) vv).2) &&
          (decide ((colPair r (Hh h) vv).1 ≠ (colPair r (Hh h) vv).2) &&
            decide (Hh h (colPair r (Hh h) vv).1 = Hh h (colPair r (Hh h) vv).2))) := fun vv ↦ by
      rw [simulateQ_bind, colPairX_eval, pure_bind, simulateQ_col_finalCheck]
    have e2 : simulateQ (col h) (forkZ r ps ext A Q >>= finalCheck) =
        simulateQ (col h) (simulateQ (extI forkI) (forkX r ps ext A Q)) >>= fun vv ↦
          simulateQ (col h) (colPairX r vv >>= finalCheck) := by
      rw [forkZ, bind_assoc, simulateQ_bind]
    rw [e2, forkCollExpH_eq, forkCollisionReduction_eq, prEvent_map]
    simp only [e]
    rw [bind_pure_comp, prEvent_map]
    refine prEvent_mono _ _ _ fun vv hv ↦ ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
    exact ⟨shortP_colPair r (Hh h) vv hv.1, hv⟩
  exact (prEvent_bind_mono' _ _ _ _ hpt).trans
    (prob_collision_le _ _ (isWeightBound_forkZ r ps ext A Q hQ))

end Fork3

end LeanDa
