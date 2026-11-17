/-
  LeanVM.Protocol.EndToEnd.Sound.CutXrun

  The cut verifier's extracted run: wherever the ghost verifier's run returns, the cut's run from
  the same state returns the same value.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.CutRun
public import LeanVM.Protocol.EndToEnd.Sound.Extractor
public import LeanVM.Protocol.Compile.Rom.Replay

/-!
# The cut verifier's run

`XCut H F p q`: wherever the extracted run of `p` (`xrun`, with the hash and permutation answers
`H`, `F`) returns a value, the extracted run of `q` from the same state and history returns it
too, with a history the first one extends by no commitment. Like `CutRel` it passes through a
common prefix program (`XCut.bind`) and a final return (`XCut.mapRet`), so the cut levels
(`xcut_whirLevelsGF`; the final level's rest opens rows but commits nothing, `NoCommitQ`) give
the cut verifier (`xcut_leanVmProgramG`).

`replayU_cut`: so the replay of the cut (`Rom.replayU`) on permutation answers agreeing with the
run's on its inputs returns the ghost verifier's value, at the extracted run's state, whose roots
hold the commitments of the ghost's whole history (`commits_cut`).
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
  LeanVM.Protocol.KeccakHash

@[expose] public section

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-! ## Programs without commitments -/

/-- No commitment on any path (openings allowed). -/
def NoCommitQ {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoCommitQ (k x)
  | .sample k => ∀ c, NoCommitQ (k c)
  | .grind _ k => NoCommitQ k
  | .commit _ _ _ => False
  | .query _ _ k => ∀ rows, NoCommitQ (k rows)

theorem NoCommitQ.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : NoCommitQ p) (hf : ∀ a, NoCommitQ (f a)) : NoCommitQ (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit _ _ _ _ => exact hp.elim
  | query _ _ k ih => exact fun rows ↦ ih rows (hp rows)

/-- **A history along a program without commitments commits nothing.** -/
theorem NoCommitQ.commits_nil {α : Type} :
    ∀ {p : VerifierProgram α} {h : List Ev} {q : VerifierProgram α},
      NoCommitQ p → p.after h = some q → commits h = []
  | _, [], _, _, _ => rfl
  | .ret _, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .fail, _ :: _, _, _, ha => by simp [VerifierProgram.after] at ha
  | .read k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    exact NoCommitQ.commits_nil (h := es) (hp _) ha
  | .sample k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    exact NoCommitQ.commits_nil (h := es) (hp _) ha
  | .grind b k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    split at ha
    · exact NoCommitQ.commits_nil (p := k) (h := es) hp ha
    · simp at ha
  | .commit _ _ _, _, _, hp, _ => hp.elim
  | .query _ _ k, e :: es, _, hp, ha => by
    cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    exact NoCommitQ.commits_nil (h := es) (hp _) ha

theorem noCommitQ_readScalars : ∀ n, NoCommitQ (VerifierProgram.readScalars n)
  | 0 => trivial
  | n + 1 => by
    unfold VerifierProgram.readScalars
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦
      NoCommitQ.bind (noCommitQ_readScalars n) fun _ ↦ trivial

theorem noCommitQ_grindProofOfWork (b : ℕ) : NoCommitQ (VerifierProgram.grindProofOfWork b) := by
  unfold VerifierProgram.grindProofOfWork
  split <;> trivial

theorem noCommitQ_require (c : Prop) [Decidable c] : NoCommitQ (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split <;> trivial

theorem noCommitQ_sumcheck (claim : E) (count : ℕ) :
    ∀ eqs : List (Option E), NoCommitQ (sumcheck claim count eqs) := by
  intro eqs
  induction eqs generalizing claim with
  | nil => trivial
  | cons e eqs ih =>
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommitQ.bind ?_ fun _ ↦ NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦
      NoCommitQ.bind (ih _) fun _ ↦ trivial
    cases e <;> unfold sumcheckRoundPoly <;> simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    · exact NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦ NoCommitQ.bind (noCommitQ_readScalars _)
        fun _ ↦ NoCommitQ.bind (noCommitQ_grindProofOfWork _) fun _ ↦ trivial
    · exact NoCommitQ.bind (noCommitQ_readScalars _) fun _ ↦
        NoCommitQ.bind (noCommitQ_grindProofOfWork _) fun _ ↦ trivial

theorem noCommitQ_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ), NoCommitQ (sampleQueriesAux depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    split
    · trivial
    · exact NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦
        NoCommitQ.bind (noCommitQ_sampleQueriesAux depth fuel _) fun _ ↦ trivial

/-- **The rest of the final level commits nothing.** -/
theorem noCommitQ_finRest (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) (tr : WhirTrace) :
    NoCommitQ ((finRest logN laneFolds eb index level s rounds tr).bind fun _ ↦
      VerifierProgram.ret tr) := by
  refine NoCommitQ.bind ?_ fun _ ↦ trivial
  cases tr with
  | mid => trivial
  | final _ folded =>
    simp only [finRest, finalTailRest, VerifierProgram.bind_eq]
    exact NoCommitQ.bind (noCommitQ_grindProofOfWork _) fun _ ↦ NoCommitQ.bind
      (NoCommitQ.bind (noCommitQ_sampleQueriesAux _ _ _) fun _ ↦
        NoCommitQ.bind (fun _ ↦ trivial) fun _ ↦ noCommitQ_require _) fun _ ↦
      NoCommitQ.bind (noCommitQ_sumcheck _ _ _) fun _ ↦ noCommitQ_require _

/-! ## The cut on runs -/

/-- **`q` cuts `p` on runs**: wherever `p`'s extracted run returns a value, `q`'s does, with a
history that `p`'s extends by no commitment. -/
def XCut {α : Type} (p q : VerifierProgram α) : Prop :=
  ∀ s h a s' hist, xrun H F p s h = some (a, s', hist) → ∃ s₁ h₁,
    xrun H F q s h = some (a, s₁, h₁) ∧ ∃ l, hist = h₁ ++ l ∧ commits l = []

variable {H F}

theorem XCut.bind {α β : Type} (p : VerifierProgram α) {f g : α → VerifierProgram β}
    (hfg : ∀ a, XCut H F (f a) (g a)) : XCut H F (p.bind f) (p.bind g) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨s₁, h₁, hg, hl⟩ := hfg r.1 _ _ _ _ _ hf
  exact ⟨s₁, h₁, by rw [hr, Option.bind_some, hg], hl⟩

theorem XCut.mapRet {α β : Type} {p q : VerifierProgram α} (hpq : XCut H F p q) (w : α → β) :
    XCut H F (p.bind fun a ↦ VerifierProgram.ret (w a)) (q.bind fun a ↦ VerifierProgram.ret (w a)) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, -, rfl⟩ := hf
  obtain ⟨s₁, h₁, hq, hl⟩ := hpq _ _ _ _ _ hr
  exact ⟨s₁, h₁, by rw [hq, Option.bind_some]; rfl, hl⟩

/-- The full final step's run returns where the cut's does, with the same trace. -/
theorem xcut_fin (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) :
    XCut H F (finFull logN laneFolds eb index level s rounds) (finCut logN index level s rounds) := by
  intro st h a s' hist hx
  rw [finFull_eq, xrun_bind] at hx
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨l, hl, hafter, -⟩ := xrun_after H F _ _ _ hf
  have hr1 : r.1 = a := by
    have := hafter
    obtain ⟨u, m₁, m₂, -, -, hret⟩ := after_bind_ret this
    exact (after_ret_eq' hret).2
  subst hr1
  exact ⟨r.2.1, r.2.2, hr, l, hl, (noCommitQ_finRest logN laneFolds eb index level s rounds r.1).commits_nil hafter⟩

/-- **The cut levels' run** returns where the full levels' does. -/
theorem xcut_whirLevelsGF (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      XCut H F (whirLevelsGF logN (finFull logN laneFolds eb) index levels s)
        (whirLevelsGF logN (finCut logN) index levels s)
  | _, [], _ => fun _ _ _ _ _ hx ↦ by simp [whirLevelsGF, xrun] at hx
  | index, [level], s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    exact XCut.bind _ fun r ↦ xcut_fin logN laneFolds eb index level r.1 r.2
  | index, level :: next :: rest, s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    refine XCut.bind _ fun r ↦ ?_
    rw [midTailC_eq_pre, midTailC_eq_pre]
    exact XCut.bind _ fun p ↦
      (xcut_whirLevelsGF logN laneFolds eb (index + 1) (next :: rest) p.2).mapRet
        fun tr ↦ WhirTrace.mid r.2 p.1 tr

theorem xcut_verifyStackedOpeningG (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    XCut H F (verifyStackedOpeningG stackLog logInvRate claims)
      (verifyStackedOpeningCut stackLog logInvRate claims) := by
  refine XCut.bind _ fun _ ↦ XCut.bind _ fun c ↦ ?_
  unfold verifyWhirG verifyWhirCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun config ↦ ?_
  rw [whirLevelsG_eq]
  exact xcut_whirLevelsGF _ _ _ _ _ _

theorem xcut_veBodyG (ev : List K → List E → E → VerifierProgram Unit) (publicInput : Digest)
    (layout : Verifier.Layout) (ρ : ℕ) :
    XCut H F (veBodyG ev publicInput layout ρ) (veBodyCut ev publicInput layout ρ) := by
  unfold veBodyG veBodyCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun _ ↦ XCut.bind _ fun ood ↦ XCut.bind _ fun r ↦ ?_
  obtain ⟨cl, kp, ks⟩ := r
  refine XCut.bind _ fun y ↦ ?_
  obtain ⟨t, w⟩ := y
  exact xcut_verifyStackedOpeningG _ _ _

/-- **The cut verifier's run** returns where the ghost verifier's does. -/
theorem xcut_leanVmProgramG (bytecode : List K) (pd : Digest) :
    XCut H F (leanVmProgramG bytecode pd) (leanVmProgramCut bytecode pd) :=
  (XCut.bind _ fun (a : Verifier.Layout × ℕ) ↦ (xcut_veBodyG _ pd a.1 a.2).mapRet
    fun tr ↦ (a, tr)).mapRet fun d ↦ (true, d)

/-! ## The replay of the cut -/

/-- An accepting extracted run of the verifier is one of the ghost verifier, with its data. -/
theorem xrun_leanVmProgramG {bytecode : List K} {pd : Digest} {s : VerifierProgramState}
    {h : List Ev} {s' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (leanVmVerifierProgram bytecode pd) s h = some (true, s', hist)) :
    ∃ d, xrun H F (leanVmProgramG bytecode pd) s h = some ((true, d), s', hist) := by
  rw [← leanVmProgramG_eq, xrun_bind] at hx
  obtain ⟨⟨⟨b, d⟩, s₁, h₁⟩, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  exact ⟨d, hr⟩

/-- **The replay of the cut returns the ghost verifier's value**: where the ghost verifier's
extracted run returns, the cut's returns the same value, and so does the replay of the cut on
permutation answers agreeing with `F` on its inputs, at the cut run's state; that state's roots
hold the commitments of the ghost's whole history. -/
theorem replayU_cut {F' : KeccakState → Option KeccakState} {bytecode : List K} {pd : Digest}
    {s : VerifierProgramState} {h : List Ev} {a : Bool × ((Verifier.Layout × ℕ) × WhirTrace)}
    {s' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (leanVmProgramG bytecode pd) s h = some (a, s', hist))
    (hR : RootsInv H s h)
    (hF : ∀ x ∈ replayIn F (leanVmProgramCut bytecode pd) s, F' x = F x) :
    ∃ s₁ h₁, xrun H F (leanVmProgramCut bytecode pd) s h = some (a, s₁, h₁) ∧
      replayU F' (leanVmProgramCut bytecode pd) s = some (a, s₁) ∧
      commits hist = s₁.roots.map fun r ↦ (r.2.1, r.2.2, extract H r.1 r.2.1 r.2.2) := by
  obtain ⟨s₁, h₁, hc, l, rfl, hl⟩ := xcut_leanVmProgramG bytecode pd s h a s' hist hx
  refine ⟨s₁, h₁, hc, ?_, ?_⟩
  · rw [replayU_congr _ _ hF]
    exact replayU_of_xrun H F _ _ _ hc
  · rw [commits_append, hl, List.append_nil]
    exact xrun_rootsInv H F _ _ _ hR hc

end
end LeanVM.Protocol.EndToEnd.Sound
