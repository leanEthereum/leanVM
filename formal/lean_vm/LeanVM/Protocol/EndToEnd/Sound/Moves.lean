/-
  LeanVM.Protocol.EndToEnd.Sound.Moves

  The prover moves a verifier program allows: a structural predicate on programs of the verifier
  language (which proofs of work it checks, whether it reads commitments), its rules, and its
  instances on every phase of leanVM's deployed verifier program.
-/

module

public import LeanVM.Protocol.Compile.Spec
public import LeanVM.Protocol.Verifier

/-!
# The prover moves of the leanVM verifier

`MovesOK g c p` says that every proof of work `p` checks has its bits in `g`, and that `p` reads a
commitment only if `c` holds. It is a structural predicate on the program, with no arithmetic,
and it composes through `bind` (`MovesOK.bind`, `MovesOK.seq`) and survives along histories
(`MovesOK.after`). Its two uses:

* `MovesOK.reach_commits`: a sub-program that reads no commitment (`c := False`) adds none to a
  run, so the words its openings answer from are the ones committed before it;
* `MovesOK.grindBits_le`: on a program whose proofs of work have at most `B` bits, every reachable
  history ends with a proof of work of at most `B` bits.

The instances follow the phases of `leanVmProgram` (`LeanVM.Protocol.Verifier`) with the
unfoldings and inductions of `LeanVM.Protocol.Verifier.Cost`: the sizes, the bus, the table
sumcheck, the public input, Flock and ring switching make no prover move other than reads; the
stack's root is the one commitment outside WHIR; the stacked opening commits WHIR's levels and
checks WHIR's query proofs of work, of `Whir.queryGrindingBits = 17` bits. Hence
`grind_bits_eq`: every proof of work of the leanVM verifier has exactly `17` bits (the
completeness theorem's one condition on the hash: its `17`-bit search succeeds), and
`grindBits_le_of_reachable`: every reachable history ends with a proof of work of at most `64`
bits, the cap at which the random-oracle theorem discounts a group's escape
(`LeanVM.Protocol.Compile.Rom.Step`).

## Deployed behaviour

The statements are on the program `leanVmProgram` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, as transcribed in `LeanVM.Protocol.Verifier`.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {α β : Type}

/-! ## The predicate -/

/-- Every prover move of `p` is allowed: every proof of work's bits satisfy `g`, and a commitment
occurs only if `c`. -/
def MovesOK (g : ℕ → Prop) (c : Prop) : Prog α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, MovesOK g c (k x)
  | .sample k => ∀ x, MovesOK g c (k x)
  | .grind b k => g b ∧ MovesOK g c k
  | .commit _ _ k => c ∧ MovesOK g c k
  | .query _ _ k => ∀ rows, MovesOK g c (k rows)

namespace MovesOK

variable {g : ℕ → Prop} {c : Prop}

/-- Monotonicity in the allowed proofs of work and commitments. -/
theorem mono {g g' : ℕ → Prop} {c c' : Prop} (hg : ∀ b, g b → g' b) (hc : c → c') :
    ∀ {p : Prog α}, MovesOK g c p → MovesOK g' c' p
  | .ret _, _ => trivial
  | .fail, _ => trivial
  | .read _, h => fun x ↦ mono hg hc (h x)
  | .sample _, h => fun x ↦ mono hg hc (h x)
  | .grind b _, h => ⟨hg b h.1, mono hg hc h.2⟩
  | .commit _ _ _, h => ⟨hc h.1, mono hg hc h.2⟩
  | .query _ _ _, h => fun rows ↦ mono hg hc (h rows)

/-- A program with no prover move other than reads is allowed under any constraint. -/
theorem of_none {g : ℕ → Prop} {c : Prop} {p : Prog α} (h : MovesOK (fun _ ↦ False) False p) :
    MovesOK g c p :=
  mono (fun _ h ↦ h.elim) False.elim h

/-- **Sequencing.** -/
theorem bind {p : Prog α} {f : α → Prog β} (hp : MovesOK g c p) (hf : ∀ a, MovesOK g c (f a)) :
    MovesOK g c (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ⟨hp.1, ih hp.2⟩
  | commit ht w k ih => exact ⟨hp.1, ih hp.2⟩
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

/-- Sequencing in `do` notation. -/
theorem seq {p : Prog α} {f : α → Prog β} (hp : MovesOK g c p) (hf : ∀ a, MovesOK g c (f a)) :
    MovesOK g c (p >>= f) :=
  bind hp hf

/-- A return is allowed. -/
theorem ret (a : α) : MovesOK g c (Prog.ret a) := trivial

/-- A rejection is allowed. -/
theorem fail : MovesOK g c (Prog.fail : Prog α) := trivial

/-- `pure` is allowed. -/
theorem pure (a : α) : MovesOK g c (Pure.pure a : Prog α) := trivial

/-- A read is allowed. -/
theorem readE : MovesOK g c Prog.readE := fun _ ↦ trivial

/-- A sample is allowed. -/
theorem sampleE : MovesOK g c Prog.sampleE := fun _ ↦ trivial

/-- `n` reads are allowed. -/
theorem readN : ∀ n, MovesOK g c (Prog.readN n)
  | 0 => trivial
  | n + 1 => seq readE fun _ ↦ seq (readN n) fun _ ↦ trivial

/-- `n` samples are allowed. -/
theorem sampleN : ∀ n, MovesOK g c (Prog.sampleN n)
  | 0 => trivial
  | n + 1 => seq sampleE fun _ ↦ seq (sampleN n) fun _ ↦ trivial

/-- A check is allowed. -/
theorem require (q : Prop) [Decidable q] : MovesOK g c (Prog.require q) := by
  unfold Prog.require
  split <;> trivial

/-- A pure step that may fail is allowed. -/
theorem liftOption (o : Option α) : MovesOK g c (Verifier.liftOption o) := by
  cases o <;> trivial

/-- A proof of work is allowed when its bits are. -/
theorem grindP {b : ℕ} (hb : g b) : MovesOK g c (Prog.grindP b) := ⟨hb, trivial⟩

/-- A commitment is allowed when commitments are. -/
theorem commitP (hc : c) (ht w : ℕ) : MovesOK g c (Prog.commitP ht w) := ⟨hc, trivial⟩

/-- An opening is allowed. -/
theorem queryP (i : ℕ) (ps : List ℕ) : MovesOK g c (Prog.queryP i ps) := fun _ ↦ trivial

/-- A conditional is allowed when both branches are. -/
theorem ite {q : Prop} [Decidable q] {p p' : Prog α} (hp : q → MovesOK g c p)
    (hp' : ¬ q → MovesOK g c p') : MovesOK g c (if q then p else p') := by
  split
  · exact hp ‹_›
  · exact hp' ‹_›

/-! ## Along histories -/

/-- The program after a history of an allowed program is allowed. -/
theorem after {p : Prog α} (hp : MovesOK g c p) :
    ∀ {l : List Ev} {q : Prog α}, p.after l = some q → MovesOK g c q := by
  induction p with
  | ret a =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [Prog.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp [Prog.after] at h
  | fail =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [Prog.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp [Prog.after] at h
  | read k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [Prog.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [Prog.after, reduceCtorEq] at h
      exact ih _ (hp _) h
  | sample k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [Prog.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [Prog.after, reduceCtorEq] at h
      exact ih _ (hp _) h
  | grind b k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [Prog.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [Prog.after, reduceCtorEq] at h
      split at h
      · exact ih hp.2 h
      · cases h
  | commit ht w k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [Prog.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [Prog.after, reduceCtorEq] at h
      split at h
      · exact ih hp.2 h
      · cases h
  | query i ps k ih =>
    intro l q h
    rcases l with _ | ⟨e, l⟩
    · simp only [Prog.after, Option.some.injEq] at h
      exact h ▸ hp
    · cases e <;> simp only [Prog.after, reduceCtorEq] at h
      exact ih _ (hp _) h

/-- The commitments of a history extended by one event. -/
private theorem commits_snoc (l : List Ev) (e : Ev) :
    commits (l ++ [e]) = commits l ++ commits [e] := by
  induction l with
  | nil => rfl
  | cons e' l ih => cases e' <;> simp [commits, ih]

/-- A program without commitments commits nothing along a run. -/
theorem reach_commits {g : ℕ → Prop} {p : Prog α} (hp : MovesOK g False p) {h₀ l : List Ev}
    (hl : p.Reach h₀ l) : commits l = [] := by
  induction hl with
  | nil => rfl
  | read x _ _ ih => simp [commits_snoc, ih, commits]
  | sample c _ _ ih => simp [commits_snoc, ih, commits]
  | grind _ _ ih => simp [commits_snoc, ih, commits]
  | commit word _ ha _ _ => exact ((hp.after ha).1).elim
  | query _ _ _ ih => simp [commits_snoc, ih, commits]

/-- Along a reachable history, the last proof of work's bits are at most `B`. -/
theorem grindBits_le {B : ℕ} {c : Prop} {P : Prog α} (hP : MovesOK (· ≤ B) c P) {h : List Ev}
    (hh : P.Reachable h) : grindBits h ≤ B := by
  cases hh with
  | nil => simp [grindBits]
  | read x _ _ => simp [grindBits]
  | sample x _ _ => simp [grindBits]
  | grind _ ha => simpa [grindBits] using (hP.after ha).1
  | commit word _ _ _ => simp [grindBits]
  | query _ _ _ => simp [grindBits]

end MovesOK

section Phases

/- The phases' programs are large closed terms; `MovesOK` is kept folded so that elaborating a
rule's conclusion does not unfold the program it is about. -/
attribute [local irreducible] MovesOK

/-! ## Sumcheck and the bus -/

/-- A round polynomial is reads. -/
theorem movesOK_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    MovesOK (fun _ ↦ False) False (sumcheckRoundPoly count claim eq) := by
  cases eq with
  | none =>
    exact MovesOK.seq MovesOK.readE fun _ ↦ MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.pure _
  | some r => exact MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.pure _

/-- A sumcheck is reads and samples. -/
theorem movesOK_sumcheck (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    MovesOK (fun _ ↦ False) False (sumcheck claim count eqs)
  | _, [] => MovesOK.pure _
  | claim, e :: es =>
    MovesOK.seq (movesOK_sumcheckRoundPoly count claim e) fun _ ↦
      MovesOK.seq MovesOK.sampleE fun _ ↦
        MovesOK.seq (movesOK_sumcheck count _ es) fun r ↦ by
          obtain ⟨point, final⟩ := r
          exact MovesOK.pure _

/-- One GKR step is reads and samples. -/
theorem movesOK_gkrStep (step : ℕ) (s : GkrState) :
    MovesOK (fun _ ↦ False) False (gkrStep step s) := by
  refine MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨x, claim⟩ := r
  exact MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.seq (MovesOK.readN _) fun _ ↦
    MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.seq (MovesOK.require _) fun _ ↦
      MovesOK.seq (MovesOK.sampleN _) fun _ ↦ MovesOK.pure _

/-- The GKR walk is reads and samples. -/
theorem movesOK_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    MovesOK (fun _ ↦ False) False (gkrLayers n s)
  | 0, _ => MovesOK.pure _
  | 1, s => MovesOK.seq (movesOK_gkrStep 1 s) fun t ↦ movesOK_gkrLayers 0 t
  | n + 2, s => by
    simp only [gkrLayers]
    split
    · exact MovesOK.seq (movesOK_gkrStep 1 s) fun t ↦ movesOK_gkrLayers (n + 1) t
    · exact MovesOK.seq (movesOK_gkrStep 2 s) fun t ↦ movesOK_gkrLayers n t

/-- The GKR grand products are reads and samples. -/
theorem movesOK_verifyGkrGrandProducts (depth : ℕ) :
    MovesOK (fun _ ↦ False) False (verifyGkrGrandProducts depth) :=
  MovesOK.seq MovesOK.readE fun _ ↦ MovesOK.seq MovesOK.readE fun _ ↦
    MovesOK.seq (movesOK_gkrLayers depth _) fun _ ↦ MovesOK.pure _

/-- The bus makes no prover move other than reads. -/
theorem movesOK_verifyBusBalance (layout : Layout) :
    MovesOK (fun _ ↦ False) False (verifyBusBalance .computed layout) := by
  refine MovesOK.seq (MovesOK.sampleN _) fun _ ↦ MovesOK.seq MovesOK.sampleE fun _ ↦
    MovesOK.seq (movesOK_verifyGkrGrandProducts _) fun r ↦ ?_
  obtain ⟨countRoot, point, treeValues⟩ := r
  exact MovesOK.seq (MovesOK.require _) fun _ ↦ MovesOK.seq (MovesOK.readN 3) fun _ ↦
    MovesOK.seq MovesOK.readE fun _ ↦ MovesOK.seq MovesOK.readE fun _ ↦
      MovesOK.seq (MovesOK.pure _) fun _ ↦ MovesOK.pure _

/-! ## The sizes, the table sumcheck and the public input -/

/-- The announced sizes are reads. -/
theorem movesOK_readSizes (bytecode : List K) :
    MovesOK (fun _ ↦ False) False (readSizes bytecode) :=
  MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.seq (MovesOK.require _) fun _ ↦
    MovesOK.seq (MovesOK.require _) fun _ ↦ MovesOK.seq (MovesOK.liftOption _) fun _ ↦
      MovesOK.seq (MovesOK.require _) fun _ ↦ MovesOK.pure _

/-- The tables' row evaluations are reads. -/
theorem movesOK_tableTerms (constraintPowers formPowers point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim),
      MovesOK (fun _ ↦ False) False
        (tableTerms constraintPowers formPowers point rows cursor final claims)
  | [], _, _, _ => MovesOK.pure _
  | (_, _, _, _) :: rest, _, _, _ =>
    MovesOK.seq (MovesOK.readN _) fun _ ↦
      movesOK_tableTerms constraintPowers formPowers point rest _ _ _

/-- The table sumcheck is reads and samples. -/
theorem movesOK_tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    MovesOK (fun _ ↦ False) False
      (tableSumcheck heights busForms constraintPowers formPowers equalityPoint target) := by
  refine MovesOK.seq (movesOK_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨challenges, claim⟩ := r
  refine MovesOK.seq (movesOK_tableTerms _ _ _ _ 0 0 []) fun r ↦ ?_
  obtain ⟨final, claims⟩ := r
  exact MovesOK.seq (MovesOK.require _) fun _ ↦ MovesOK.pure _

/-- The table phase makes no prover move other than reads. -/
theorem movesOK_tablePhase (layout : Layout) (bus : BusResult) :
    MovesOK (fun _ ↦ False) False (tablePhase layout bus) :=
  MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_tableSumcheck _ _ _ _ _ _) fun _ ↦
    MovesOK.pure _

/-- The public-input phase makes no prover move: one challenge. -/
theorem movesOK_publicInputPhase (layout : Layout) (publicInput : Digest) :
    MovesOK (fun _ ↦ False) False (publicInputPhase layout publicInput) :=
  MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.pure _

/-! ## Flock and ring switching -/

/-- The Flock zerocheck is reads and samples. -/
theorem movesOK_verifyFlockZerocheck (logN : ℕ) :
    MovesOK (fun _ ↦ False) False (verifyFlockZerocheck logN) := by
  refine MovesOK.seq (MovesOK.sampleN _) fun _ ↦ MovesOK.seq (MovesOK.readN _) fun _ ↦
    MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨chi, running⟩ := r
  exact MovesOK.seq MovesOK.readE fun _ ↦ MovesOK.seq MovesOK.readE fun _ ↦ MovesOK.pure _

/-- The Flock lincheck is reads and samples. -/
theorem movesOK_verifyFlockLincheck (zc : ZerocheckResult) :
    MovesOK (fun _ ↦ False) False (verifyFlockLincheck .computed zc) := by
  refine MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨roundChallenges, rLc⟩ := r
  exact MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.seq (MovesOK.pure _) fun _ ↦
    MovesOK.seq (MovesOK.require _) fun _ ↦ MovesOK.pure _

/-- Flock makes no prover move other than reads. -/
theorem movesOK_verifyFlock (logN : ℕ) :
    MovesOK (fun _ ↦ False) False (verifyFlock .computed logN) :=
  MovesOK.seq (movesOK_verifyFlockZerocheck logN) fun zc ↦ movesOK_verifyFlockLincheck zc

/-- Ring switching only samples. -/
theorem movesOK_ringSwitch (point s : List E) :
    MovesOK (fun _ ↦ False) False (ringSwitch point s) :=
  MovesOK.seq (MovesOK.sampleN _) fun _ ↦ MovesOK.pure _

/-! ## WHIR -/

/-- A WHIR level's fold rounds are reads and samples. -/
theorem movesOK_foldRounds : ∀ (n : ℕ) (s : WhirState) (levelFolds : List E),
    MovesOK (fun _ ↦ False) False (foldRounds n s levelFolds)
  | 0, _, _ => MovesOK.pure _
  | n + 1, _, _ =>
    MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.seq (movesOK_sumcheckRoundPoly 3 _ none)
      fun _ ↦ movesOK_foldRounds n _ _

/-- The final WHIR level's tail rounds are reads and samples. -/
theorem movesOK_tailRounds : ∀ (n : ℕ) (target : E) (quad : List E),
    MovesOK (fun _ ↦ False) False (tailRounds n target quad)
  | 0, _, _ => MovesOK.pure _
  | n + 1, _, _ =>
    MovesOK.seq MovesOK.sampleE fun _ ↦ MovesOK.ite (fun _ ↦ MovesOK.pure _) fun _ ↦
      MovesOK.seq (movesOK_sumcheckRoundPoly 3 _ none) fun _ ↦
        MovesOK.seq (movesOK_tailRounds n _ _) fun r ↦ by
          obtain ⟨rest, target⟩ := r
          exact MovesOK.pure _

/-- The query sampling loop only samples. -/
theorem movesOK_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    MovesOK (fun _ ↦ False) False (sampleQueriesAux depth fuel remaining)
  | 0, _ => MovesOK.pure _
  | fuel + 1, _ =>
    MovesOK.ite (fun _ ↦ MovesOK.pure _) fun _ ↦ MovesOK.seq MovesOK.sampleE fun _ ↦
      MovesOK.seq (movesOK_sampleQueriesAux depth fuel _) fun _ ↦ MovesOK.pure _

/-- WHIR's query proof of work has at most `64` bits. -/
theorem queryGrindingBits_le : Whir.queryGrindingBits ≤ 64 := by decide

/-- The WHIR levels: commitments, and proofs of work of `Whir.queryGrindingBits` bits. -/
theorem movesOK_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState),
      MovesOK (· = Whir.queryGrindingBits) True (whirLevels logN laneFolds evaluateBasis index levels s)
  | [], _, _ => MovesOK.fail
  | [level], index, s => by
    refine MovesOK.seq (MovesOK.of_none (movesOK_foldRounds level.fold s [])) fun r ↦ ?_
    obtain ⟨s', levelFolds⟩ := r
    refine MovesOK.seq (MovesOK.readN _) fun _ ↦ MovesOK.seq (MovesOK.pure _) fun _ ↦
      MovesOK.seq (MovesOK.grindP rfl) fun _ ↦
        MovesOK.seq (MovesOK.of_none (movesOK_sampleQueriesAux _ _ _)) fun queries ↦
          MovesOK.seq MovesOK.sampleE fun lam ↦ MovesOK.seq (MovesOK.queryP index queries)
            fun words ↦ MovesOK.seq (MovesOK.of_none (movesOK_sumcheckRoundPoly 3 _ none))
              fun intro ↦ MovesOK.seq (MovesOK.of_none (movesOK_tailRounds _ _ _)) fun r ↦ ?_
    obtain ⟨tailFolds, target⟩ := r
    exact MovesOK.require _
  | level :: next :: rest, index, s => by
    refine MovesOK.seq (MovesOK.of_none (movesOK_foldRounds level.fold s [])) fun r ↦ ?_
    obtain ⟨s', levelFolds⟩ := r
    exact MovesOK.seq (MovesOK.commitP trivial _ _) fun _ ↦
      MovesOK.seq (MovesOK.sampleN _) fun _ ↦ MovesOK.seq MovesOK.readE fun _ ↦
        MovesOK.seq (MovesOK.of_none (movesOK_sumcheckRoundPoly 3 _ none)) fun _ ↦
          MovesOK.seq (MovesOK.pure _) fun _ ↦
            MovesOK.seq (MovesOK.grindP rfl) fun _ ↦
              MovesOK.seq (MovesOK.of_none (movesOK_sampleQueriesAux _ _ _)) fun queries ↦
                MovesOK.seq MovesOK.sampleE fun lam ↦
                  MovesOK.seq (MovesOK.queryP index queries) fun words ↦
                    MovesOK.seq (MovesOK.of_none (movesOK_sumcheckRoundPoly 3 _ none))
                      fun intro ↦ movesOK_whirLevels logN laneFolds evaluateBasis
                        (next :: rest) (index + 1) _

/-- WHIR: its levels' commitments, and proofs of work of `Whir.queryGrindingBits` bits. -/
theorem movesOK_verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) :
    MovesOK (· = Whir.queryGrindingBits) True (verifyWhir logN logInvRate target evaluateBasis) :=
  MovesOK.seq (MovesOK.liftOption _) fun config ↦
    MovesOK.seq (MovesOK.of_none (movesOK_sumcheckRoundPoly 3 _ none)) fun _ ↦
      movesOK_whirLevels logN _ evaluateBasis config 0 _

/-- The stack's root: one commitment, no proof of work. -/
theorem movesOK_commitStack (logN logInvRate : ℕ) :
    MovesOK (fun _ ↦ False) True (commitStack logN logInvRate) := by
  refine MovesOK.seq (MovesOK.liftOption _) fun config ↦ ?_
  cases config with
  | nil => exact MovesOK.fail
  | cons level rest => exact MovesOK.commitP trivial _ _

/-- The stacked opening: WHIR's commitments and its proofs of work of `Whir.queryGrindingBits`
bits. -/
theorem movesOK_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    MovesOK (· = Whir.queryGrindingBits) True (verifyStackedOpening stackLog logInvRate claims) :=
  MovesOK.seq MovesOK.sampleE fun _ ↦ movesOK_verifyWhir _ _ _ _

/-! ## The whole program -/

/-- `verify_execution`: commitments, and proofs of work of `Whir.queryGrindingBits` bits. -/
theorem movesOK_verifyExecution (bytecode : List K) (publicInput : Digest) :
    MovesOK (· = Whir.queryGrindingBits) True (verifyExecution .computed bytecode publicInput) := by
  refine MovesOK.seq (MovesOK.of_none (movesOK_readSizes bytecode)) fun p ↦ ?_
  obtain ⟨layout, logInverseRate⟩ := p
  refine MovesOK.seq ((movesOK_commitStack _ _).mono (fun _ h ↦ h.elim) id) fun _ ↦
    MovesOK.seq (MovesOK.of_none (movesOK_verifyBusBalance layout)) fun bus ↦
      MovesOK.seq (MovesOK.of_none (movesOK_tablePhase layout bus)) fun _ ↦
        MovesOK.seq (MovesOK.of_none (movesOK_publicInputPhase layout publicInput)) fun _ ↦
          MovesOK.seq (MovesOK.of_none (movesOK_verifyFlock _)) fun r ↦ ?_
  obtain ⟨flockPoint, flockS⟩ := r
  refine MovesOK.seq (MovesOK.of_none (movesOK_ringSwitch flockPoint flockS)) fun r ↦ ?_
  obtain ⟨ringTarget, ringWeight⟩ := r
  exact movesOK_verifyStackedOpening _ _ _

end Phases

/-- **The leanVM verifier program**: its commitments, and proofs of work of
`Whir.queryGrindingBits = 17` bits. -/
theorem movesOK_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    MovesOK (· = Whir.queryGrindingBits) True (leanVmProgram bytecode publicInput) :=
  MovesOK.seq (movesOK_verifyExecution bytecode publicInput) fun _ ↦ MovesOK.pure _

/-- **Every reachable history of the leanVM verifier ends with a proof of work of at most 64
bits.** -/
theorem grindBits_le_of_reachable (bytecode : List K) (publicInput : Digest) {h : List Ev}
    (hh : (leanVmProgram bytecode publicInput).Reachable h) : grindBits h ≤ 64 :=
  ((movesOK_leanVmProgram bytecode publicInput).mono (fun _ hb ↦ hb ▸ queryGrindingBits_le)
    id).grindBits_le hh

/-- **Every proof of work of the leanVM verifier has `Whir.queryGrindingBits = 17` bits**, along
any history. -/
theorem grind_bits_eq (bytecode : List K) (publicInput : Digest) {h : List Ev} {bits : ℕ}
    {k : Prog Bool} (hg : (leanVmProgram bytecode publicInput).after h = some (.grind bits k)) :
    bits = Whir.queryGrindingBits :=
  ((movesOK_leanVmProgram bytecode publicInput).after hg).1

end
end LeanVM.Protocol.EndToEnd.Sound
